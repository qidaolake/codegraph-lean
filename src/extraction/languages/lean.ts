/**
 * Lean 4 extraction configuration.
 *
 * Grammar: Julian/tree-sitter-lean (MIT), vendored as
 * `src/extraction/wasm/tree-sitter-lean.wasm`. Node names mirror Lean's own
 * `SyntaxNodeKind`s (`Lean.Parser.Command.import` → `import`).
 *
 * ---------------------------------------------------------------------------
 * WHY THIS EXTRACTOR DRIVES ITS OWN WALK
 * ---------------------------------------------------------------------------
 * Unlike the other language configs, this one takes over the traversal at the
 * `module` root (see `visitNode`) instead of declaring node-type lists and
 * letting the core dispatch. Four Lean-specific facts force that:
 *
 * 1. **`namespace`/`section` are top-level SIBLINGS, not containers.** The
 *    declarations they scope are not their children, so the core's
 *    containment-derived scope stack can never produce a qualified name. Lean
 *    code references `Sanctions.clipS'` while the declaration is written
 *    `clipS'` inside `namespace Sanctions` — without qualification those
 *    references are permanently dead. Driving the walk lets us keep an O(n)
 *    namespace stack in a local variable (no cross-file state on this shared
 *    singleton) and hand each node an explicit dotted `qualifiedName`.
 *
 * 2. **`structure` / `class` / `inductive` have no `body:` field.** Their
 *    members are direct children. `extractAggregate` bails on a missing body
 *    (and, unlike its twin `extractEnum`, never consults `resolveBody`), so
 *    every Lean type declaration produced *no node at all* — measured at zero
 *    struct/enum nodes across 9,006 indexed Mathlib files against 1,787
 *    `structure` + 2,027 `class` + 349 `inductive` in source.
 *
 * 3. **A theorem's dependencies live in its SIGNATURE, not only its proof.**
 *    `theorem foo {α} [Monoid α] (h : IsUnit x) : MyGoal` depends on `Monoid`,
 *    `IsUnit` and `MyGoal` regardless of how it is proved. The core only ever
 *    walks the body, so `signature`/`return_type` were NULL on every Lean node
 *    and ~79k instance-implicit class dependencies were invisible.
 *
 * 4. **Binders separate `name:` from `type:` structurally.** That is what makes
 *    (3) safe: we walk only `type:` subtrees, so a binder NAME can never be
 *    mistaken for a reference. This matters — in one 315-file Mathlib slice,
 *    106 of 472 binder names collide with real declaration names, so a
 *    naive "walk the signature" would manufacture wrong edges wholesale.
 *
 * ---------------------------------------------------------------------------
 * CONTRACT: CITED DEPENDENCIES, NOT SEMANTIC ONES
 * ---------------------------------------------------------------------------
 * This extractor records what the source text *names*. It deliberately does not
 * attempt: typeclass instance resolution, simp-set closure under bare `simp`,
 * coercion insertion, macro-generated declarations, or generalized dot notation
 * (`b.foo` needs the type of `b`). All of those are decided during elaboration
 * and leave no token behind. For those, Lean's own tooling is the answer —
 * `.ilean` files, or `ConstantInfo.value!.getUsedConstants` over a built
 * environment. Treat a Lean `callers`/`impact` answer as "who cites this",
 * which for a formalization is usually the question anyway.
 */

import type { Node as SyntaxNode } from 'web-tree-sitter';
import { getNodeText } from '../tree-sitter-helpers';
import type { ExtractorContext, ImportInfo, LanguageExtractor } from '../tree-sitter-types';
import type { NodeKind } from '../../types';

// ---------------------------------------------------------------------------
// Filtering
// ---------------------------------------------------------------------------

/**
 * Tactic names, structural keywords and proof-term primitives that appear in
 * identifier position but are never a project declaration.
 *
 * Tuned against four corpora: a private development, then `batteries` (whose
 * test suite is built out of `guard_target`/`fail_if_success`) and `mathlib4`
 * itself (which surfaced `simp_rw` 6,825× and `filter_upwards` 1,420×). Every
 * entry here was, at some point, a top-ranked false "external dependency".
 */
const TACTIC_STOPWORDS: ReadonlySet<string> = new Set([
  // core tactics
  'simp', 'simpa', 'dsimp', 'rfl', 'exact', 'exact_mod_cast', 'intro', 'intros',
  'apply', 'rw', 'rwa', 'refine', 'use', 'have', 'show', 'calc',
  'assumption', 'contradiction', 'trivial', 'decide', 'rcases', 'obtain',
  'cases', 'rintro', 'induction', 'unfold', 'subst', 'congr', 'ext', 'funext',
  'constructor', 'exfalso', 'left', 'right', 'split', 'specialize', 'revert',
  'change', 'convert', 'set', 'let', 'fun', 'match', 'with', 'from', 'this',
  'by', 'do', 'then', 'else', 'return', 'pure', 'try', 'repeat', 'all_goals',
  'any_goals', 'first', 'skip', 'done', 'stop', 'guard', 'clear', 'rename',
  // automation
  'ring', 'ring_nf', 'omega', 'linarith', 'nlinarith', 'polyrith', 'positivity',
  'norm_num', 'norm_cast', 'push_cast', 'field_simp', 'aesop', 'tauto',
  'gcongr', 'bound', 'measurability', 'continuity', 'fun_prop', 'monotonicity',
  'interval_cases', 'fin_cases', 'linear_combination',
  // test/meta tactics and declaration keywords (batteries)
  'simp_all', 'simp_arith', 'simp_rw', 'guard_target', 'guard_hyp', 'guard_expr',
  'fail_if_success', 'success_if_fail', 'termination_by', 'decreasing_by',
  'rename_i', 'next', 'case', 'focus', 'iterate', 'conv', 'norm_fin',
  'push_neg', 'by_cases', 'by_contra', 'split_ands', 'split_ifs', 'omega_nat',
  'exists',
  // high-volume tactic names surfaced by indexing mathlib4 itself
  'filter_upwards', 'infer_instance', 'norm_num1', 'gcongr_discharger',
  'apply_fun', 'field_simp_discharge', 'ext1', 'obtain_or', 'rcases_or',
  'inferInstanceAs', 'inferInstance', 'exact_mod_cast', 'push_cast', 'norm_num2',
]);

/** Synthetic target for `sorry`, so "what depends on an unproven lemma" is a graph query. */
const SORRY_AX = 'sorryAx';

/**
 * Does this identifier look like a reference to a real declaration?
 *
 * Lean naming convention does most of the work: lemma names are snake_case
 * (`add_zero_eq`), cross-namespace references are dotted (`Nat.add_comm`), and
 * types are PascalCase (`RegularEconomyCertificate`). Local hypotheses and
 * binders are short lowercase (`h`, `hx`, `ih`) and tactics are lowercase words.
 *
 * Tuned to be QUIET: a missed reference costs one edge, a false one pollutes
 * every impact query that passes through it.
 */
function isLikelyDeclarationRef(name: string, inLemmaList = false): boolean {
  if (name.length < 3) return false;
  if (TACTIC_STOPWORDS.has(name)) return false;

  const dot = name.indexOf('.');
  if (dot >= 0) {
    // A dotted name is either a namespace-qualified reference (`Set.Icc`) or a
    // field projection off a local binder (`x.val`, `p.δ`). Binders in Lean
    // proofs are near-universally one or two characters and a real namespace
    // almost never is, so the head segment's length separates them. Projections
    // were the single largest source of junk rows in `unresolved_refs`.
    return dot > 2;
  }

  // Three naming classes, matching Lean/Mathlib convention:
  //   snake_case  → theorems and lemmas   (`add_zero_eq`)
  //   PascalCase  → types and structures  (`RegularEconomyCertificate`)
  //   camelCase   → DEFINITIONS           (`banachIter`, `cesaroAverage`, `clipS'`)
  // The camelCase class was missing until a spot-check showed `banachIter` — a
  // project definition cited in a theorem statement — being silently dropped.
  // It is the convention for `def`, so omitting it discarded the dependency edge
  // for a whole category of declaration. Require an interior capital and length
  // >= 4 so lowercase tactic words (`simp`, `omega`, `aesop`) still fall out.
  if (name.includes('_') || /^[A-Z]/.test(name)) return true;
  if (name.length >= 4 && /^[a-z][A-Za-z0-9]*[A-Z]/.test(name)) return true;
  // Plain all-lowercase (`b2clip`, `sqrt`, `deriv`) is a legitimate Lean
  // definition shape, but accepting it everywhere is a bad trade: measured at
  // +1,060 edges against +13,009 junk rows, because local hypothesis names
  // share the shape and can collide with a real declaration to make a WRONG
  // edge. Inside a tactic's bracketed lemma list it is safe — `norm_num
  // [b2sdyn, b2pt, b2clip, b2lam]` names four lemmas and nothing else.
  return inLemmaList && /^[a-z][a-z0-9]*$/.test(name);
}

/**
 * Normalise an identifier into the reference name to record, or null to drop it.
 *
 * Single source of truth for reference filtering. It exists because the filter
 * was previously inlined at each emission site, and the ERROR-rescue path was
 * then missed — leaving 704 `_root_.`-prefixed junk rows on mathlib that the
 * main path had already been fixed to strip.
 */
function normalizeRefName(name: string, inLemmaList = false): string | null {
  if (!name || name === '_root_') return null;
  // `_root_.Foo.bar` names a symbol absolutely, escaping the enclosing
  // namespace. `qualify` strips the marker from declaration names, so the
  // reference must be stripped identically or it can never match.
  const bare = name.startsWith('_root_.') ? name.slice('_root_.'.length) : name;
  return isLikelyDeclarationRef(bare, inLemmaList) ? bare : null;
}

// ---------------------------------------------------------------------------
// Small AST helpers
// ---------------------------------------------------------------------------

/**
 * Last NAMED child carrying `fieldName`.
 *
 * Never use `childForFieldName` on this grammar: it tags BOTH the punctuation
 * separator and the real payload with the same field, and returns the FIRST —
 * so `body` yields the `:=` token and `type` yields the `:` token. Taking the
 * last named child skips the separator in every form.
 */
function lastField(node: SyntaxNode, fieldName: string): SyntaxNode | null {
  let found: SyntaxNode | null = null;
  for (let i = 0; i < node.childCount; i++) {
    if (node.fieldNameForChild(i) !== fieldName) continue;
    const child = node.child(i);
    if (child && child.isNamed) found = child;
  }
  return found;
}

/** All named children carrying `fieldName` (Lean repeats `name:` on attributes, `namespace:` on open). */
function allFields(node: SyntaxNode, fieldName: string): SyntaxNode[] {
  const out: SyntaxNode[] = [];
  for (let i = 0; i < node.childCount; i++) {
    if (node.fieldNameForChild(i) !== fieldName) continue;
    const child = node.child(i);
    if (child && child.isNamed) out.push(child);
  }
  return out;
}

/** Named children of `node`, as an array. */
function namedChildren(node: SyntaxNode): SyntaxNode[] {
  const out: SyntaxNode[] = [];
  for (let i = 0; i < node.namedChildCount; i++) {
    const c = node.namedChild(i);
    if (c) out.push(c);
  }
  return out;
}

const BINDER_TYPES: ReadonlySet<string> = new Set([
  'explicit_binder', 'implicit_binder', 'instance_binder', 'strict_implicit_binder',
  'anonymous_binder', 'binder', 'simple_binder',
]);

/** Declaration node types we own, mapped to the graph's NodeKind vocabulary. */
const DECL_KINDS: ReadonlyMap<string, NodeKind> = new Map<string, NodeKind>([
  ['def', 'function'],
  ['theorem', 'function'],       // `lemma` normalizes to `theorem` in this grammar
  ['abbrev', 'function'],
  ['opaque', 'function'],
  ['axiom', 'function'],
  ['instance', 'function'],
  ['example', 'function'],
  ['structure', 'struct'],       // `class Foo where` also parses as `structure`
  ['inductive', 'enum'],
]);

// ---------------------------------------------------------------------------
// Reference emission
// ---------------------------------------------------------------------------

/**
 * Walk a subtree and emit a `calls` reference for every identifier that looks
 * like a declaration and is not locally bound.
 *
 * `locals` holds names bound by the enclosing declaration's binders (and by
 * section `variable`s). Suppressing them is what keeps the signature walk
 * honest — without it, a binder named `inf` or `comap` resolves to the
 * same-named Mathlib declaration and manufactures a wrong edge.
 *
 * We walk children unconditionally, INCLUDING through ERROR nodes: tactic
 * blocks frequently fail to parse (the grammar does not cover the full Mathlib
 * tactic set), but tree-sitter keeps lexing inside an ERROR, so the lemma names
 * are still present as `identifier` nodes. That is the whole reason proof
 * dependencies survive at all.
 */
function emitRefs(
  subtree: SyntaxNode | null,
  fromNodeId: string,
  ctx: ExtractorContext,
  locals: ReadonlySet<string>,
  declLines?: ReadonlyMap<number, string>,
  binderTypes?: ReadonlyMap<string, string>
): void {
  if (!subtree) return;

  const walk = (node: SyntaxNode, inLemmaList: boolean): void => {
    if (node.type === 'identifier') {
      const name = getNodeText(node, ctx.source).trim();
      // A declaration's own name at its own header is a binding occurrence, not
      // a citation. Without this, a declaration swallowed into a neighbour's
      // ERROR span gets a fabricated inbound edge from that neighbour.
      if (declLines !== undefined && declLines.get(node.startPosition.row) === name) return;
      if (name && !locals.has(name)) {
        const line = node.startPosition.row + 1;
        const column = node.startPosition.column;
        // Generalized dot notation off a binder whose type is written down.
        //
        // `C.hT_loss_margin` is a real citation, but the head is a binder, so
        // the general rule below drops it rather than resolve every `x.val`
        // and `p.δ` onto whatever happens to share the tail's name. When the
        // binder is declared `(C : p.StandardComplianceLocalCertificate)` the
        // owner is right there in the signature, no elaboration required —
        // emit `StandardComplianceLocalCertificate.hT_loss_margin` and let the
        // resolver's suffix match land it on that structure's field.
        //
        // Qualifying is the whole point. Emitting the bare tail instead
        // recovers the same declarations and takes cross-layer edges from 13
        // to 158, because `F_mem` and friends exist in several structures;
        // scoping the reference to the owner cannot make that mistake.
        const dotAt = name.indexOf('.');
        if (dotAt > 0 && binderTypes !== undefined) {
          const owner = binderTypes.get(name.slice(0, dotAt));
          if (owner !== undefined) {
            let tail = name.slice(dotAt + 1);
            const nextDot = tail.indexOf('.');
            if (nextDot > 0) tail = tail.slice(0, nextDot);
            // A one-character tail is fine: `solution.π` is a real field, and an
            // owner-scoped reference cannot collide the way a bare `π` would.
            // Requiring two characters silently dropped every such projection —
            // 18 previously-resolving `solution.π` edges on mathlib alone, which
            // is how the guard was caught. Only a numeric tail is excluded, being
            // tuple projection (`z.1`) rather than a name.
            if (tail.length >= 1 && !/^[0-9]+$/.test(tail) && !TACTIC_STOPWORDS.has(tail)) {
              ctx.addUnresolvedReference({
                fromNodeId,
                referenceName: `${owner}.${tail}`,
                referenceKind: 'calls',
                line,
                column,
              });
            }
            return;
          }
        }
        // `_root_.Foo.bar` escapes the enclosing namespace and names the symbol
        // absolutely. The marker itself is a resolution directive, not a symbol
        // (emitting it produced 1,537 junk rows on mathlib), and the REFERENCE
        // has to be stripped the same way `qualify` strips it from declaration
        // names — otherwise a `_root_.Foo.bar` citation can never match the node
        // stored as `Foo.bar`.
        const bare = normalizeRefName(name, inLemmaList);
        if (bare === null) return;
        ctx.addUnresolvedReference({ fromNodeId, referenceName: bare, referenceKind: 'calls', line, column });
        // `dualParams.F` / `lowDeltaShocked.smear` are dot notation: the head is
        // a real project definition and the tail is a projection we cannot
        // resolve without types. Emitting the HEAD as well converts what was
        // pure noise in `unresolved_refs` into a genuine dependency edge on the
        // definition being projected.
        const dot = bare.indexOf('.');
        if (dot > 2) {
          const head = bare.slice(0, dot);
          if (head !== '_root_' && !locals.has(head) && isLikelyDeclarationRef(head, inLemmaList)) {
            ctx.addUnresolvedReference({ fromNodeId, referenceName: head, referenceKind: 'calls', line, column });
          }
        }
      }
      return;
    }

    // `sorry` is not a dependency in the ordinary sense, but "what transitively
    // depends on an unproven lemma" is the highest-value query in a live
    // formalization, so route it to a synthetic target.
    if (node.type === 'sorry') {
      ctx.addUnresolvedReference({
        fromNodeId,
        referenceName: SORRY_AX,
        referenceKind: 'calls',
        line: node.startPosition.row + 1,
        column: node.startPosition.column,
      });
      return;
    }

    for (let i = 0; i < node.namedChildCount; i++) {
      const child = node.namedChild(i);
      // A declaration nested inside this subtree (typically one swallowed by an
      // ERROR span) owns its own citations — attributing them to the enclosing
      // declaration would invent dependencies it does not have.
      // `[foo, bar]` after a tactic is a lemma list, not an expression.
      if (child && !DECL_KINDS.has(child.type)) walk(child, inLemmaList || node.type === 'list_lit');
    }
  };

  walk(subtree, false);
}

/**
 * Collect binder names (binding occurrences) and emit refs from their TYPES.
 *
 * Also records each binder's declared type head in `binderTypes`, which is what
 * lets `emitRefs` resolve `C.hT_loss_margin` — see {@link typeHeadOf}.
 */
function processBinders(
  binderHost: SyntaxNode | null,
  fromNodeId: string | null,
  ctx: ExtractorContext,
  locals: Set<string>,
  binderTypes?: Map<string, string>
): void {
  if (!binderHost) return;
  for (const binder of namedChildren(binderHost)) {
    if (!BINDER_TYPES.has(binder.type)) continue;
    const typeNode = lastField(binder, 'type');
    const owner = binderTypes ? typeHeadOf(typeNode, ctx.source) : null;
    // Binding occurrences: record as local, never emit.
    for (const nameNode of allFields(binder, 'name')) {
      const n = getNodeText(nameNode, ctx.source).trim();
      if (!n) continue;
      locals.add(n);
      if (owner && binderTypes) binderTypes.set(n, owner);
    }
    // The TYPE is the dependency — `[Monoid α]`, `(h : IsUnit x)`.
    if (fromNodeId) emitRefs(lastField(binder, 'type'), fromNodeId, ctx, locals);
  }
}

/**
 * The name of the structure a binder's type denotes, or null.
 *
 * `(C : p.StandardComplianceLocalCertificate)` → `StandardComplianceLocalCertificate`
 * `(h : Semi F M)`                            → `Semi`
 * `{α : Type*}` / `(n : ℕ)`                   → null (not a project structure)
 *
 * Only the head matters: arguments are irrelevant to which structure owns the
 * field, and the leading segments are a namespace path that the resolver's
 * suffix match handles.
 */
function typeHeadOf(typeNode: SyntaxNode | null, source: string): string | null {
  let node = typeNode;
  // `Semi F M` parses as nested `app`s; the leftmost `fn` is the head.
  while (node && node.type === 'app') node = lastField(node, 'fn') ?? node.namedChild(0);
  if (!node || node.type !== 'identifier') return null;
  const text = getNodeText(node, source).trim();
  if (!text) return null;
  const head = text.slice(text.lastIndexOf('.') + 1);
  // A structure name is PascalCase in Lean convention. Requiring it keeps type
  // variables (`α`, `ι`) and abbreviations out, and costs nothing: a field can
  // only be projected off a structure.
  return /^[A-Z]/.test(head) ? head : null;
}

/**
 * Collect every name BOUND inside a subtree — tactic hypotheses and lambda
 * parameters, not just the declaration's own binders.
 *
 * Lean hypothesis names are shaped exactly like lemma names (`hV_T_gain`,
 * `h_stage_sender`, `hFsc`), so `isLikelyDeclarationRef` cannot tell them
 * apart. Without this pass a `have h_stage_sender : … := …` emits a reference
 * at its binding site AND at every later use; if some other file happens to
 * declare a real theorem of that name each one becomes a WRONG edge, and if
 * not, a junk `unresolved_refs` row. Measured on a 331-file development: 118
 * edges crossing from `Theory/`+`Foundations/` into `Examples/` — a layering
 * violation that would have been alarming had it been real. Every one was a
 * local hypothesis, and the import graph confirms no such import exists.
 *
 * The grammar makes this cheap: `have`/`obtain`/`set`/`let` all parse as
 * `have` or `let` carrying a `name:` field — either an `identifier` or an
 * `anon_ctor_binder` holding the destructured names of an `obtain ⟨a, b, c⟩`.
 * `fun x hx => …` puts bare identifiers under `binders`.
 *
 * `intro x hx` and `rcases … with ⟨ha, hb⟩` parse as plain applications, so
 * their bindings are indistinguishable from arguments and are NOT collected.
 * That is tolerable because those names are near-universally one or two
 * characters, which `isLikelyDeclarationRef` already rejects on length.
 */
function collectBoundNames(
  root: SyntaxNode | null,
  source: string,
  visit: (name: string, row: number) => void
): void {
  if (!root) return;

  // A binding position: a single identifier, or an `obtain`-style destructuring
  // whose DIRECT identifier children are the bound names. Deliberately does not
  // recurse further — an `anon_ctor_binder` can contain ERROR nodes (the `-`
  // placeholder in `⟨a, b, -⟩`) whose descendants are not binding occurrences.
  const takeName = (n: SyntaxNode | null): void => {
    if (!n) return;
    if (n.type === 'identifier') {
      const text = getNodeText(n, source).trim();
      // A binding occurrence is always a simple atom. A DOTTED name in binder
      // position is the grammar misreading an application — the `calc` block
      // `|U (Sanctions.clipS' (y + h)) - …|` parses as an `explicit_binder`
      // named `Sanctions.clipS'`. Trusting that suppressed 24 genuine
      // citations of `clipS'` in one file alone; this guard is what stops the
      // pass trading one class of wrong answer for another.
      if (text && !text.includes('.')) visit(text, n.startPosition.row);
      return;
    }
    if (n.type === 'anon_ctor_binder' || n.type === 'anon_ctor') {
      for (const child of namedChildren(n)) {
        if (child.type === 'identifier') takeName(child);
      }
    }
  };

  const walk = (node: SyntaxNode): void => {
    if (node.type === 'have' || node.type === 'let') {
      takeName(lastField(node, 'name'));
    } else if (node.type === 'fun') {
      const host = lastField(node, 'binders') ?? findChildByType(node, 'binders');
      if (host) {
        for (const child of namedChildren(host)) {
          if (child.type === 'identifier') takeName(child);
          else if (BINDER_TYPES.has(child.type)) for (const nn of allFields(child, 'name')) takeName(nn);
        }
      }
    } else if (BINDER_TYPES.has(node.type) && lastField(node, 'type') !== null) {
      // Declaration binders. Redundant with `processBinders` on the parsed
      // path, but the ERROR-span rescue has no binder handling of its own and
      // this is where it gets it — `(hFsc : SanctionSemiconcave F M)` on a
      // signature line the grammar could not structure.
      //
      // A `type:` field is REQUIRED here because this branch, unlike
      // `processBinders`, matches a binder node ANYWHERE in the tree rather
      // than only under the declaration's own `binders` host — so it sees
      // every parenthesised expression the grammar mislabels as a binder. The
      // shape this exists to catch is always written `(name : type)`; without
      // the colon it is an application, not a binding.
      for (const nn of allFields(node, 'name')) takeName(nn);
    }
    for (const child of namedChildren(node)) walk(child);
  };
  walk(root);
}

// ---------------------------------------------------------------------------
// Declaration handling
// ---------------------------------------------------------------------------

interface WalkState {
  /** Dotted namespace prefix components currently open (sections contribute nothing). */
  readonly ns: string[];
  /** Start rows of declarations the grammar parsed, so rescue never duplicates one. */
  readonly parsedLines: Set<number>;
  /** Names bound by section-level `variable` commands, suppressed as references. */
  readonly sectionLocals: Set<string>;
  /** Section-`variable` binder name -> the structure its type names. */
  readonly sectionBinderTypes: Map<string, string>;
  /** Docstring seen immediately before the current declaration. */
  pendingDoc: string | undefined;
  /** Line -> name declared there, so a binding occurrence is never cited. */
  readonly declLines: ReadonlyMap<number, string>;
  /** The file's lines, so a declaration can read back rows the parser dropped. */
  readonly sourceLines: readonly string[];
  /** Per-row flag: is this line inside a `/- -/` block? Prose is not code. */
  readonly commentLines: Uint8Array;
}

/**
 * Split a source file into lines with any trailing CR removed.
 *
 * Not cosmetic. JavaScript's `.` does not match `\r` any more than `\n`, so on
 * a CRLF file a trailing-anchored pattern like `(.+)$` fails on EVERY line —
 * silently, and only on the half of a mixed-endings corpus that happens to use
 * CRLF. That is exactly how it presented: the first measurement of
 * {@link rescueDroppedFieldLines} recovered edges from the LF files and none
 * at all from the CRLF ones.
 */
function splitSourceLines(source: string): string[] {
  const out = source.split(NEWLINE);
  for (let i = 0; i < out.length; i++) {
    const line = out[i] as string;
    if (line.endsWith(CARRIAGE_RETURN)) out[i] = line.slice(0, -1);
  }
  return out;
}

/**
 * `field := value` on a line the parser dropped. Group 1 is the value side.
 *
 * `!`/`?` are legal in Lean identifiers (`get!`, `find?`) and so is `'`.
 */
const FIELD_ASSIGN = /^[ \t]*[A-Za-z_À-￿][A-Za-z0-9_'!?À-￿]*[ \t]*:=[ \t]*(.+)$/;

/** Identifier-shaped tokens inside a dropped line's right-hand side. */
const RHS_TOKEN = /[A-Za-z_À-￿][A-Za-z0-9_'!?.À-￿]*/g;

/**
 * Emit citations from lines the PARSER DISCARDED.
 *
 * tree-sitter's error recovery does not merely mislabel a `where`-struct — it
 * can drop the tokens outright. In one real witness file, `def b2Class :
 * b2Params.ValueClass2 where` yields a single `struct_field` for line 1069 and
 * then jumps straight to line 1075: `isClosed_S := b2CarrierS_isClosed` and its
 * three neighbours produce NO `identifier` node anywhere in the tree. No walk
 * can recover a token the parser never emitted, so those citations were
 * invisible — the largest single class of missing citation on a 259-file
 * development, and the reason four genuinely-used lemmas there reported as
 * uncited.
 *
 * The fallback is the same move `rescueFromErrorSpan` makes for dropped
 * declarations: read the text. Scoped tightly to keep it honest —
 *
 *   - only rows INSIDE this declaration,
 *   - only the `field := value` shape, whose right-hand side is the citation
 *     (the left is a field name, a binding position),
 *   - only tokens the parser produced NO identifier node for, checked per
 *     TOKEN rather than per row, so a citation can never be emitted twice.
 *     Per-row was too coarse: on `carrier_S := b2CarrierS` the parser keeps
 *     `carrier_S` — as an argument of the PREVIOUS line's application — but
 *     drops `b2CarrierS`, so the row looks covered while the half that is
 *     actually the citation is the half that went missing.
 *   - and every token still passes `normalizeRefName` and the locals set.
 */
function emitFieldAssignRefs(
  fromNodeId: string,
  startRow: number,
  endRow: number,
  covered: ReadonlyMap<number, ReadonlySet<string>>,
  sourceLines: readonly string[],
  locals: ReadonlySet<string>,
  ctx: ExtractorContext
): void {
  for (let row = startRow; row <= endRow; row++) {
    const text = sourceLines[row];
    if (text === undefined) continue;
    const assign = FIELD_ASSIGN.exec(text);
    if (!assign) continue;
    const seen = covered.get(row);
    const rhs = assign[1] as string;
    // A comment on the value side is prose, not a citation.
    const code = rhs.split('--')[0] as string;
    RHS_TOKEN.lastIndex = 0;
    let token: RegExpExecArray | null;
    while ((token = RHS_TOKEN.exec(code)) !== null) {
      const raw = token[0];
      if (seen?.has(raw)) continue;
      if (locals.has(raw)) continue;
      const refName = normalizeRefName(raw);
      if (refName === null) continue;
      ctx.addUnresolvedReference({
        fromNodeId,
        referenceName: refName,
        referenceKind: 'calls',
        line: row + 1,
        column: token.index,
      });
    }
  }
}

function rescueDroppedFieldLines(
  decl: SyntaxNode,
  fromNodeId: string,
  ctx: ExtractorContext,
  locals: ReadonlySet<string>,
  state: WalkState
): void {
  const last = Math.min(decl.endPosition.row, state.sourceLines.length - 1);

  // Cheap pre-pass. The overwhelming majority of declarations are theorems with
  // no `field := value` line anywhere in them, and for those the tree walk
  // below is pure cost — a second full traversal of every declaration in the
  // corpus. Scanning the raw lines first keeps this off the hot path.
  let hasFieldAssign = false;
  for (let row = decl.startPosition.row; row <= last; row++) {
    const text = state.sourceLines[row];
    if (text !== undefined && FIELD_ASSIGN.test(text)) { hasFieldAssign = true; break; }
  }
  if (!hasFieldAssign) return;

  const covered = new Map<number, Set<string>>();
  const mark = (n: SyntaxNode): void => {
    if (n.type === 'identifier') {
      const row = n.startPosition.row;
      const text = getNodeText(n, ctx.source).trim();
      const bucket = covered.get(row);
      if (bucket) bucket.add(text); else covered.set(row, new Set([text]));
    }
    for (const child of namedChildren(n)) mark(child);
  };
  mark(decl);

  emitFieldAssignRefs(
    fromNodeId, decl.startPosition.row, last, covered, state.sourceLines, locals, ctx
  );
}

/** Compose a Lean-style dotted qualified name, honouring `_root_.`. */
function qualify(ns: readonly string[], name: string): { name: string; qualifiedName: string } {
  if (name.startsWith('_root_.')) {
    const bare = name.slice('_root_.'.length);
    return { name: bare, qualifiedName: bare };
  }
  return { name, qualifiedName: [...ns, name].join('.') };
}

/**
 * Does this declaration's wrapper contain an ERROR sibling?
 *
 * When the grammar cannot parse a command (`alias`, `notation3`, `elab`), the
 * command is swallowed into an ERROR that lands inside the FOLLOWING
 * declaration's wrapper — which made 1,271 real Mathlib declarations inherit a
 * `@[deprecated]`/`@[simp]` that belonged to the swallowed command above them.
 * When we see that shape, decline to attach attributes rather than lie.
 */
function wrapperIsContaminated(wrapper: SyntaxNode | null): boolean {
  if (!wrapper) return false;
  for (const child of namedChildren(wrapper)) {
    if (child.type === 'ERROR') return true;
  }
  return false;
}

/** Resolve the display name for a declaration, including the anonymous forms. */
function declName(decl: SyntaxNode, ctx: ExtractorContext): string | null {
  // An `example` NEVER has a name in Lean. Check before consulting the grammar:
  // on a multi-line `example :` header it can still hand back a `name:` field,
  // which is how two nodes literally called `rfl` got minted — and a node named
  // `rfl` then steals every reference to the real `rfl`.
  if (decl.type === 'example') return `example@${decl.startPosition.row + 1}`;

  const named = lastField(decl, 'name');
  if (named) {
    const text = getNodeText(named, ctx.source).trim();
    if (text) return text;
  }

  // Anonymous `instance : Inhabited Point where …` — name it after the class it
  // instantiates. Note `lastField`, not `childForFieldName`: the latter returns
  // the `:` token and every anonymous instance in a file then collapses onto one
  // node id (664 collisions in a single 315-file Mathlib slice).
  if (decl.type === 'instance') {
    const type = lastField(decl, 'type');
    if (type) {
      const head = type.type === 'app' ? lastField(type, 'fn') ?? type : type;
      const cls = getNodeText(head, ctx.source).trim();
      if (cls) return `instance:${cls}`;
    }
    return `instance@${decl.startPosition.row + 1}`;
  }

  return null;
}

/** Extract and index one declaration, walking signature and body for dependencies. */
function handleDeclaration(
  decl: SyntaxNode,
  ctx: ExtractorContext,
  state: WalkState
): void {
  const kind = DECL_KINDS.get(decl.type);
  if (!kind) return;

  const rawName = declName(decl, ctx);
  if (!rawName) return;
  state.parsedLines.add(decl.startPosition.row);

  const { name, qualifiedName } = qualify(state.ns, rawName);

  // The signature is the header text up to the body separator — for a theorem
  // that is the whole mathematical content.
  const bodyNode = lastField(decl, 'body');
  const sigEnd = bodyNode ? bodyNode.startIndex : decl.endIndex;
  const signature = ctx.source.slice(decl.startIndex, sigEnd).trim().replace(/\s+/g, ' ').slice(0, 400);

  const node = ctx.createNode(kind, name, decl, {
    qualifiedName,
    signature,
    docstring: state.pendingDoc,
  });
  state.pendingDoc = undefined;
  if (!node) return;

  ctx.pushScope(node.id);
  try {
    // Locals start from section `variable`s, then accumulate this declaration's
    // own binders. Everything in this set is suppressed as a reference.
    const locals = new Set(state.sectionLocals);
    // Binder name -> the structure its declared type names, so a projection
    // `C.field` can be emitted scoped to that structure. Seeded from any
    // section-level `variable` binders already in force.
    const binderTypes = new Map(state.sectionBinderTypes);
    processBinders(
      lastField(decl, 'binders') ?? findChildByType(decl, 'binders'),
      node.id, ctx, locals, binderTypes
    );
    // Then every name the PROOF binds — `have`, `obtain`, `set`, `let`, `fun`.
    // Collected up front over the whole declaration rather than tracked as the
    // walk descends: a tactic hypothesis is bound for the rest of the proof, so
    // scope-exact tracking would buy nothing here, and a name bound anywhere in
    // a declaration is not plausibly also a citation elsewhere in the same one.
    collectBoundNames(decl, ctx.source, name => locals.add(name));

    // `structure Foo extends Bar` — the parent sits as an unlabeled `app`/
    // `identifier` child between the binders and the fields.
    const fieldOffsets = fieldChildOffsets(decl);
    for (const child of namedChildren(decl)) {
      if (child.type === 'app' && !fieldOffsets.has(child.startIndex)) {
        emitRefs(child, node.id, ctx, locals, state.declLines, binderTypes);
      }
    }

    // The statement / return type. For a theorem this IS the content.
    emitRefs(lastField(decl, 'type'), node.id, ctx, locals, state.declLines, binderTypes);

    // Members: structure fields and inductive constructors.
    for (const child of namedChildren(decl)) {
      if (child.type === 'field' || child.type === 'struct_field') {
        emitMember(child, 'field', ctx, locals, qualifiedName, state.commentLines);
      } else if (child.type === 'ctor' || child.type === 'ctor_alt') {
        emitMember(child, 'enum_member', ctx, locals, qualifiedName, state.commentLines);
      }
    }

    // Body, in all three shapes the grammar produces:
    //   `:= term` / `:= by tactics`  → the `body` field
    //   `where` struct instances     → `where_struct` children
    //   equation-style `| pat => e`  → `match_alt` children
    emitRefs(bodyNode, node.id, ctx, locals, state.declLines, binderTypes);
    for (const child of namedChildren(decl)) {
      if (child.type === 'where_struct') {
        for (const sf of namedChildren(child)) {
          if (sf.type === 'struct_field') emitRefs(lastField(sf, 'value'), node.id, ctx, locals, state.declLines, binderTypes);
        }
      } else if (child.type === 'match_alt') {
        emitRefs(lastField(child, 'body') ?? child, node.id, ctx, locals, state.declLines, binderTypes);
      } else if (child.type === 'where_aux_def' || child.type === 'ERROR') {
        // `where`-bound auxiliary definitions, and anything the grammar could
        // not structure — both still carry real citations.
        emitRefs(child, node.id, ctx, locals, state.declLines, binderTypes);
      }
    }

    // Last: the rows the parser threw away entirely, which no walk can reach.
    rescueDroppedFieldLines(decl, node.id, ctx, locals, state);
  } finally {
    ctx.popScope();
  }
}

/**
 * Start offsets of `parent`'s children that occupy a NAMED field.
 *
 * Computed once per declaration. The previous per-child scan was quadratic on
 * wide declarations and dominated index time on large corpora.
 */
function fieldChildOffsets(parent: SyntaxNode): Set<number> {
  const out = new Set<number>();
  for (let i = 0; i < parent.childCount; i++) {
    if (parent.fieldNameForChild(i) === null) continue;
    const c = parent.child(i);
    if (c) out.add(c.startIndex);
  }
  return out;
}

/** Declarations buried inside an unparseable span, in source order. */
function declarationsWithin(node: SyntaxNode): SyntaxNode[] {
  const out: SyntaxNode[] = [];
  const walk = (n: SyntaxNode): void => {
    if (DECL_KINDS.has(n.type)) { out.push(n); return; }
    for (const c of namedChildren(n)) walk(c);
  };
  for (const c of namedChildren(node)) walk(c);
  return out;
}

function findChildByType(node: SyntaxNode, type: string): SyntaxNode | null {
  for (const c of namedChildren(node)) if (c.type === type) return c;
  return null;
}

/** Create a field / constructor node and emit its type dependencies. */
function emitMember(
  member: SyntaxNode,
  kind: NodeKind,
  ctx: ExtractorContext,
  locals: ReadonlySet<string>,
  ownerQualifiedName: string,
  commentLines: Uint8Array
): void {
  const nameNode = lastField(member, 'name');
  if (!nameNode) return;
  const typeNode = lastField(member, 'type');

  const emitOne = (idNode: SyntaxNode): void => {
    const name = getNodeText(idNode, ctx.source).trim();
    if (!name) return;
    // Dotted, like every other Lean name — the core would compose `A::B::c`.
    // Anchor each name on its OWN line: when the second name is really a
    // separate field the grammar mis-attached (see below), reporting it at the
    // first field's line would send every `file:line` answer to the wrong row.
    const node = ctx.createNode(kind, name, member, {
      qualifiedName: ownerQualifiedName ? `${ownerQualifiedName}.${name}` : name,
      startLine: idNode.startPosition.row + 1,
      endLine: member.endPosition.row + 1,
    });
    if (!node) return;
    // The field's TYPE is its dependency; its own name is a binding occurrence.
    emitRefs(typeNode, node.id, ctx, locals);
  };

  emitOne(nameNode);

  // `structure A where a b : Nat` declares TWO fields sharing one type, and the
  // grammar puts every name after the first in a `binders` child. Reading only
  // `name:` dropped all but the first — silently, since the structure and its
  // other fields all extract fine.
  //
  // The same shape is how a field typed with `|…|` swallows its successor. On
  //
  //   multiLineWithPipes :
  //     ∀ x y : Nat, |(x : Int) - (y : Int)| ≤ 0
  //   afterPipes : Nat
  //
  // the `|` opens an ERROR, the parser resumes mid-field, and `afterPipes`
  // lands in this same `binders` slot — indistinguishable from multi-name
  // syntax, and recovered by the same code. That mattered in practice: a
  // sanction-chord field written `|p.F x s₂ - p.F x s₁| ≤ d * (s₂ - s₁)` sits
  // in two certificate structures of one development, and the field after it
  // in each — including `hS_margin`, among the most-queried in the tree — was
  // absent from the index entirely.
  //
  // Only for structure fields: an inductive constructor's `binders` are real
  // parameters, not extra constructor names. Bare identifiers only, so a
  // genuine parameter list (`myMethod (x : Nat) : Nat`) is left alone.
  if (kind !== 'field') return;
  const extraNames = findChildByType(member, 'binders');
  if (!extraNames) return;
  for (const child of namedChildren(extraNames)) {
    if (child.type !== 'identifier') continue;
    // The `binders` slot also collects whatever the ERROR recovery swept up.
    // Two properties separate a field name from that debris, and neither is
    // specific to any one project: a field name is never DOTTED, and it always
    // sits to the LEFT of its type ascription.
    //
    //   ∀ s ∈ I, |p.U_T x a s| ≤ cube_T          no ascription — an expression
    //   attribute [to_dual existing] Order.toMax  no ascription — a command
    //   le_total := LinearOrder.le_total          `:=` assigns, never declares
    //   end / export / namespace / refine / at    keywords, no ascription
    //   cube_S : ℝ                                a field
    //
    // An earlier version accepted anything that opened its own line. That held
    // on the one development the bug was reported against and failed
    // everywhere else: measured across mathlib4 and batteries it minted `end`,
    // `export`, `namespace`, `apply`, `at` and `attribute` as structure fields.
    //
    // The name must also OPEN its own line. Anything sharing the field's line
    // is a BINDER of that field, never a second field — confirmed against Lean
    // 4.29, which rejects
    //
    //   structure Multi where
    //     alpha beta : Nat
    //
    // with "failed to infer type of binder `beta`". Lean 3 allowed the grouped
    // form and Lean 4 does not; assuming it did minted a spurious field for the
    // parameter of every `tendsto_mul_left m : …` declaration in mathlib.
    if (!isFirstTokenOnLine(child, ctx.source)) continue;
    const text = getNodeText(child, ctx.source);
    if (text.includes('.')) continue;
    if (LEAN_KEYWORDS.has(text)) continue;
    if (!precedesTypeAscription(child, ctx.source)) continue;
    const line = sourceLineOf(child, ctx.source);
    // A declaration header ascribes too (`theorem foo : True`), as does a
    // command (`variable {R : Type u}`, `attribute [simp] Foo.bar`). Both pass
    // the test above and must be excluded by the line they sit on. Sweeping a
    // declaration in here would give it the `field` kind and the enclosing
    // structure's qualified name — worse than the status quo of missing it.
    if (HEADER_LINE.test(line) || COMMAND_LINE.test(line)) continue;
    // Prose is not code. A docstring sentence that happens to contain a colon
    // — "More precisely, it does so in a relative setting:" — otherwise mints
    // a field for every word to its left.
    if (commentLines[child.startPosition.row] === 1) continue;
    if (line.slice(0, child.startPosition.column).includes('--')) continue;
    emitOne(child);
  }
}

/**
 * Keywords and modifiers that can appear in identifier position after an ERROR
 * but are never a name being declared.
 */
const LEAN_KEYWORDS: ReadonlySet<string> = new Set([
  'protected', 'private', 'noncomputable', 'partial', 'unsafe', 'scoped', 'local',
  'mutual', 'deriving', 'extends', 'where', 'with', 'from', 'this', 'at', 'in',
  'fun', 'let', 'have', 'show', 'match', 'do', 'then', 'else', 'if', 'by',
  'end', 'export', 'namespace', 'section', 'open', 'variable', 'universe',
  'attribute', 'instance', 'macro', 'notation', 'syntax', 'infixl', 'infixr',
  'prefix', 'postfix', 'set_option', 'include', 'omit', 'import',
]);

/** A top-level command whose line declares no structure field. */
const COMMAND_LINE =
  /^[ \t]*(variable|attribute|open|export|namespace|section|end|universe|set_option|include|omit|import|deriving|notation|macro|syntax|infixl|infixr|prefix|postfix|local|scoped)\b/;

/** Is `node` the first non-whitespace token on its source line? */
function isFirstTokenOnLine(node: SyntaxNode, source: string): boolean {
  for (let i = node.startIndex - 1; i >= 0; i--) {
    const ch = source[i];
    if (ch === NEWLINE) return true;
    if (ch !== ' ' && ch !== '\t' && ch !== CARRIAGE_RETURN) return false;
  }
  return true;
}

/**
 * Does `node` sit to the left of a type ascription on its own line?
 *
 * The shape of a Lean structure field in both its forms — `a : T` and the
 * multi-name `a b : T`. `:=` is rejected deliberately: a `where`-struct
 * assignment binds a value to an already-declared field and introduces no
 * new name.
 */
function precedesTypeAscription(node: SyntaxNode, source: string): boolean {
  const line = sourceLineOf(node, source);
  for (let i = 0; i < line.length; i++) {
    if (line[i] !== ':') continue;
    if (line[i + 1] === '=') return false;
    return node.startPosition.column < i;
  }
  return false;
}

/** The full text of the source line containing `node`. */
function sourceLineOf(node: SyntaxNode, source: string): string {
  let start = node.startIndex;
  while (start > 0 && source[start - 1] !== NEWLINE) start--;
  let end = node.startIndex;
  while (end < source.length && source[end] !== NEWLINE) end++;
  return source.slice(start, end);
}

// ---------------------------------------------------------------------------
// Rescue: declarations the grammar loses inside an ERROR span
// ---------------------------------------------------------------------------

/**
 * A declaration header written at column 0.
 *
 * Only used inside ERROR spans. When the grammar meets Mathlib notation it does
 * not know (`↥(S : Set ℝ) →ᵇ ℝ`, `|c₁.V' x - c₂.V' x|`, the image operator `''`)
 * it can derail and swallow everything up to the next construct it recognises —
 * measured at 59 ERROR spans in one 2.6k-line file, one of which absorbed 60+
 * lines. Declarations inside such a span are not mis-parsed, they are *absent*:
 * `noncomputable def banachIter` (cited 37×) came through only as a bare
 * `identifier` inside an `app` chain, so no amount of AST walking can find it.
 *
 * Column 0 is the discriminator. A Lean declaration is written at column 0 (or
 * at the start of its line inside a section); the same words appearing inside an
 * expression, a tactic block or a docstring are indented or mid-line.
 */
const RESCUE_HEADER =
  /^(?:@\[[^\]]*\][ \t]*)*(?:private |protected |noncomputable |partial |unsafe |scoped |local )*(theorem|lemma|def|abbrev|instance|structure|class|inductive|axiom|opaque|example)\b[ \t]*([A-Za-z_À-￿][A-Za-z0-9_'!?.À-￿]*)?/gm;

const RESCUE_KINDS: ReadonlyMap<string, NodeKind> = new Map<string, NodeKind>([
  ['theorem', 'function'], ['lemma', 'function'], ['def', 'function'],
  ['abbrev', 'function'], ['instance', 'function'], ['axiom', 'function'],
  ['opaque', 'function'], ['structure', 'struct'], ['class', 'struct'],
  ['inductive', 'enum'], ['example', 'function'],
]);

/** Declaration keywords that are legitimately anonymous (`instance : C X where`). */
const RESCUE_ANONYMOUS: ReadonlySet<string> = new Set(['instance', 'example']);

/** Line separator, built without an escape sequence. */
const NEWLINE = String.fromCharCode(10);
const CARRIAGE_RETURN = String.fromCharCode(13);

/** Non-global twin of RESCUE_HEADER, for testing one line at a time. */
const HEADER_LINE = new RegExp(RESCUE_HEADER.source);

/**
 * Per-line flag: does this line BEGIN inside a `/- ... -/` block comment?
 *
 * The text-level rescue matches declaration headers at column 0, and Lean prose
 * wraps: "...its three-goals" / "theorem routes Step 1..." puts `theorem` at
 * column 0 inside a comment, and the rescue then mints a declaration called
 * `routes`. Measured at 8 of 3,771 declarations (0.21%) on a real development --
 * all with a null signature, none absorbing an inbound edge, but all landing in
 * the zero-inbound pool that the unused-declaration question reads.
 */
function blockCommentLineFlags(source: string): Uint8Array {
  const lines = source.split(/\r?\n/);
  const flags = new Uint8Array(lines.length);
  let depth = 0;
  for (let i = 0; i < lines.length; i++) {
    flags[i] = depth > 0 ? 1 : 0;
    const line = lines[i] ?? '';
    let opens = 0;
    let closes = 0;
    for (let j = 0; j + 1 < line.length; j++) {
      if (line[j] === '/' && line[j + 1] === '-') opens++;
      else if (line[j] === '-' && line[j + 1] === '/') closes++;
    }
    depth += opens - closes;
    if (depth < 0) depth = 0;
  }
  return flags;
}

/**
 * Map of 0-based line number to the declaration name written on that line.
 *
 * A declaration's own name at its own definition site is a BINDING occurrence,
 * never a citation. When a parse cascade swallows declaration Y into another
 * declaration's ERROR span, the reference walker would otherwise harvest Y's
 * name from its own header and emit it as a citation — inventing an inbound
 * edge for Y and hiding that nothing actually uses it. Measured at 419 such
 * edges on a real development, each one masking its target's true inbound count,
 * which is exactly what the unused-declaration question reads.
 *
 * Serves two purposes: suppressing those harvests, and bounding how far a
 * rescued declaration may claim identifiers (it stops at the next header).
 */
function declaredNameByLine(source: string): Map<number, string> {
  const out = new Map<number, string>();
  const lines = source.split(NEWLINE);
  for (let i = 0; i < lines.length; i++) {
    HEADER_LINE.lastIndex = 0;
    const m = HEADER_LINE.exec(lines[i] ?? '');
    // Group 1 is the KEYWORD, group 2 is the declared name.
    if (m && m[2]) out.set(i, m[2]);
  }
  return out;
}

/** Every ERROR node in a subtree, outermost first. */
function errorSpans(root: SyntaxNode): SyntaxNode[] {
  const out: SyntaxNode[] = [];
  const walk = (n: SyntaxNode): void => {
    if (n.type === 'ERROR') { out.push(n); return; }
    for (const c of namedChildren(n)) walk(c);
  };
  walk(root);
  return out;
}

/**
 * Recover declarations from an unparseable span by reading its text, and
 * attribute the identifiers in each one's line range to it.
 *
 * `seenLines` prevents re-creating a declaration the grammar DID parse.
 */
function rescueFromErrorSpan(
  err: SyntaxNode,
  ns: readonly string[],
  ctx: ExtractorContext,
  seenLines: Set<number>,
  commentLines: Uint8Array,
  declLines: ReadonlyMap<number, string>,
  sourceLines: readonly string[]
): void {
  const text = ctx.source.slice(err.startIndex, err.endIndex);
  const baseLine = err.startPosition.row;
  // The ERROR may begin mid-line; only offsets after the first newline are
  // reliably at column 0 relative to the file.
  const firstNewline = text.indexOf('\n');
  if (firstNewline < 0) return;

  const found: Array<{ line: number; kind: NodeKind; name: string }> = [];
  RESCUE_HEADER.lastIndex = 0;
  let m: RegExpExecArray | null;
  while ((m = RESCUE_HEADER.exec(text)) !== null) {
    if (m.index < firstNewline) continue;
    const keyword = m[1] as string;
    const kind = RESCUE_KINDS.get(keyword);
    if (!kind) continue;
    const line = baseLine + (text.slice(0, m.index).match(/\n/g)?.length ?? 0);
    // Prose inside a block comment is not a declaration, however it wraps.
    if (commentLines[line] === 1) continue;
    // `instance : Foo where` and `example :` carry no name; that was the
    // largest remaining rescue gap (11.4% of FLT's instances), because the
    // header pattern demanded an identifier. Name them positionally, exactly
    // as `declName` does on the parsed path.
    const name = m[2] ?? (RESCUE_ANONYMOUS.has(keyword) ? keyword + '@' + (line + 1) : undefined);
    if (!name) continue;
    if (seenLines.has(line)) continue;
    seenLines.add(line);
    found.push({ line, kind, name });
  }
  if (found.length === 0) return;

  // Index the ERROR's descendants by line so each rescued declaration can claim
  // the identifiers written under it.
  const byLine = new Map<number, SyntaxNode[]>();
  const collect = (n: SyntaxNode): void => {
    if (n.type === 'identifier') {
      const row = n.startPosition.row;
      const bucket = byLine.get(row);
      if (bucket) bucket.push(n); else byLine.set(row, [n]);
    }
    for (const c of namedChildren(n)) collect(c);
  };
  collect(err);

  // Names bound inside the span, by row. The rescue has no binder handling of
  // its own — it claims every identifier written under a header — so without
  // this a theorem's own hypothesis `(hFsc : SanctionSemiconcave F M)` is
  // emitted as a citation from its signature line, and again at every use.
  const boundRows: Array<{ row: number; name: string }> = [];
  collectBoundNames(err, ctx.source, (name, row) => { boundRows.push({ row, name }); });

  // The identifiers the parser DID keep, by row — the complement of what
  // `emitFieldAssignRefs` has to read out of the raw text.
  const coveredTokens = new Map<number, Set<string>>();
  for (const [row, ids] of byLine) {
    coveredTokens.set(row, new Set(ids.map(id => getNodeText(id, ctx.source).trim())));
  }

  const endLine = err.endPosition.row;
  for (let i = 0; i < found.length; i++) {
    const entry = found[i]!;
    const until = i + 1 < found.length ? found[i + 1]!.line : endLine + 1;
    const { name, qualifiedName } = qualify(ns, entry.name);
    // Anchor on the ERROR node and override the line range explicitly, rather
    // than requiring a real node on the header's line. A CATASTROPHIC span emits
    // almost no named nodes at all — one FLT file parses as a single 880-line
    // ERROR whose only children are `ERROR` and `str_lit` — so an anchor
    // requirement silently dropped all 87 of its declarations. `createNode`
    // spreads `extra` after its own fields, so the true position wins.
    const node = ctx.createNode(entry.kind, name, err, {
      qualifiedName,
      startLine: entry.line + 1,
      endLine: until,
      docstring: undefined,
    });
    if (!node) continue;

    // Identifiers from this header up to the next rescued header belong to it.
    // Anything this region binds is local to it, exactly as on the parsed path.
    const locals = new Set<string>();
    for (const b of boundRows) {
      if (b.row >= entry.line && b.row < until) locals.add(b.name);
    }
    ctx.pushScope(node.id);
    try {
      for (let row = entry.line; row < until; row++) {
        // A declaration's own name at its own header is a BINDING occurrence,
        // so suppress just that token — do NOT stop the walk here. An earlier
        // version broke out of the range at any header line, which orphaned
        // every region whose header the rescue itself skips (already parsed,
        // inside a comment, anonymous): nobody walked it and its citations were
        // emitted by no one. That cost ~8 genuine declarations their last
        // inbound edge against ~133 artifacts removed — a net gain, but the
        // wrong shape of fix. Suppress the token, keep the coverage.
        const declaredHere = declLines.get(row);
        for (const id of byLine.get(row) ?? []) {
          const raw = getNodeText(id, ctx.source).trim();
          if (declaredHere !== undefined && declaredHere === raw) continue;
          if (locals.has(raw)) continue;
          const refName = normalizeRefName(raw);
          if (refName === null || refName === name) continue;
          ctx.addUnresolvedReference({
            fromNodeId: node.id,
            referenceName: refName,
            referenceKind: 'calls',
            line: id.startPosition.row + 1,
            column: id.startPosition.column,
          });
        }
      }

      // A rescued declaration can carry a perfectly ordinary `where`-struct
      // whose rows the parser still dropped, and the loop above can only claim
      // identifiers the parser kept. `ofBall` in one development sits inside a
      // 108-row cascade and cites `valBall_isClosed`/`valBall_nonempty` in
      // plain `field := value` syntax; both reported as uncited because this
      // path had no text fallback of its own while the parsed path did.
      emitFieldAssignRefs(
        node.id, entry.line, Math.min(until - 1, sourceLines.length - 1),
        coveredTokens, sourceLines, locals, ctx
      );
    } finally {
      ctx.popScope();
    }
  }
}

// ---------------------------------------------------------------------------
// The extractor
// ---------------------------------------------------------------------------

export const leanExtractor: LanguageExtractor = {
  // Dispatch is taken over at the `module` root (see `visitNode`), so these
  // lists are documentation rather than wiring. They are kept accurate so the
  // config still reads as a description of the language.
  functionTypes: ['def', 'theorem', 'abbrev', 'opaque', 'axiom', 'instance', 'example'],
  classTypes: [],
  methodTypes: [],
  interfaceTypes: [],
  structTypes: ['structure'],
  enumTypes: ['inductive'],
  enumMemberTypes: ['ctor', 'ctor_alt'],
  typeAliasTypes: [],
  importTypes: ['import', 'open'],
  callTypes: [],
  variableTypes: [],
  fieldTypes: ['field', 'struct_field'],

  nameField: 'name',
  bodyField: 'body',
  paramsField: 'binders',
  returnField: 'type',

  /** See `lastField` — the grammar tags the `:=` separator with the `body` field too. */
  resolveBody(node: SyntaxNode, bodyField: string): SyntaxNode | null {
    return lastField(node, bodyField);
  },

  /**
   * `@[simp]`, `@[simp, norm_cast]`, `private`, `noncomputable` → node decorators.
   *
   * Attribute membership is a PROPERTY of a lemma, not a dependency of it:
   * `@[simp]` does not mean "this theorem calls simp". Recording it here keeps
   * "what is in the simp set" queryable without inventing an edge to a target
   * that is not in the graph.
   */
  extractModifiers(node: SyntaxNode): string[] | undefined {
    const wrapper = node.parent;
    if (!wrapper || wrapper.type !== 'declaration') return undefined;
    if (wrapperIsContaminated(wrapper)) return undefined;

    const out: string[] = [];
    for (const child of namedChildren(wrapper)) {
      if (child.type === 'attributes') {
        for (const n of allFields(child, 'name')) {
          const text = n.text.trim();
          if (text) out.push(`@[${text}]`);
        }
      } else if (child.type === 'decl_modifiers') {
        const text = child.text.trim();
        if (text) out.push(text);
      }
    }
    return out.length > 0 ? out : undefined;
  },

  /**
   * `import Mathlib.Order.Basic` and `open Nat Finset`.
   *
   * Lean module paths are dot-separated and map to file paths the way Java/Kotlin
   * FQNs do (`Mathlib.Order.Basic` → `Mathlib/Order/Basic.lean`).
   */
  extractImport(node: SyntaxNode, source: string): ImportInfo | null {
    if (node.type === 'import') {
      const name = lastField(node, 'name');
      if (!name) return null;
      const moduleName = getNodeText(name, source).trim();
      if (!moduleName) return null;
      return { moduleName, signature: `import ${moduleName}` };
    }

    if (node.type === 'open') {
      // `open _root_.MulOpposite` opens the root-level namespace; the escape
      // marker is not part of its name. This is the last emission path that was
      // not going through `normalizeRefName`, and the only remaining source of
      // `_root_.`-prefixed rows (17 on mathlib, 2 on FLT).
      const namespaces = allFields(node, 'namespace')
        .map((n) => getNodeText(n, source).trim())
        .map((n) => (n.startsWith('_root_.') ? n.slice('_root_.'.length) : n));
      const first = namespaces.find((n) => n.length > 0);
      if (!first) return null;
      return { moduleName: first, signature: `open ${namespaces.join(' ')}` };
    }

    return null;
  },

  /**
   * Drive the whole file from the `module` root.
   *
   * The namespace stack lives in a local variable for the duration of this one
   * call, so nothing leaks between files even though the extractor object is a
   * shared singleton. `section` is deliberately NOT a namespace: it scopes
   * `variable`s but contributes nothing to a declaration's name, and treating it
   * as one would fabricate a prefix on the majority of Lean sections.
   */
  visitNode(node: SyntaxNode, ctx: ExtractorContext): boolean {
    // Drive from the file root whatever the grammar called it. On roughly 9% of
    // real files (11% of batteries) the root parses as ERROR rather than
    // `module` — one unknown notation near the top is enough. Keying strictly on
    // `module` silently handed those whole files back to the core's generic
    // walk: no namespace qualification, no signature dependencies, no struct
    // nodes, and phantom `example` nodes named after their first identifier.
    const isRoot = node.parent === null;
    if (node.type !== 'module' && !isRoot) {
      // Defensive: if the core ever dispatches a Lean declaration itself, own it
      // here rather than let the generic path mint a mis-named node.
      if (DECL_KINDS.has(node.type)) {
        handleDeclaration(node, ctx, {
          ns: [], parsedLines: new Set(), sectionLocals: new Set(), sectionBinderTypes: new Map(),
          pendingDoc: undefined, declLines: declaredNameByLine(ctx.source),
          sourceLines: splitSourceLines(ctx.source),
          commentLines: blockCommentLineFlags(ctx.source),
        });
        return true;
      }
      return false;
    }

    interface Block {
      kind: 'namespace' | 'section';
      pushedScope: boolean;
      savedLocals: Set<string>;
      savedBinderTypes: Map<string, string>;
    }
    const blocks: Block[] = [];
    const pendingRescue: Array<{ err: SyntaxNode; ns: string[] }> = [];
    const declLines = declaredNameByLine(ctx.source);
    const state: WalkState = {
      ns: [], parsedLines: new Set(), sectionLocals: new Set(), sectionBinderTypes: new Map(),
      pendingDoc: undefined, declLines, sourceLines: splitSourceLines(ctx.source),
      commentLines: blockCommentLineFlags(ctx.source),
    };

    const closeBlock = (): void => {
      const block = blocks.pop();
      if (!block) return;
      if (block.kind === 'namespace') state.ns.pop();
      if (block.pushedScope) ctx.popScope();
      state.sectionLocals.clear();
      for (const n of block.savedLocals) state.sectionLocals.add(n);
      state.sectionBinderTypes.clear();
      for (const [k, v] of block.savedBinderTypes) state.sectionBinderTypes.set(k, v);
    };

    for (const child of namedChildren(node)) {
      switch (child.type) {
        case 'doc_comment':
        case 'module_doc_comment': {
          state.pendingDoc = getNodeText(child, ctx.source).trim().slice(0, 1000);
          break;
        }

        case 'namespace': {
          const nameNode = lastField(child, 'name');
          const nsName = nameNode ? getNodeText(nameNode, ctx.source).trim() : '';
          const saved = new Set(state.sectionLocals);
          const savedTypes = new Map(state.sectionBinderTypes);
          if (!nsName) {
            blocks.push({ kind: 'namespace', pushedScope: false, savedLocals: saved, savedBinderTypes: savedTypes });
            break;
          }
          const qualifiedName = [...state.ns, nsName].join('.');
          const nsNode = ctx.createNode('namespace', nsName, child, { qualifiedName });
          state.ns.push(nsName);
          if (nsNode) ctx.pushScope(nsNode.id);
          blocks.push({
            kind: 'namespace', pushedScope: Boolean(nsNode),
            savedLocals: saved, savedBinderTypes: savedTypes,
          });
          break;
        }

        case 'section': {
          // A section scopes `variable`s but never qualifies a name.
          blocks.push({
            kind: 'section', pushedScope: false,
            savedLocals: new Set(state.sectionLocals),
            savedBinderTypes: new Map(state.sectionBinderTypes),
          });
          break;
        }

        case 'end': {
          closeBlock();
          break;
        }

        case 'variable': {
          // Section variables bind names that later declarations may use. Record
          // the names so they are never mistaken for references, and emit their
          // TYPES once against the enclosing scope rather than re-attributing
          // them to every following declaration (which would over-connect).
          const owner = ctx.nodeStack.length > 0 ? ctx.nodeStack[ctx.nodeStack.length - 1] : null;
          processBinders(child, owner ?? null, ctx, state.sectionLocals, state.sectionBinderTypes);
          break;
        }

        case 'declaration': {
          if (wrapperIsContaminated(child)) {
            // A swallowed command (alias / notation3 / elab) landed in this
            // wrapper. Still index the declaration, but its attributes are not
            // trustworthy — `extractModifiers` declines separately.
          }
          for (const inner of namedChildren(child)) {
            if (DECL_KINDS.has(inner.type)) {
              handleDeclaration(inner, ctx, state);
            } else if (inner.type === 'ERROR') {
              for (const buried of declarationsWithin(inner)) {
                handleDeclaration(buried, ctx, state);
              }
            }
          }
          // A derailed parse can bury later declarations ARBITRARILY deep inside
          // this one — not as declaration nodes, but as loose identifiers. Read
          // them back out of the source text.
          for (const e of errorSpans(child)) pendingRescue.push({ err: e, ns: [...state.ns] });
          break;
        }

        default: {
          if (DECL_KINDS.has(child.type)) {
            // A declaration not wrapped in `declaration` (some forms are bare).
            handleDeclaration(child, ctx, state);
          } else if (child.type === 'ERROR') {
            pendingRescue.push({ err: child, ns: [...state.ns] });
            // A command the grammar cannot parse (`alias`, `notation3`, `elab`)
            // swallows everything up to the next thing it recognises, and real
            // declarations get caught inside. Driving the walk from `module`
            // would silently drop them, so recover any declaration buried in the
            // ERROR. The namespace prefix in force here is the right one: an
            // ERROR span never opens or closes a namespace block.
            for (const buried of declarationsWithin(child)) {
              handleDeclaration(buried, ctx, state);
            }
          } else {
            // imports, opens, and anything else the core knows how to handle.
            ctx.visitNode(child);
          }
        }
      }
    }

    while (blocks.length > 0) closeBlock();

    // A root that failed to parse holds declarations no walk can see.
    if (node.type !== 'module') pendingRescue.push({ err: node, ns: [] });

    // Rescue runs last: `parsedLines` must be complete first, so a declaration
    // the grammar handled is never duplicated by the text scan. Namespace
    // context is gone by now, which is why rescued names take the prefix that
    // was open at their own position — recorded when the span was queued.
    const seenLines = new Set(state.parsedLines);
    // `state.commentLines` is computed once per file. This used to build a
    // second copy lazily, from when the rescue was its only consumer.
    for (const { err, ns } of pendingRescue) {
      rescueFromErrorSpan(
        err, ns, ctx, seenLines, state.commentLines, state.declLines, state.sourceLines
      );
    }
    return true;
  },
};
