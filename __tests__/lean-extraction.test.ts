/**
 * Lean 4 end-to-end extraction tests.
 *
 * Lives in its own file rather than upstream's high-churn
 * `__tests__/extraction.test.ts`, so an upstream release never conflicts here.
 * See LEAN_FORK.md.
 *
 * The contract these pin is PRECISION of the dependency graph, because that is
 * what a formalization is indexed for: "which lemmas does this proof cite",
 * "what breaks if I change this definition", "which lemmas are unused". A
 * missing edge costs one answer; a WRONG edge silently corrupts every impact
 * and layering query that passes through it.
 *
 * The motivating regression: Lean hypothesis names are shaped exactly like
 * lemma names (`h_stage_sender`, `hV_T_gain`, `hFsc`), so the naming-convention
 * heuristic cannot tell them apart. Until bound names were collected, a
 * `have h_stage_sender : … := …` emitted a reference at its binding site and at
 * every later use — and on a real 259-file development that manufactured 118
 * edges from `Theory/` and `Foundations/` into `Examples/`, a layering
 * violation that would have been alarming had any of it been real. No file in
 * those directories imports `Sanctions.Examples` at all.
 */
import { describe, it, expect, beforeAll, afterEach } from 'vitest';
import * as fs from 'fs';
import * as path from 'path';
import * as os from 'os';
import { CodeGraph } from '../src';
import { initGrammars, loadAllGrammars } from '../src/extraction/grammars';

beforeAll(async () => {
  await initGrammars();
  await loadAllGrammars();
});

/**
 * Edge kinds that mean "cites".
 *
 * `contains` is NOT one of them, and the distinction is easy to miss: a Lean
 * declaration inside `namespace Demo` always has an inbound `contains` edge
 * from the namespace, so "has an inbound edge" and "is cited" are different
 * questions. Counting unfiltered edges makes an uncited lemma look used.
 */
const CITES = new Set(['calls', 'instantiates', 'references']);

/** Names of declarations this node cites. */
function citedNames(cg: CodeGraph, fromId: string): string[] {
  return cg
    .getOutgoingEdges(fromId)
    .filter((e) => CITES.has(e.kind))
    .map((e) => cg.getNode(e.target))
    .filter((n): n is NonNullable<typeof n> => !!n)
    .map((n) => n.name);
}

/** Inbound CITATIONS only — see {@link CITES}. */
function citationsTo(cg: CodeGraph, nodeId: string): number {
  return cg.getIncomingEdges(nodeId).filter((e) => CITES.has(e.kind)).length;
}

describe('Lean 4 extraction', () => {
  let tmpDir: string | undefined;
  let graph: CodeGraph | undefined;

  /** Index a fixture directory and register both for teardown. */
  async function indexFixture(dir: string): Promise<CodeGraph> {
    const cg = CodeGraph.initSync(dir);
    await cg.indexAll();
    graph = cg;
    return cg;
  }

  afterEach(() => {
    // Close before unlinking: on Windows the open SQLite handle makes rmSync
    // fail with EBUSY, which would fail the test for an unrelated reason.
    graph?.close();
    graph = undefined;
    if (tmpDir) {
      try {
        fs.rmSync(tmpDir, { recursive: true, force: true });
      } catch {
        /* the WAL can linger briefly; a leftover temp dir is not a failure */
      }
    }
    tmpDir = undefined;
  });

  it('never cites a tactic-bound hypothesis that shares a name with a real theorem', async () => {
    tmpDir = fs.mkdtempSync(path.join(os.tmpdir(), 'cg-lean-locals-'));

    // A real theorem whose name is ALSO the conventional name for a hypothesis.
    // This is not contrived: it is exactly how `h_stage_sender` is written in
    // the development that surfaced the bug.
    fs.writeFileSync(
      path.join(tmpDir, 'Witness.lean'),
      'namespace Demo\n' +
        '\n' +
        'theorem h_stage_sender : True := trivial\n' +
        '\n' +
        'theorem realTargetLemma : True := trivial\n' +
        '\n' +
        'end Demo\n'
    );

    // A proof that BINDS `h_stage_sender` as a hypothesis and uses it twice.
    // Neither the binding nor the uses are citations of Demo.h_stage_sender.
    fs.writeFileSync(
      path.join(tmpDir, 'Proof.lean'),
      'theorem consumer (hyp : True) : True := by\n' +
        '  have h_stage_sender : True := trivial\n' +
        '  have hV_T_gain : True := realTargetLemma\n' +
        '  obtain ⟨hFsc, hSlo⟩ := someProduct\n' +
        '  exact h_stage_sender\n'
    );

    const cg = await indexFixture(tmpDir);

    const fns = cg.getNodesByKind('function');
    const consumer = fns.find((n) => n.name === 'consumer');
    const target = fns.find((n) => n.name === 'h_stage_sender');
    expect(consumer).toBeDefined();
    expect(target).toBeDefined();

    // The hypothesis must not be mistaken for the theorem.
    expect(citedNames(cg, consumer!.id)).not.toContain('h_stage_sender');
    expect(citationsTo(cg, target!.id)).toBe(0);

    // …while a genuine citation on the very same `have` line still lands.
    expect(citedNames(cg, consumer!.id)).toContain('realTargetLemma');

    // `obtain ⟨…⟩` destructuring binds too — those names are not citations.
    expect(citedNames(cg, consumer!.id)).not.toContain('hFsc');
    expect(citedNames(cg, consumer!.id)).not.toContain('hSlo');
  });

  it('cites a namespace-qualified definition used inside a calc block', async () => {
    tmpDir = fs.mkdtempSync(path.join(os.tmpdir(), 'cg-lean-calc-'));

    // The other direction of the same fix: bound-name collection must not eat
    // genuine citations. On a real file the grammar parses the parenthesised
    // applications inside `calc |…|` as `explicit_binder`s whose `name:` is the
    // dotted `Sanctions.clipS'`; trusting that as a binding occurrence
    // suppressed 24 real citations of `clipS'` in that file alone. Hence the
    // two guards in `collectBoundNames`: a bound name must be an undotted atom,
    // and outside a `fun` its binder must carry a real `type:` field.
    //
    // HONEST LIMIT: that misparse depends on whole-file parse state and does
    // NOT reproduce in a fixture this size — verified by dumping the AST of
    // both a synthetic case and the real 20-line slice, neither of which yields
    // a dotted binder name. So this pins the CONTRACT (a qualified reference in
    // a calc block is cited) rather than the specific grammar defect; it would
    // not, by itself, catch a regression that dropped those guards.
    fs.writeFileSync(
      path.join(tmpDir, 'Defs.lean'),
      'namespace Demo\n' +
        "def clipS' (z : Nat) : Nat := z\n" +
        'end Demo\n'
    );

    fs.writeFileSync(
      path.join(tmpDir, 'Uses.lean'),
      'theorem usesClip (y h : Nat) : True := by\n' +
        '  calc\n' +
        "    |(U (Demo.clipS' (y + h)) - U (Demo.clipS' (y - h)))| / 2\n" +
        '        ≤ 2 := by trivial\n' +
        '  trivial\n'
    );

    const cg = await indexFixture(tmpDir);

    const fns = cg.getNodesByKind('function');
    const clip = fns.find((n) => n.name === "clipS'");
    const uses = fns.find((n) => n.name === 'usesClip');
    expect(clip).toBeDefined();
    expect(uses).toBeDefined();

    expect(citedNames(cg, uses!.id)).toContain("clipS'");
  });

  it('suppresses a signature binder without losing the type it depends on', async () => {
    tmpDir = fs.mkdtempSync(path.join(os.tmpdir(), 'cg-lean-binder-'));

    // `(hFsc : SanctionSemiconcave F M)` — the NAME is a binding occurrence,
    // the TYPE is a genuine dependency. The ERROR-span rescue used to claim
    // every identifier on the line, so it emitted the binder name too.
    fs.writeFileSync(
      path.join(tmpDir, 'Sig.lean'),
      'structure SanctionSemiconcave where\n' +
        '  dummy : Nat\n' +
        '\n' +
        'theorem hFsc : True := trivial\n' +
        '\n' +
        'theorem usesIt (hFsc : SanctionSemiconcave) : True := trivial\n'
    );

    const cg = await indexFixture(tmpDir);

    const usesIt = cg.getNodesByKind('function').find((n) => n.name === 'usesIt');
    expect(usesIt).toBeDefined();
    const cited = citedNames(cg, usesIt!.id);

    expect(cited).toContain('SanctionSemiconcave'); // the type IS a dependency
    expect(cited).not.toContain('hFsc'); // the binder name is NOT
  });

  it('cites where-struct fields on lines the parser discarded', async () => {
    tmpDir = fs.mkdtempSync(path.join(os.tmpdir(), 'cg-lean-dropped-'));

    // tree-sitter's error recovery does not merely mislabel a `where`-struct,
    // it can drop the tokens outright: in one real witness the tree jumps from
    // the first field straight past four more, so `isClosed_S :=
    // b2CarrierS_isClosed` produces NO identifier node anywhere. Those four
    // lemmas then reported as uncited — which, in a project that uses
    // zero-inbound to decide what is dead, is the expensive kind of wrong.
    //
    // Written with CRLF on purpose. JavaScript's `.` matches neither `\n` nor
    // `\r`, so a trailing-anchored pattern fails on every line of a CRLF file;
    // the first version of this rescue silently recovered edges only from the
    // LF half of a mixed-endings corpus.
    //
    // HONEST LIMIT: like the calc test above, this pins the CONTRACT and not
    // the parser defect. The drop depends on parse state carried from earlier
    // in a real 1,100-line file — verified by dumping the AST of this exact
    // fixture, and of a variant with a deliberately malformed preamble, both of
    // which yield a clean `where_struct` with every `struct_field` present. So
    // this passes with or without `rescueDroppedFieldLines`; what it guards is
    // that the right-hand sides stay cited and the field names stay uncited.
    const crlf = (...lines: string[]): string => lines.join('\r\n') + '\r\n';

    fs.writeFileSync(
      path.join(tmpDir, 'Defs.lean'),
      crlf(
        'def carrierT : Nat := 1',
        'def carrierS : Nat := 2',
        'theorem carrierT_isClosed : True := trivial',
        'theorem carrierS_isClosed : True := trivial',
        'theorem carrierT_nonempty : True := trivial',
        'theorem carrierS_nonempty : True := trivial'
      )
    );

    fs.writeFileSync(
      path.join(tmpDir, 'Witness.lean'),
      crlf(
        'def demoClass : demoParams.ValueClass2 where',
        '  carrier_T := carrierT',
        '  carrier_S := carrierS',
        '  isClosed_T := carrierT_isClosed',
        '  isClosed_S := carrierS_isClosed',
        '  nonempty_T := carrierT_nonempty',
        '  nonempty_S := carrierS_nonempty',
        '  sender_unique_on := fun _ hW => senderUnique hW'
      )
    );

    const cg = await indexFixture(tmpDir);

    const demo = cg.getNodesByKind('function').find((n) => n.name === 'demoClass');
    expect(demo).toBeDefined();
    const cited = citedNames(cg, demo!.id);

    // Every field's right-hand side is a citation; the field names are not.
    for (const rhs of [
      'carrierT_isClosed',
      'carrierS_isClosed',
      'carrierT_nonempty',
      'carrierS_nonempty',
    ]) {
      expect(cited).toContain(rhs);
    }

    // And each cited lemma is no longer reported as unused.
    for (const name of ['carrierS_isClosed', 'carrierS_nonempty']) {
      const lemma = cg.getNodesByKind('function').find((n) => n.name === name);
      expect(lemma).toBeDefined();
      expect(citationsTo(cg, lemma!.id)).toBeGreaterThan(0);
    }
  });

  it('keeps the field after one whose type contains |…|', async () => {
    tmpDir = fs.mkdtempSync(path.join(os.tmpdir(), 'cg-lean-pipes-'));

    // A field whose type contains absolute-value bars opens an ERROR; the
    // parser then resumes MID-FIELD and files the next field's name under the
    // previous field's `binders`. The successor vanished from the index
    // entirely — silent, and every query about it answered confidently about
    // nothing. Absolute value in a hypothesis is ordinary mathematics, so this
    // is not specific to any development.
    fs.writeFileSync(
      path.join(tmpDir, 'Repro.lean'),
      'structure A where\n' +
        '  before : Nat\n' +
        '  multiLineNoPipes :\n' +
        '    ∀ x : Nat,\n' +
        '      x = x\n' +
        '  afterPlain : Nat\n' +
        '  multiLineWithPipes :\n' +
        '    ∀ x y : Nat,\n' +
        '      |(x : Int) - (y : Int)| ≤ 0\n' +
        '  afterPipes : Nat\n' +
        '  tail : Nat\n'
    );

    const cg = await indexFixture(tmpDir);
    const fields = cg.getNodesByKind('field').map((n) => n.name);

    expect(fields).toContain('afterPipes');
    // The plain multi-line field is the control: it never regressed, and its
    // successor must keep working.
    expect(fields).toContain('afterPlain');
    expect(fields).toEqual(
      expect.arrayContaining([
        'before',
        'multiLineNoPipes',
        'afterPlain',
        'multiLineWithPipes',
        'afterPipes',
        'tail',
      ])
    );

    // Reported at its OWN line, not the swallowing field's.
    const afterPipes = cg.getNodesByKind('field').find((n) => n.name === 'afterPipes');
    expect(afterPipes?.startLine).toBe(10);
  });

  it('never treats a field binder as a second field', async () => {
    tmpDir = fs.mkdtempSync(path.join(os.tmpdir(), 'cg-lean-binder-field-'));

    // The guard on the fix above. Recovering a swallowed field means reading
    // names out of a `binders` slot, and everything else in that slot must
    // stay out of the index.
    //
    // Lean 4 does NOT support the grouped form `alpha beta : Nat` — verified
    // against 4.29, which rejects it with "failed to infer type of binder
    // `beta`". Anything sharing a field's line is a BINDER of that field. An
    // earlier version of the fix assumed the Lean 3 reading and minted a
    // spurious field for the parameter of every `tendsto_mul_left m : …` in
    // mathlib.
    fs.writeFileSync(
      path.join(tmpDir, 'Binders.lean'),
      'structure Params where\n' +
        '  tendsto_mul_left m : Nat\n' +
        '  star_inner x y : Nat\n' +
        '  real_field : Nat\n'
    );

    const cg = await indexFixture(tmpDir);
    const fields = cg.getNodesByKind('field').map((n) => n.name);

    expect(fields).toContain('tendsto_mul_left');
    expect(fields).toContain('real_field');
    for (const binder of ['m', 'x', 'y']) expect(fields).not.toContain(binder);
  });

  it('never mints a keyword, command or docstring word as a field', async () => {
    tmpDir = fs.mkdtempSync(path.join(os.tmpdir(), 'cg-lean-debris-'));

    // The other half of the guard. A cascade sweeps whatever follows into the
    // same `binders` slot; measured across mathlib4 and batteries, an earlier
    // rule minted `end`, `export`, `namespace`, `apply`, `at`, `attribute` and
    // individual docstring words as structure fields.
    fs.writeFileSync(
      path.join(tmpDir, 'Debris.lean'),
      'namespace Demo\n' +
        '\n' +
        'structure S where\n' +
        '  chord : ∀ x y : Nat, |(x : Int) - (y : Int)| ≤ 0\n' +
        '  genuine : Nat\n' +
        '\n' +
        '/-- More precisely, it does so in a relative setting:\n' +
        'Then the Leibniz rule asserts for all `x : L` that -/\n' +
        'variable {R : Type} {A : Type}\n' +
        '\n' +
        'attribute [simp] Demo.S.genuine\n' +
        '\n' +
        'end Demo\n'
    );

    const cg = await indexFixture(tmpDir);
    const fields = cg.getNodesByKind('field').map((n) => n.name);

    expect(fields).toContain('genuine');
    for (const debris of [
      'end', 'export', 'namespace', 'attribute', 'variable',
      'More', 'Then', 'Leibniz', 'asserts', 'setting', 'R', 'A',
    ]) {
      expect(fields).not.toContain(debris);
    }
  });

  it('resolves a projection off a binder whose type is written down', async () => {
    tmpDir = fs.mkdtempSync(path.join(os.tmpdir(), 'cg-lean-proj-'));

    // `C.hT_loss_margin` is a real citation, but the head is a binder, so the
    // general rule drops it rather than resolve every `x.val` onto whatever
    // shares the tail's name. When the binder is DECLARED `(C : Cert)` the
    // owner is in the signature already — no elaboration needed.
    //
    // The decisive part is that the emitted reference is OWNER-SCOPED. Two
    // structures here declare a field called `margin`; a bare-tail reference
    // would pick one arbitrarily, which on a real corpus took spurious
    // cross-layer edges from 13 to 158.
    fs.writeFileSync(
      path.join(tmpDir, 'Certs.lean'),
      'structure Cert where\n' +
        '  margin : Nat\n' +
        '  hT_loss_margin : Nat\n' +
        '\n' +
        'structure Decoy where\n' +
        '  margin : Nat\n'
    );

    fs.writeFileSync(
      path.join(tmpDir, 'Uses.lean'),
      'theorem reader (C : Cert) : Nat :=\n' +
        '  C.hT_loss_margin + C.margin\n'
    );

    const cg = await indexFixture(tmpDir);
    const reader = cg.getNodesByKind('function').find((n) => n.name === 'reader');
    expect(reader).toBeDefined();

    const cited = cg
      .getOutgoingEdges(reader!.id)
      .filter((e) => CITES.has(e.kind))
      .map((e) => cg.getNode(e.target))
      .filter((n): n is NonNullable<typeof n> => !!n);

    expect(cited.map((n) => n.name)).toContain('hT_loss_margin');

    // `C.margin` must land on Cert.margin, never Decoy.margin.
    const margin = cited.find((n) => n.name === 'margin');
    expect(margin).toBeDefined();
    expect(margin!.qualifiedName).toContain('Cert');
    expect(margin!.qualifiedName).not.toContain('Decoy');

    // A field of the decoy that nothing projects stays uncited.
    const decoyMargin = cg
      .getNodesByKind('field')
      .find((n) => n.qualifiedName?.includes('Decoy'));
    expect(decoyMargin).toBeDefined();
    expect(citationsTo(cg, decoyMargin!.id)).toBe(0);
  });

  it('does not invent a projection when the binder type is unknown', async () => {
    tmpDir = fs.mkdtempSync(path.join(os.tmpdir(), 'cg-lean-proj-neg-'));

    // The guard. Only a binder with a written-down structure type earns the
    // rewrite; a type variable does not, or the pass degenerates into the
    // bare-tail matching it exists to avoid.
    fs.writeFileSync(
      path.join(tmpDir, 'Neg.lean'),
      'structure Decoy where\n' +
        '  hidden_field : Nat\n' +
        '\n' +
        'theorem opaqueReader {α : Type} (x : α) : Nat :=\n' +
        '  x.hidden_field\n'
    );

    const cg = await indexFixture(tmpDir);
    const reader = cg.getNodesByKind('function').find((n) => n.name === 'opaqueReader');
    expect(reader).toBeDefined();
    expect(citedNames(cg, reader!.id)).not.toContain('hidden_field');
  });

  it('recovers a declaration whose own header opens an unparseable span', async () => {
    tmpDir = fs.mkdtempSync(path.join(os.tmpdir(), 'cg-lean-col0-'));

    // The ERROR-span rescue skipped any header found before the span's first
    // newline, a guard written for spans that begin MID-LINE, where the leading
    // text starts at an arbitrary column. But a span that begins at column 0 is
    // a declaration header that failed to parse, and its own first line is the
    // likeliest thing to rescue. Skipping it discarded exactly one declaration
    // per catastrophic span — invisible, because every OTHER declaration in the
    // file still extracted.
    //
    // The cost was not one node. `affine_sender_chord_on` had no node at all,
    // so its five call sites could not attach to anything, and the tool
    // reported zero consumers for a theorem read by five witness files. That
    // read as a dot-notation blind spot; it was a missing declaration.
    //
    // HONEST LIMIT: like the calc and where-struct tests, this pins the
    // CONTRACT and not the parser state. The real trigger needed ~70 lines of
    // surrounding context — verified by slicing the reporting file, which does
    // reproduce, and by two synthetic reductions that do not. Measured instead
    // on corpora: +36 declarations on the reporting development, +105 on a
    // 3,655-file mathlib slice, +5 on batteries, none lost anywhere.
    fs.writeFileSync(
      path.join(tmpDir, 'Cascade.lean'),
      'namespace Demo\n' +
        '\n' +
        '    p.SomeCombinedChordOn D xT sbar :=\n' +
        '  p.someDecompositionHelper hxT_mem\n' +
        '    (dlo := p.delta) (by rw [hF]; exact someLowerChord p.delta)\n' +
        '\n' +
        '/-- The declaration whose header opens the span. -/\n' +
        'theorem recoveredAtColumnZero (n : Nat) : True := trivial\n' +
        '\n' +
        'theorem afterIt : True := trivial\n' +
        '\n' +
        'end Demo\n'
    );

    const cg = await indexFixture(tmpDir);
    const fns = cg.getNodesByKind('function').map((n) => n.name);
    expect(fns).toContain('recoveredAtColumnZero');
    expect(fns).toContain('afterIt');
  });

  it('keeps the namespace on a declaration recovered from an unparseable file', async () => {
    tmpDir = fs.mkdtempSync(path.join(os.tmpdir(), 'cg-lean-ns-'));

    // When a whole file fails to parse, the rescue used to run on the root span
    // with NO namespace, so every declaration it recovered got a bare qualified
    // name — `helper` instead of `Demo.Inner.helper`. A bare qualified name
    // cannot be matched BY qualified name, so those declarations fall through
    // to short-name matching, which is exactly the collision that produces
    // wrong cross-module edges. Measured: 2,726 declarations on a 3,655-file
    // mathlib slice, 446 on a 148-file development.
    //
    // The prefix now comes from the namespace open at each recovered
    // declaration's OWN line, which is also the only thing that is right for a
    // span crossing a `namespace`/`end`.
    //
    // HONEST LIMIT: this pins the CONTRACT and not the failure. Reproducing it
    // needs a file whose ROOT parses as ERROR, and three attempts here all
    // yielded a clean `module` root with the ERROR as a child, where the walk
    // tracks namespaces normally and both builds pass. The evidence is the
    // corpora: bare qualified names fell 25,218 -> 22,492 on a 3,655-file
    // mathlib slice, 162 -> 119 on batteries, 553 -> 461 on a 148-file
    // development, with node counts unchanged on all three.
    fs.writeFileSync(
      path.join(tmpDir, 'Broken.lean'),
      'namespace Demo\n' +
        'namespace Inner\n' +
        '\n' +
        '    p.DanglingFragment D xT :=\n' +
        '  p.helperCall (dlo := p.delta) (by rw [hF]; exact chord p.delta)\n' +
        '\n' +
        'theorem recoveredInner : True := trivial\n' +
        '\n' +
        'end Inner\n' +
        '\n' +
        'theorem recoveredOuter : True := trivial\n' +
        '\n' +
        'end Demo\n'
    );

    const cg = await indexFixture(tmpDir);
    const fns = cg.getNodesByKind('function');

    const inner = fns.find((n) => n.name === 'recoveredInner');
    const outer = fns.find((n) => n.name === 'recoveredOuter');
    expect(inner).toBeDefined();
    expect(outer).toBeDefined();

    // The prefix must track the line, not the file: `recoveredOuter` sits after
    // `end Inner`, so it is Demo-only even though it is in the same span.
    expect(inner!.qualifiedName).toBe('Demo.Inner.recoveredInner');
    expect(outer!.qualifiedName).toBe('Demo.recoveredOuter');
  });

  it('records a sorry as a dependency so unproven lemmas are a graph query', async () => {
    tmpDir = fs.mkdtempSync(path.join(os.tmpdir(), 'cg-lean-sorry-'));
    fs.writeFileSync(
      path.join(tmpDir, 'Open.lean'),
      'theorem stillOpen : True := by\n  sorry\n'
    );

    const cg = await indexFixture(tmpDir);

    const open = cg.getNodesByKind('function').find((n) => n.name === 'stillOpen');
    expect(open).toBeDefined();

    // `sorryAx` is synthetic: it has no declaration site anywhere in the
    // project, so it never becomes a node and stays a pending reference. That
    // is still useful — "which lemmas are unproven" is a table scan away — but
    // CodeGraph exposes no public accessor for pending refs, so reach through
    // to the query layer rather than assert nothing at all.
    const pending = (
      cg as unknown as {
        queries: { getUnresolvedReferences(): Array<{ referenceName: string }> };
      }
    ).queries.getUnresolvedReferences();
    expect(pending.map((r) => r.referenceName)).toContain('sorryAx');
  });
});
