#!/usr/bin/env node
// Enrich a Lean CodeGraph index with the ELABORATED reference graph that
// `lake build` already wrote to disk.
//
// WHY THIS EXISTS
// ---------------
// The extractor records what the source text NAMES. That is the right contract
// for an index that must work on a tree that does not compile, but it can never
// see what elaboration decides: `x.val` needs the type of `x`, a coercion leaves
// no token, `simp` names nothing.
//
// Lean already computes all of this. Every `lake build` writes a `.ilean` file
// per module — JSON, not the opaque blob the Lake docs imply — containing:
//
//   decls          fully-qualified name -> source range
//   directImports  the module's imports, i.e. the real layering graph
//   references     constant -> [[l, c, l, c, ENCLOSING DECLARATION], ...]
//
// `references` is the citation graph after elaboration, with each usage tagged
// by the declaration that contains it. That is exactly the edge set the
// extractor approximates, and it is free: the build already paid for it.
//
// Measured on a 259-file development, this adds the projections the source
// walk cannot attribute (`Subtype.val`, `p.δ`, `C.field` off an untyped head)
// and drops zero-inbound declarations well below what any heuristic reaches.
//
// WHAT IT STILL DOES NOT COVER
// ----------------------------
// `.ilean` records references the elaborator resolved from WRITTEN syntax. A
// lemma fired by a bare `simp` is not written anywhere, so it does not appear —
// verified at 5 of 93 `@[simp]` declarations on the corpus above. Those need
// `getUsedConstants` over the built environment, which does capture them (a
// `simp` rewrite that is not definitionally true leaves its lemma in the proof
// term). That is a different tool: it needs a Lean meta-program, not JSON.
//
// CAVEATS
// -------
//   - Requires a SUCCESSFUL `lake build`. A stale build means stale edges.
//   - Added edges are tagged `provenance = 'ilean'` and this script deletes its
//     own previous output first, so re-running is idempotent. Corrected edges
//     are tagged `'ilean-repoint'` and are NOT deleted on re-run: the wrong
//     original they replaced is already gone, so removing them would just lose
//     the correction. A full re-index restores the originals and the next run
//     corrects them again.
//   - `codegraph index` rebuilds the edge table and drops the added edges.
//   - `codegraph sync` does NOT drop them outside the files it re-indexed — but
//     it DOES undo the pruning, because pruning deletes SOURCE-resolved edges
//     and sync re-extracts exactly those from source. Measured: a pruned pair
//     went 0 -> 65 after editing one unrelated file and syncing.
//
//     So the rule is simply "re-run after sync too", which costs ~2s and is
//     idempotent. Doing better means applying the import-closure constraint
//     when the edge is CREATED rather than deleting it afterwards, and that
//     lives in codegraph's resolver: `getNodesByName` is cached globally by
//     name with no requesting-module parameter, so scoping it means threading
//     module reachability through `src/resolution/index.ts` and
//     `name-matcher.ts` — both high-churn upstream files this fork otherwise
//     does not touch. Deliberately not done; see LEAN_FORK.md.
//
//   - It also PRUNES impossible edges (see below). `--no-prune` disables that.
//
// Usage: node scripts/lean-ilean-enrich.mjs [projectRoot] [--dry-run] [--no-prune]

import { readFileSync, readdirSync, existsSync, statSync } from 'node:fs';
import { join, resolve } from 'node:path';
import { DatabaseSync } from 'node:sqlite';

const argv = process.argv.slice(2);
const dryRun = argv.includes('--dry-run');
const noPrune = argv.includes('--no-prune');
const root = resolve(argv.find((a) => !a.startsWith('--')) ?? process.cwd());

const dbPath = join(root, '.codegraph', 'codegraph.db');
if (!existsSync(dbPath)) {
  console.error(`[ilean] no index at ${dbPath} — run \`codegraph init\` first`);
  process.exit(2);
}

/** Every `.ilean` under the project's own build tree (never dependencies'). */
function findIleans(dir, out = []) {
  let entries;
  try {
    entries = readdirSync(dir, { withFileTypes: true });
  } catch {
    return out;
  }
  for (const e of entries) {
    const p = join(dir, e.name);
    if (e.isDirectory()) {
      if (e.name === 'packages') continue; // dependency builds are not this project
      findIleans(p, out);
    } else if (e.name.endsWith('.ilean')) {
      out.push(p);
    }
  }
  return out;
}

const buildRoot = join(root, '.lake', 'build');
if (!existsSync(buildRoot)) {
  console.error(`[ilean] no ${buildRoot} — run \`lake build\` first`);
  process.exit(2);
}
const ileans = findIleans(buildRoot);
if (ileans.length === 0) {
  console.error('[ilean] no .ilean files found — was the build successful?');
  process.exit(2);
}

const db = new DatabaseSync(dbPath);

// ---------------------------------------------------------------------------
// Name resolution: Lean's fully-qualified name -> a node in the index
// ---------------------------------------------------------------------------
const byQualified = new Map();
const byShort = new Map();
// Only kinds a citation can actually target. Including `namespace` / `import` /
// `file` rows made a declaration look AMBIGUOUS whenever its qualified name
// matched a namespace node of the same name — `Sanctions.Foundations.Foo` as
// both a namespace and a structure — and `resolveName` declines ambiguity, so
// those citations were silently dropped. Invisible until the namespace fix made
// qualified names correct enough to start colliding.
const TARGET_KINDS = "('function','struct','enum','class','field','method','constant')";

const nodeFile = new Map();
for (const row of db
  .prepare(`SELECT id, name, qualified_name, file_path FROM nodes WHERE kind IN ${TARGET_KINDS}`)
  .all()) {
  if (row.qualified_name) {
    const bucket = byQualified.get(row.qualified_name);
    if (bucket) bucket.push(row.id);
    else byQualified.set(row.qualified_name, [row.id]);
  }
  const short = String(row.name);
  const sb = byShort.get(short);
  if (sb) sb.push(row.id);
  else byShort.set(short, [row.id]);
  nodeFile.set(row.id, String(row.file_path));
}

/**
 * Strip Lean's `private` name mangling.
 *
 * A `private theorem foo` in module `A.B` is stored by the elaborator as
 * `_private.A.B.0.A.B.foo`, and `.ilean` reports that mangled form. The
 * extractor sees the source and records `A.B.foo`, which is correct — so
 * without this the two never meet. Measured at 361 declarations on a 148-file
 * development, all of them resolvable once the prefix comes off.
 */
const PRIVATE_PREFIX = /^_private\..+?\.\d+\./;
const unmanglePrivate = (n) => n.replace(PRIVATE_PREFIX, '');

/**
 * A Lean name resolves when the index holds exactly one node for it.
 *
 * Exact qualified name first (93.5% of declarations on the measured corpus).
 * The short-name fallback applies ONLY when unambiguous — the whole value of
 * `.ilean` is that its names are unambiguous, so guessing between candidates
 * would throw that away and reintroduce the collisions it fixes.
 */
function resolveName(rawFqn) {
  const fqn = unmanglePrivate(rawFqn);
  const exact = byQualified.get(fqn);
  if (exact && exact.length === 1) return exact[0];
  if (exact && exact.length > 1) return null;
  const short = byShort.get(fqn.slice(fqn.lastIndexOf('.') + 1));
  return short && short.length === 1 ? short[0] : null;
}

// ---------------------------------------------------------------------------
// Walk the reference graph
// ---------------------------------------------------------------------------
/** module -> its direct imports, straight from `.ilean`. The real module graph. */
const directImports = new Map();

let usages = 0;
let selfRefs = 0;
let unresolvedTarget = 0;
let unresolvedSource = 0;
const pending = new Map(); // "src|tgt|line" -> {source, target, line, col}

for (const file of ileans) {
  let doc;
  try {
    doc = JSON.parse(readFileSync(file, 'utf8'));
  } catch {
    console.error(`[ilean] skipping unreadable ${file}`);
    continue;
  }
  if (typeof doc.module === 'string') {
    directImports.set(
      doc.module,
      (doc.directImports ?? []).map((i) => (Array.isArray(i) ? i[0] : i)).filter((x) => typeof x === 'string')
    );
  }
  for (const [key, entry] of Object.entries(doc.references ?? {})) {
    if (!key.startsWith('{')) continue;
    let constName;
    try {
      constName = JSON.parse(key)?.c?.n;
    } catch {
      continue;
    }
    if (typeof constName !== 'string') continue;
    const target = resolveName(constName);
    for (const u of entry.usages ?? []) {
      usages++;
      const enclosing = u[4];
      if (typeof enclosing !== 'string') continue;
      if (target === null) { unresolvedTarget++; continue; }
      const source = resolveName(enclosing);
      if (source === null) { unresolvedSource++; continue; }
      if (source === target) { selfRefs++; continue; }
      // `.ilean` positions are 0-based; the index stores 1-based lines.
      const line = (u[0] | 0) + 1;
      pending.set(`${source}|${target}|${line}`, { source, target, line, col: u[1] | 0 });
    }
  }
}

// ---------------------------------------------------------------------------
// Prune: an edge into a module the source module cannot reach is impossible
// ---------------------------------------------------------------------------
//
// `directImports` is the real module graph, and Lean has no cycles in it. If
// module B is not in module A's transitive import closure, then nothing in A
// can name anything in B — not through elaboration, not through a macro, not at
// all. Any such edge is a resolver artifact.
//
// This is what closes name-based resolution: a reference resolves to a
// same-named node anywhere in the project, so `F_mem` declared in five
// structures lands wherever the index looked first. Those wrong edges are worst
// exactly where they are most believable — a layering query ("does Theory
// depend on Examples?") reads as authoritative and is not.
//
// The rule only fires when BOTH endpoints sit in modules this build knows, so a
// file that failed to compile, or a directory outside the Lean library, is left
// alone rather than silently stripped.

/** `Sanctions.Theory.Foo` -> `Sanctions/Theory/Foo.lean`, matching node paths. */
const moduleToPath = (m) => `${m.split('.').join('/')}.lean`;

/** Node paths use the host separator; module paths never do. */
const fwd = (p) => String(p).split(String.fromCharCode(92)).join('/');

const pathToModule = new Map();
for (const m of directImports.keys()) pathToModule.set(moduleToPath(m), m);

/**
 * Transitive import closure, memoised. Lean forbids import cycles.
 *
 * `complete` is false when the walk hit a module this build has no `.ilean`
 * for, which means its own imports are unknown and the closure may be missing
 * branches. Pruning on a truncated closure would delete real edges, so callers
 * must skip those source modules entirely. Dependency modules (mathlib, core)
 * are expected to be absent and are not the concern — only a module whose
 * declarations are IN the index can be a prune target, and those all have
 * `.ilean` files or the build did not succeed.
 */
const closureCache = new Map();
function importClosure(mod) {
  const hit = closureCache.get(mod);
  if (hit) return hit;
  const seen = new Set();
  let complete = true;
  const stack = [...(directImports.get(mod) ?? [])];
  while (stack.length) {
    const next = stack.pop();
    if (seen.has(next)) continue;
    seen.add(next);
    const imports = directImports.get(next);
    // Unknown module: only truncating if something in the index lives there.
    if (imports === undefined) {
      if (indexedModules.has(next)) complete = false;
      continue;
    }
    for (const d of imports) if (!seen.has(d)) stack.push(d);
  }
  const result = { modules: seen, complete };
  closureCache.set(mod, result);
  return result;
}

/** Modules that actually hold indexed nodes — the only possible prune targets. */
const indexedModules = new Set();
for (const r of db.prepare('SELECT DISTINCT file_path FROM nodes').all()) {
  const m = pathToModule.get(fwd(r.file_path));
  if (m) indexedModules.add(m);
}

/** name -> [{id, module}] for every node that could be a citation target. */
const candidatesByName = new Map();
for (const r of db
  .prepare(`SELECT id, name, file_path FROM nodes WHERE kind IN ${TARGET_KINDS}`)
  .all()) {
  const bucket = candidatesByName.get(r.name);
  const entry = { id: r.id, module: pathToModule.get(fwd(r.file_path)) };
  if (bucket) bucket.push(entry);
  else candidatesByName.set(r.name, [entry]);
}

let impossible = [];
let repoint = [];
let skippedTruncated = 0;

/**
 * Find every citation edge whose target module the source module cannot reach.
 *
 * Run AFTER the enrichment rows are inserted, deliberately: `resolveName`'s
 * short-name fallback can land on a same-named declaration in an unreachable
 * module, and this is the check that catches it. Measured at 96 of 30,060
 * added edges (0.3%) — small, but they are exactly the wrong-target kind this
 * pass exists to remove, so it must police its own output too.
 */
function findImpossible() {
  impossible = [];
  repoint = [];
  skippedTruncated = 0;
  const rows = db
    .prepare(
      `SELECT e.id, e.provenance, e.source, e.kind, e.line, e.col,
              s.file_path AS sf, t.file_path AS tf, s.name AS sn, t.name AS tn
         FROM edges e JOIN nodes s ON s.id = e.source JOIN nodes t ON t.id = e.target
        WHERE e.kind IN ('calls','instantiates','references')`
    )
    .all();
  for (const r of rows) {
    const srcMod = pathToModule.get(fwd(r.sf));
    const tgtMod = pathToModule.get(fwd(r.tf));
    if (!srcMod || !tgtMod || srcMod === tgtMod) continue;
    const closure = importClosure(srcMod);
    if (!closure.complete) { skippedTruncated++; continue; }
    if (closure.modules.has(tgtMod)) continue;
    // The citation is real — a token was written — but it landed on a module
    // the source cannot see. If exactly ONE declaration of that name is
    // reachable, that is necessarily the one meant, so move the edge instead of
    // dropping it. Deleting would lose the dependency altogether, and a lost
    // dependency reads as "safe to change" — the direction that costs most.
    const reachable = (candidatesByName.get(r.tn) ?? []).filter(
      (c) => c.module && (c.module === srcMod || closure.modules.has(c.module))
    );
    if (reachable.length === 1) {
      repoint.push({
        id: r.id, to: reachable[0].id,
        source: r.source, kind: r.kind, line: r.line, col: r.col,
      });
    }
    else impossible.push(r);
  }
}
if (!noPrune) findImpossible();

const existing = new Set(
  db
    .prepare("SELECT source, target, line FROM edges WHERE kind IN ('calls','instantiates','references')")
    .all()
    .map((r) => `${r.source}|${r.target}|${r.line}`)
);
const fresh = [...pending.values()].filter(
  (e) => !existing.has(`${e.source}|${e.target}|${e.line}`)
);

console.log(`[ilean] ${ileans.length} module(s), ${usages} recorded usages`);
console.log(`[ilean]   resolvable project-internal citations: ${pending.size}`);
console.log(`[ilean]   target outside the index (core/mathlib): ${unresolvedTarget}`);
console.log(`[ilean]   enclosing declaration not in the index: ${unresolvedSource}`);
console.log(`[ilean]   self-references skipped: ${selfRefs}`);
console.log(`[ilean]   NOT already present as an edge: ${fresh.length}`);
if (!noPrune) {
  const bySrc = new Map();
  for (const r of impossible) {
    const k = `${fwd(r.sf)} -> ${fwd(r.tf)}`;
    bySrc.set(k, (bySrc.get(k) ?? 0) + 1);
  }
  const fromIlean = impossible.filter((r) => r.provenance === 'ilean').length;
  console.log(`[ilean] IMPOSSIBLE edges (target module not in the source module's import closure): ${impossible.length + repoint.length}`);
  console.log(`[ilean]   re-pointed to the one reachable declaration of that name: ${repoint.length}`);
  console.log(`[ilean]   deleted (no reachable declaration of that name): ${impossible.length}`);
  console.log(`[ilean]   across ${bySrc.size} file pair(s); ${fromIlean} of them from this script's own output`);
  if (skippedTruncated) {
    console.log(`[ilean]   ${skippedTruncated} edge(s) left alone: their module's import closure is incomplete`);
  }
  for (const [pair, n] of [...bySrc.entries()].sort((a, b) => b[1] - a[1]).slice(0, 8)) {
    console.log(`[ilean]     ${n.toString().padStart(4)}  ${pair}`);
  }
}


// Drop enrichment rows that the import graph forbids BEFORE writing them.
// `resolveName`'s short-name fallback can land on a same-named declaration in a
// module the source cannot reach; inserting those and deleting them again in
// the prune below worked, but made every run redo the same 96 rows.
let misresolved = 0;
if (!noPrune) {
  for (const [key, e] of [...pending.entries()]) {
    const sm = pathToModule.get(fwd(nodeFile.get(e.source)));
    const tm = pathToModule.get(fwd(nodeFile.get(e.target)));
    if (!sm || !tm || sm === tm) continue;
    const closure = importClosure(sm);
    if (!closure.complete || closure.modules.has(tm)) continue;
    pending.delete(key);
    misresolved++;
  }
  if (misresolved) {
    console.log(`[ilean]   ${misresolved} enrichment row(s) dropped: name resolved into an unreachable module`);
  }
}

if (dryRun) {
  console.log('[ilean] --dry-run: nothing written');
  process.exit(0);
}

const priorRow = db.prepare("SELECT count(*) AS n FROM edges WHERE provenance = 'ilean'").get();
db.exec('BEGIN');
try {
  db.exec("DELETE FROM edges WHERE provenance = 'ilean'");
  const insert = db.prepare(
    `INSERT OR IGNORE INTO edges (source, target, kind, metadata, line, col, provenance)
     VALUES (?, ?, 'calls', NULL, ?, ?, 'ilean')`
  );
  for (const e of pending.values()) insert.run(e.source, e.target, e.line, e.col);

  // Prune LAST, over the table the enrichment just wrote, so the pass polices
  // its own output as well as the extractor's. Doing it first left 96
  // mis-resolved enrichment edges behind and made a second run find work to do.
  if (!noPrune) {
    findImpossible();
    const drop = db.prepare('DELETE FROM edges WHERE id = ?');
    for (const r of impossible) drop.run(r.id);
    // Delete-then-insert rather than UPDATE: `idx_edges_identity` makes
    // (source, target, kind, line, col) unique, so an UPDATE onto an edge that
    // already exists silently does nothing and leaves the WRONG row in place.
    const add = db.prepare(
      `INSERT OR IGNORE INTO edges (source, target, kind, metadata, line, col, provenance)
       VALUES (?, ?, ?, NULL, ?, ?, 'ilean-repoint')`
    );
    for (const r of repoint) {
      drop.run(r.id);
      add.run(r.source, r.to, r.kind, r.line, r.col);
    }
    console.log(
      `[ilean] pruned after insert: deleted ${impossible.length}, re-pointed ${repoint.length}`
    );
  }
  db.exec('COMMIT');
} catch (err) {
  db.exec('ROLLBACK');
  console.error('[ilean] write failed, index unchanged:', err.message);
  process.exit(1);
}

const after = db.prepare("SELECT count(*) AS n FROM edges WHERE provenance = 'ilean'").get();
console.log(`[ilean] wrote ${after.n} edges tagged provenance='ilean' (replaced ${priorRow.n})`);
console.log("[ilean] re-indexing drops these — re-run after `codegraph index` (`sync` is fine)");
