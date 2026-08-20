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
//   - Edges are tagged `provenance = 'ilean'` and this script deletes its own
//     previous output first, so re-running is idempotent.
//   - Re-indexing (`codegraph index`, or the file watcher) rebuilds the edge
//     table and DROPS these. Re-run afterwards.
//
// Usage: node scripts/lean-ilean-enrich.mjs [projectRoot] [--dry-run]

import { readFileSync, readdirSync, existsSync, statSync } from 'node:fs';
import { join, resolve } from 'node:path';
import { DatabaseSync } from 'node:sqlite';

const argv = process.argv.slice(2);
const dryRun = argv.includes('--dry-run');
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
for (const row of db.prepare('SELECT id, name, qualified_name FROM nodes').all()) {
  if (row.qualified_name) {
    const bucket = byQualified.get(row.qualified_name);
    if (bucket) bucket.push(row.id);
    else byQualified.set(row.qualified_name, [row.id]);
  }
  const short = String(row.name);
  const sb = byShort.get(short);
  if (sb) sb.push(row.id);
  else byShort.set(short, [row.id]);
}

/**
 * A Lean name resolves when the index holds exactly one node for it.
 *
 * Exact qualified name first (93.5% of declarations on the measured corpus).
 * The short-name fallback applies ONLY when unambiguous — the whole value of
 * `.ilean` is that its names are unambiguous, so guessing between candidates
 * would throw that away and reintroduce the collisions it fixes.
 */
function resolveName(fqn) {
  const exact = byQualified.get(fqn);
  if (exact && exact.length === 1) return exact[0];
  if (exact && exact.length > 1) return null;
  const short = byShort.get(fqn.slice(fqn.lastIndexOf('.') + 1));
  return short && short.length === 1 ? short[0] : null;
}

// ---------------------------------------------------------------------------
// Walk the reference graph
// ---------------------------------------------------------------------------
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
  db.exec('COMMIT');
} catch (err) {
  db.exec('ROLLBACK');
  console.error('[ilean] write failed, index unchanged:', err.message);
  process.exit(1);
}

const after = db.prepare("SELECT count(*) AS n FROM edges WHERE provenance = 'ilean'").get();
console.log(`[ilean] wrote ${after.n} edges tagged provenance='ilean' (replaced ${priorRow.n})`);
console.log("[ilean] re-indexing drops these — re-run after `codegraph index`");
