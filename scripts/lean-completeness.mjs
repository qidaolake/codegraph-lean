#!/usr/bin/env node
// Report which declarations the extractor MISSED, using `.ilean` as an oracle.
//
// `lake build` writes, per module, the exact list of declarations that module
// contains. That turns extractor completeness from something you sample into a
// set difference — so a fork can regression-test itself on any project that
// builds, and the number should only ever go down.
//
// Exit codes make it usable in CI:
//   0  no missing declarations, or at or below --max
//   1  more missing than --max allows
//   2  could not run (no index, no build)
//
// Usage:
//   node scripts/lean-completeness.mjs [projectRoot] [--max=N] [--json]
//
// Names that are EXPECTED to differ are excluded rather than counted:
//   - `_private.A.B.0.` mangling on private declarations, stripped before
//     comparing (the extractor reads source and records the plain name);
//   - auto-bound instance names (`instFooBar`), which Lean generates for
//     `instance : Foo Bar` and the extractor names positionally instead;
//   - structure plumbing Lean synthesises and no source line declares
//     (`.mk`, `.rec`, `.recOn`, `.noConfusion`, `.sizeOf`, `.below`, …);
//   - macro-expansion auxiliaries (`_aux_…_macroRules_…`).
//
// STALENESS: the oracle is only as current as the build. A declaration the
// build knows about but the source no longer contains will be reported as
// missing, and it is the BUILD that is wrong. If a reported name does not
// appear in its file at all, re-run `lake build` before believing the number.

import { readFileSync, readdirSync, existsSync } from 'node:fs';
import { join, resolve } from 'node:path';
import { DatabaseSync } from 'node:sqlite';

const argv = process.argv.slice(2);
const asJson = argv.includes('--json');
const maxArg = argv.find((a) => a.startsWith('--max='));
const max = maxArg ? Number(maxArg.slice('--max='.length)) : Infinity;
const root = resolve(argv.find((a) => !a.startsWith('--')) ?? process.cwd());

const dbPath = join(root, '.codegraph', 'codegraph.db');
const buildRoot = join(root, '.lake', 'build');
if (!existsSync(dbPath)) {
  console.error(`[completeness] no index at ${dbPath} — run \`codegraph init\` first`);
  process.exit(2);
}
if (!existsSync(buildRoot)) {
  console.error(`[completeness] no ${buildRoot} — run \`lake build\` first`);
  process.exit(2);
}

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
      if (e.name === 'packages') continue;
      findIleans(p, out);
    } else if (e.name.endsWith('.ilean')) out.push(p);
  }
  return out;
}

const ileans = findIleans(buildRoot);
if (ileans.length === 0) {
  console.error('[completeness] no .ilean files — was the build successful?');
  process.exit(2);
}

const PRIVATE_PREFIX = /^_private\..+?\.\d+\./;
/** Compiler-synthesised members: no source line declares them. */
const SYNTHETIC_TAIL = new Set([
  'mk', 'rec', 'recOn', 'casesOn', 'brecOn', 'below', 'ibelow', 'binductionOn',
  'noConfusion', 'noConfusionType', 'sizeOf', 'sizeOf_spec', 'ofNat', 'ndrec',
  'ndrecOn', 'injEq', 'inj', 'toCtorIdx',
]);
/** Lean's auto-generated name for an anonymous `instance`. */
const AUTO_INSTANCE = /^inst[A-Z]/;
/** Macro-expansion auxiliaries (`_aux_…_macroRules_…`): no source line declares them. */
const MACRO_AUX = /^_aux_/;

const declared = new Map(); // plain fully-qualified name -> { module, line }
for (const file of ileans) {
  let doc;
  try {
    doc = JSON.parse(readFileSync(file, 'utf8'));
  } catch {
    continue;
  }
  for (const [raw, pos] of Object.entries(doc.decls ?? {})) {
    const name = raw.replace(PRIVATE_PREFIX, '');
    const tail = name.slice(name.lastIndexOf('.') + 1);
    if (SYNTHETIC_TAIL.has(tail)) continue;
    if (AUTO_INSTANCE.test(tail)) continue;
    if (MACRO_AUX.test(tail) || MACRO_AUX.test(name)) continue;
    if (!declared.has(name)) {
      declared.set(name, { module: doc.module, line: (pos?.[0] | 0) + 1 });
    }
  }
}

const db = new DatabaseSync(dbPath);
const haveQualified = new Set();
const haveShort = new Set();
for (const row of db
  .prepare(
    `SELECT name, qualified_name FROM nodes
      WHERE kind IN ('function','struct','enum','class','field','method','constant')`
  )
  .all()) {
  if (row.qualified_name) haveQualified.add(row.qualified_name);
  haveShort.add(String(row.name));
}

const missing = [];
for (const [name, where] of declared) {
  if (haveQualified.has(name)) continue;
  // A short-name hit means the declaration IS indexed; a qualified-name
  // mismatch is a different defect and this tool does not conflate them.
  if (haveShort.has(name.slice(name.lastIndexOf('.') + 1))) continue;
  missing.push({ name, ...where });
}
missing.sort((a, b) => (a.module === b.module ? a.line - b.line : a.module < b.module ? -1 : 1));

const pct = ((100 * missing.length) / Math.max(declared.size, 1)).toFixed(2);
if (asJson) {
  console.log(JSON.stringify({ declared: declared.size, missing: missing.length, pct: Number(pct), items: missing }, null, 2));
} else {
  console.log(`[completeness] ${ileans.length} module(s), ${declared.size} declarations in .ilean`);
  console.log(`[completeness] absent from the index: ${missing.length} (${pct}%)`);
  const byModule = new Map();
  for (const m of missing) byModule.set(m.module, (byModule.get(m.module) ?? 0) + 1);
  if (byModule.size) console.log(`[completeness] across ${byModule.size} module(s)`);
  for (const m of missing.slice(0, 40)) {
    console.log(`  ${m.module.split('.').pop()}:${m.line}  ${m.name.slice(m.name.lastIndexOf('.') + 1)}`);
  }
  if (missing.length > 40) console.log(`  … and ${missing.length - 40} more (use --json for all)`);
}

if (missing.length > max) {
  console.error(`[completeness] FAIL: ${missing.length} missing exceeds --max=${max}`);
  process.exit(1);
}
