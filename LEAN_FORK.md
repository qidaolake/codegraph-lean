# CodeGraph — Lean 4 fork

A private fork of [colbymchenry/codegraph](https://github.com/colbymchenry/codegraph) that adds
**Lean 4 (`.lean`) indexing**, so `codegraph_callees` / `codegraph_impact` work on a formalization:
which lemmas a proof cites, what breaks if a definition changes, which lemmas are unused.

Upstream is MIT; the vendored grammar
([Julian/tree-sitter-lean](https://github.com/Julian/tree-sitter-lean), pinned at
`86c2bcb379fe0b2ad13d8b3411400deff75b2785`) is MIT.

## Why a private repo and not a GitHub fork

A GitHub fork of a public repository **cannot be made private** — forks inherit the parent's
visibility. This is a standalone private repo with upstream added as a second remote, which is also
what the rebase workflow below wants.

## Branches

| Branch | Purpose |
|---|---|
| `main` | pure upstream mirror. Never edited — only fast-forwarded from `upstream/main`. |
| `lean-support` | the Lean delta, rebased onto each upstream release. |

## Setting up on another machine

Requires **Node ≥ 22.5 built with FTS5** — and the FTS5 part is the one that bites.

Upstream documents "Node >= 22.5", which is correct for `node:sqlite` *existing*. But the schema
creates an FTS5 virtual table (`src/db/schema.sql`, `nodes_fts USING fts5`), and Node's bundled
SQLite was compiled **without** `SQLITE_ENABLE_FTS5` for much of the 22.x line. On such a build,
indexing dies immediately with:

```
Failed: no such module: fts5
```

That is not a fork problem — it fails during `Initializing CodeGraph`, before any Lean code runs.
Verified: Node 22.21.0 ships SQLite 3.50.4 **with** FTS5; earlier 22.x builds ship 3.47.2 **without**
it. Check the machine — and the specific shell, since a stale `PATH` or nvm default is a common
cause:

```bash
node --version
node -e "const{DatabaseSync}=require('node:sqlite');const d=new DatabaseSync(':memory:');\
console.log(d.prepare('select sqlite_version() v').get().v);\
try{d.exec('CREATE VIRTUAL TABLE t USING fts5(x)');console.log('FTS5 OK')}catch(e){console.log('FTS5 MISSING')}"
```

Expect `FTS5 OK`. If not, upgrade Node — but **upgrade into a window, not forward**.

Upstream's `engines` is `>=20.0.0 <25.0.0`, so the usable range is **Node 22.21+ or 24.x, and
nothing at 25 or above**. On Windows this matters concretely: winget's default `OpenJS.NodeJS`
package is currently 26.x and out of range. Install `OpenJS.NodeJS.LTS` instead.

| Node | Bundled SQLite | FTS5 | In `engines` range |
|---|---|---|---|
| 22.14 | 3.47.2 | no | yes |
| 22.21 | 3.50.4 | **yes** | yes |
| 24.19 | 3.53.3 | **yes** | yes |
| 26.x | — | yes | **no** |

Upstream never hits the FTS5 problem because its installer ships a bundled Node; building this fork
from source uses the system Node instead.

```bash
git clone <your-private-repo-url> codegraph-lean
cd codegraph-lean
git checkout lean-support
npm install
npm run build
```

The compiled Lean grammar (`src/extraction/wasm/tree-sitter-lean.wasm`, 7.5 MB) is committed, so
**no grammar toolchain is needed** to use the fork. See "Rebuilding the grammar" only if you need to
bump it.

Point your MCP client at the built CLI. In `~/.claude.json`:

```json
"codegraph": {
  "type": "stdio",
  "command": "node",
  "args": ["C:/path/to/codegraph-lean/dist/bin/codegraph.js", "serve", "--mcp"],
  "env": { "CODEGRAPH_NO_UPDATE_CHECK": "1" }
}
```

`CODEGRAPH_NO_UPDATE_CHECK=1` matters: without it the server polls upstream releases and nags you to
run `codegraph upgrade`, which is wrong for a fork. Running from a source checkout also makes
`codegraph upgrade` a no-op by design, so it can never overwrite this build — but do **not**
`npm i -g @colbymchenry/codegraph`, which would.

### The MCP surface is one tool by default — widen it for audit work

`tools/list` advertises **only `codegraph_explore`**. That is upstream's deliberate choice
(`DEFAULT_MCP_TOOLS = new Set(['explore'])` in `src/mcp/tools.ts`), on the reasoning that every other
tool is a narrower slice of what explore already does and that their mere presence steers mis-picks.

For a formalization audit that reasoning inverts: `impact`, `callers` and `callees` ARE the
questions. They stay fully functional and callable, but an agent reading the tool list will never
discover them. Re-enable the ones you want with an allowlist, which **replaces** the default:

```json
"env": {
  "CODEGRAPH_NO_UPDATE_CHECK": "1",
  "CODEGRAPH_MCP_TOOLS": "explore,impact,callers,callees,node,search"
}
```

### Filter edge kinds when you query the database directly

`contains` is an edge. A declaration inside `namespace Foo` always has an inbound `contains` edge
from the namespace, so **"has an inbound edge" and "is cited" are different questions** — counting
unfiltered edges makes an uncited lemma look used. Every citation query wants
`WHERE e.kind IN ('calls','instantiates','references')`.

Attributes are queryable too: `@[simp]` and friends are stored as node decorators, so
`SELECT name FROM nodes WHERE decorators LIKE '%simp%'` turns "is this lemma load-bearing or just a
simp lemma?" into a column rather than a manual check.

## What the delta is

Deliberately small, to keep upstream releases cheap to absorb:

```
 M src/types.ts                      +1    'lean' in the LANGUAGES union
 M src/extraction/grammars.ts        +6    wasm file, .lean extension, display name, vendored set
 M src/extraction/languages/index.ts +2    import + EXTRACTORS entry
 ?? src/extraction/languages/lean.ts        the extractor (~1,130 lines)
 ?? src/extraction/wasm/tree-sitter-lean.wasm
 ?? __tests__/lean-extraction.test.ts       precision contract for the dependency graph
```

**Three shared files, eight inserted lines.** Every registration entry is inserted *mid-list* next to
`kotlin`, never appended at the end — upstream appends new languages at the tail, so appending there
too would collide on every release. Tests live in `__tests__/lean-extraction.test.ts` rather than
upstream's high-churn `__tests__/extraction.test.ts`, for the same reason.

## Absorbing an upstream release

```bash
git fetch upstream --tags
git checkout main && git merge --ff-only upstream/main
git checkout lean-support && git rebase v<next>
npm run build && npx vitest run
```

### Validate on more than one corpus

Then re-index and confirm declaration recovery is still ~98% — on **mathlib4 and
batteries as well as your own development**, comparing node counts before and
after, and reading the *diff* rather than the totals.

This is not ceremony. Extraction heuristics look right on the corpus they were
written against and fail elsewhere, and the failure is silent because totals
barely move. A rule for recovering a structure field swallowed by an ERROR
passed on the development that reported the bug, then minted `end`, `export`,
`namespace`, `apply` and `attribute` as structure fields on batteries and
mathlib — visible only as `+4 nodes` unless you list which ones.

The same applies to language assumptions. Lean 4 does **not** accept the
grouped field form `alpha beta : Nat`; it reads `beta` as a binder of `alpha`
and fails to infer its type. When a rule depends on what the language means,
check it against `lake env lean` rather than intuition — Lean 3 habits and
other-language habits both mislead here.

## Indexing scope

Measured on a 209-file development (full numbers in the design note):

| Scope | Resolution | Index time | DB |
|---|---|---|---|
| own code only | 51.3% | 7s | 46 MB |
| **+ direct imports (recommended)** | **61.8%** | 13s | 82 MB |
| + transitive closure | 76.9% | 358s | 1.2 GB |
| + everything | 76.9% | 359s | 1.3 GB |

`.lake/` is gitignored in every Lean project, so **own-code-only is the default with no
configuration**. Resolution saturates at 76.9% — roughly a quarter of references can never resolve
from source alone (dot notation needs types, macro-generated names do not exist in the text). For
comparison, Python and Go projects indexed the ordinary way resolve 26–44%, so partial resolution is
codegraph's normal regime, not a Lean problem.

## Optional: enrich the index from `.ilean` (the elaborated reference graph)

The extractor records what the source text **names**. That is the right contract for an index that
must work on a tree which does not compile, but it can never see what elaboration decides.

Lean already computes the rest, and `lake build` already wrote it to disk. Every module gets a
`.ilean` file — **JSON**, despite the Lake docs describing it as a binary LSP blob — holding:

| key | contents |
|---|---|
| `decls` | fully-qualified declaration name → source range |
| `directImports` | the module's imports: the real layering graph |
| `references` | constant → `[[line, col, line, col, ENCLOSING DECLARATION], …]` |

`references` is the citation graph *after* elaboration, each usage tagged with the declaration that
contains it — the edge set this extractor spends its heuristics approximating.

```bash
lake build                                     # .ilean is a build artifact
node scripts/lean-ilean-enrich.mjs . --dry-run # see what it would add
node scripts/lean-ilean-enrich.mjs .
```

Measured on a 259-file development, against the source-only index:

| | source only | + `.ilean` |
|---|---|---|
| dependency edges | 59,366 | 89,192 (+17,188 new, 0 removed) |
| zero-inbound declarations | 1,594 (30.5%) | 1,386 (26.5%) |
| false "unused" vs elaboration | 249 (15.6%) | 41 (3.0%) |

26.5% is essentially the floor: `.ilean` itself says 25.4% of this project's declarations are cited
by nothing else in it.

**What it does not cover.** `.ilean` records references the elaborator resolved from *written*
syntax. A lemma fired by a bare `simp` is written nowhere, so it does not appear — measured at 5 of
93 `@[simp]` declarations. Those are reachable, but only from the built environment:
`ConstantInfo.value!.getUsedConstants` does return a simp lemma, provided the rewrite was not
definitionally true (when `simp` closes a goal by `rfl` the lemma is erased from the proof term).
That needs a Lean meta-program, not JSON.

**Caveats.**

- Requires a **successful** `lake build`. A stale build means stale edges.
- Edges are tagged `provenance = 'ilean'`; the script deletes its own previous output first, so
  re-running is idempotent. `WHERE provenance IS NULL` isolates the source-extracted graph.
- **Re-indexing rebuilds the edge table and drops them.** Re-run after `codegraph index`, and after
  the file watcher has fired.

That provenance tag is also the cheapest audit available. On the corpus above, all 13 remaining
suspicious `Theory/` → `Examples/` edges carry `provenance IS NULL` and none is corroborated by
`.ilean` — which is the layering claim confirmed from the build rather than argued from a heuristic:

```sql
SELECT e.provenance, count(*) FROM edges e
  JOIN nodes s ON s.id = e.source JOIN nodes t ON t.id = e.target
 WHERE e.kind IN ('calls','instantiates','references')
   AND s.file_path LIKE '%Theory%' AND t.file_path LIKE '%Examples%'
 GROUP BY 1;
```

## Rebuilding the grammar

Only needed to bump the grammar. No Docker or emscripten required — tree-sitter CLI 0.26+
auto-downloads a WASI SDK.

```bash
git clone https://github.com/Julian/tree-sitter-lean
cd tree-sitter-lean && git checkout 86c2bcb379fe0b2ad13d8b3411400deff75b2785
npx tree-sitter-cli@0.26.12 build --wasm .
cp tree-sitter-lean.wasm <fork>/src/extraction/wasm/
```

Then health-check it before trusting it — an ABI-13 grammar silently corrupts the shared wasm heap:

```bash
node scripts/add-lang/check-grammar.mjs src/extraction/wasm/tree-sitter-lean.wasm sample.lean
```

Expect `ABI version: 15` and `RESULT: PASS`.

## Known limits

The extractor records **cited** dependencies — what the source text names. It does not attempt
typeclass instance resolution, simp-set closure under bare `simp`, coercion insertion, or
macro-generated declarations. Those are decided during elaboration and leave no token behind; for
them, Lean's own tooling (`.ilean` files, or `getUsedConstants` over a built environment) is the
answer.

`@[simp]` deserves singling out: an attribute-registered lemma is consumed by `simp` calls that
never name it, so it is cited constantly and textually invisible. No source-level extractor will
ever reclassify these, and neither will `.ilean` (see above). Check the `decorators` column before
believing a zero-inbound result — or reach for `getUsedConstants`, which does see them.

Dot notation is **partly** covered. When the projection's head is a binder whose type is written
down in the signature — `(C : p.StandardComplianceLocalCertificate)`, `variable (solution :
relations.Solution M)` — the owning structure is recoverable from the source alone, and `C.field` is
emitted as `StandardComplianceLocalCertificate.field`, which the resolver matches against that
structure's qualified name.

Scoping to the owner is the whole point, not an implementation detail. Emitting the bare tail
instead recovers a similar number of declarations and takes spurious cross-layer edges from 13 to
158, because field names like `F_mem` and `hFsc` exist in several structures at once.

What remains uncovered is a projection whose head has no written-down type: `fun x => x.val`, a
`have`-bound term, or a head whose type is a variable. For those the answer is still elaboration.
So **a lemma consumed only through an untyped projection still reports as uncited** — treat a
zero-inbound result as "no *textual* citation the extractor can attribute", and grep `\.name\b`
before concluding anything is dead.

Resolution is also **name-based, not import-scoped**: a reference resolves to a same-named node
anywhere in the project. Where two structures share a field name, the edge can land in the wrong
file. Measured on a 259-file development after the bound-name fix: 13 such edges remain, all of
them field-name collisions. So a *layering* query — "does Theory depend on Examples?" — is the one
question to verify against the import graph rather than trust outright.
