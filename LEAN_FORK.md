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

Requires **Node ≥ 22.5** (the DB backend uses `node:sqlite`; there is no wasm fallback).

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

## What the delta is

Deliberately small, to keep upstream releases cheap to absorb:

```
 M src/types.ts                      +1    'lean' in the LANGUAGES union
 M src/extraction/grammars.ts        +6    wasm file, .lean extension, display name, vendored set
 M src/extraction/languages/index.ts +2    import + EXTRACTORS entry
 ?? src/extraction/languages/lean.ts        the extractor (~880 lines)
 ?? src/extraction/wasm/tree-sitter-lean.wasm
```

**Three shared files, eight inserted lines.** Every registration entry is inserted *mid-list* next to
`kotlin`, never appended at the end — upstream appends new languages at the tail, so appending there
too would collide on every release. Tests live in their own file rather than upstream's
high-churn `__tests__/extraction.test.ts`, for the same reason.

## Absorbing an upstream release

```bash
git fetch upstream --tags
git checkout main && git merge --ff-only upstream/main
git checkout lean-support && git rebase v<next>
npm run build && npx vitest run
```

Then re-index a Lean project and confirm declaration recovery is still ~98%.

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
typeclass instance resolution, simp-set closure under bare `simp`, coercion insertion,
macro-generated declarations, or generalized dot notation (`b.foo` needs the type of `b`). Those are
decided during elaboration and leave no token behind; for them, Lean's own tooling (`.ilean` files,
or `getUsedConstants` over a built environment) is the answer.
