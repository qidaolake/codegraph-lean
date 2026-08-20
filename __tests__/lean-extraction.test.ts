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
