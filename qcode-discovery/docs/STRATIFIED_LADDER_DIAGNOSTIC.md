# Stratified target-aware ladder diagnostic

This diagnostic is a read-only decision gate after the published-volume
twisted-torus search sealed exactly 12 Stage-1 rounds. It does not add a
thirteenth round, mutate the source pipeline, or promote a code into a release.

## Frozen cohort

- Select 64 candidates (within the requested 48–96 range).
- Require a currently replayable two-sector `w <= 4` UNSAT proof, hence a
  formal search lower bound `d >= 5`.
- Exclude Stage-1 audits, committed/pending/deferred Stage-2 selections,
  current known-code registry matches, and replayable structural
  target-negative witnesses.
- Balance the cohort over published volume, lattice, lattice–twist cell,
  algebraic mechanism, and support split. BP/OSD fields receive no selection
  credit.
- Bind the exact ranked snapshot, source inputs, registry, source ledger bytes,
  selected rows, runtime, and diagnostic implementation by SHA-256.

The source pipeline has no external candidate-reservation API. Therefore the
cohort is formally “unaudited at first diagnostic launch.” If the source
pipeline later evaluates the same candidate, that may duplicate work but does
not alter the frozen diagnostic evidence.

## Proof ladder

For each candidate, run both logical sectors at:

1. `w <= 6`;
2. `w <= 8`;
3. `w <= required_distance - 1`, if still unresolved.

A SAT result counts only after its logical operator replays against the exact
matrices. A lower bound advances only when both sectors return replayable
UNSAT. UNKNOWN, timeout, worker failure, and proof-verification failure all
stop that candidate and count it as a fail-open survivor.

## Preregistered decision

For `N=64`:

- Change ansatz within generalized-toric/BB when at least 52 candidates are
  excluded by `w <= 8`, at most 12 survive, no candidate reaches `LB >= 9`,
  and no candidate has target gap at most 3.
- Retain the generalized-toric/BB family for targeted deep proof when at least
  13 survive `w <= 8`, or any candidate reaches `LB >= 9`, or any candidate
  has target gap at most 3.
- Retention signals take precedence if signals overlap. Neither outcome
  authorizes abandoning the whole algebraic family.

The next same-family ansatz must make variable support splits genuinely
reachable, remove fixed `1+x`/`1+y` anchors, use replayed X/Z witnesses only as
negative structural feedback, enforce volume/lattice–twist/mechanism audit
quotas (including volumes 127 and 132), and reconstruct published anchors
blindly rather than injecting them.

A switch to a different algebraic family is allowed only after a preregistered
finite richer-ansatz domain is completely audited, every candidate is excluded
by a trusted upper bound, and there are no unresolved entries. A future
different-family template may then use constructions such as the
[Panteleev–Kalachev lifted product](https://arxiv.org/abs/2012.04068). BP/OSD
remains diagnostic only, consistent with the caution required by the
[qcode-discovery project](https://github.com/qiskit-community/qcode-discovery).
