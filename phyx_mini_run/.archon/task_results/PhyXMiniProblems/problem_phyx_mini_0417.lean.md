# Prover result: `problem_phyx_mini_0417.lean`

## Status

Complete. Both proof obligations are closed:

- `PhyXMiniProblems.ProblemPhyXMini0417.workDoneByGasOnTriangularCycleLegs`
- `PhyXMiniProblems.ProblemPhyXMini0417.netWorkDoneByGasPerTriangularCycle`

The frozen declaration signatures and physical hypotheses were preserved. No
`sorry`, `admit`, axiom, `sorryAx`, or other escape hatch remains in the
assigned file.

## Proof summary

- Transferred the three plotted pressure and volume readouts to the
  corresponding thermodynamic states using
  `plottedCoordinatesAreGasStates`.
- Instantiated the quasistatic straight-leg boundary-work law on all three
  directed legs and substituted their depicted endpoints.
- Normalized the exact conversion
  `101325 / 10^6 J/(atm·cm³)`, deriving leg works `0 J`, `4053/50 J`, and
  `-4053/100 J`.
- Applied cycle-work additivity to obtain exact net work `4053/100 J`.
- Exhausted the four answer labels and proved by exact arithmetic that choice C
  (`40 J`) is the unique nearest displayed value.

## Verification

- `lake env lean PhyXMiniProblems/problem_phyx_mini_0417.lean` exits with code
  `0` and no diagnostics.
- `git diff --check` reports no whitespace errors.
- Source scan finds no `sorry`, `admit`, `axiom`, `sorryAx`, or
  `native_decide`.
- `lean_verify` on the target theorem reports no warnings and only the standard
  foundational axioms `propext`, `Classical.choice`, and `Quot.sound`.

## Blueprint

The supporting lemma and target theorem proof environments are ready for
deterministic `\leanok` synchronization. Per the explicit prover write
permissions, the protected blueprint chapter was not edited.

The requested run-local `.archon/AGENTS.md` is absent, as already noted in
`.archon/PROGRESS.md`; the supplied role instructions and
`.archon/prover-modes/physics.md` were followed.

## Redraft needed

None.
