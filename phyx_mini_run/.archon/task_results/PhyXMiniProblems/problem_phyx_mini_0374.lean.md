# Prover result: `problem_phyx_mini_0374.lean`

## Outcome

- Closed `pistonHeightFromIdealGasAndEquilibrium` by eliminating the gas
  pressure and volume from the ideal-gas, cylinder-volume, and vertical-force
  equations. Positivity of the physical pressure, area, mass, and gravity
  establishes the required nonzero denominator.
- Closed `pistonHeight_supportedByFigureAndGoverningLaws`.
  The proof derives the exact centimetre expression from the figure readouts
  and standard constants, proves `3.14156 < π < 3.1417` from the imported
  complex-exponential remainder bound, obtains
  `23.512 cm < h < 23.513 cm`, and checks the four answer constructors to show
  that B is uniquely closest.
- No `sorry` remains, and no declaration signature or hypothesis was changed.
- No redraft is needed.

## Verification

- `lake env lean PhyXMiniProblems/problem_phyx_mini_0374.lean` succeeded.
- `lake build` succeeded.
- Lean LSP diagnostics report no errors or warnings.
- `lean_verify` reports only `propext`, `Classical.choice`, and `Quot.sound`
  for both completed declarations, with no source-scan warnings.
- A direct source scan found no `sorry`, `admit`, `axiom`, `sorryAx`,
  `native_decide`, or whitespace errors.

## Blueprint readiness

- `PhyXMiniProblems.ProblemPhyXMini0374.pistonHeightFromIdealGasAndEquilibrium`
  is proof-closed and ready for deterministic `\leanok` synchronization.
- `PhyXMiniProblems.ProblemPhyXMini0374.pistonHeight_supportedByFigureAndGoverningLaws`
  is proof-closed and ready for deterministic `\leanok` synchronization.
- The blueprint chapter was not edited because prover permissions make it
  read-only and assign marker maintenance to the synchronization phase.
