# Prover result: `problem_phyx_mini_0027.lean`

## Outcome

Real progress: closed all four assigned sorries. The sorry count changed from
4 to 0.

- `namedImageDistances_eq`: instantiated the four thin-lens equations, used
  positive real-image distances to clear the reciprocal denominators, and
  solved the resulting linear equations to obtain `105 / 4` and `140 / 3`.
- `imageHeight_bPrime_eq`: combined `q_b = 105 / 4`, the `30 cm` object
  distance, the `10 cm` object height, and signed transverse magnification to
  derive `-35 / 4`.
- `imageHeight_cPrime_eq`: combined `q_c = 140 / 3`, the `20 cm` object
  distance, the `10 cm` object height, and signed transverse magnification to
  derive `-70 / 3`.
- `problem_phyx_mini_0027`: reused the exact `c'` height and normalized the
  absolute error against answer D (`-23.3 cm`) to prove the nearest-tenth
  bound.

The declaration signatures and all physical hypotheses were preserved
verbatim. No helper declarations, axioms, admissions, or proof-laundering
constructs were introduced.

## Verification

- Lean LSP diagnostics: no errors and no `declaration uses sorry` warnings.
- `lake env lean PhyXMiniProblems/problem_phyx_mini_0027.lean`: exit code 0.
  The only compiler diagnostic is the pre-existing-signature linter warning
  that `h_planes` is not needed by `namedImageDistances_eq`; the four
  per-corner thin-lens equations plus equal object readouts already determine
  all four scalar image distances.
- Source scan: no `sorry`, `admit`, `axiom`, `sorryAx`, or `native_decide`.
- Axiom verification for
  `PhyXMiniProblems.ProblemPhyXMini0027.problem_phyx_mini_0027` reports only
  Lean's standard `propext`, `Classical.choice`, and `Quot.sound`.

The root Lake package does not register `PhyXMiniProblems/problem_phyx_mini_0027.lean`
as a module target, so the direct `lake env lean` check is the applicable
file-level compilation check.

## Blueprint readiness

The proof environments for `namedImageDistances_eq`,
`imageHeight_bPrime_eq`, `imageHeight_cPrime_eq`, and
`problem_phyx_mini_0027` are ready for `\leanok`. The prover write boundary
forbids editing blueprint chapters, and the project instructions assign
`\leanok` maintenance to the deterministic synchronization phase.

## Redraft needed

None.
