# Prover result: `problem_phyx_mini_0428.lean`

## Status

Proof-complete but still source-semantics-blocked on mandatory proof-Review
retry 2. The assigned Lean file already contains honest closed proofs of
`derivedTemperatureHeatAndWorkReadouts` and `problem_phyx_mini_0428`; there are
no `sorry` placeholders. No Lean proof-body edit can resolve the reviewer's
remaining answer-choice objection while the declaration signature is frozen.

The existing proof derives the exact modeled efficiency

`((7 : ℝ) + 3 / Real.rpow 6 (2 / 3 : ℝ)) / 25`

from the stated ideal-gas, monatomic internal-energy, first-law, boundary-work,
and adiabatic laws. It then proves that this value lies in the half-cent
rounding interval around `0.32`.

## Verification

- Lean language-server diagnostics: no errors (only blank-line style warnings).
- `lake env lean PhyXMiniProblems/problem_phyx_mini_0428.lean`: exit code 0.
- Source verification: no `sorry`, `admit`, `sorryAx`, `native_decide`, custom
  `axiom`, or metaprogramming escape.
- `lean_verify` for both proved declarations reports only `propext`,
  `Classical.choice`, and `Quot.sound`.
- Every declaration header and hypothesis remains unchanged.

## Blueprint readiness

The lemma
`PhyXMiniProblems.ProblemPhyXMini0428.derivedTemperatureHeatAndWorkReadouts`
and theorem
`PhyXMiniProblems.ProblemPhyXMini0428.problem_phyx_mini_0428`
are proof-closed and ready for deterministic `\leanok` synchronization. The
blueprint was not edited because prover write permissions make it read-only.

## Redraft needed

- Original problem id: `phyx_mini_0428`.
- Source report: `reports/phyx_mini/problem_phyx_mini_0428.source.json`.
- Theorem:
  `PhyXMiniProblems.ProblemPhyXMini0428.problem_phyx_mini_0428`.
- Blocker: the exact efficiency is approximately `0.31634`. It lies in the
  theorem's two-decimal rounding interval around recorded choice D (`0.32`),
  but printed choice C (`0.316`) is numerically closer. Neither the source
  question nor the blueprint states that the efficiency must first be rounded
  to two decimal places. Thus the frozen theorem is provable, but its
  D-selecting reporting convention is not licensed by the source and cannot
  be repaired inside its proof body.
- Smallest faithful change if D is intended: add an explicit source/contract
  requirement that the efficiency is reported to two decimal places before
  matching choices, retaining `RoundsToTwoDecimalPlaces`.
- Alternative if ordinary closest-displayed-value semantics are intended:
  change the recorded answer to C and replace the rounding conclusion with a
  unique-closest-choice predicate over all four displayed values.
