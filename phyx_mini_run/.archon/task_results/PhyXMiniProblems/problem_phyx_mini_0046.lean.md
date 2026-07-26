# Prover result: `PhyXMiniProblems/problem_phyx_mini_0046.lean`

## Outcome

- Closed the sole `sorry` in
  `PhyXMiniProblems.ProblemPhyXMini0046.wavelength_rounds_to_recordedAnswerB`.
- Preserved the declaration signature and all physical hypotheses.
- No `sorry`, `admit`, `axiom`, or `sorryAx` remains in the assigned file.

## Proof

The proof derives the exact Physlib unit conversions
`1 mm = 1000 m-readout units` and `1 nm = 10^9 m-readout units` from each
`Dimensionful` length's scaling law. It then obtains

- `tan θ = 949 / 100000`,
- `λ_nm = (200000 / 3) sin θ`, and
- `10000900601 sin² θ = 900601`

from the screen geometry, bright-fringe law, and
`sin² θ + cos² θ = 1`. Exact polynomial arithmetic proves
`632.5 ≤ λ_nm < 633.5`, and `round_eq_iff` yields `round λ_nm = 633`.

## Verification

- Lean LSP diagnostics: no errors.
- `lake env lean PhyXMiniProblems/problem_phyx_mini_0046.lean`: exit code 0.
- Axiom/source verification reports only standard imported foundations:
  `propext`, `Classical.choice`, and `Quot.sound`; no suspicious source
  patterns.

## Blueprint status

The target theorem proof environment
`thm:physics:phyx_mini_0046:target` is ready for the deterministic
`\leanok` synchronization. The blueprint was not edited because prover
permissions make it read-only.

## Redraft needed

None.
