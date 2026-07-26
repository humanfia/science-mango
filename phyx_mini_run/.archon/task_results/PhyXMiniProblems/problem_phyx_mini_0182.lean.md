# Prover result: `problem_phyx_mini_0182.lean`

## Outcome

Closed both placeholders without changing either declaration signature:

- `linearDensity_harmonic_ratio`
- `problem_phyx_mini_0182`

There are no remaining `sorry`, `admit`, `sorryAx`, `native_decide`, or local
axiom declarations in the assigned file.

## Proof summary

At SI readouts, the standing-wave laws and equal string lengths give
`n_left * lambda_left = n_right * lambda_right`. Equal driving frequencies and
wave kinematics then give `n_left * v_left = n_right * v_right`. Squaring this
relation and combining it with the two stretched-string tension laws and
spring force balance yields the density/harmonic relation after cancelling
the strictly positive left speed.

The `Dimensionful` scaling law transports that SI relation to an arbitrary
coherent unit choice. The final theorem applies the ratio lemma, substitutes
the figure readouts `n_left = 2`, `n_right = 3` and
`mu_left = mu_0`, and proves equality of the dimensionful quantities by
extensionality.

## Verification

- `archon-lean-lsp` diagnostics: success, no errors or warnings.
- `lake env lean PhyXMiniProblems/problem_phyx_mini_0182.lean`: success.
- `git diff --check`: success.
- Axiom audit for both proved declarations reports only Lean's standard
  `propext`, `Classical.choice`, and `Quot.sound`; the source scan reports no
  suspicious proof escapes.

## Notes

- Source report:
  `reports/phyx_mini/problem_phyx_mini_0182.source.json`.
- No `/- USER: ... -/` hint occurs in the assigned Lean file.
- The requested `.archon/AGENTS.md` is absent from this checkout; the injected
  prover instructions and `.archon/prover-modes/physics.md` were followed.
- The blueprint was not edited because the prover lane explicitly permits
  writes only to the assigned Lean file and this result file. A synchronization
  agent should add `\leanok` to the environments for
  `linearDensity_harmonic_ratio` and `problem_phyx_mini_0182`.
- No redraft is needed.
