# Prover result: `problem_phyx_mini_0292`

## Status

Complete. All four `sorry` placeholders in
`PhyXMiniProblems/problem_phyx_mini_0292.lean` were replaced by sound proofs,
with no declaration header or physical contract changed.

## Proofs completed

- `stringOneSupportingTensions_are_49_over_20_newtons`: ideal tension
  transmission equates the two String-1 support tensions; movable-pulley
  equilibrium, `M = 1/2 kg`, and `g = 49/5 m/s²` then give `49/20 N` for
  each tension.
- `stringTwoTension_is_49_over_20_newtons`: massless-knot equilibrium
  transfers the right String-1 support tension to the knot-side segment of
  String 2.
- `stringTwoWaveSpeed_exact`: positivity makes the String-2 density nonzero;
  substituting `T₂ = 49/20 N` and `μ₂ = 5/1000 kg/m` into the taut-string
  wave law gives the exact readout `Real.sqrt 490`.
- `problem_phyx_mini_0292`: after unfolding recorded choice D, the proof uses
  `Real.sqrt_nonneg` and `Real.sq_sqrt` to certify
  `|sqrt 490 - 22.1| ≤ 0.05` by nonlinear arithmetic.

## Verification

- `lake env lean PhyXMiniProblems/problem_phyx_mini_0292.lean` exited with
  code 0 and produced no diagnostics.
- A source scan found no remaining `sorry`, `admit`, declaration-level
  `axiom`, `sorryAx`, or `native_decide`.
- No file-specific `/- USER: ... -/` comment is present.

## Blueprint synchronization

The proof descriptions in
`blueprint/src/chapters/PhyXMiniProblems_problem_phyx_mini_0292.tex` match the
completed Lean derivation. The blueprint was not edited because this prover
task explicitly grants write access only to the assigned Lean file and this
result file. The coordinating synchronization phase should add `\leanok` to
the three completed lemma environments and the target theorem environment.

## Redraft needed

None.

## Environment note

The requested project file `.archon/AGENTS.md` is absent from this workspace.
The supplied prover-stage instructions, `.archon/PROGRESS.md`, the physics
blueprint chapter, and the iteration-015 proof plan provided the applicable
role and proof guidance.
