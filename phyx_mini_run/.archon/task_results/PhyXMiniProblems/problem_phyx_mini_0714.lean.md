# Result: `problem_phyx_mini_0714.lean`

## Status

Complete. The sole `sorry` in
`PhyXMiniProblems.ProblemPhyXMini0714.problem_phyx_mini_0714` was replaced by
an honest proof, and no theorem signature was changed.

## Proof summary

- Used the figure and problem hypotheses to reduce the asymptotic kinetic and
  potential energies to zero and instantiate conservation during coasting.
- Substituted the surface kinetic and potential laws, used the stated
  `1000 kg` rocket mass, and cleared the positive Earth-radius denominator to
  derive `v² = 2GM/R`.
- Used positivity of the launch speed and radicand to select the positive
  square root.
- Substituted the exact Earth calibration and proved with `norm_num` that the
  square root is at most `11200 m/s`. Since every displayed choice is at least
  `11200 m/s`, choice C has the least absolute error.

## Verification

`lake env lean PhyXMiniProblems/problem_phyx_mini_0714.lean` completed with
exit code 0 and no output. The assigned file contains no `sorry`, `admit`,
`axiom`, or `sorryAx`.

## Notes

- `.archon/AGENTS.md` is absent in this run, as also recorded in
  `.archon/PROGRESS.md`; `.archon/prover-modes/physics.md` supplied the
  available role instructions.
- The blueprint chapter was read, but its target environment contains the
  autoformalization placeholder rather than an informal proof. I did not add
  `\leanok` because the explicit prover write permissions allow edits only to
  the assigned Lean file and this task-result file.

## Redraft needed

None.
