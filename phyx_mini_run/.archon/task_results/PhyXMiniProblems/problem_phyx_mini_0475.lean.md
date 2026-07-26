# Prover result: `problem_phyx_mini_0475.lean`

## Outcome

All three `sorry` placeholders were replaced with sound proofs, with every
declaration signature left unchanged.

- `internalEnergy_conserved` simplifies the first law using the insulated
  process (`Q = 0`) and expansion into vacuum (`W = 0`).
- `finalVolume_eq_two_mul_initialVolume` rewrites the final occupied volume as
  the sum of the two equal compartment volumes and uses the initial-occupancy
  readout.
- `entropyChange_eq_nR_log_two` unfolds Physlib's `entropy`, substitutes
  conservation of internal energy and mole count together with
  `V_f = 2 V_i`, applies `Real.log_mul`, and closes the remaining polynomial
  identity by `ring`.

No redraft is needed. The formalized theorem faithfully proves recorded answer
B, `ΔS = n R log 2`.

## Sources read

- Physics blueprint:
  `blueprint/src/chapters/PhyXMiniProblems_problem_phyx_mini_0475.tex`
- Source report:
  `reports/phyx_mini/problem_phyx_mini_0475.source.json`
- Reference inventory: `references/summary.md`
- Prover role fallback: `.archon/prover-modes/physics.md`

The requested `.archon/AGENTS.md` was absent. The blueprint was not edited to
add `\leanok` because the task's explicit write permissions restrict edits to
the assigned Lean file and this result file.

## Verification

- Lean language-server diagnostics: no errors or warnings.
- `lake env lean PhyXMiniProblems/problem_phyx_mini_0475.lean`: exit code 0.
- Source scan: no `sorry`, `admit`, `axiom`, `sorryAx`, or `native_decide`.
- Axiom verification for
  `PhyXMini0475.entropyChange_eq_nR_log_two`: only `propext`,
  `Classical.choice`, and `Quot.sound`.
