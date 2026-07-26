# Prover result: `problem_phyx_mini_0349.lean` (iteration 016)

## Result

Closed all three proof obligations without changing any declaration signature:

- `leg_work_and_heat_readouts`
- `net_work_and_absorbed_heat_readouts`
- `problem_phyx_mini_0349`

The first lemma specializes the figure readouts and ideal-gas/internal-energy
laws at all four vertices, derives each isochoric or isobaric work value, and
then applies the first law to obtain the four signed heats. The second lemma
sums the leg work and uses positivity to evaluate the positive parts of the
four heats. The target theorem applies the efficiency law, cancels the
strictly positive factor `p₀ V₀`, obtains the exact value `2 / 19`, and checks
that it lies within the stated tolerance of displayed choice B (`10.5%`).

No redraft is needed, and no new declarations were introduced.

## Verification

- `lake env lean PhyXMiniProblems/problem_phyx_mini_0349.lean` exits with
  status 0 and no output.
- The assigned source contains no `sorry`, `admit`, `axiom`, `sorryAx`,
  `native_decide`, or other escape hatch.
- `lean_verify` reports no suspicious source patterns. The final theorem
  depends only on the standard foundational axioms `propext`,
  `Classical.choice`, and `Quot.sound`.
- No `/- USER: ... -/` file-specific hint is present.

## Project-instruction notes

- The requested `.archon/AGENTS.md` does not exist in this workspace; the
  available `.archon/prover-modes/physics.md` role instructions were read and
  followed.
- The target blueprint environment is ready for `\leanok`, but the blueprint
  was not edited because the explicit write permissions restrict this prover
  to the assigned Lean file and this task-result file. The review/orchestration
  stage should synchronize that marker.
