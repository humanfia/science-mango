# Prover result: `problem_phyx_mini_0812.lean`

## Outcome

- Closed the sole `sorry` in
  `PhyXMiniProblems.ProblemPhyXMini0812.returnSpeedAtRampBottom_is_answerB`.
- Preserved the theorem statement, hypotheses, and all supporting declarations.
- No redraft is needed.

## Proof summary

The proof specializes the kinetic-energy and two work--energy laws to SI.
The figure/data hypotheses supply

- mass `12`,
- gravitational acceleration `49 / 5`,
- upward and return distances `8 / 5`,
- initial and turning-point speeds `5` and `0`, and
- incline angle `π / 6`, so its sine is `1 / 2`.

Eliminating the common kinetic-friction readout between the upward and
downward equations gives the return-speed square `159 / 25`. The return-speed
readout is nonnegative because it is the real coercion of an `NNReal`, so it
equals `Real.sqrt (159 / 25)`. Exact squared bounds
`5 / 2 ≤ Real.sqrt (159 / 25) ≤ 57 / 20` then prove by cases that displayed
choice B has no greater absolute error than choices A, B, C, or D.

## Verification

- `lake env lean PhyXMiniProblems/problem_phyx_mini_0812.lean`: exit code 0.
- Lean LSP diagnostics: no errors; only the expected unused-variable warning
  for the frozen `hPhysical` hypothesis.
- `lean_verify` source scan: no warnings.
- The theorem uses only the standard imported axioms `propext`,
  `Classical.choice`, and `Quot.sound`.
- The assigned file contains no `sorry`, `admit`, `axiom`, or
  `native_decide`.

The target theorem's blueprint proof environment is ready for `\leanok`.
Per prover permissions and the canonical AGENTS instructions, the blueprint
was not edited; the deterministic synchronization phase owns that marker.
The run-local `.archon/AGENTS.md` is absent, as recorded in `PROGRESS.md`, so
the identical canonical archived AGENTS file and the active physics prover
mode were followed.
