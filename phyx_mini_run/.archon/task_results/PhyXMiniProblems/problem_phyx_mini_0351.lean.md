# Prover result: `problem_phyx_mini_0351.lean`

## Status

- Complete: the sole `sorry` in
  `PhyXMiniProblems.ProblemPhyXMini0351.problem_phyx_mini_0351` was replaced
  by a faithful proof.
- The declaration header and all physical hypotheses were left unchanged.
- No `sorry`, `admit`, `sorryAx`, new axiom, or metaprogramming escape hatch
  remains in the assigned file.

## Proof

- The isochoric and isothermal state relations, the three pressure readouts,
  and the ideal-gas laws imply
  `volume c / volume b = 3`.
- The monatomic internal-energy law, leg work laws, and first law give the
  signed heats
  `Q_ab = 300000 V_b`, `Q_bc = 300000 V_b log 3`, and
  `Q_ca = -500000 V_b`.
- Positivity of `V_b` and `log 3` reduces positive-part heat accounting to
  `Q_in = 300000 V_b (1 + log 3)`. Net-work accounting gives
  `W_net = 100000 V_b (3 log 3 - 2)`, so the positive volume factor cancels
  and proves
  `(3 * log 3 - 2) / (3 + 3 * log 3)`.
- Mathlib's certified `Real.log_three_gt_d9` and
  `Real.log_three_lt_d9` bounds prove that `round (1000 * efficiency) = 206`.
  Direct evaluation then proves agreement with `20.6%` and disagreement with
  all four displayed choices.

## Verification

- `archon-lean-lsp`: no diagnostics.
- `lake env lean PhyXMiniProblems/problem_phyx_mini_0351.lean`: exit code 0,
  no output.
- `lean_verify` source scan: no warnings. The theorem uses only the standard
  logical axioms `propext`, `Classical.choice`, and `Quot.sound`.

## Blueprint

The target environment
`thm:physics:phyx_mini_0351:target` is proof-closed and ready for `\leanok`.
The prover did not edit the blueprint because the role instructions reserve
blueprint writes and marker synchronization for the coordinator.

## Redraft needed

None for the frozen Lean statement.
