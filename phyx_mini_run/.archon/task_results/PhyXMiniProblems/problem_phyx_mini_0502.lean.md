# Prover result: `problem_phyx_mini_0502.lean`

## Status

Complete. Both `sorry` placeholders were replaced by sound proofs without
changing either declaration header.

## Proof

- `centralStripProbability_eq_five_thousandths` uses the stated narrow-strip
  relation to rewrite the probability as density at the strip center times its
  width.
- `MatchesProblemStatementAndFigure.modelDensityAtPeak`, together with the
  central peak center and density readouts, gives
  `densityPerMillimeter 0 = 1 / 2`.
- Unfolding the requested strip supplies width `1 / 100`; `norm_num` proves
  `(1 / 2) * (1 / 100) = 5 / 1000`.
- `problem_phyx_mini_0502` unfolds choice C's displayed probability and applies
  the helper lemma.

The Born-law premise is not needed for this consequence because the
narrow-strip approximation already relates the model probability directly to
the figure-calibrated density. It remains in the frozen signature.

## Verification

- Archon Lean LSP diagnostics report no errors. The sole warning is that
  `hBorn` is unused in the private helper lemma; its binding cannot be removed
  from the frozen declaration header.
- `lake env lean PhyXMiniProblems/problem_phyx_mini_0502.lean` exited with
  status 0.
- The assigned source contains no `sorry`, `admit`, introduced `axiom`,
  `sorryAx`, or `native_decide`.
- `lean_verify` found no suspicious source patterns. The main theorem depends
  only on `propext`, `Classical.choice`, and `Quot.sound`.

## Notes

- The requested run-local `.archon/AGENTS.md` is absent; `PROGRESS.md` states
  that the identical canonical archive supplies the active instructions, and
  that archived role file was read.
- The file-specific `/- USER: ... -/` comment only records that the assigned
  Lean file did not exist when autoformalization began.
- The blueprint lemma and target theorem environments are ready for `\leanok`.
  The blueprint was not edited because prover write permission is restricted
  to the assigned Lean file and this task-result file; deterministic
  `sync_leanok` should apply the markers.
- No redraft is needed.
