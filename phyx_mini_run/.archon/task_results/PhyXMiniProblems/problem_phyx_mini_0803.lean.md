# Prover result: `problem_phyx_mini_0803.lean`

## Status

Complete. Both proof placeholders were closed without changing any declaration
signature:

- `elevatorAccelerationFromStoppingData`
- `scaleReadingWhileDescendingAndSlowing`

## Proof summary

- Specialized the constant-acceleration law to metres and seconds and rewrote
  the signed readouts as `v_i = -10`, `v_f = 0`, and `Δy = -25`.
  `nlinarith` then proves the upward acceleration readout is `2`.
- Used the figure hypotheses to obtain `w = 490 N`, the problem data to obtain
  `m = 50 kg`, the shared-acceleration law to obtain the woman's
  `a_y = 2 m/s²`, Newton's second law `n - w = m a_y`, and the ideal-scale law.
  The resulting scale readout is `590 N`.

The proof derives the physically consistent displayed choice A and does not
use the inconsistent recorded dataset answer B.

## Verification

- `lake env lean PhyXMiniProblems/problem_phyx_mini_0803.lean` exited with code
  `0`.
- The only diagnostic is an unused-variable linter warning for the frozen
  `physical` hypothesis.
- Source scan found no `sorry`, `admit`, `sorryAx`, new `axiom`, or `unsafe`
  declaration.
- Axiom verification for both proved declarations reports only the standard
  imported axioms `propext`, `Classical.choice`, and `Quot.sound`.

## Blueprint readiness

The lemma and theorem proof environments are ready for `\leanok`. The blueprint
was not edited because the canonical prover instructions reserve marker updates
for the deterministic sync step and prohibit prover writes to blueprint files.

## Notes

- No `/- USER: ... -/` file-specific hint is present.
- The run-local `.archon/AGENTS.md` is absent as documented in
  `.archon/PROGRESS.md`; the canonical archived `AGENTS.md` was read instead.
- No redraft is needed.
