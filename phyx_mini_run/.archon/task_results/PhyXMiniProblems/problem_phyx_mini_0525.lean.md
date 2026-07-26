# Prover result: `problem_phyx_mini_0525.lean`

## Status

Complete. Both assigned `sorry` placeholders were replaced by sound proofs:

- `measuredBeatFrequency_exact_readout`
- `problem_phyx_mini_0525`

The numerical lemma derives the exact carrier and speed readouts, specializes
the approaching-reflector relation, proves that the reflected frequency is
larger than the transmitted frequency, removes the mixer's absolute value, and
establishes the strict `2.000 kHz < beat < 2.005 kHz` bounds. The target theorem
then proves rounding to `2.00 kHz` and unfolds answer choice D.

## Verification

- `lake env lean PhyXMiniProblems/problem_phyx_mini_0525.lean` — passed.
- Lean LSP diagnostics — no errors; only unused-hypothesis linter warnings for
  contract fields not needed by the numerical proof.
- Source scan — no `sorry`, `admit`, `sorryAx`, or declared `axiom`.
- Axiom checks for both declarations report only Lean's standard
  `propext`, `Classical.choice`, and `Quot.sound`.

## Notes

- No redraft is needed.
- `.archon/AGENTS.md` was absent, so the role-specific instructions available
  in the objective and `.archon/prover-modes/physics.md` were followed.
- The blueprint was not edited because this prover assignment explicitly
  restricts writes to the assigned Lean file and this result file. The
  coordinator should add `\leanok` to the target theorem and exact-readout
  lemma environments.
