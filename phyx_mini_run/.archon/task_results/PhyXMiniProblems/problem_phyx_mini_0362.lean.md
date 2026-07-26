# PhyXMiniProblems/problem_phyx_mini_0362.lean

## `finalAbsoluteTemperatureInKelvins_eq_3519` (line 254)

### Attempt 1

- **Approach:** Extract the endpoint pressure and volume readouts from the
  diagram-agreement hypotheses; unfold the textbook Celsius conversion to get
  `T₁ = 1173`; specialize the fixed-sample ideal-gas law at both endpoints;
  solve the first equation for `nR` and substitute into the second.
- **Result:** RESOLVED.
- **Proof-body size:** 1 line (`sorry`) before, 28 lines after.

## `finalTemperature_matches_recordedAnswerA` (line 316)

### Attempt 1

- **Approach:** Apply `finalAbsoluteTemperatureInKelvins_eq_3519`, unfold the
  Celsius offset and recorded answer definitions, and normalize both numeric
  conclusions.
- **Result:** RESOLVED.
- **Proof-body size:** 1 line (`sorry`) before, 10 lines after.

## Verification

- `lake env lean PhyXMiniProblems/problem_phyx_mini_0362.lean` exited 0.
- Lean LSP diagnostics are empty.
- Source scan found no `sorry`, `admit`, or introduced axiom.
- Axiom verification reports only standard imported axioms: `propext`,
  `Classical.choice`, and `Quot.sound`.
- No new declarations were introduced, so no blueprint entry is needed.
- The blueprint chapter was left unchanged because this prover lane has write
  permission only for the assigned Lean file and this result file; the
  review/plan lane should add `\leanok` to the proved lemma and theorem
  environments.

## Summary

- Sorry count: **2 → 0**.
- Closed:
  `finalAbsoluteTemperatureInKelvins_eq_3519`,
  `finalTemperature_matches_recordedAnswerA`.
- Remaining sorries: none.
- Both assigned placeholders were attempted; there were no adjacent sorries.

## Why I stopped

Real progress: closed both sorries and completed clean standalone compilation
and axiom/source verification.
