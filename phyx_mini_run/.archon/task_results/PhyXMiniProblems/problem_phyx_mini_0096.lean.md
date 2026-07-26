# PhyXMiniProblems/problem_phyx_mini_0096.lean

## Status

The assigned file is proof-closed and compiles successfully:

```text
lake env lean PhyXMiniProblems/problem_phyx_mini_0096.lean
```

The command exited with status 0 and no diagnostics. The file has no
`sorry`, `admit`, `axiom`, `sorryAx`, or `/- USER: ... -/` occurrence.

No Lean code was changed in iteration 015. The existing proofs honestly prove
their frozen Lean statements. The mandatory review blocker is a physical
mis-specification in those statements and cannot be repaired by editing only
proof bodies after `:= by`.

## `predictedMaximum_isGreatestTIRIncidence` (line 255)

### Attempt 1

- **Approach:** Rechecked the limiting-ray construction and upper-bound
  argument against the blueprint, source image, Snell laws, and acute-angle
  hypotheses.
- **Result:** RESOLVED for the current Lean contract. The proof constructs the
  critical ray as a member and proves every admissible incidence is at most its
  entry angle.
- **Dead end:** This relies essentially on the frozen non-strict predicate
  `criticalAngleSolidToAir.toReal ≤ incidenceAngleAtVerticalFace.toReal`.
  Replacing it by physical TIR (`<`) removes the critical ray from the set, so
  the requested `IsGreatest` conclusion becomes physically wrong; no
  proof-body refactor can change that contract.

## `predictedMaximum_matches_recorded_choice` (line 445)

### Attempt 1

- **Approach:** Audited the certified inverse-trigonometric bounds and their
  conversion through `degreeReadout` and `abs_le`.
- **Result:** RESOLVED for the current Lean contract. The existing proof
  establishes the strict interval
  `71.95° < degreeReadout predictedMaximum < 72°`, which implies the stated
  `0.15°` compatibility with recorded choice A (`72.1°`).
- **Dead end:** The same interval proves that D (`71.9°`) is strictly closer:
  its error is below `0.1°`, while A's error is above `0.1°`. Thus the frozen
  tolerance predicate accepts A but does not select it uniquely; it also
  accepts D. This is a conclusion-definition issue, not a proof-body issue.

## `problem_phyx_mini_0096` (line 670)

### Attempt 1

- **Approach:** Rechecked that the theorem combines the two proved component
  lemmas without an escape hatch or an unstated numerical premise.
- **Result:** RESOLVED for the current Lean contract and verified by a clean
  Lean compilation.
- **Dead end:** The conjunction inherits both semantic defects above.

## Redraft needed

- **Original problem:** `phyx_mini_0096`
- **Source report:** `reports/phyx_mini/problem_phyx_mini_0096.source.json`
- **Affected declarations:**
  - `UndergoesTotalInternalReflectionAtA`
  - `predictedMaximum_isGreatestTIRIncidence`
  - `predictedMaximum_matches_recorded_choice`
  - `problem_phyx_mini_0096`

At the solid--air critical angle, Snell's law gives a grazing transmitted ray.
Actual total internal reflection requires the solid-side incidence angle to be
strictly greater than the critical angle. The current definition instead uses
non-strict `≤`, deliberately admitting the boundary ray. Consequently the
current `IsGreatest` theorem is provable, but it describes the closed onset
set rather than the set of rays that actually undergo TIR.

The smallest faithful statement redraft is:

1. Change `UndergoesTotalInternalReflectionAtA` to
   `setup.criticalAngleSolidToAir.toReal <
   ray.incidenceAngleAtVerticalFace.toReal`.
2. Replace `IsGreatest` by `IsLUB` in
   `predictedMaximum_isGreatestTIRIncidence` and
   `problem_phyx_mini_0096`.
3. Replace the answer-selection conjunct by a unique-nearest-choice predicate
   selecting D for the exact `n = 1.38` readout. If preservation of the
   dataset's recorded A is required, state it separately only as non-unique
   compatibility with the coarse `0.15°` tolerance.

These are forbidden signature/definition changes in prover mode, so they were
not attempted in the Lean file.

## Summary

- Sorry count: **0 → 0**.
- Sorries closed this iteration: none; all three proof declarations were
  already closed.
- Sorries still open: none.
- Adjacent sorries attempted: not applicable; the assigned file contains no
  other open placeholders.
- New declarations: none.
- Blueprint edits: none. The explicit write permissions exclude the blueprint;
  the closed declarations remain ready for the deterministic `\leanok` sync
  phase.

## Why I stopped

- **Real progress:** none in Lean code; sorry count remained 0 → 0.
- **Cosmetics only:** no Lean formatting, comments, or proof bodies were
  changed.
- **Specific blocker:** the proof Review failure requires changing a frozen
  physical predicate and theorem conclusions. Every legal proof-body goal is
  already proved and compiles.
- **Approaches written but not attempted:** the strict-TIR/`IsLUB`/nearest-D
  redraft was not implemented because it changes protected contracts and is
  expressly outside this prover lane's write authority.
- **Directive compliance:** the frozen signatures were preserved; no theorem
  was weakened, no unsupported physical premise was introduced, and no proof
  escape was used.
