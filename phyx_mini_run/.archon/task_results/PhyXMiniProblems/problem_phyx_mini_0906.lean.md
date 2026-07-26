# Autoformalization result: `problem_phyx_mini_0906.lean`

## Iteration 002 retry resolution

- The iteration-001 review gate did not identify a defect in the Lean model;
  its exact reason was that no post-formalization task-result evidence could be
  found.  This file is the required post-formalization evidence and was
  re-audited in iteration 002.
- The primary raster `phyx_data/test_image/906.png` was inspected directly.  It
  confirms the two `50 cm` strings, two `10°` angle labels, `+100 nC` and
  `-100 nC` sphere labels, common support and dashed vertical, and a `3 × 3`
  array of nine leftward electric-field arrows represented in the Lean model.
- Fresh LeanExplore searches in iteration 002 again returned
  `Dimensionful`, `UnitChoices.SI`, `Electromagnetism.ElectricField`,
  `Electromagnetism.EMSystem.coulombConstant`, `MassUnit.grams`, and
  `LengthUnit.centimeters`; source and module information was fetched for
  precisely these intended declarations.

## Assumption/target split

### Governing laws

- `IsUniformLeftwardElectricField`: the Physlib field is uniform with coherent-SI vector readout `(-E, 0)`.
- `SatisfiesElectricForceLaw`: the signed horizontal force on each sphere is `q E_x`.
- `SatisfiesCoulombInteractionLaw`: the signed axial interaction is `k qᵢ qⱼ d / |d|^3`.
- `SatisfiesWeightLaw`: each independent weight magnitude is `m g`.
- `HasSymmetricSuspensionGeometry`: the string projections are `L sin θ` and `L cos θ`, and the independent separation agrees with the horizontal coordinate difference.
- `SatisfiesStaticForceBalance`: horizontal and vertical force components vanish in static equilibrium.
- `UsesSchoolReferenceValues`: the multiple-choice calculation uses `k = 9 * 10^9` and `g = 9.8` in coherent SI units.

### Previous-part results

- None; the source report lists no previous parts.

### Figure/data readouts

- Two identical small spheres suspended from a common point.
- Left red sphere: plus glyph and `+100 nC`; right pale-teal sphere: minus glyph and `-100 nC`.
- Two shown strings, each `50 cm` long and each at `10°` from the dashed vertical reference.
- Nine uniformly spaced electric-field arrows pointing left in the primary image.
- Problem-statement field magnitude `100000 N/C`.
- The physical charges, string lengths, and angles are explicitly calibrated to these labels by `MatchesProblemAndFigureReadouts`.

### Current target conclusions

- For each sphere, its mass rounds to the recorded `4.1 g` choice at the nearest `0.1 g`.
- Choice C is the unique nearest displayed mass among `3 g`, `4.4 g`, `4.1 g`, and `5.2 g`.
- The target is approximate rather than the false exact equality `mass = 4.1 g`: the stated rounded constants give approximately `4.0597643 g`.

## Goal-faithfulness audit

- `SuspendedChargedSpheresSetup.mass` is an independent `MassQuantity` observable for each sphere; it is not defined by the target or by a force-balance expression.
- No premise field gives a numerical mass, a rounding conclusion, an answer label, or the value `4.1`.
- The identical-sphere premise equates the two independent masses but does not determine their common value.
- The force and geometry premise structures state general physical laws and calibrated source data. They do not contain the current target conclusion.
- `AnswerChoice.massInGrams` and `recordedDatasetAnswer` only name the displayed target-side alternatives. Unfolding them cannot prove the theorem because the independent physical mass still has to be derived from the laws.
- `RoundsToNearestTenthGram` records the precision implied by the displayed answer; it does not define the actual mass.

## Declarations created

- Blueprint label `thm:physics:phyx_mini_0906:target` corresponds to `PhyXMiniProblems.ProblemPhyXMini0906.problem_phyx_mini_0906`.
- Supporting derived lemmas:
  - `sphereSeparation_eq_sum_horizontal_projections`
  - `massInKilograms_eq_force_balance_expression`
- Typed physical interfaces:
  - `SuspendedSpheresFigure`
  - `SuspendedChargedSpheresSetup`
  - `MatchesIdenticalSmallSphereScenario`
  - `MatchesProblemAndFigureReadouts`
  - `HasSymmetricSuspensionGeometry`
  - `HasPhysicalSuspensionParameters`
  - all governing-law structures listed above
- Displayed-answer declarations:
  - `AnswerChoice`
  - `AnswerChoice.massInGrams`
  - `recordedDatasetAnswer`
  - `RoundsToNearestTenthGram`
  - `IsUniqueNearestDisplayedMass`

## LeanExplore queries/candidates actually used

All searches used package filters `Mathlib` and `Physlib`.

- Query `dimensionful electric charge mass force length electric field SI units`:
  - used `Dimensionful` and `Electromagnetism.ElectricField`;
  - also confirmed `Dimension.C𝓭` and `UnitChoices.SI_charge` as nearby unit infrastructure.
- Query `Coulomb force law between two point charges`:
  - used `Electromagnetism.EMSystem.coulombConstant`;
  - no packaged school-level force law matching this suspended-sphere calculation was returned.
- Query `Electromagnetism.EMSystem coulombConstant`:
  - used `Electromagnetism.EMSystem` and `Electromagnetism.EMSystem.coulombConstant`.
- Query `MassUnit grams Dimensionful WithDim`:
  - used `MassUnit.grams` and `Dimensionful`.
- Query `DimMass dimensionful mass`:
  - used `Dimensionful`; no dedicated `DimMass` candidate was returned.
- Query `force dimension Newton Dimensionful WithDim`:
  - used `Dimensionful`; the `UnitExamples.NewtonsSecondWithDim` results were examples rather than a reusable force quantity.
- Query `electric field strength dimension Dimensionful`:
  - used `Dimensionful` and `Electromagnetism.ElectricField`.
- Query `uniform electric field force q times E`:
  - returned field declarations but no matching `F = qE` law, motivating a local governing-law predicate.
- Query `Real.sin degrees radians pi`:
  - used `Real.sin`; Mathlib's real trigonometric API also supplies the `Real.cos`, `Real.tan`, and `Real.pi` names used in the geometry.

Source/module details fetched for intended candidates:

- `Dimensionful` — `Physlib.Units.Basic`.
- `Electromagnetism.EMSystem.coulombConstant` — `Physlib.Electromagnetism.Basic`.
- `Electromagnetism.ElectricField` — `Physlib.Electromagnetism.Basic`.
- `MassUnit.grams` — `Physlib.ClassicalMechanics.Mass.MassUnit`.
- `Real.sin` — `Mathlib.Analysis.Complex.Trigonometric`.

## Physlib/Mathlib names grounded

- `Dimensionful`, `WithDim`, `Dimension`, `M𝓭`, `L𝓭`, `T𝓭`, `C𝓭`, `UnitChoices.SI`
- `MassUnit.kilograms`, `MassUnit.grams`, `LengthUnit.meters`, `LengthUnit.centimeters`
- `Electromagnetism.ElectricField`, `Electromagnetism.EMSystem`, `Electromagnetism.EMSystem.coulombConstant`
- `Time`, `Space`, `Real.pi`, `Real.sin`, `Real.cos`, `Real.tan`

Lean LSP local search and a self-contained snippet verified the principal imports, quantity types, field-vector notation, and candidate signatures before the file was written.

## Local abstractions introduced

- Dimensionful mass, length, signed charge, acceleration, electric-field-strength, and force aliases were built from Physlib `Dimensionful (WithDim ...)`. These are unit-independent physical quantities, not transparent scalar aliases or one-field scalar wrappers.
- `SuspendedSpheresFigure` preserves literal image evidence separately from physical quantities.
- `SuspendedChargedSpheresSetup` preserves independent masses, charges, geometry, the full Physlib electric field, and force observables.
- School-level `qE`, Coulomb interaction, weight, projection geometry, and equilibrium structures were introduced because LeanExplore did not return reusable laws with compatible signatures. Each abstraction states a general physical relation and none states the requested mass.
- Nearest-tenth and unique-nearest predicates preserve the multiple-choice precision without asserting an unjustified exact equality.

## Grounding gaps and redraft requests

- No compatible packaged theorem for point-charge force, electric force `F = qE`, or suspended-body component equilibrium was found; faithful local predicates are used.
- The requested `.archon/AGENTS.md` file was absent. The available `.archon/prover-modes/physics-formalize.md` was read and followed instead.
- The `archon` executable was not available on `PATH`, so the optional DAG query could not be run. This chapter has no recorded previous-part dependencies.
- The assigned Lean file did not exist initially, so there were no pre-existing `/- USER: ... -/` hints; this is recorded in the new file.
- The blueprint theorem environment still needs `\leanok`. It was not edited because this task's explicit write permissions allow changes only to the assigned Lean file and this task-result file and explicitly prohibit editing blueprint chapters.

## Verification

- Lean language-server diagnostics: success, with exactly three expected `declaration uses sorry` warnings.
- `lake env lean PhyXMiniProblems/problem_phyx_mini_0906.lean`: success, with the same three expected warnings.
- `git diff --check` on the assigned Lean file: clean.

## Prover iteration 020

### Result

All three original `sorry` placeholders were replaced without changing any
declaration signature:

- `sphereSeparation_eq_sum_horizontal_projections` now follows from the two
  projection identities and the separation identity.
- `massInKilograms_eq_force_balance_expression` derives the signs of the
  electric and Coulomb forces from the readouts and physical laws, combines
  horizontal and vertical static balance, and eliminates the string tension.
- `problem_phyx_mini_0906` performs the exact unit conversions, derives the
  separation and force values, proves certified rational bounds on
  `sin (π / 18)` and `cos (π / 18)`, bounds each mass between `4.05 g` and
  `4.15 g`, and proves both rounding to choice C and its strict uniqueness.

The sine lower bound uses `Real.sin_three_mul` and
`Real.sin_pi_div_six`, followed by rational cubic refinements. The remaining
trigonometric bounds use Mathlib's `Real.sin_bound`, `Real.cos_bound`, and
monotonicity lemmas together with `Real.pi_gt_d4` and `Real.pi_lt_d4`.

### Redraft needed

None.

### Blueprint status

The blueprint chapter was not edited or marked `\leanok`, because the
prover-stage write permissions explicitly restrict edits to the assigned Lean
file and this task-result file.

### Verification

- `lake env lean PhyXMiniProblems/problem_phyx_mini_0906.lean` completed with
  exit code 0. Its only output was two stylistic
  `linter.unnecessarySeqFocus` warnings; there were no compiler errors.
- A source scan found no `sorry`, `admit`, `axiom`, `sorryAx`, or
  `native_decide`.
- `git diff --check` passed for the assigned Lean file and this task-result
  file.
