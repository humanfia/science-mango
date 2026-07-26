# Autoformalization result: `problem_phyx_mini_0911.lean`

## Assumption/target split

### Governing laws

- `SatisfiesAlignedIonDipoleForceLaw.forceLawWithRemainder` states that the signed axial force on the water molecule is the attractive unscreened point-ion/aligned-dipole leading term `-2 k |q| p / r^3` plus an independent, dimensionful signed remainder.
- `SatisfiesAlignedIonDipoleForceLaw.controlledApproximationRemainder` bounds the remainder by one percent of the magnitude of that leading term. This is the explicit fixed-distance approximation contract added to repair the review gate's globalized-approximation blocker.
- `SatisfiesIonDipoleActionReaction.equalAndOppositeForces` records Newton's third-law relation between the two force components pictured in the figure.

### Previous-part results

- None. The source report has `previous_parts: []`, and the chapter contains no dependency declarations other than the target.

### Figure/data readouts

- Prose/reference data: permanent water dipole moment `6.2 * 10⁻³⁰ C m`, singly charged sodium ion `1.60 * 10⁻¹⁹ C`, and Coulomb constant `8.99 * 10⁹` in coherent SI.
- Primary bitmap `911.png`: sodium ion on the left, water molecule on the right, positive sodium glyph, negative ion-facing water end, positive far end, force-on-ion arrow pointing right, force-on-dipole arrow pointing left, dashed attraction arc, double-headed separation arrow, and `r = 10 nm`.
- Geometry: the sodium position is left of the water position and their coordinate difference is the positive physical separation.
- Scenario/model tags: saltwater medium, point-ion model, negative dipole end toward the ion, and the controlled unscreened point-ion/dipole approximation used by the recorded textbook calculation.

### Current target conclusions

- `forceComponentInNewtons setup.forceIonOnDipole < 0`, meaning the ion-on-dipole force is leftward/toward the sodium ion.
- The magnitude of that force lies within half of the last displayed decimal place of choice C, `1.8 * 10⁻¹⁴ N`.

## Goal-faithfulness audit

- Neither target conjunct appears as a premise or structure field. No premise states that the physical force is negative, equals choice C, or lies in choice C's rounding interval.
- The force observables and the approximation remainder are independent `Dimensionful (WithDim forceDimension ℝ)` quantities in `SodiumIonWaterDipoleSetup`; none is defined from the answer.
- The force law contains only the general leading expression `2 k |q| p / r^3` and a generic 1% relative remainder bound. It contains no answer label, `1.8 * 10⁻¹⁴`, or display tolerance.
- `MatchesSuppliedIonDipoleFigure.forceArrowDirections` transcribes visual evidence from the primary raster. It is not linked by definition to the signed scalar force and therefore does not make the numerical direction conclusion true by unfolding.
- `AnswerChoice.forceInNewtons`, `choiceCDisplayToleranceInNewtons`, and `recordedDatasetAnswer` are source metadata. Only the theorem conclusion compares the independently modeled physical force with that metadata.

## Declarations and blueprint correspondence

- `problem_phyx_mini_0911` formalizes `thm:physics:phyx_mini_0911:target`.
- Supporting dimensional declarations: `forceDimension`, `electricDipoleMomentDimension`, the five dimensionful quantity aliases, and their coherent-SI readout functions.
- Supporting image/model declarations: the figure-label enums and lookup functions, `SodiumIonWaterFigure`, `SodiumIonWaterDipoleSetup`, and `ionOnDipoleForceMagnitudeInNewtons`.
- Supporting premise declarations: `MatchesSodiumIonWaterScenario`, `HasIonDipolePhysicalData`, `MatchesSuppliedIonDipoleFigure`, `HasIonWaterAxialGeometry`, `SatisfiesAlignedIonDipoleForceLaw`, and `SatisfiesIonDipoleActionReaction`.
- Supporting answer metadata: `AnswerChoice`, `AnswerChoice.forceInNewtons`, `choiceCDisplayToleranceInNewtons`, and `recordedDatasetAnswer`.
- The chapter has no separate labels for these supporting declarations. The target theorem is ready for the project-managed `\leanok` synchronization; the blueprint was not edited because prover write permissions explicitly forbid blueprint edits.

## LeanExplore queries and candidates actually used

All searches used `packages: ["Mathlib", "Physlib"]`.

- Natural-language query `electric dipole moment ion dipole force Coulomb`: found and grounded `Electromagnetism.EMSystem.coulombConstant` and `Electromagnetism.EMSystem`. It found no ion-dipole force or electric-dipole-moment declaration suitable for this problem.
- Likely-name query `EMSystem coulombConstant`: confirmed `Electromagnetism.EMSystem` and `Electromagnetism.EMSystem.coulombConstant` from `Physlib.Electromagnetism.Basic`.
- Combined concept/name query `Dimensionful WithDim physical units charge force length`: grounded `Dimensionful`, `Dimension`, `Dimension.L𝓭`, `Dimension.C𝓭`, and `UnitChoices.SI`.
- Exact-name query `WithDim`: grounded `WithDim` from `Physlib.Units.WithDim.Basic`.
- Natural-language/name query `NNReal nonnegative real numbers`: grounded Mathlib's `NNReal` for nonnegative magnitudes and separations.
- Query `IsLittleO asymptotic remainder approximation at infinity`: returned `Asymptotics.IsLittleO.forall_isBigOWith`. It was inspected but not used because the problem concerns one fixed `10 nm` configuration; a pointwise, dimensionful remainder and explicit relative bound provide the relevant validity contract.

Source/module/docstring data were fetched for `Dimensionful`, `Dimension`, `Dimension.L𝓭`, `Dimension.C𝓭`, `UnitChoices.SI`, `WithDim`, `NNReal`, `Electromagnetism.EMSystem`, `Electromagnetism.EMSystem.coulombConstant`, and the considered `Asymptotics.IsLittleO.forall_isBigOWith` candidate.

## PhysLean/Mathlib names grounded

- PhysLean: `Dimensionful`, `WithDim`, `Dimension`, `Dimension.M𝓭`, `Dimension.L𝓭`, `Dimension.T𝓭`, `Dimension.C𝓭`, `UnitChoices.SI`, `Electromagnetism.EMSystem`, and `Electromagnetism.EMSystem.coulombConstant`.
- Mathlib: `NNReal`, `ℝ`, integer powers on reals, and real absolute value notation.

## Local abstractions introduced

- PhysLean supplies dimension infrastructure but no dedicated electric-dipole-moment or axial-force object. The file therefore uses `Dimensionful (WithDim d α)` with explicit dimensions `C L` and `M L T⁻²`; this preserves physical roles while allowing coherent-SI scalar projections.
- Local enums preserve the object, dipole-end, sign, arrow, direction, medium, ion-model, orientation, and approximation roles visible or implied in the source.
- Local setup/evidence structures separate independent physical observables, source calibrations, image readouts, geometry, and governing laws.
- `alignedPointDipoleRemainder` is an independent dimensionful force component. Exposing it and bounding it in `SatisfiesAlignedIonDipoleForceLaw` prevents the point-dipole leading term from being globalized as an exact physical law.

## Source/law/answer audit

- With the supplied idealized data, the unscreened leading magnitude is
  `2 * 8.99e9 * 1.60e-19 * 6.2e-30 / (10e-9)^3 = 1.783616e-14 N`, which rounds to choice C.
- A 1% remainder is at most `1.783616e-16 N`; combined with the leading term's `1.6384e-16 N` difference from `1.8e-14 N`, this remains below the `5e-16 N` display tolerance and cannot reverse the attractive sign.
- The primary image, not the auxiliary caption, was followed for arrow direction: force on the sodium ion points right and force on the water dipole points left.
- The image and prose state saltwater but provide no dielectric constant, ionic strength, Debye length, molecular size, or empirical error estimate. Thus the recorded answer is supportable only conditionally under the explicit controlled unscreened approximation contract.

## Grounding gaps and redraft requests

- No Mathlib/PhysLean declaration for the aligned ion-dipole force law or a permanent electric-dipole-moment quantity was found; faithful local dimensionful abstractions remain necessary.
- The source should explicitly say that screening is neglected and justify an accuracy bound, or supply saltwater dielectric/screening data. The 1% bound is an explicit theorem premise needed to make the recorded displayed-precision answer honest, not a datum recoverable from the current source.
- The blueprint chapter is marked `% archon:physics` but its proof block contains only the autoformalization instruction, not the numerical derivation above. A plan pass should add that derivation and explain the approximation contract.
- `.archon/AGENTS.md` is absent in this checkout. The identical-SHA canonical project role file from the run archive/template, the injected role instructions, and `.archon/prover-modes/physics-formalize.md` were followed.
- `archon` was not available on `PATH`, so the optional DAG queries could not run. The source report independently confirms there are no previous parts.

## Verification

- `archon-lean-lsp` diagnostics: successful elaboration with exactly one expected `declaration uses sorry` warning and no errors.
- `lake env lean PhyXMiniProblems/problem_phyx_mini_0911.lean`: exit code 0 with the same single expected warning.
