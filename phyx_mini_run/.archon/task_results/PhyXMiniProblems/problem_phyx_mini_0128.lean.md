# Autoformalization result: `problem_phyx_mini_0128.lean`

## Assumption/target split

### Governing laws

- A reflection from a lower refractive index to a higher refractive index contributes one phase half-turn (`π`); otherwise it contributes zero half-turns.
- The extra round-trip optical path of reflected ray 2 is `2 * n_coating * thickness`, stated for every `UnitChoices` readout.
- Destructive reflected interference of order `m` obeys
  `2 * roundTripOpticalPath + (lowerPhase - upperPhase) * wavelength = (2 * m + 1) * wavelength`.
- Complete cancellation uses equal normalized magnitudes for reflected rays 1 and 2.
- The conventional thinnest antireflection design uses destructive order zero. This fixes an order label but does not assign the coating thickness.
- Physical refractive indices, wavelength, coating thickness, and normalized reflected amplitudes are positive.

### Previous-part results

- None. The source report has an empty `previous_parts` list.

### Problem and figure/data readouts

- The stack is air → MgF₂ coating → glass.
- Refractive-index readouts are `n_air = 1`, `n_MgF₂ = 1.38 = 69/50`, and `n_glass = 1.50 = 3/2`.
- The design wavelength in air is `550 nm`, represented as a nanometre readout of a dimensionful length.
- Incidence is normal, represented by angle zero radians from the normal.
- The figure has incident and both reflected rays in air, the transmitted ray in glass, ray 1 reflected at the air–coating interface, and ray 2 reflected at the coating–glass interface.
- The displayed answer values are `77.8`, `88.9`, `99.6`, and `66.7` nanometres for A–D; the recorded dataset label is C.

### Current target conclusions

- The two interface phase contributions have zero relative difference.
- The exact first-order coating thickness is `6875/69 nm`.
- That exact value rounds to `99.6 nm` at one decimal place and therefore matches recorded answer choice C.

## Goal-faithfulness audit

`AntireflectionCoatingSetup.coatingThickness` remains an unknown dimensionful physical length. No premise, setup field, law field, or helper definition sets it to `6875/69`, `99.6`, or any displayed answer value.

The numerical premises constrain only source data: refractive indices, air wavelength, normal incidence, and the first destructive order. The thin-film laws are symbolic in thickness, wavelength, refractive index, phase shifts, and interference order. The answer table and `recordedDatasetAnswer` only encode supplied multiple-choice metadata; `MatchesAnswerToNearestTenthNanometer` is a general rounding relation and does not establish that the unknown thickness matches C.

Thus the exact numerical thickness and its rounded answer classification remain solely on the conclusion side of `coatingThickness_exact` and `problem_phyx_mini_0128`.

## Declarations created and blueprint labels

- Physical/unit layer: `LengthQuantity`, `lengthValueIn`, `nanometersValue`.
- Geometry and labels: `OpticalMedium`, `FilmInterface`, `FilmInterface.incidentMedium`, `FilmInterface.transmittedMedium`, `ReflectedRay`, `FigureRay`.
- Model and premises: `AntireflectionCoatingSetup`, `HasProblemReadouts`, `MatchesCoatingFigure`, `HasPhysicalOpticalParameters`, `UsesThinnestAntireflectionOrder`, `SatisfiesAntireflectionThinFilmLaws`.
- Answer metadata: `AnswerChoice`, `displayedThicknessNanometers`, `MatchesAnswerToNearestTenthNanometer`, `recordedDatasetAnswer`.
- Derived declarations: `reflectedInterfacePhaseDifference_eq_zero`, `coatingThickness_exact`.
- Blueprint target `thm:physics:phyx_mini_0128:target`: `problem_phyx_mini_0128`.

## LeanExplore queries/candidates actually used

- Query `thin film interference antireflection coating normal incidence refractive index quarter wavelength`: no relevant optics declaration; returned unrelated incidence/reflection algebra declarations.
- Query `refractive index wavelength optics`: no relevant optics declaration.
- Queries `physical quantity length nanometer SI unit` and `Quantity Length nanometer`: found `LengthUnit`, `LengthUnit.nanometers`, `UnitChoices.SI`, and `Dimension.L𝓭`.
- Queries `dimensionful physical quantity with units real value length` and `DimensionfulQuantity`: found `Dimensionful`, `Dimension`, `CarriesDimension.toDimensionful`, `WithDim.scaleUnit_val`, and related unit-scaling infrastructure.
- Query `SI unit value quantity length`: found `UnitChoices.SI`, `UnitChoices.SI_length`, and the dimensionful example `UnitExamples.meters400`.
- Query `LengthUnit.nanometers value conversion`: confirmed `LengthUnit.nanometers` and its scaling infrastructure.
- Query `round a real number to the nearest integer round`: found Mathlib's `round`; its fetched source/docstring confirms nearest-integer rounding with ties toward positive infinity.

Source/module/docstring details were fetched for `LengthUnit`, `LengthUnit.nanometers`, `UnitChoices.SI`, `UnitChoices.SI_length`, `Dimensionful`, `Dimension`, `WithDim.scaleUnit_val`, `UnitExamples.meters400`, and `round` before use or pattern selection.

## PhysLean/Mathlib names grounded

- Physlib: `Dimensionful`, `WithDim`, `Dimension.L𝓭`, `UnitChoices`, `UnitChoices.SI`, `LengthUnit`, and `LengthUnit.nanometers`.
- Mathlib: `round` from `Mathlib.Algebra.Order.Round`.

The physical lengths use `Dimensionful (WithDim L𝓭 ℝ)` rather than a scalar alias. Bare real values occur only for explicitly dimensionless quantities or named unit readouts.

## Local abstractions introduced

- `OpticalMedium`, `FilmInterface`, `ReflectedRay`, and `FigureRay` preserve the material stack and labels visible in the supplied image.
- `AntireflectionCoatingSetup` preserves the unknown dimensionful thickness, wavelength, refractive-index function, phase data, optical path, order, and normalized reflected-amplitude data.
- The premise structures separate source readouts, figure evidence, positivity, design-order choice, and governing physics.
- `SatisfiesAntireflectionThinFilmLaws` supplies the missing thin-film optics interface without defining the requested answer.

These abstractions were necessary because LeanExplore exposed no Mathlib/Physlib API for refractive index, Fresnel reflection, antireflection coatings, or thin-film interference.

## Grounding gaps

- No relevant thin-film interference or refractive-index declaration was found in Mathlib/Physlib; the local optics law is therefore explicit and documented.
- The requested `archon dag-query` navigation could not run because the `archon` executable was not on `PATH` in this environment.
- The requested `.archon/AGENTS.md` role file was absent. The available `.archon/prover-modes/physics-formalize.md` and the user-supplied role instructions were followed instead.

## Verification and redraft requests

- `archon-lean-lsp` reports only the three expected `declaration uses sorry` warnings.
- `lake env lean PhyXMiniProblems/problem_phyx_mini_0128.lean` exits successfully with the same three expected warnings.
- `git diff --check` passes for the assigned Lean file.
- The blueprint chapter exists and is substantive. Its theorem environment was not edited to add `\leanok` because the task's explicit write permissions prohibit editing blueprint chapters. A blueprint-owning agent should add `\leanok` for `thm:physics:phyx_mini_0128:target` after accepting this formalization.
