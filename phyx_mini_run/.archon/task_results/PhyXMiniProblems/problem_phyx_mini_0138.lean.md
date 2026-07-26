# Autoformalization result: `problem_phyx_mini_0138.lean`

## Assumption/target split

### Governing laws

- `HasPhysicalParameters` requires positive refractive indices, positive slab thickness, and the nonnegative acute branch for the four refraction angles. It does not assign a value to `thetaB`.
- `SatisfiesPlaneParallelGeometry` states that the entry and exit face normals are equal and that the internal incidence angle at the exit face equals the internal refraction angle at the entry face.
- `SnellLawAtInterface` states the general relation `n₁ sin(theta₁) = n₂ sin(theta₂)`.
- `SatisfiesSnellsLaw` applies that relation separately at the air-to-glass and glass-to-air faces.

### Previous-part results

- None. The source report has an empty `previous_parts` list.

### Figure/data readouts

- `MatchesProblemReadouts` records left air, glass, right air, equality of the two outer air media, glass index `1.50 = 3/2`, and incident angle `60 degrees = pi/3`.
- `MatchesSuppliedFigure` records the flat uniformly thick slab, the object and face origins of the labeled rays, solid physical rays, the dashed apparent-image extension, magenta coloring, and the shared direction of the extension and emergent ray.
- Direct inspection of `phyx_data/test_image/138.png` confirms that the two slab faces are parallel and vertical, the dashed gray lines are the interface normals, the incident and emergent air regions are on opposite sides of the glass, and the magenta dashed segment is a backward extension of the emergent ray toward the apparent image.
- `ParallelGlassSlabSetup` keeps distinct fields for the incident ray, internal ray, emergent ray, apparent-image extension, entry and exit faces, face normals, `thetaA` at each face, and `thetaB`.
- `displayedAnswerValue` faithfully records A `0.666`, B `0.966`, C `0.866`, and D `0.766`; this table is not a theorem premise.

### Current target conclusions

- `emergentAngle_eq_incidentAngle`: `thetaB` equals the incident angle.
- `problem_phyx_mini_0138`: `thetaB = pi/3`, `sin(thetaB) = sqrt(3)/2`, and C is the unique displayed value matching that sine to the nearest thousandth.

## Source/law/answer audit

- **Source data:** incident angle `60 degrees`, glass index `1.50`, air on both sides, the parallel slab, labeled rays/normals, and the four printed decimals.
- **Governing laws:** Snell's law is imposed independently at the entry and exit interfaces; plane-parallel geometry transfers the internal angle between the two faces; positivity and the acute branch select the physical sine solution.
- **Supported physical answer:** because the outer media are the same, the emergent angle equals the incident angle, hence `thetaB = 60 degrees = pi/3`.
- **Dataset-answer interpretation:** the printed `0.866` is dimensionless and equals `sin(thetaB)` to the displayed precision. It is not an angle in degrees or radians. The theorem therefore states the exact physical angle first and treats choice C separately as a nearest-thousandth sine readout.
- **Previous parts:** none; `reports/phyx_mini/problem_phyx_mini_0138.source.json` has an empty `previous_parts` list.

## Goal-faithfulness audit

`thetaB` is an unconstrained data field of `ParallelGlassSlabSetup`. No setup field, physical-parameter predicate, problem readout, figure readout, plane-parallel geometry field, or Snell-law field asserts `thetaB = pi/3`, `thetaB = incidentAngle`, its sine value, or that C matches it. The premises mention `thetaB` only as the unknown outgoing angle in the second general Snell equation and in the physical angular range.

The incident `60 degree` readout is legitimately a hypothesis because it is stated source data. Equal outer media, the two Snell equations, parallel-face transfer, and injectivity of sine on the physical branch must still be combined by the later prover to obtain the target. `MatchesDisplayedSineToNearestThousandth` and `IsUniqueMatchingDisplayedSine` occur only on the conclusion side of the main theorem. No local definition unfolds to the requested emergent-angle equality.

## Declarations and blueprint correspondence

- Namespace: `PhyXMiniProblems.ProblemPhyXMini0138`.
- Physical data: `LengthQuantity`, `DiagramPoint`, `DiagramRay`, `OpticalMedium`, and `ParallelGlassSlabSetup`.
- Figure labels: `MediumKind`, `MediumRegion`, `SlabFace`, `RayLabel`, `RayStyle`, `FigureColor`, and `SlabModel`.
- Premise interfaces: `IsPhysicalRefractionAngle`, `HasPhysicalParameters`, `MatchesProblemReadouts`, `MatchesSuppliedFigure`, `SatisfiesPlaneParallelGeometry`, `SnellLawAtInterface`, and `SatisfiesSnellsLaw`.
- Answer provenance: `AnswerChoice`, `displayedAnswerValue`, `recordedDatasetAnswer`, `MatchesDisplayedSineToNearestThousandth`, and `IsUniqueMatchingDisplayedSine`.
- Derived declarations: `emergentAngle_eq_incidentAngle` and `problem_phyx_mini_0138`.
- `problem_phyx_mini_0138` corresponds to blueprint label `thm:physics:phyx_mini_0138:target`.

The blueprint file was not edited to add `\leanok` because the task's final write-permission section authorizes edits only to the assigned Lean file and this result file.

## LeanExplore queries/candidates actually used

- Iteration 002 reran all searches with `packages: ["Mathlib", "Physlib"]`.
- Query `Snell's law refraction refractive index incident angle sine`: no Snell-law declaration was returned. The relevant returned candidates were `Real.Angle.sin` and `Real.Angle.sin_toReal`.
- Query `geometrical optics light ray optical medium refractive index`: candidate `Module.Ray` was selected as the ray-direction primitive. No compatible optical-medium or refractive-index structure was returned.
- Likely-name query `Module.Ray`: confirmed `Module.Ray` and related ray declarations.
- Likely-name query `Real.Angle sin toReal`: confirmed `Real.Angle.sin`, `Real.Angle.toReal`, and `Real.Angle.sin_toReal`.
- Query `dimensionful physical length WithDim` and likely-name queries `WithDim` and `UnitChoices.SI`: confirmed Physlib's `Dimensionful`, `WithDim`, `Dimension.L𝓭`, and the SI unit choice used for the scalar meter readout.
- Likely-name queries `Real.sin_pi_div_three` and `Real.injOn_sin`: confirmed the exact sine theorem and sine injectivity theorem for the intended later proof route.

Fetched sources/modules for the candidates actually used or intended in the proof route:

- `Module.Ray` — `Mathlib.LinearAlgebra.Ray`.
- `Real.Angle.sin`, `Real.Angle.sin_toReal` — `Mathlib.Analysis.SpecialFunctions.Trigonometric.Angle`.
- `Real.injOn_sin`, `Real.sin_pi_div_three` — `Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic`.
- `Dimensionful` — `Physlib.Units.Basic`.
- `WithDim` — `Physlib.Units.WithDim.Basic`.
- `Dimension.L𝓭` — `Physlib.Units.Dimension`.

## PhysLean/Mathlib names grounded

- Mathlib: `Module.Ray`, `Real.Angle`, `Real.Angle.sin`, `Real.Angle.toReal`, `Real.Angle.sin_toReal`, `Real.injOn_sin`, `Real.sin_pi_div_three`, and `Real.sqrt`.
- PhysLean/Physlib: `Dimensionful`, `WithDim`, `Dimension.L𝓭`, and `UnitChoices.SI`.

The Lean LSP snippet verified the `Module.Ray ℝ (Fin 2 → ℝ)` type, coercion of `pi/3` to `Real.Angle`, `Real.Angle.toReal`, and `Real.Angle.sin` before the file was written.

## Local abstractions introduced

- `OpticalMedium` preserves the physical medium kind and its dimensionless refractive index; positivity is deliberately separate.
- `ParallelGlassSlabSetup` preserves spatial ray directions, face normals, dimensionful thickness, region labels, line styles, the apparent-image extension, and independent angle measurements.
- `SnellLawAtInterface` and `SatisfiesSnellsLaw` are faithful local governing-law interfaces because no matching Mathlib/PhysLean optics declaration was found.
- `SatisfiesPlaneParallelGeometry` prevents the equality of the two internal angles from being hidden by identifying them definitionally.

## Grounding gaps and redraft requests

- Mathlib/PhysLean search exposed general rays, angles, and dimensionful quantities, but no geometric-optics API for optical media, refractive index, plane glass slabs, or Snell's law. The local abstractions above fill this gap without assuming the requested answer.
- The prose asks for the angle `thetaB`, while all displayed choices are dimensionless decimals and recorded choice C (`0.866`) equals `sin(60 degrees)` to three decimal places, not the angle in degrees or radians. The formalization therefore concludes the exact angle `pi/3` and separately formalizes C as the nearest-thousandth sine readout. A blueprint redraft should clarify whether the original question intended to ask for `sin(thetaB)`.
- `.archon/AGENTS.md` was absent in this project checkout, so the supplied turn instructions and `.archon/prover-modes/physics-formalize.md` were used as the role specification.
- The documented `archon dag-query` navigation command was unavailable on `PATH`; the chapter has no declared dependency lemmas in any case.
- The assigned Lean file contained no `/- USER: ... -/` comments, so there were no file-specific hints to apply.
- The blueprint was not marked `\\leanok`: the task's explicit write permissions authorize edits only to the assigned Lean file and this result file, and expressly prohibit editing the blueprint chapter.

## Verification

- Iteration 002 `archon-lean-lsp` diagnostics: success, with exactly two expected `declaration uses sorry` warnings at the helper lemma and target theorem, and no errors.
- Iteration 002 `lake env lean PhyXMiniProblems/problem_phyx_mini_0138.lean`: exit code 0, with the same two expected warnings and no errors.
