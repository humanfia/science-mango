# Autoformalization result: `problem_phyx_mini_0014.lean`

## Assumption/target split

### Governing laws

- `ObeysSpecularReflection setup trace` states the unfolded equal-angle reflection law in every `UnitChoices`: crossing number `n` has vertical rise `n * mirrorGap * tan incidenceAngle`.
- The same predicate states the physical finite-segment/contact bookkeeping: odd candidates are left-mirror contacts, even candidates are right-mirror contacts, and a candidate is counted exactly when its SI height lies between the common lower and upper edges.

### Previous-part results

- None. The source report has an empty `previous_parts` array, and the chapter does not invoke an earlier subproblem.

### Figure/data readouts

- `HasFigureReadout setup` records a `1 m` horizontal mirror separation and a `1 m` common vertical span.
- It records the initial contact as the lower endpoint of the right mirror.
- It records the ray inclination as `5 degrees` above the horizontal mirror normal.
- These facts were checked against the primary image `phyx_data/test_image/14.png`; the image, rather than the inconsistent auxiliary caption sentence about first striking the left mirror, supports the right-lower-endpoint convention used by the blueprint.

### Current target conclusion

- `trace.leftMirrorReflectionIndices.card = 6`, i.e. answer choice C.

## Goal-faithfulness audit

The value `6`, the cardinality equality, and answer-choice selection occur only in the conclusion and theorem documentation. Neither `HasFigureReadout`, `ObeysSpecularReflection`, `ParallelMirrorSetup`, nor `ReflectedBeamTrace` contains the requested cardinality or an equivalent precomputed answer. `ObeysSpecularReflection` supplies only the general per-crossing propagation law, parity rule, and finite-mirror membership criterion. Thus the six-contact result still requires the nontrivial facts that the left candidates at odd indices through `11` lie in the span while the next candidate at `13` lies above it.

No local definition makes the target true by unfolding. `valueInMeters` is solely an SI coordinate projection, and `angleOfDegrees` is solely a unit conversion.

## Declarations created

- `LengthQuantity`: Physlib dimensionful length type.
- `valueInMeters`: SI-metre scalar projection of a dimensionful length.
- `angleOfDegrees`: degree-readout conversion to `Real.Angle`.
- `ParallelMirrorSetup`: dimensionful mirror coordinates, initial-contact coordinates, and incidence angle.
- `ReflectedBeamTrace`: dimensionful candidate heights and the two finite reflection-index sets.
- `HasFigureReadout`: source/image readouts only.
- `ObeysSpecularReflection`: local governing-law interface for unfolded specular reflection.
- `leftMirrorReflectionCount_eq_six`: formalizes blueprint label `thm:physics:phyx_mini_0014:target`.

The helper declarations do not yet have separate blueprint environments. The blueprint is read-only under this task's write permissions, so the plan/blueprint agent should add helper entries as needed and mark the target environment with `\leanok` after names stabilize.

## LeanExplore queries/candidates actually used

All searches used package filters `Mathlib` and `Physlib`.

- Query `physical dimension length quantity SI metre`: found `Dimension`, `Dimension.L𝓭`, `UnitChoices.SI`, and `UnitExamples.meters400`.
- Query `Length dimension Quantity SI meter`: found `HasDimension`, `Dimension.L𝓭`, `UnitChoices.SI`, and `UnitChoices.SI_length`.
- Query `unit system dimension length`: confirmed `UnitChoices.SI`, `Dimension.L𝓭`, and the Physlib unit-scaling infrastructure.
- Query `Real.Angle tangent angle degrees`: found and used `Real.Angle` and `Real.Angle.tan`.
- Query `geometrical optics specular reflection ray mirror angle of incidence`: found `EuclideanGeometry.reflection`, `Module.Ray`, and `RayVector`, but no geometrical-optics law matching a ray repeatedly reflecting between finite mirrors.

Source/module/docstring details were fetched for `Dimension`, `Dimension.L𝓭`, `UnitChoices.SI`, `HasDimension`, `UnitExamples.meters400`, `Real.Angle.tan`, and `EuclideanGeometry.reflection`. `UnitExamples.meters400` supplied the canonical construction pattern `Dimensionful (WithDim L𝓭 ℝ)` but was not imported because its source module explicitly says examples should not be dependencies of other modules.

## Physlib/Mathlib names grounded

- Physlib: `Dimension`, `Dimension.L𝓭`, `Dimensionful`, `WithDim`, `UnitChoices`, and `UnitChoices.SI` from `Physlib.Units.WithDim.Basic` and its public imports.
- Mathlib: `Real.Angle`, `Real.Angle.tan`, `Finset`, `Odd`, and `Even`.
- `EuclideanGeometry.reflection` was inspected but not used: it is an affine isometry reflecting points in a complete affine subspace, not an optics propagation/contact law for finite mirrors.

## Local abstractions introduced

- `LengthQuantity` abbreviates `Dimensionful (WithDim Dimension.L𝓭 ℝ)`. It is not a transparent scalar alias: its values are physical lengths with the correct Physlib dimension and unit-scaling law.
- `valueInMeters` exposes only the named SI-metre coordinate needed to state figure readouts and compare heights.
- `ParallelMirrorSetup` preserves the two labelled vertical-line coordinates, their shared endpoints, the depicted starting point, and the physical angle.
- `ReflectedBeamTrace` preserves dimensionful contact heights rather than replacing them with unexplained reals.
- `ObeysSpecularReflection` is the smallest local optics interface found that captures straight-line propagation after unfolding, equal-angle reflection, mirror parity, and finite segment termination without assuming the requested count.

## Source/law/answer audit

- Primary-image facts: vertical parallel mirrors, `1.00 m` separation, `1.00 m` height, a right-lower-endpoint initial contact, and a `5.00 degree` ray angle.
- Governing law: the unfolded path rises by `tan(5 degrees) m` per one-metre crossing.
- Supported answer: left contacts have heights `(2k+1) tan(5 degrees) m`; `11 tan(5 degrees) < 1` and `13 tan(5 degrees) > 1`, leaving exactly six left contacts. This agrees with recorded choice C.
- No current-answer contradiction was found.

## Grounding gaps and redraft requests

- No Physlib declaration for repeated geometrical-optics specular reflection at finite mirrors was found. The local governing-law predicate records this missing interface faithfully.
- `.archon/AGENTS.md` was absent at the exact instructed path. The stage and role constraints supplied in the task prompt and `.archon/PROGRESS.md` were followed.
- The assigned Lean file contained no `/- USER: ... -/` hint.
- Standalone verification with `lake env lean PhyXMiniProblems/problem_phyx_mini_0014.lean` succeeds with only the expected theorem-body `sorry` warning.
