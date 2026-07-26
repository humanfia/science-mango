# Autoformalization result: `problem_phyx_mini_0907.lean`

## Assumption/target split

### Governing laws

- `SatisfiesVectorCoulombForceLaw`: for each of the two sources, the force on the target is the signed vector law `k q_target q_source r / ‖r‖³`.
- `SatisfiesElectrostaticForceSuperposition`: the resultant force is the sum of the two source-force vectors.
- `SatisfiesResultantForceMagnitudeLaw`: the independent dimensionful magnitude observable agrees with the norm of the resultant vector.
- `UsesSchoolCoulombConstant`: the coherent-SI scalar is calibrated to the textbook value `9 * 10^9 N m²/C²`.

### Previous-part results

- None. The source report lists no previous parts.

### Figure/data readouts

- The left source is `+10 nC`, the upper target is `-1.0 nC`, and the right charge is the unspecified physical charge `q`.
- The three charges occupy the left-base, upper-vertex, and right-base sites of the displayed triangle.
- The horizontal base is `5.0 cm`; its printed endpoint angles are `60°` and `30°`.
- `SatisfiesDisplayedTriangleGeometry` realizes the corresponding `30°`--`60°`--`90°` geometry, including the dashed altitude and its foot.
- The red arrow is shown at the target charge and represents the net force. `CalibratesDisplayedDownwardForceDirection` states only that its horizontal component is zero and its vertical component is negative.
- The raster contains no numerical force label.

### Current target conclusions

- The force magnitude lies strictly between `33 / 200000 N = 1.65 * 10^-4 N` and `7 / 40000 N = 1.75 * 10^-4 N`.
- It therefore rounds at resolution `10^-5 N` to the displayed `1.7 * 10^-4 N`.
- Answer choice C is uniquely closest among the four displayed choices.

## Goal-faithfulness audit

- The setup stores the unknown charge, pairwise forces, resultant force, and resultant magnitude as independent physical quantities. None is defined from an answer choice.
- The unknown `q` has no numerical premise. Its needed value/sign information must be derived from the downward net-force direction together with Coulomb's law and superposition.
- The force-arrow premise gives direction only; it contains no magnitude, numerical bound, rounding claim, or answer label.
- Neither `1.7 * 10^-4 N`, the bounding interval, nor choice C appears in any physics-law, scenario, geometry, figure, or readout premise.
- `displayedForceMagnitudeInNewtons` is only a transcription of the four choices. Agreement with choice C and unique-nearest selection occur on the conclusion side of `problem_phyx_mini_0907`.
- No target is made true by unfolding a local definition, and no proposition was replaced by `True`, reflexivity, or an unrelated algebraic statement.

## Declarations and blueprint correspondence

- `problem_phyx_mini_0907` corresponds to `thm:physics:phyx_mini_0907:target`.
- `source_target_distances_from_triangle` corresponds to `lem:physics:phyx-mini-0907:phyxminiproblems-problemphyxmini0907-source-target-distances-from-triangle`.
- `resultant_force_magnitude_numerical_bounds` corresponds to `lem:physics:phyx-mini-0907:phyxminiproblems-problemphyxmini0907-resultant-force-magnitude-numerical-bounds`.
- Every supporting public definition has the matching generated topology label `def:physics:phyx-mini-0907:...` in the chapter. In particular, the physical quantity definitions (`forceDimension`, `LengthQuantity`, `SignedChargeQuantity`, `PlanarPositionQuantity`, `PlanarForceQuantity`, and `ForceMagnitudeQuantity`), the SI readout definitions, `ThreeChargeTriangleFigure`, `ThreeChargeTriangleSetup`, all scenario/figure/geometry/law predicates, and the displayed-answer predicates are pinned there by their exact `\lean{}` names.
- The revised Lean declarations were already present at the start of this final evidence retry. They were re-audited against the source report and primary raster and preserved because the gate reason identified missing evidence rather than a semantic defect.

## LeanExplore grounding

All searches used `packages: ["Mathlib", "Physlib"]`.

Queries issued:

- `dimensionful physical quantity coherent SI unit choice WithDim Dimensionful UnitChoices.SI`
- `electromagnetic system Coulomb constant Electromagnetism.EMSystem.coulombConstant`
- `EuclideanSpace real Fin 2 norm planar vector`
- `signed vector Coulomb force electrostatic point charges superposition`
- `Dimension.L𝓭 Dimension.T𝓭 Dimension.M𝓭 Dimension.C𝓭`
- `WithDim`
- `Dimension.M𝓭`

Candidates whose Lean source and module were both fetched and which are used
by the formalization:

- `Dimension`, `Dimension.L𝓭`, `Dimension.T𝓭`, `Dimension.M𝓭`, and `Dimension.C𝓭` for physical dimensions.
- `WithDim` and `Dimensionful` for dimension-tagged, unit-independent physical quantities.
- `UnitChoices.SI` for coherent-SI readouts.
- `Electromagnetism.EMSystem` and `Electromagnetism.EMSystem.coulombConstant` for the electromagnetic-system parameter and Coulomb constant.
- `EuclideanSpace ℝ (Fin 2)` for planar positions and force vectors.

The fetched sources grounded these names in `Physlib.Units.Dimension`, `Physlib.Units.Basic`, `Physlib.Units.WithDim.Basic`, `Physlib.Electromagnetism.Basic`, and `Mathlib.Analysis.InnerProductSpace.PiL2`.

## PhysLean/Mathlib names grounded

- PhysLean/Physlib: `Dimension`, `Dimension.L𝓭`, `Dimension.T𝓭`,
  `Dimension.M𝓭`, `Dimension.C𝓭`, `WithDim`, `Dimensionful`,
  `UnitChoices.SI`, `Electromagnetism.EMSystem`, and
  `Electromagnetism.EMSystem.coulombConstant`.
- Mathlib: `EuclideanSpace ℝ (Fin 2)` for planar vectors; `NNReal`,
  `Real.Angle`, `Real.sqrt`, Euclidean norm notation, finite sums, and
  `!₂[...]` vector notation were additionally confirmed by successful LSP and
  Lake elaboration of their concrete uses in the file.

Near misses not used:

- The signed-vector-force query returned `signedDist`,
  `FluidDynamics.BodyForce`, and charge-distribution declarations alongside
  `Electromagnetism.EMSystem.coulombConstant`, but no ready-made theorem or
  predicate for the signed planar pairwise Coulomb **force** law plus
  superposition required here.
- The Euclidean-space search grounded planar vectors and their norm. The exact
  figure geometry is more directly represented by a coordinate realization of
  the `30°`--`60°`--`90°` triangle than by adding a separate angle API.

## Local abstractions introduced

- `ThreeChargeTriangleFigure` preserves literal raster content, including the unknown `q`, charge signs/colors, dashed sides, angle/base labels, altitude/right-angle marker, and force-arrow semantics.
- `ThreeChargeTriangleSetup` keeps all physical observables independent and dimensionful.
- `SatisfiesVectorCoulombForceLaw`, `SatisfiesElectrostaticForceSuperposition`, and `SatisfiesResultantForceMagnitudeLaw` provide the missing local governing-law interface without inserting the requested answer.
- `CalibratesDisplayedDownwardForceDirection` translates the qualitative arrow into component conditions without supplying a magnitude.
- `RoundsToAtResolution` and `IsUniqueClosestDisplayedForceChoice` make the multiple-choice approximation semantics explicit.

These abstractions preserve the physical roles that were not covered by a directly matching Physlib declaration; they do not collapse charge, length, position, or force to transparent scalar aliases.

## Source/law/answer audit

- The primary raster was inspected directly. It shows `+10 nC`, `-1.0 nC`, an
  unspecified `q`, a `5.0 cm` base, the `60°` and `30°` base angles, a dashed
  altitude with a right-angle marker, and a downward net-force arrow with no
  numerical magnitude.
- The local governing laws are exactly the signed vector Coulomb law,
  superposition, and magnitude-as-norm. The numerical answer is not included
  in any of those laws.
- The geometry and horizontal cancellation determine the contribution of the
  unknown charge without assuming its value. They support a resultant near
  `1.66 * 10^-4 N`, consistent with recorded answer C, `1.7 * 10^-4 N` after
  rounding.
- No source contradiction or redraft request was found.

## Grounding gaps

- No directly matching library declaration for the full signed vector Coulomb force law on dimensionful point charges was found, so the faithful local law predicate above was required.

## Project notes

- `.archon/AGENTS.md` was absent. The supplied role prompt and the complete `.archon/prover-modes/physics-formalize.md` were used as the available role instructions. The assigned file's `USER` comment records that the file was absent during the original autoformalization; the revised file was present for this final evidence retry.
- The `archon` executable was not available on `PATH`, so the optional dependency-graph query could not run.
- The blueprint environment was not edited to add `\leanok` because the task's explicit write permissions prohibit editing blueprint chapters. A blueprint-maintaining agent should add `\leanok` to `thm:physics:phyx_mini_0907:target`.

## Verification

- `archon-lean-lsp` diagnostics reported only the three expected `declaration uses sorry` warnings.
- `lake env lean PhyXMiniProblems/problem_phyx_mini_0907.lean` exited successfully with exactly those three warnings.
