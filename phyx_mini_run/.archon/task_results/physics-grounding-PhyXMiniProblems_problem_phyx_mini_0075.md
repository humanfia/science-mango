# Physics LeanExplore Grounding Log

- Target Lean file: `PhyXMiniProblems/problem_phyx_mini_0075.lean`
- Blueprint chapter: `blueprint/src/chapters/PhyXMiniProblems_problem_phyx_mini_0075.tex`
- Grounding status: complete
- Search backend: local
- Input fingerprint: sha256:c97788a037dc1f3323d49f89ca093af86f330395ce32adbb86f6b141ae453ee1
- Packages searched: Mathlib, Physlib

## LeanExplore queries/candidates actually used

### Query: `Physics formalization target`
- `Path.target` | module `Mathlib.Topology.Path` | package Mathlib | **Target of a Path.** For a path $\gamma$ from $x$ to $y$ in a topological space, the value of the path at the endpoint of the unit interval, $\gamma(1)$, is equal to $y$.
- `semiformal_result` | module `Physlib.Meta.Informal.SemiFormal` | package PhysLean | A semiformal result is either a - definition in which the type is given but not the definition. - proof in which the proposition is given but not the proof. Semiformal results cannot be used in further code. They are...
- `stereographic_target` | module `Mathlib.Geometry.Manifold.Instances.Sphere` | package Mathlib | **Target of the Stereographic Projection.** For any unit vector $v$ in an inner product space, the target of the stereographic projection associated with $v$ is the entire codomain (the orthogonal complement of the su...

### Query: `Length Quantity`
- `LengthUnit` | module `Physlib.SpaceAndTime.Space.LengthUnit` | package PhysLean | The choices of translationally-invariant metrics on the space-manifold. Such a choice corresponds to a choice of units for length.
- `Computation.length` | module `Mathlib.Data.Seq.Computation` | package Mathlib | `length s` gets the number of steps of a terminating computation
- `LengthUnit.links` | module `Physlib.SpaceAndTime.Space.LengthUnit` | package PhysLean | The length unit of link (0.201168 meters).

### Query: `length Readout`
- `Computation.length` | module `Mathlib.Data.Seq.Computation` | package Mathlib | `length s` gets the number of steps of a terminating computation
- `LengthUnit.rods` | module `Physlib.SpaceAndTime.Space.LengthUnit` | package PhysLean | The length unit of a rod (5.0292 meters)
- `Cycle.length` | module `Mathlib.Data.List.Cycle` | package Mathlib | The length of the `s : Cycle α`, which is the number of elements, counting duplicates.

### Query: `length In Meters`
- `LengthUnit.meters` | module `Physlib.SpaceAndTime.Space.LengthUnit` | package PhysLean | The definition of a length unit of meters.
- `LengthUnit.links` | module `Physlib.SpaceAndTime.Space.LengthUnit` | package PhysLean | The length unit of link (0.201168 meters).
- `LengthUnit.rods` | module `Physlib.SpaceAndTime.Space.LengthUnit` | package PhysLean | The length unit of a rod (5.0292 meters)

### Query: `length In Millimeters`
- `LengthUnit.millimeters` | module `Physlib.SpaceAndTime.Space.LengthUnit` | package PhysLean | The length unit of millimeters (10⁻³ of a meter).
- `LengthUnit.miles` | module `Physlib.SpaceAndTime.Space.LengthUnit` | package PhysLean | The length unit of a mile (1609.344 meters).
- `LengthUnit.micrometers` | module `Physlib.SpaceAndTime.Space.LengthUnit` | package PhysLean | The length unit of micrometers (10⁻⁶ of a meter).

### Query: `length In Nanometers`
- `LengthUnit.nanometers` | module `Physlib.SpaceAndTime.Space.LengthUnit` | package PhysLean | The length unit of nanometers (10⁻⁹ of a meter).
- `LengthUnit.femtometers` | module `Physlib.SpaceAndTime.Space.LengthUnit` | package PhysLean | The length unit of femtometers (10⁻¹⁵ of a meter).
- `LengthUnit.picometers` | module `Physlib.SpaceAndTime.Space.LengthUnit` | package PhysLean | The length unit of picometers (10⁻¹² of a meter).

### Query: `length In Feet`
- `LengthUnit.feet` | module `Physlib.SpaceAndTime.Space.LengthUnit` | package PhysLean | The length unit of feet (0.3048 meters)
- `LengthUnit.rods` | module `Physlib.SpaceAndTime.Space.LengthUnit` | package PhysLean | The length unit of a rod (5.0292 meters)
- `DimArea.acre_eq_mul_squareFeet` | module `Physlib.Units.WithDim.Area` | package PhysLean | One acre is exactly `43560` square feet.

### Query: `Figure Length Label`
- `LengthUnit.feet` | module `Physlib.SpaceAndTime.Space.LengthUnit` | package PhysLean | The length unit of feet (0.3048 meters)
- `MonadCont.Label` | module `Mathlib.Control.Monad.Cont` | package Mathlib | **Continuation Label.** A continuation label is a structure that encapsulates a function mapping values of type $\alpha$ to computations in a monad $m$ that produce values of type $\beta$.
- `LengthUnit.links` | module `Physlib.SpaceAndTime.Space.LengthUnit` | package PhysLean | The length unit of link (0.201168 meters).

### Query: `Figure Angle Label`
- `Real.Angle.sign` | module `Mathlib.Analysis.SpecialFunctions.Trigonometric.Angle` | package Mathlib | The sign of a `Real.Angle` is `0` if the angle is `0` or `π`, `1` if the angle is strictly between `0` and `π` and `-1` is the angle is strictly between `-π` and `0`. It is defined as the sign of the sine of the angle.
- `EuclideanGeometry.angle` | module `Mathlib.Geometry.Euclidean.Angle.Unoriented.Affine` | package Mathlib | The undirected angle at `p₂` between the line segments to `p₁` and `p₃`. If either of those points equals `p₂`, this is π/2. Use `open scoped EuclideanGeometry` to access the `∠ p₁ p₂ p₃` notation.
- `EuclideanGeometry.angle_lt_pi_div_three_of_le_of_le_of_ne` | module `Mathlib.Geometry.Euclidean.Triangle` | package Mathlib | The least angle of a possibly degenerate triangle is less than `π / 3`, unless all angles are equal.

### Query: `Lighting Condition`
- `NormalizerCondition` | module `Mathlib.Algebra.Group.Subgroup.Basic` | package Mathlib | Every proper subgroup `H` of `G` is a proper normal subgroup of the normalizer of `H` in `G`.
- `LightProfinite` | module `Mathlib.Topology.Category.LightProfinite.Basic` | package Mathlib | `LightProfinite` is the category of second countable profinite spaces.
- `LightCondensed.ofSheafLightProfinite` | module `Mathlib.Condensed.Light.Explicit` | package Mathlib | The light condensed object associated to a presheaf on `LightProfinite` which preserves finite products and satisfies the equalizer condition.

## Grounded Mathlib/PhysLean names

- `Path.target` (Mathlib)
- `semiformal_result` (PhysLean)
- `stereographic_target` (Mathlib)
- `LengthUnit` (PhysLean)
- `Computation.length` (Mathlib)
- `LengthUnit.links` (PhysLean)
- `Computation.length` (Mathlib)
- `LengthUnit.rods` (PhysLean)
- `Cycle.length` (Mathlib)
- `LengthUnit.meters` (PhysLean)
- `LengthUnit.links` (PhysLean)
- `LengthUnit.rods` (PhysLean)
- `LengthUnit.millimeters` (PhysLean)
- `LengthUnit.miles` (PhysLean)
- `LengthUnit.micrometers` (PhysLean)
- `LengthUnit.nanometers` (PhysLean)
- `LengthUnit.femtometers` (PhysLean)
- `LengthUnit.picometers` (PhysLean)
- `LengthUnit.feet` (PhysLean)
- `LengthUnit.rods` (PhysLean)
- `DimArea.acre_eq_mul_squareFeet` (PhysLean)
- `LengthUnit.feet` (PhysLean)
- `MonadCont.Label` (Mathlib)
- `LengthUnit.links` (PhysLean)
- `Real.Angle.sign` (Mathlib)
- `EuclideanGeometry.angle` (Mathlib)
- `EuclideanGeometry.angle_lt_pi_div_three_of_le_of_le_of_ne` (Mathlib)
- `NormalizerCondition` (Mathlib)
- `LightProfinite` (Mathlib)
- `LightCondensed.ofSheafLightProfinite` (Mathlib)

## Local abstractions introduced

- `PhyXMiniProblems.ProblemPhyXMini0075.AcuityLimitation`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMiniProblems.ProblemPhyXMini0075.AnswerChoice`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMiniProblems.ProblemPhyXMini0075.EyeChartResolutionSetup`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMiniProblems.ProblemPhyXMini0075.FigureAngleLabel`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMiniProblems.ProblemPhyXMini0075.FigureLengthLabel`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMiniProblems.ProblemPhyXMini0075.HasPhysicalParameters`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMiniProblems.ProblemPhyXMini0075.IsClosestDisplayedChoice`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMiniProblems.ProblemPhyXMini0075.IsUniqueClosestDisplayedChoice`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMiniProblems.ProblemPhyXMini0075.LengthQuantity`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMiniProblems.ProblemPhyXMini0075.LightingCondition`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMiniProblems.ProblemPhyXMini0075.MatchesProblemReadouts`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMiniProblems.ProblemPhyXMini0075.ResolutionRegime`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMiniProblems.ProblemPhyXMini0075.SatisfiesControlledFigureGeometry`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMiniProblems.ProblemPhyXMini0075.SatisfiesParaxialFigureGeometry`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMiniProblems.ProblemPhyXMini0075.SatisfiesPupilAcuityTrend`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMiniProblems.ProblemPhyXMini0075.SatisfiesRayleighCriterion`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMiniProblems.ProblemPhyXMini0075.SourceLeavesWavelengthUnspecified`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMiniProblems.ProblemPhyXMini0075.UsesControlledRayleighRegime`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMiniProblems.ProblemPhyXMini0075.UsesRayleighParaxialRegime`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMiniProblems.ProblemPhyXMini0075.UsesRepresentativeVisibleWavelength`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMiniProblems.ProblemPhyXMini0075.WavelengthModel`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMiniProblems.ProblemPhyXMini0075.WavelengthProvenance`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.

## Grounding gaps

- No unresolved LeanExplore grounding gaps were recorded by this preflight.
