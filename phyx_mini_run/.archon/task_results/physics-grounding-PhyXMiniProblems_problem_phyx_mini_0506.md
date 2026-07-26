# Physics LeanExplore Grounding Log

- Target Lean file: `PhyXMiniProblems/problem_phyx_mini_0506.lean`
- Blueprint chapter: `blueprint/src/chapters/PhyXMiniProblems_problem_phyx_mini_0506.tex`
- Grounding status: complete
- Search backend: local
- Input fingerprint: sha256:d306e367b5372d13250e193a6574aa7dc3d47ba19e51e1b9e531167a3a9efcf7
- Packages searched: Mathlib, Physlib

## LeanExplore queries/candidates actually used

### Query: `Physics formalization target`
- `Path.target` | module `Mathlib.Topology.Path` | package Mathlib | **Target of a Path.** For a path $\gamma$ from $x$ to $y$ in a topological space, the value of the path at the endpoint of the unit interval, $\gamma(1)$, is equal to $y$.
- `semiformal_result` | module `Physlib.Meta.Informal.SemiFormal` | package PhysLean | A semiformal result is either a - definition in which the type is given but not the definition. - proof in which the proposition is given but not the proof. Semiformal results cannot be used in further code. They are...
- `stereographic_target` | module `Mathlib.Geometry.Manifold.Instances.Sphere` | package Mathlib | **Target of the Stereographic Projection.** For any unit vector $v$ in an inner product space, the target of the stereographic projection associated with $v$ is the entire codomain (the orthogonal complement of the su...

### Query: `left Wall Millimetres`
- `LengthUnit.millimeters` | module `Physlib.SpaceAndTime.Space.LengthUnit` | package PhysLean | The length unit of millimeters (10⁻³ of a meter).
- `LengthUnit.miles` | module `Physlib.SpaceAndTime.Space.LengthUnit` | package PhysLean | The length unit of a mile (1609.344 meters).
- `LengthUnit.micrometers` | module `Physlib.SpaceAndTime.Space.LengthUnit` | package PhysLean | The length unit of micrometers (10⁻⁶ of a meter).

### Query: `right Wall Millimetres`
- `LengthUnit.millimeters` | module `Physlib.SpaceAndTime.Space.LengthUnit` | package PhysLean | The length unit of millimeters (10⁻³ of a meter).
- `LengthUnit.miles` | module `Physlib.SpaceAndTime.Space.LengthUnit` | package PhysLean | The length unit of a mile (1609.344 meters).
- `DimPressure.millimeterOfMercury` | module `Physlib.Units.WithDim.Pressure` | package PhysLean | The dimensional pressure corresponding to 1 millimeter of mercury (133.322387415 pascals).

### Query: `query Lower Millimetres`
- `lowerClosure` | module `Mathlib.Order.UpperLower.Closure` | package Mathlib | The least lower set containing a given set.
- `LengthUnit.millimeters` | module `Physlib.SpaceAndTime.Space.LengthUnit` | package PhysLean | The length unit of millimeters (10⁻³ of a meter).
- `DimPressure.millimeterOfMercury` | module `Physlib.Units.WithDim.Pressure` | package PhysLean | The dimensional pressure corresponding to 1 millimeter of mercury (133.322387415 pascals).

### Query: `query Upper Millimetres`
- `upperClosure` | module `Mathlib.Order.UpperLower.Closure` | package Mathlib | The greatest upper set containing a given set.
- `LengthUnit.millimeters` | module `Physlib.SpaceAndTime.Space.LengthUnit` | package PhysLean | The length unit of millimeters (10⁻³ of a meter).
- `LengthUnit.micrometers` | module `Physlib.SpaceAndTime.Space.LengthUnit` | package PhysLean | The length unit of micrometers (10⁻⁶ of a meter).

### Query: `position Probability`
- `MeasureTheory.IsProbabilityMeasure` | module `Mathlib.MeasureTheory.Measure.Typeclasses.Probability` | package Mathlib | A measure `μ` is called a probability measure if `μ univ = 1`.
- `FieldSpecification.FieldOp.position` | module `Physlib.QFT.PerturbationTheory.FieldSpecification.Basic` | package PhysLean | **Position Field Operator Construction.** For a given field specification, a position field operator is defined by a triple consisting of a field $f$, a position label associated with $f$, and a point in spacetime.
- `QuantumMechanics.positionOperator` | module `Physlib.QuantumMechanics.Operators.Position` | package PhysLean | The operator on `SpaceDHilbertSpace d` acting by multiplication by `fun x ↦ xᵢ`.

### Query: `Rounds To Hundredth`
- `round` | module `Mathlib.Algebra.Order.Round` | package Mathlib | `round x` rounds `x` to the nearest integer, breaking ties towards positive infinity. `round (0.5 : ℚ) = 1`.
- `Mathlib.CountHeartbeats.roundDownIf` | module `Mathlib.Util.CountHeartbeats` | package Mathlib | Round down the number `n` to the nearest thousand, if `approx` is `true`.
- `toEuclidean` | module `Mathlib.Analysis.InnerProductSpace.EuclideanDist` | package Mathlib | If `E` is a finite-dimensional space over `ℝ`, then `toEuclidean` is a continuous `ℝ`-linear equivalence between `E` and the Euclidean space of the same dimension.

### Query: `central interval probability`
- `intervalIntegral` | module `Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic` | package Mathlib | The interval integral `∫ x in a..b, f x ∂μ` is defined as `∫ x in Ioc a b, f x ∂μ - ∫ x in Ioc b a, f x ∂μ`. If `a ≤ b`, then it equals `∫ x in Ioc a b, f x ∂μ`, otherwise it equals `-∫ x in Ioc b a, f x ∂μ`.
- `ProbabilityTheory.centralMoment` | module `Mathlib.Probability.Moments.Basic` | package Mathlib | Central moment of a real random variable, `μ[(X - μ[X]) ^ p]`.
- `ProbabilityTheory.centralMoment_zero` | module `Mathlib.Probability.Moments.Basic` | package Mathlib | **The Central Moment of the Zero Function.** For any non-zero natural number $p$ and any measure $\mu$, the $p$-th central moment of the constant function $0$ is equal to $0$.

## Grounded Mathlib/PhysLean names

- `Path.target` (Mathlib)
- `semiformal_result` (PhysLean)
- `stereographic_target` (Mathlib)
- `LengthUnit.millimeters` (PhysLean)
- `LengthUnit.miles` (PhysLean)
- `LengthUnit.micrometers` (PhysLean)
- `LengthUnit.millimeters` (PhysLean)
- `LengthUnit.miles` (PhysLean)
- `DimPressure.millimeterOfMercury` (PhysLean)
- `lowerClosure` (Mathlib)
- `LengthUnit.millimeters` (PhysLean)
- `DimPressure.millimeterOfMercury` (PhysLean)
- `upperClosure` (Mathlib)
- `LengthUnit.millimeters` (PhysLean)
- `LengthUnit.micrometers` (PhysLean)
- `MeasureTheory.IsProbabilityMeasure` (Mathlib)
- `FieldSpecification.FieldOp.position` (PhysLean)
- `QuantumMechanics.positionOperator` (PhysLean)
- `round` (Mathlib)
- `Mathlib.CountHeartbeats.roundDownIf` (Mathlib)
- `toEuclidean` (Mathlib)
- `intervalIntegral` (Mathlib)
- `ProbabilityTheory.centralMoment` (Mathlib)
- `ProbabilityTheory.centralMoment_zero` (Mathlib)

## Local abstractions introduced

- `PhyXMini0506.RoundsToHundredth`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.

## Grounding gaps

- No unresolved LeanExplore grounding gaps were recorded by this preflight.
