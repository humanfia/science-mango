# Physics LeanExplore Grounding Log

- Target Lean file: `PhyXMiniProblems/problem_phyx_mini_0039.lean`
- Blueprint chapter: `blueprint/src/chapters/PhyXMiniProblems_problem_phyx_mini_0039.tex`
- Grounding status: complete
- Search backend: local
- Input fingerprint: sha256:d2eef08e198c4e95613d37acdfa4a53b391468c30bfd8b9268dd64d630d1e3cc
- Packages searched: Mathlib, Physlib

## LeanExplore queries/candidates actually used

### Query: `Gauss law divergence electric field`
- `Electromagnetism.ElectromagneticPotential.electricField` | module `Physlib.Electromagnetism.Kinematics.ElectricField` | package PhysLean | The electric field from the electromagnetic potential.
- `Electromagnetism.ElectricField` | module `Physlib.Electromagnetism.Basic` | package PhysLean | The electric field is a map from `d`+1 dimensional spacetime to the vector space `ℝ^d`.
- `Space.distDiv_inv_pow_eq_dim` | module `Physlib.SpaceAndTime.Space.Norm.Basic` | package PhysLean | The distributional divergence of the radial field `x ↦ ‖x‖ ^ (-d) • x` (i.e. `x / ‖x‖ ^ d`) equals `d * volume (Metric.ball 0 1)` — the surface area of the unit sphere `S^{d-1}` — times the Dirac delta at the origin....

### Query: `Physics formalization target`
- `Path.target` | module `Mathlib.Topology.Path` | package Mathlib | **Target of a Path.** For a path $\gamma$ from $x$ to $y$ in a topological space, the value of the path at the endpoint of the unit interval, $\gamma(1)$, is equal to $y$.
- `semiformal_result` | module `Physlib.Meta.Informal.SemiFormal` | package PhysLean | A semiformal result is either a - definition in which the type is given but not the definition. - proof in which the proposition is given but not the proof. Semiformal results cannot be used in further code. They are...
- `stereographic_target` | module `Mathlib.Geometry.Manifold.Instances.Sphere` | package Mathlib | **Target of the Stereographic Projection.** For any unit vector $v$ in an inner product space, the target of the stereographic projection associated with $v$ is the entire codomain (the orthogonal complement of the su...

### Query: `Length Quantity`
- `LengthUnit` | module `Physlib.SpaceAndTime.Space.LengthUnit` | package PhysLean | The choices of translationally-invariant metrics on the space-manifold. Such a choice corresponds to a choice of units for length.
- `Computation.length` | module `Mathlib.Data.Seq.Computation` | package Mathlib | `length s` gets the number of steps of a terminating computation
- `LengthUnit.links` | module `Physlib.SpaceAndTime.Space.LengthUnit` | package PhysLean | The length unit of link (0.201168 meters).

### Query: `centimeter Unit Choices`
- `UnitChoices` | module `Physlib.Units.Basic` | package PhysLean | The choice of units.
- `IsUnit` | module `Mathlib.Algebra.Group.Units.Defs` | package Mathlib | An element `a : M` of a `Monoid` is a unit if it has a two-sided inverse. The actual definition says that `a` is equal to some `u : Mˣ`, where `Mˣ` is a bundled version of `IsUnit`.
- `LengthUnit.centimeters` | module `Physlib.SpaceAndTime.Space.LengthUnit` | package PhysLean | The length unit of centimeters (10⁻² of a meter).

### Query: `length In Centimeters`
- `LengthUnit.centimeters` | module `Physlib.SpaceAndTime.Space.LengthUnit` | package PhysLean | The length unit of centimeters (10⁻² of a meter).
- `LengthUnit.links` | module `Physlib.SpaceAndTime.Space.LengthUnit` | package PhysLean | The length unit of link (0.201168 meters).
- `LengthUnit.rods` | module `Physlib.SpaceAndTime.Space.LengthUnit` | package PhysLean | The length unit of a rod (5.0292 meters)

### Query: `Spherical Mirror Kind`
- `Cosmology.SpatialGeometry.Spherical` | module `Physlib.Cosmology.FLRW.Basic` | package PhysLean | **Spherical Spatial Geometry.** A spherical spatial geometry is characterized by a curvature parameter $k$ that is strictly less than zero.
- `Metric.sphere` | module `Mathlib.Topology.MetricSpace.Pseudo.Defs` | package Mathlib | `sphere x ε` is the set of all points `y` with `dist y x = ε`
- `Polynomial.mirror` | module `Mathlib.Algebra.Polynomial.Mirror` | package Mathlib | mirror of a polynomial: reverses the coefficients while preserving `Polynomial.natDegree`

### Query: `Axis Location`
- `RigidBody.intermediate_axis_instability` | module `Physlib.ClassicalMechanics.RigidBody.Basic` | package PhysLean | Rotations about the largest and smallest principal axes are stable under small perturbations; rotation about the intermediate axis is unstable (tennis-racket effect).
- `HahnSeries.orderTop` | module `Mathlib.RingTheory.HahnSeries.Basic` | package Mathlib | The orderTop of a Hahn series `x` is a minimal element of `WithTop Γ` where `x` has a nonzero coefficient if `x ≠ 0`, and is `⊤` when `x = 0`.
- `RigidBody.parallel_axis_theorem` | module `Physlib.ClassicalMechanics.RigidBody.Basic` | package PhysLean | If I_O is the inertia tensor about a point O, then the inertia tensor about a parallel point O' displaced by a is I_{O'} = I_O + M(|a|² 1 − a ⊗ a). This is the parallel-axis theorem.

### Query: `Ornament Mirror Setup`
- `Polynomial.mirror` | module `Mathlib.Algebra.Polynomial.Mirror` | package Mathlib | mirror of a polynomial: reverses the coefficients while preserving `Polynomial.natDegree`
- `HahnSeries.orderTop` | module `Mathlib.RingTheory.HahnSeries.Basic` | package Mathlib | The orderTop of a Hahn series `x` is a minimal element of `WithTop Γ` where `x` has a nonzero coefficient if `x ≠ 0`, and is `⊤` when `x = 0`.
- `OrthonormalBasis.adjustToOrientation` | module `Mathlib.Analysis.InnerProductSpace.Orientation` | package Mathlib | Given an orthonormal basis and an orientation, return an orthonormal basis giving that orientation: either the original basis, or one constructed by negating a single (arbitrary) basis vector.

### Query: `Matches Figure Readouts`
- `RegularExpression.matches'` | module `Mathlib.Computability.RegularExpressions` | package Mathlib | `matches' P` provides a language which contains all strings that `P` matches. Not named `matches` since that is a reserved word.
- `RegularExpression.matches'_char` | module `Mathlib.Computability.RegularExpressions` | package Mathlib | **Language of a Character Regular Expression.** The language associated with the regular expression representing a single character $a$ is the singleton set containing the string consisting of only that character, den...
- `RegularExpression.matches'_add` | module `Mathlib.Computability.RegularExpressions` | package Mathlib | **Language of the Sum of Regular Expressions.** The language associated with the sum of two regular expressions $P$ and $Q$ is equal to the sum (union) of the languages associated with $P$ and $Q$ individually.

### Query: `Has Depicted Axis Geometry`
- `RigidBody.intermediate_axis_instability` | module `Physlib.ClassicalMechanics.RigidBody.Basic` | package PhysLean | Rotations about the largest and smallest principal axes are stable under small perturbations; rotation about the intermediate axis is unstable (tennis-racket effect).
- `AlgebraicGeometry.Scheme` | module `Mathlib.AlgebraicGeometry.Scheme` | package Mathlib | We define `Scheme` as an `X : LocallyRingedSpace`, along with a proof that every point has an open neighbourhood `U` so that the restriction of `X` to `U` is isomorphic, as a locally ringed space, to `Spec.toLocallyRi...
- `RigidBody.parallel_axis_theorem` | module `Physlib.ClassicalMechanics.RigidBody.Basic` | package PhysLean | If I_O is the inertia tensor about a point O, then the inertia tensor about a parallel point O' displaced by a is I_{O'} = I_O + M(|a|² 1 − a ⊗ a). This is the parallel-axis theorem.

## Grounded Mathlib/PhysLean names

- `Electromagnetism.ElectromagneticPotential.electricField` (PhysLean)
- `Electromagnetism.ElectricField` (PhysLean)
- `Space.distDiv_inv_pow_eq_dim` (PhysLean)
- `Path.target` (Mathlib)
- `semiformal_result` (PhysLean)
- `stereographic_target` (Mathlib)
- `LengthUnit` (PhysLean)
- `Computation.length` (Mathlib)
- `LengthUnit.links` (PhysLean)
- `UnitChoices` (PhysLean)
- `IsUnit` (Mathlib)
- `LengthUnit.centimeters` (PhysLean)
- `LengthUnit.centimeters` (PhysLean)
- `LengthUnit.links` (PhysLean)
- `LengthUnit.rods` (PhysLean)
- `Cosmology.SpatialGeometry.Spherical` (PhysLean)
- `Metric.sphere` (Mathlib)
- `Polynomial.mirror` (Mathlib)
- `RigidBody.intermediate_axis_instability` (PhysLean)
- `HahnSeries.orderTop` (Mathlib)
- `RigidBody.parallel_axis_theorem` (PhysLean)
- `Polynomial.mirror` (Mathlib)
- `HahnSeries.orderTop` (Mathlib)
- `OrthonormalBasis.adjustToOrientation` (Mathlib)
- `RegularExpression.matches'` (Mathlib)
- `RegularExpression.matches'_char` (Mathlib)
- `RegularExpression.matches'_add` (Mathlib)
- `RigidBody.intermediate_axis_instability` (PhysLean)
- `AlgebraicGeometry.Scheme` (Mathlib)
- `RigidBody.parallel_axis_theorem` (PhysLean)

## Local abstractions introduced

- `PhyXMiniProblems.ProblemPhyXMini0039.AnswerChoice`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMiniProblems.ProblemPhyXMini0039.AxisLocation`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMiniProblems.ProblemPhyXMini0039.HasDepictedAxisGeometry`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMiniProblems.ProblemPhyXMini0039.LengthQuantity`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMiniProblems.ProblemPhyXMini0039.MatchesFigureReadouts`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMiniProblems.ProblemPhyXMini0039.OrnamentMirrorSetup`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMiniProblems.ProblemPhyXMini0039.RoundsToNearestTenth`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMiniProblems.ProblemPhyXMini0039.SatisfiesParaxialMirrorLaws`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMiniProblems.ProblemPhyXMini0039.SphericalMirrorKind`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.

## Grounding gaps

- No unresolved LeanExplore grounding gaps were recorded by this preflight.
