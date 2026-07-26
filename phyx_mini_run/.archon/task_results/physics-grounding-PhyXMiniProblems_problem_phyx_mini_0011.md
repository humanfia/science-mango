# Physics LeanExplore Grounding Log

- Target Lean file: `PhyXMiniProblems/problem_phyx_mini_0011.lean`
- Blueprint chapter: `blueprint/src/chapters/PhyXMiniProblems_problem_phyx_mini_0011.tex`
- Grounding status: complete
- Search backend: local
- Input fingerprint: sha256:c410b4857112763d8ded38a8ba9b58f7d723e7d0ce631d7af6ad0a02e229aa25
- Packages searched: Mathlib, Physlib

## LeanExplore queries/candidates actually used

### Query: `Physics formalization target`
- `Path.target` | module `Mathlib.Topology.Path` | package Mathlib | **Target of a Path.** For a path $\gamma$ from $x$ to $y$ in a topological space, the value of the path at the endpoint of the unit interval, $\gamma(1)$, is equal to $y$.
- `semiformal_result` | module `Physlib.Meta.Informal.SemiFormal` | package PhysLean | A semiformal result is either a - definition in which the type is given but not the definition. - proof in which the proposition is given but not the proof. Semiformal results cannot be used in further code. They are...
- `stereographic_target` | module `Mathlib.Geometry.Manifold.Instances.Sphere` | package Mathlib | **Target of the Stereographic Projection.** For any unit vector $v$ in an inner product space, the target of the stereographic projection associated with $v$ is the entire codomain (the orthogonal complement of the su...

### Query: `Optical Medium`
- `HahnSeries.orderTop` | module `Mathlib.RingTheory.HahnSeries.Basic` | package Mathlib | The orderTop of a Hahn series `x` is a minimal element of `WithTop Γ` where `x` has a nonzero coefficient if `x ≠ 0`, and is `⊤` when `x = 0`.
- `HahnSeries.order_abs` | module `Mathlib.RingTheory.HahnSeries.Lex` | package Mathlib | **Order of the Absolute Value of a Hahn Series.** For any Hahn series $x$ in a lexicographically ordered Hahn series ring, the order of its absolute value $|x|$ is equal to the order of $x$.
- `HahnSeries.single` | module `Mathlib.RingTheory.HahnSeries.Basic` | package Mathlib | `single a r` is the Hahn series which has coefficient `r` at `a` and zero otherwise.

### Query: `Figure Point`
- `genericPoint` | module `Mathlib.Topology.Sober` | package Mathlib | A generic point of a sober irreducible space.
- `OnePoint.infty` | module `Mathlib.Topology.Compactification.OnePoint.Basic` | package Mathlib | The point at infinity
- `OnePoint` | module `Mathlib.Topology.Compactification.OnePoint.Basic` | package Mathlib | The one-point extension of an arbitrary topological space `X`

### Query: `Planar Direction`
- `AffineSubspace.direction` | module `Mathlib.LinearAlgebra.AffineSpace.AffineSubspace.Defs` | package Mathlib | The direction of an affine subspace is the submodule spanned by the pairwise differences of points. (Except in the case of an empty affine subspace, where the direction is the zero submodule, every vector in the direc...
- `Space.Direction` | module `Physlib.SpaceAndTime.Space.Module` | package PhysLean | Notion of direction where `unit` returns a unit vector in the direction specified.
- `Affine.Simplex.direction_mongePlane` | module `Mathlib.Geometry.Euclidean.MongePoint` | package Mathlib | The direction of a Monge plane.

### Query: `Axis Orientation`
- `Orientation.oangle` | module `Mathlib.Geometry.Euclidean.Angle.Oriented.Basic` | package Mathlib | The oriented angle from `x` to `y`, modulo `2 * π`. If either vector is 0, this is 0. See `InnerProductGeometry.angle` for the corresponding unoriented angle definition.
- `Orientation.finOrthonormalBasis_orientation` | module `Mathlib.Analysis.InnerProductSpace.Orientation` | package Mathlib | `Orientation.finOrthonormalBasis` gives a basis with the required orientation.
- `RigidBody.parallel_axis_theorem` | module `Physlib.ClassicalMechanics.RigidBody.Basic` | package PhysLean | If I_O is the inertia tensor about a point O, then the inertia tensor about a parallel point O' displaced by a is I_{O'} = I_O + M(|a|² 1 − a ⊗ a). This is the parallel-axis theorem.

### Query: `Rotation Axis`
- `Orientation.rotation` | module `Mathlib.Geometry.Euclidean.Angle.Oriented.Rotation` | package Mathlib | A rotation by the oriented angle `θ`.
- `RigidBody.intermediate_axis_instability` | module `Physlib.ClassicalMechanics.RigidBody.Basic` | package PhysLean | Rotations about the largest and smallest principal axes are stable under small perturbations; rotation about the intermediate axis is unstable (tennis-racket effect).
- `RigidBody.parallel_axis_theorem` | module `Physlib.ClassicalMechanics.RigidBody.Basic` | package PhysLean | If I_O is the inertia tensor about a point O, then the inertia tensor about a parallel point O' displaced by a is I_{O'} = I_O + M(|a|² 1 − a ⊗ a). This is the parallel-axis theorem.

### Query: `Diamond Rotation Setup`
- `Orientation.rotation` | module `Mathlib.Geometry.Euclidean.Angle.Oriented.Rotation` | package Mathlib | A rotation by the oriented angle `θ`.
- `rotation` | module `Mathlib.Analysis.Complex.Isometry` | package Mathlib | An element of the unit circle defines a `LinearIsometryEquiv` from `ℂ` to itself, by rotation.
- `Orientation.rightAngleRotation` | module `Mathlib.Analysis.InnerProductSpace.TwoDim` | package Mathlib | An isometric automorphism of an oriented real inner product space of dimension 2 (usual notation `J`). This automorphism squares to -1. We will define rotations in such a way that this automorphism is equal to rotatio...

### Query: `degrees To Radians`
- `Real.Angle.toReal` | module `Mathlib.Analysis.SpecialFunctions.Trigonometric.Angle` | package Mathlib | Convert a `Real.Angle` to a real number in the interval `Ioc (-π) π`.
- `MvPolynomial.degrees` | module `Mathlib.Algebra.MvPolynomial.Degrees` | package Mathlib | The maximal degrees of each variable in a multi-variable polynomial, expressed as a multiset. (For example, `degrees (x^2 * y + y^3)` would be `{x, x, y, y, y}`.)
- `MvPolynomial.degrees_C` | module `Mathlib.Algebra.MvPolynomial.Degrees` | package Mathlib | **Degrees of a Constant Multivariate Polynomial.** For any element $a$ in a commutative semiring $R$, the multiset of degrees of the constant multivariate polynomial $C(a)$ is empty.

### Query: `radians To Degrees`
- `Real.Angle.toReal` | module `Mathlib.Analysis.SpecialFunctions.Trigonometric.Angle` | package Mathlib | Convert a `Real.Angle` to a real number in the interval `Ioc (-π) π`.
- `MvPolynomial.degrees` | module `Mathlib.Algebra.MvPolynomial.Degrees` | package Mathlib | The maximal degrees of each variable in a multi-variable polynomial, expressed as a multiset. (For example, `degrees (x^2 * y + y^3)` would be `{x, x, y, y, y}`.)
- `MvPolynomial.degrees_C` | module `Mathlib.Algebra.MvPolynomial.Degrees` | package Mathlib | **Degrees of a Constant Multivariate Polynomial.** For any element $a$ in a commutative semiring $R$, the multiset of degrees of the constant multivariate polynomial $C(a)$ is empty.

### Query: `Has Positive Refractive Indices`
- `IsStrictlyPositive` | module `Mathlib.Algebra.Algebra.StrictPositivity` | package Mathlib | An element of an ordered algebra is *strictly positive* if it is nonnegative and invertible. NOTE: This definition will be generalized to the non-unital case in the future; do not unfold the definition and use the API...
- `Nat.bitIndices` | module `Mathlib.Data.Nat.BitIndices` | package Mathlib | The function which maps each natural number `∑ i ∈ s, 2 ^ i` to the list of elements of `s` in increasing order.
- `RootPairing.Base.IsPos.reflectionPerm` | module `Mathlib.LinearAlgebra.RootSystem.Base` | package Mathlib | **Positivity of Reflected Roots.** Let $b$ be a base for a root pairing $P$. For any indices $i$ and $j$, if $i$ is a positive root with respect to $b$, $j$ is in the support of $b$, and $i \neq j$, then the image of...

## Grounded Mathlib/PhysLean names

- `Path.target` (Mathlib)
- `semiformal_result` (PhysLean)
- `stereographic_target` (Mathlib)
- `HahnSeries.orderTop` (Mathlib)
- `HahnSeries.order_abs` (Mathlib)
- `HahnSeries.single` (Mathlib)
- `genericPoint` (Mathlib)
- `OnePoint.infty` (Mathlib)
- `OnePoint` (Mathlib)
- `AffineSubspace.direction` (Mathlib)
- `Space.Direction` (PhysLean)
- `Affine.Simplex.direction_mongePlane` (Mathlib)
- `Orientation.oangle` (Mathlib)
- `Orientation.finOrthonormalBasis_orientation` (Mathlib)
- `RigidBody.parallel_axis_theorem` (PhysLean)
- `Orientation.rotation` (Mathlib)
- `RigidBody.intermediate_axis_instability` (PhysLean)
- `RigidBody.parallel_axis_theorem` (PhysLean)
- `Orientation.rotation` (Mathlib)
- `rotation` (Mathlib)
- `Orientation.rightAngleRotation` (Mathlib)
- `Real.Angle.toReal` (Mathlib)
- `MvPolynomial.degrees` (Mathlib)
- `MvPolynomial.degrees_C` (Mathlib)
- `Real.Angle.toReal` (Mathlib)
- `MvPolynomial.degrees` (Mathlib)
- `MvPolynomial.degrees_C` (Mathlib)
- `IsStrictlyPositive` (Mathlib)
- `Nat.bitIndices` (Mathlib)
- `RootPairing.Base.IsPos.reflectionPerm` (Mathlib)

## Local abstractions introduced

- `PhyXMiniProblems.ProblemPhyXMini0011.AnswerChoice`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMiniProblems.ProblemPhyXMini0011.AxisOrientation`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMiniProblems.ProblemPhyXMini0011.DiamondRotationSetup`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMiniProblems.ProblemPhyXMini0011.FigurePoint`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMiniProblems.ProblemPhyXMini0011.HasFigureReadouts`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMiniProblems.ProblemPhyXMini0011.HasMaterialReadouts`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMiniProblems.ProblemPhyXMini0011.HasPhysicalAngleRanges`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMiniProblems.ProblemPhyXMini0011.HasPositiveRefractiveIndices`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMiniProblems.ProblemPhyXMini0011.HasRotatedRayGeometry`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMiniProblems.ProblemPhyXMini0011.IsAtFirstExitThresholdAtP`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMiniProblems.ProblemPhyXMini0011.IsClosestDisplayedAnswer`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMiniProblems.ProblemPhyXMini0011.OpticalMedium`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMiniProblems.ProblemPhyXMini0011.PlanarDirection`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMiniProblems.ProblemPhyXMini0011.RotationAxis`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMiniProblems.ProblemPhyXMini0011.SatisfiesSnellLawAtEntry`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMiniProblems.ProblemPhyXMini0011.SatisfiesSnellLawAtP`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.

## Grounding gaps

- No unresolved LeanExplore grounding gaps were recorded by this preflight.
