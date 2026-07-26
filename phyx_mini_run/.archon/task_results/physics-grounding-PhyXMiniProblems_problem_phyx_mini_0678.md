# Physics LeanExplore Grounding Log

- Target Lean file: `PhyXMiniProblems/problem_phyx_mini_0678.lean`
- Blueprint chapter: `blueprint/src/chapters/PhyXMiniProblems_problem_phyx_mini_0678.tex`
- Grounding status: complete
- Search backend: local
- Input fingerprint: sha256:23be54ad5ef349b8386c4e7fcaa6e363cbcbce31139629a12a6706b92fe33c56
- Packages searched: Mathlib, Physlib

## LeanExplore queries/candidates actually used

### Query: `EuclideanSpace vector components`
- `EuclideanSpace` | module `Mathlib.Analysis.InnerProductSpace.PiL2` | package Mathlib | The standard real/complex Euclidean space, functions on a finite type. For an `n`-dimensional space use `EuclideanSpace 𝕜 (Fin n)`. For the case when `n = Fin _`, there is `!₂[x, y, ...]` notation for building element...
- `Space.fderiv_space_components` | module `Physlib.SpaceAndTime.Space.Module` | package PhysLean | **Components of the Fréchet Derivative of a Vector-Valued Function.** For a differentiable function $f$ mapping from a normed space $M$ to the space of $d$-dimensional vectors $\mathbb{R}^d$, the $\mu$-th component of...
- `Lorentz.ContrMod.toSpace` | module `Physlib.Relativity.Tensors.RealTensor.Vector.Pre.Modules` | package PhysLean | The underlying space part of a `ContrMod` formed by removing the first element. A better name for this might be `tail`.

### Query: `Physics formalization target`
- `Path.target` | module `Mathlib.Topology.Path` | package Mathlib | **Target of a Path.** For a path $\gamma$ from $x$ to $y$ in a topological space, the value of the path at the endpoint of the unit interval, $\gamma(1)$, is equal to $y$.
- `semiformal_result` | module `Physlib.Meta.Informal.SemiFormal` | package PhysLean | A semiformal result is either a - definition in which the type is given but not the definition. - proof in which the proposition is given but not the proof. Semiformal results cannot be used in further code. They are...
- `stereographic_target` | module `Mathlib.Geometry.Manifold.Instances.Sphere` | package Mathlib | **Target of the Stereographic Projection.** For any unit vector $v$ in an inner product space, the target of the stereographic projection associated with $v$ is the entire codomain (the orthogonal complement of the su...

### Query: `Diagram Plane`
- `Complex.slitPlane` | module `Mathlib.Analysis.Complex.Basic` | package Mathlib | The *slit plane* is the complex plane with the closed negative real axis removed.
- `LightDiagram'` | module `Mathlib.Topology.Category.LightProfinite.Basic` | package Mathlib | This is an auxiliary definition used to show that `LightDiagram` is essentially small. Note that below we put a category instance on this structure which is completely different from the category instance on `ℕᵒᵖ ⥤ Fi...
- `Sym2.IsDiag` | module `Mathlib.Data.Sym.Sym2` | package Mathlib | A predicate for testing whether an element of `Sym2 α` is on the diagonal.

### Query: `Planar Displacement Quantity`
- `RigidBodyMotion.displacement` | module `Physlib.ClassicalMechanics.RigidBody.Motion` | package PhysLean | The rigid displacement carrying the body frame into the inertial frame at time `t`: the rotation `orientation t` about the centre of mass, followed by the translation placing the centre of mass at `comTrajectory t`.
- `HahnSeries.orderTop` | module `Mathlib.RingTheory.HahnSeries.Basic` | package Mathlib | The orderTop of a Hahn series `x` is a minimal element of `WithTop Γ` where `x` has a nonzero coefficient if `x ≠ 0`, and is `⊤` when `x = 0`.
- `signedDist_vsub_self_rev` | module `Mathlib.Geometry.Euclidean.SignedDist` | package Mathlib | **Signed Distance with Reversed Displacement.** The signed distance from a point $p$ to a point $q$ relative to the displacement vector $p - q$ is equal to the negative of the distance between $p$ and $q$.

### Query: `Scalar Length Quantity`
- `Dimensionful.smul_apply` | module `Physlib.Units.Basic` | package PhysLean | **Scalar Multiplication of Dimensionful Quantities.** For any nonnegative real number $a$, dimensionful quantity $f$, and choice of units $u$, the value of the scalar product $a \cdot f$ evaluated at $u$ is equal to t...
- `List.Vector.length` | module `Mathlib.Data.Vector.Defs` | package Mathlib | The length of a vector.
- `LengthUnit` | module `Physlib.SpaceAndTime.Space.LengthUnit` | package PhysLean | The choices of translationally-invariant metrics on the space-manifold. Such a choice corresponds to a choice of units for length.

### Query: `displacement Vector In Meters`
- `LengthUnit.meters` | module `Physlib.SpaceAndTime.Space.LengthUnit` | package PhysLean | The definition of a length unit of meters.
- `AffineMap.lineMap_vsub_left` | module `Mathlib.LinearAlgebra.AffineSpace.AffineMap` | package Mathlib | **Vector Displacement from the Start of an Affine Line Map.** For any two points $p_0, p_1$ in an affine space and a scalar $c$, the displacement vector from $p_0$ to the point $c$ along the line through $p_0$ and $p_...
- `RigidBodyMotion.displacement` | module `Physlib.ClassicalMechanics.RigidBody.Motion` | package PhysLean | The rigid displacement carrying the body frame into the inertial frame at time `t`: the rotation `orientation t` about the centre of mass, followed by the translation placing the centre of mass at `comTrajectory t`.

### Query: `length In Meters`
- `LengthUnit.meters` | module `Physlib.SpaceAndTime.Space.LengthUnit` | package PhysLean | The definition of a length unit of meters.
- `LengthUnit.links` | module `Physlib.SpaceAndTime.Space.LengthUnit` | package PhysLean | The length unit of link (0.201168 meters).
- `LengthUnit.rods` | module `Physlib.SpaceAndTime.Space.LengthUnit` | package PhysLean | The length unit of a rod (5.0292 meters)

### Query: `displacement Magnitude In Meters`
- `RigidBodyMotion.displacement` | module `Physlib.ClassicalMechanics.RigidBody.Motion` | package PhysLean | The rigid displacement carrying the body frame into the inertial frame at time `t`: the rotation `orientation t` about the centre of mass, followed by the translation placing the centre of mass at `comTrajectory t`.
- `JoinedIn` | module `Mathlib.Topology.Connected.PathConnected` | package Mathlib | The relation "being joined by a path in `F`". Not quite an equivalence relation since it's not reflexive for points that do not belong to `F`.
- `LengthUnit.meters` | module `Physlib.SpaceAndTime.Space.LengthUnit` | package PhysLean | The definition of a length unit of meters.

### Query: `degrees To Radians`
- `Real.Angle.toReal` | module `Mathlib.Analysis.SpecialFunctions.Trigonometric.Angle` | package Mathlib | Convert a `Real.Angle` to a real number in the interval `Ioc (-π) π`.
- `MvPolynomial.degrees` | module `Mathlib.Algebra.MvPolynomial.Degrees` | package Mathlib | The maximal degrees of each variable in a multi-variable polynomial, expressed as a multiset. (For example, `degrees (x^2 * y + y^3)` would be `{x, x, y, y, y}`.)
- `MvPolynomial.degrees_C` | module `Mathlib.Algebra.MvPolynomial.Degrees` | package Mathlib | **Degrees of a Constant Multivariate Polynomial.** For any element $a$ in a commutative semiring $R$, the multiset of degrees of the constant multivariate polynomial $C(a)$ is empty.

### Query: `unit Vector At Angle Degrees`
- `MvPolynomial.degrees` | module `Mathlib.Algebra.MvPolynomial.Degrees` | package Mathlib | The maximal degrees of each variable in a multi-variable polynomial, expressed as a multiset. (For example, `degrees (x^2 * y + y^3)` would be `{x, x, y, y, y}`.)
- `Orientation.oangle` | module `Mathlib.Geometry.Euclidean.Angle.Oriented.Basic` | package Mathlib | The oriented angle from `x` to `y`, modulo `2 * π`. If either vector is 0, this is 0. See `InnerProductGeometry.angle` for the corresponding unoriented angle definition.
- `Orientation.left_ne_zero_of_oangle_eq_pi` | module `Mathlib.Geometry.Euclidean.Angle.Oriented.Basic` | package Mathlib | If the angle between two vectors is `π`, the first vector is nonzero.

## Grounded Mathlib/PhysLean names

- `EuclideanSpace` (Mathlib)
- `Space.fderiv_space_components` (PhysLean)
- `Lorentz.ContrMod.toSpace` (PhysLean)
- `Path.target` (Mathlib)
- `semiformal_result` (PhysLean)
- `stereographic_target` (Mathlib)
- `Complex.slitPlane` (Mathlib)
- `LightDiagram'` (Mathlib)
- `Sym2.IsDiag` (Mathlib)
- `RigidBodyMotion.displacement` (PhysLean)
- `HahnSeries.orderTop` (Mathlib)
- `signedDist_vsub_self_rev` (Mathlib)
- `Dimensionful.smul_apply` (PhysLean)
- `List.Vector.length` (Mathlib)
- `LengthUnit` (PhysLean)
- `LengthUnit.meters` (PhysLean)
- `AffineMap.lineMap_vsub_left` (Mathlib)
- `RigidBodyMotion.displacement` (PhysLean)
- `LengthUnit.meters` (PhysLean)
- `LengthUnit.links` (PhysLean)
- `LengthUnit.rods` (PhysLean)
- `RigidBodyMotion.displacement` (PhysLean)
- `JoinedIn` (Mathlib)
- `LengthUnit.meters` (PhysLean)
- `Real.Angle.toReal` (Mathlib)
- `MvPolynomial.degrees` (Mathlib)
- `MvPolynomial.degrees_C` (Mathlib)
- `MvPolynomial.degrees` (Mathlib)
- `Orientation.oangle` (Mathlib)
- `Orientation.left_ne_zero_of_oangle_eq_pi` (Mathlib)

## Local abstractions introduced

- `PhyXMiniProblems.ProblemPhyXMini0678.AnswerChoice`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMiniProblems.ProblemPhyXMini0678.DiagramPlane`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMiniProblems.ProblemPhyXMini0678.FigureDirection`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMiniProblems.ProblemPhyXMini0678.FigureFeature`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMiniProblems.ProblemPhyXMini0678.MatchesDisplayedAnswerToThreeDecimalPlaces`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMiniProblems.ProblemPhyXMini0678.MatchesProblemAndPrimaryFigure`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMiniProblems.ProblemPhyXMini0678.ObeysPerpendicularProjectionLaw`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMiniProblems.ProblemPhyXMini0678.PlanarDisplacementQuantity`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMiniProblems.ProblemPhyXMini0678.ScalarLengthQuantity`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMiniProblems.ProblemPhyXMini0678.SkiSlopeDisplacementSetup`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMiniProblems.ProblemPhyXMini0678.SkiSlopeFigure`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.

## Grounding gaps

- No unresolved LeanExplore grounding gaps were recorded by this preflight.
