# Physics LeanExplore Grounding Log

- Target Lean file: `PhyXMiniProblems/problem_phyx_mini_0142.lean`
- Blueprint chapter: `blueprint/src/chapters/PhyXMiniProblems_problem_phyx_mini_0142.tex`
- Grounding status: complete
- Search backend: local
- Input fingerprint: sha256:12f2de95f55293763b4b8c338afb433aefb71a3b47d851f396ee8971aa57515c
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

### Query: `Optical Plane`
- `Complex.isOpen_slitPlane` | module `Mathlib.Analysis.Complex.Basic` | package Mathlib | **Openness of the Slit Plane.** The slit plane, defined as the set of complex numbers $z$ such that $\text{Re}(z) > 0$ or $\text{Im}(z) \neq 0$, is an open subset of the complex plane.
- `EuclideanGeometry.orthogonalProjection` | module `Mathlib.Geometry.Euclidean.Projection` | package Mathlib | The orthogonal projection of a point onto a nonempty affine subspace.
- `UpperHalfPlane` | module `Mathlib.Analysis.Complex.UpperHalfPlane.Basic` | package Mathlib | The open upper half plane, denoted as `ℍ` within the `UpperHalfPlane` namespace

### Query: `degrees In Radians`
- `MvPolynomial.degrees` | module `Mathlib.Algebra.MvPolynomial.Degrees` | package Mathlib | The maximal degrees of each variable in a multi-variable polynomial, expressed as a multiset. (For example, `degrees (x^2 * y + y^3)` would be `{x, x, y, y, y}`.)
- `Real.Angle.toReal` | module `Mathlib.Analysis.SpecialFunctions.Trigonometric.Angle` | package Mathlib | Convert a `Real.Angle` to a real number in the interval `Ioc (-π) π`.
- `MvPolynomial.degrees_rename` | module `Mathlib.Algebra.MvPolynomial.Degrees` | package Mathlib | **Degrees of a Renamed Multivariate Polynomial.** For any map $f : \sigma \to \tau$ and any multivariate polynomial $\phi$ with variables indexed by $\sigma$, the multiset of degrees of the renamed polynomial $\text{r...

### Query: `Mirror Label`
- `HahnSeries.orderTop` | module `Mathlib.RingTheory.HahnSeries.Basic` | package Mathlib | The orderTop of a Hahn series `x` is a minimal element of `WithTop Γ` where `x` has a nonzero coefficient if `x ≠ 0`, and is `⊤` when `x = 0`.
- `Polynomial.mirror` | module `Mathlib.Algebra.Polynomial.Mirror` | package Mathlib | mirror of a polynomial: reverses the coefficients while preserving `Polynomial.natDegree`
- `Polynomial.mirror_mirror` | module `Mathlib.Algebra.Polynomial.Mirror` | package Mathlib | **Involution of the Mirror Polynomial.** For any polynomial $p$, applying the mirror operation twice results in the original polynomial $p$.

### Query: `Ray Segment`
- `segment` | module `Mathlib.Analysis.Convex.Segment` | package Mathlib | Segments in a vector space. Denoted as `[x -[𝕜] y]` within the `Convex` namespace.
- `sameRay_of_mem_segment` | module `Mathlib.Analysis.Convex.Segment` | package Mathlib | **Same Ray Property for Points on a Segment.** If a point $x$ lies on the closed line segment connecting two points $y$ and $z$ in a module over a strictly ordered commutative ring, then the vectors $x - y$ and $z - x...
- `mem_segment_iff_sameRay` | module `Mathlib.Analysis.Convex.Segment` | package Mathlib | **Characterization of Segments via Same Ray.** A point $x$ belongs to the closed segment $[y, z]$ if and only if the vectors $x - y$ and $z - x$ lie on the same ray.

### Query: `Reflection Site`
- `RootPairing.reflection` | module `Mathlib.LinearAlgebra.RootSystem.Defs` | package Mathlib | The reflection associated to a root.
- `Submodule.reflection_reflection` | module `Mathlib.Analysis.InnerProductSpace.Projection.Reflection` | package Mathlib | Reflecting twice in the same subspace.
- `RootPairing.weylGroup.ofIdx` | module `Mathlib.LinearAlgebra.RootSystem.WeylGroup` | package Mathlib | The `ith` reflection as a term of the Weyl group.

### Query: `Figure Angle Label`
- `Real.Angle.sign` | module `Mathlib.Analysis.SpecialFunctions.Trigonometric.Angle` | package Mathlib | The sign of a `Real.Angle` is `0` if the angle is `0` or `π`, `1` if the angle is strictly between `0` and `π` and `-1` is the angle is strictly between `-π` and `0`. It is defined as the sign of the sine of the angle.
- `EuclideanGeometry.angle` | module `Mathlib.Geometry.Euclidean.Angle.Unoriented.Affine` | package Mathlib | The undirected angle at `p₂` between the line segments to `p₁` and `p₃`. If either of those points equals `p₂`, this is π/2. Use `open scoped EuclideanGeometry` to access the `∠ p₁ p₂ p₃` notation.
- `EuclideanGeometry.angle_lt_pi_div_three_of_le_of_le_of_ne` | module `Mathlib.Geometry.Euclidean.Triangle` | package Mathlib | The least angle of a possibly degenerate triangle is less than `π / 3`, unless all angles are equal.

### Query: `Plane Mirror`
- `Polynomial.mirror_smul` | module `Mathlib.Algebra.Polynomial.Mirror` | package Mathlib | **Scalar Multiplication of Mirror Polynomials.** For any scalar $a$ and polynomial $p$ over a domain $R$, the mirror of the scalar product $a \cdot p$ is equal to the scalar product of $a$ and the mirror of $p$.
- `UpperHalfPlane` | module `Mathlib.Analysis.Complex.UpperHalfPlane.Basic` | package Mathlib | The open upper half plane, denoted as `ℍ` within the `UpperHalfPlane` namespace
- `Polynomial.mirror` | module `Mathlib.Algebra.Polynomial.Mirror` | package Mathlib | mirror of a polynomial: reverses the coefficients while preserving `Polynomial.natDegree`

### Query: `Directed Light Ray`
- `SameRay` | module `Mathlib.LinearAlgebra.Ray` | package Mathlib | Two vectors are in the same ray if either one of them is zero or some positive multiples of them are equal (in the typical case over a field, this means one of them is a nonnegative multiple of the other).
- `LightDiagram'` | module `Mathlib.Topology.Category.LightProfinite.Basic` | package Mathlib | This is an auxiliary definition used to show that `LightDiagram` is essentially small. Note that below we put a category instance on this structure which is completely different from the category instance on `ℕᵒᵖ ⥤ Fi...
- `Lorentz.Vector.CausalCharacter.lightLike` | module `Physlib.Relativity.Tensors.RealTensor.Vector.Causality.Basic` | package PhysLean | **Lightlike Causal Character.** A classification of a Lorentz vector indicating that it is lightlike.

## Grounded Mathlib/PhysLean names

- `EuclideanSpace` (Mathlib)
- `Space.fderiv_space_components` (PhysLean)
- `Lorentz.ContrMod.toSpace` (PhysLean)
- `Path.target` (Mathlib)
- `semiformal_result` (PhysLean)
- `stereographic_target` (Mathlib)
- `Complex.isOpen_slitPlane` (Mathlib)
- `EuclideanGeometry.orthogonalProjection` (Mathlib)
- `UpperHalfPlane` (Mathlib)
- `MvPolynomial.degrees` (Mathlib)
- `Real.Angle.toReal` (Mathlib)
- `MvPolynomial.degrees_rename` (Mathlib)
- `HahnSeries.orderTop` (Mathlib)
- `Polynomial.mirror` (Mathlib)
- `Polynomial.mirror_mirror` (Mathlib)
- `segment` (Mathlib)
- `sameRay_of_mem_segment` (Mathlib)
- `mem_segment_iff_sameRay` (Mathlib)
- `RootPairing.reflection` (Mathlib)
- `Submodule.reflection_reflection` (Mathlib)
- `RootPairing.weylGroup.ofIdx` (Mathlib)
- `Real.Angle.sign` (Mathlib)
- `EuclideanGeometry.angle` (Mathlib)
- `EuclideanGeometry.angle_lt_pi_div_three_of_le_of_le_of_ne` (Mathlib)
- `Polynomial.mirror_smul` (Mathlib)
- `UpperHalfPlane` (Mathlib)
- `Polynomial.mirror` (Mathlib)
- `SameRay` (Mathlib)
- `LightDiagram'` (Mathlib)
- `Lorentz.Vector.CausalCharacter.lightLike` (PhysLean)

## Local abstractions introduced

- `PhyXMiniProblems.ProblemPhyXMini0142.AnswerChoice`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMiniProblems.ProblemPhyXMini0142.DirectedLightRay`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMiniProblems.ProblemPhyXMini0142.FigureAngleLabel`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMiniProblems.ProblemPhyXMini0142.HasPhysicalGeometry`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMiniProblems.ProblemPhyXMini0142.IsFlatPlaneMirror`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMiniProblems.ProblemPhyXMini0142.IsSpecularReflectionAt`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMiniProblems.ProblemPhyXMini0142.MatchesSuppliedFigure`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMiniProblems.ProblemPhyXMini0142.MirrorLabel`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMiniProblems.ProblemPhyXMini0142.OpticalPlane`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMiniProblems.ProblemPhyXMini0142.PerpendicularMirrorExperiment`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMiniProblems.ProblemPhyXMini0142.PlaneMirror`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMiniProblems.ProblemPhyXMini0142.RaySegment`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMiniProblems.ProblemPhyXMini0142.ReflectionSite`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMiniProblems.ProblemPhyXMini0142.SatisfiesPerpendicularMirrorGeometry`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMiniProblems.ProblemPhyXMini0142.SatisfiesRayPathGeometry`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMiniProblems.ProblemPhyXMini0142.SatisfiesSpecularReflectionLaws`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.

## Grounding gaps

- No unresolved LeanExplore grounding gaps were recorded by this preflight.
