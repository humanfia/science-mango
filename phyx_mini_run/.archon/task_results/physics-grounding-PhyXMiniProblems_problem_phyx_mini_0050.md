# Physics LeanExplore Grounding Log

- Target Lean file: `PhyXMiniProblems/problem_phyx_mini_0050.lean`
- Blueprint chapter: `blueprint/src/chapters/PhyXMiniProblems_problem_phyx_mini_0050.tex`
- Grounding status: complete
- Search backend: local
- Input fingerprint: sha256:7bba985185e7560c8aac7fd1b8b24b32ec13b30a62c3702f3cfcc0956b3a3e2b
- Packages searched: Mathlib, Physlib

## LeanExplore queries/candidates actually used

### Query: `Physics formalization target`
- `Path.target` | module `Mathlib.Topology.Path` | package Mathlib | **Target of a Path.** For a path $\gamma$ from $x$ to $y$ in a topological space, the value of the path at the endpoint of the unit interval, $\gamma(1)$, is equal to $y$.
- `semiformal_result` | module `Physlib.Meta.Informal.SemiFormal` | package PhysLean | A semiformal result is either a - definition in which the type is given but not the definition. - proof in which the proposition is given but not the proof. Semiformal results cannot be used in further code. They are...
- `stereographic_target` | module `Mathlib.Geometry.Manifold.Instances.Sphere` | package Mathlib | **Target of the Stereographic Projection.** For any unit vector $v$ in an inner product space, the target of the stereographic projection associated with $v$ is the entire codomain (the orthogonal complement of the su...

### Query: `Dimensionless Quantity`
- `DimSpeed` | module `Physlib.Units.WithDim.Speed` | package PhysLean | The type of speeds in the absence of a choice of unit.
- `UnitChoices.dimScale` | module `Physlib.Units.Basic` | package PhysLean | Given two choices of units `u1` and `u2` and a dimension `d`, the element of `ℝ≥0` corresponding to the scaling (by definition) of a quantity of dimension `d` when changing from units `u1` to `u2`.
- `DimArea` | module `Physlib.Units.WithDim.Area` | package PhysLean | The type of areas in the absence of a choice of unit.

### Query: `dimensionless Readout`
- `DimSpeed` | module `Physlib.Units.WithDim.Speed` | package PhysLean | The type of speeds in the absence of a choice of unit.
- `UnitChoices.dimScale` | module `Physlib.Units.Basic` | package PhysLean | Given two choices of units `u1` and `u2` and a dimension `d`, the element of `ℝ≥0` corresponding to the scaling (by definition) of a quantity of dimension `d` when changing from units `u1` to `u2`.
- `DimArea` | module `Physlib.Units.WithDim.Area` | package PhysLean | The type of areas in the absence of a choice of unit.

### Query: `radians Of Degrees`
- `MvPolynomial.degrees` | module `Mathlib.Algebra.MvPolynomial.Degrees` | package Mathlib | The maximal degrees of each variable in a multi-variable polynomial, expressed as a multiset. (For example, `degrees (x^2 * y + y^3)` would be `{x, x, y, y, y}`.)
- `Real.pi` | module `Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic` | package Mathlib | The number π = 3.14159265... Defined here using choice as twice a zero of cos in [1,2], from which one can derive all its properties. For explicit bounds on π, see `Mathlib/Analysis/Real/Pi/Bounds.lean`. Denoted `π`,...
- `Real.Angle.toReal` | module `Mathlib.Analysis.SpecialFunctions.Trigonometric.Angle` | package Mathlib | Convert a `Real.Angle` to a real number in the interval `Ioc (-π) π`.

### Query: `Optical Region`
- `Set.Ioi` | module `Mathlib.Order.Interval.Set.Defs` | package Mathlib | `Ioi a` is the left-open right-infinite interval $(a, ∞)$.
- `regionBetween` | module `Mathlib.MeasureTheory.Measure.Lebesgue.Basic` | package Mathlib | The region between two real-valued functions on an arbitrary set.
- `regionBetween_subset` | module `Mathlib.MeasureTheory.Measure.Lebesgue.Basic` | package Mathlib | **Subset Property of the Region Between Two Functions.** For any two real-valued functions $f$ and $g$ defined on a set $\alpha$ and any subset $s \subseteq \alpha$, the region between $f$ and $g$ over $s$ is a subset...

### Query: `Prism Vertex`
- `VertexOperator` | module `Mathlib.Algebra.Vertex.VertexOperator` | package Mathlib | A vertex operator over a commutative ring `R` is an `R`-linear map from an `R`-module `V` to Laurent series with coefficients in `V`. We write this as a specialization of the heterogeneous case.
- `HahnSeries.orderTop` | module `Mathlib.RingTheory.HahnSeries.Basic` | package Mathlib | The orderTop of a Hahn series `x` is a minimal element of `WithTop Γ` where `x` has a nonzero coefficient if `x ≠ 0`, and is `⊤` when `x = 0`.
- `PrincipalSeg.cocone_pt` | module `Mathlib.CategoryTheory.Limits.Shapes.Preorder.PrincipalSeg` | package Mathlib | **Vertex of the Cocone for a Principal Segment.** Given a principal segment $f$ from a partially ordered set $\alpha$ to a partially ordered set $\beta$ and a functor $F$ from $\beta$ (viewed as a category) to a categ...

### Query: `Prism Face`
- `Affine.Simplex.faceOpposite` | module `Mathlib.LinearAlgebra.AffineSpace.Simplex.Basic` | package Mathlib | The face of a simplex with all but one point.
- `BoxIntegral.Box.face` | module `Mathlib.Analysis.BoxIntegral.Box.Basic` | package Mathlib | Face of a box in `ℝⁿ⁺¹ = Fin (n + 1) → ℝ`: the box in `ℝⁿ = Fin n → ℝ` with corners at `I.lower ∘ Fin.succAbove i` and `I.upper ∘ Fin.succAbove i`.
- `CategoryTheory.ComposableArrows.precomp_δ₀` | module `Mathlib.CategoryTheory.ComposableArrows.Basic` | package Mathlib | **Face Map of a Precomposed Sequence.** For any object $X$ and any morphism $f : X \to F(0)$ from $X$ to the leftmost object of a sequence of $n$ composable arrows $F$, the $0$-th face map $\delta_0$ of the sequence f...

### Query: `Ray Segment`
- `segment` | module `Mathlib.Analysis.Convex.Segment` | package Mathlib | Segments in a vector space. Denoted as `[x -[𝕜] y]` within the `Convex` namespace.
- `sameRay_of_mem_segment` | module `Mathlib.Analysis.Convex.Segment` | package Mathlib | **Same Ray Property for Points on a Segment.** If a point $x$ lies on the closed line segment connecting two points $y$ and $z$ in a module over a strictly ordered commutative ring, then the vectors $x - y$ and $z - x...
- `mem_segment_iff_sameRay` | module `Mathlib.Analysis.Convex.Segment` | package Mathlib | **Characterization of Segments via Same Ray.** A point $x$ belongs to the closed segment $[y, z]$ if and only if the vectors $x - y$ and $z - x$ lie on the same ray.

### Query: `Prism Laser Setup`
- `HahnSeries.orderTop` | module `Mathlib.RingTheory.HahnSeries.Basic` | package Mathlib | The orderTop of a Hahn series `x` is a minimal element of `WithTop Γ` where `x` has a nonzero coefficient if `x ≠ 0`, and is `⊤` when `x = 0`.
- `Mathlib.Notation3.setupLCtx` | module `Mathlib.Util.Notation3` | package Mathlib | Adds all the names in `boundNames` to the local context with types that are fresh metavariables. This is used for example when initializing `p` in `(scoped p => ...)` when elaborating `...`.
- `HahnSeries.single` | module `Mathlib.RingTheory.HahnSeries.Basic` | package Mathlib | `single a r` is the Hahn series which has coefficient `r` at `a` and zero otherwise.

### Query: `angle From Propagation Normal`
- `InnerProductGeometry.angle_normalize_left` | module `Mathlib.Geometry.Euclidean.Angle.Unoriented.Basic` | package Mathlib | The angle between a normalized vector and another vector is equal to the angle between the original vectors.
- `Orientation.oangle` | module `Mathlib.Geometry.Euclidean.Angle.Oriented.Basic` | package Mathlib | The oriented angle from `x` to `y`, modulo `2 * π`. If either vector is 0, this is 0. See `InnerProductGeometry.angle` for the corresponding unoriented angle definition.
- `Real.Angle` | module `Mathlib.Analysis.SpecialFunctions.Trigonometric.Angle` | package Mathlib | The type of angles

## Grounded Mathlib/PhysLean names

- `Path.target` (Mathlib)
- `semiformal_result` (PhysLean)
- `stereographic_target` (Mathlib)
- `DimSpeed` (PhysLean)
- `UnitChoices.dimScale` (PhysLean)
- `DimArea` (PhysLean)
- `DimSpeed` (PhysLean)
- `UnitChoices.dimScale` (PhysLean)
- `DimArea` (PhysLean)
- `MvPolynomial.degrees` (Mathlib)
- `Real.pi` (Mathlib)
- `Real.Angle.toReal` (Mathlib)
- `Set.Ioi` (Mathlib)
- `regionBetween` (Mathlib)
- `regionBetween_subset` (Mathlib)
- `VertexOperator` (Mathlib)
- `HahnSeries.orderTop` (Mathlib)
- `PrincipalSeg.cocone_pt` (Mathlib)
- `Affine.Simplex.faceOpposite` (Mathlib)
- `BoxIntegral.Box.face` (Mathlib)
- `CategoryTheory.ComposableArrows.precomp_δ₀` (Mathlib)
- `segment` (Mathlib)
- `sameRay_of_mem_segment` (Mathlib)
- `mem_segment_iff_sameRay` (Mathlib)
- `HahnSeries.orderTop` (Mathlib)
- `Mathlib.Notation3.setupLCtx` (Mathlib)
- `HahnSeries.single` (Mathlib)
- `InnerProductGeometry.angle_normalize_left` (Mathlib)
- `Orientation.oangle` (Mathlib)
- `Real.Angle` (Mathlib)

## Local abstractions introduced

- `PhyXMiniProblems.ProblemPhyXMini0050.AnswerChoice`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMiniProblems.ProblemPhyXMini0050.DimensionlessQuantity`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMiniProblems.ProblemPhyXMini0050.HasDepictedPrismGeometry`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMiniProblems.ProblemPhyXMini0050.HasDepictedRayPath`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMiniProblems.ProblemPhyXMini0050.HasPhysicalRefractiveIndices`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMiniProblems.ProblemPhyXMini0050.MatchesAnswerToNearestHundredth`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMiniProblems.ProblemPhyXMini0050.MatchesFigureReadouts`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMiniProblems.ProblemPhyXMini0050.OpticalRegion`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMiniProblems.ProblemPhyXMini0050.PrismFace`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMiniProblems.ProblemPhyXMini0050.PrismLaserSetup`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMiniProblems.ProblemPhyXMini0050.PrismVertex`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMiniProblems.ProblemPhyXMini0050.RaySegment`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMiniProblems.ProblemPhyXMini0050.SatisfiesSnellLawAtPrismFaces`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.

## Grounding gaps

- No unresolved LeanExplore grounding gaps were recorded by this preflight.
