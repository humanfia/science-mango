# Physics LeanExplore Grounding Log

- Target Lean file: `PhyXMiniProblems/problem_phyx_mini_0102.lean`
- Blueprint chapter: `blueprint/src/chapters/PhyXMiniProblems_problem_phyx_mini_0102.tex`
- Grounding status: complete
- Search backend: local
- Input fingerprint: sha256:d6365641b71ae814c224d62c1a41b56e523ddea5736263a49c28963c116b7310
- Packages searched: Mathlib, Physlib

## LeanExplore queries/candidates actually used

### Query: `Physics formalization target`
- `Path.target` | module `Mathlib.Topology.Path` | package Mathlib | **Target of a Path.** For a path $\gamma$ from $x$ to $y$ in a topological space, the value of the path at the endpoint of the unit interval, $\gamma(1)$, is equal to $y$.
- `semiformal_result` | module `Physlib.Meta.Informal.SemiFormal` | package PhysLean | A semiformal result is either a - definition in which the type is given but not the definition. - proof in which the proposition is given but not the proof. Semiformal results cannot be used in further code. They are...
- `stereographic_target` | module `Mathlib.Geometry.Manifold.Instances.Sphere` | package Mathlib | **Target of the Stereographic Projection.** For any unit vector $v$ in an inner product space, the target of the stereographic projection associated with $v$ is the entire codomain (the orthogonal complement of the su...

### Query: `Dim Length`
- `Order.LTSeries.length_le_krullDim` | module `Mathlib.Order.KrullDimension` | package Mathlib | **Length of a Strictly Increasing Sequence and Krull Dimension.** For any strictly increasing sequence in a preorder, its length is less than or equal to the Krull dimension of that preorder.
- `Dimension.L𝓭_mass` | module `Physlib.Units.Dimension` | package PhysLean | **Mass component of the length dimension.** The mass dimension component of the length dimension $L_d$ is equal to $0$.
- `Order.krullDim_eq_iSup_length` | module `Mathlib.Order.KrullDimension` | package Mathlib | A definition of krullDim for nonempty `α` that avoids `WithBot`

### Query: `centimeter Unit Choices`
- `UnitChoices` | module `Physlib.Units.Basic` | package PhysLean | The choice of units.
- `IsUnit` | module `Mathlib.Algebra.Group.Units.Defs` | package Mathlib | An element `a : M` of a `Monoid` is a unit if it has a two-sided inverse. The actual definition says that `a` is equal to some `u : Mˣ`, where `Mˣ` is a bundled version of `IsUnit`.
- `LengthUnit.centimeters` | module `Physlib.SpaceAndTime.Space.LengthUnit` | package PhysLean | The length unit of centimeters (10⁻² of a meter).

### Query: `value In Centimeters`
- `LengthUnit.centimeters` | module `Physlib.SpaceAndTime.Space.LengthUnit` | package PhysLean | The length unit of centimeters (10⁻² of a meter).
- `JoinedIn` | module `Mathlib.Topology.Connected.PathConnected` | package Mathlib | The relation "being joined by a path in `F`". Not quite an equivalence relation since it's not reflexive for points that do not belong to `F`.
- `AbsoluteValue` | module `Mathlib.Algebra.Order.AbsoluteValue.Basic` | package Mathlib | `AbsoluteValue R S` is the type of absolute values on `R` mapping to `S`: the maps that preserve `*`, are nonnegative, positive definite and satisfy the triangle inequality.

### Query: `degrees To Radians`
- `Real.Angle.toReal` | module `Mathlib.Analysis.SpecialFunctions.Trigonometric.Angle` | package Mathlib | Convert a `Real.Angle` to a real number in the interval `Ioc (-π) π`.
- `MvPolynomial.degrees` | module `Mathlib.Algebra.MvPolynomial.Degrees` | package Mathlib | The maximal degrees of each variable in a multi-variable polynomial, expressed as a multiset. (For example, `degrees (x^2 * y + y^3)` would be `{x, x, y, y, y}`.)
- `MvPolynomial.degrees_C` | module `Mathlib.Algebra.MvPolynomial.Degrees` | package Mathlib | **Degrees of a Constant Multivariate Polynomial.** For any element $a$ in a commutative semiring $R$, the multiset of degrees of the constant multivariate polynomial $C(a)$ is empty.

### Query: `Diagram Plane`
- `Complex.slitPlane` | module `Mathlib.Analysis.Complex.Basic` | package Mathlib | The *slit plane* is the complex plane with the closed negative real axis removed.
- `LightDiagram'` | module `Mathlib.Topology.Category.LightProfinite.Basic` | package Mathlib | This is an auxiliary definition used to show that `LightDiagram` is essentially small. Note that below we put a category instance on this structure which is completely different from the category instance on `ℕᵒᵖ ⥤ Fi...
- `Sym2.IsDiag` | module `Mathlib.Data.Sym.Sym2` | package Mathlib | A predicate for testing whether an element of `Sym2 α` is on the diagonal.

### Query: `Ray Direction`
- `SameRay` | module `Mathlib.LinearAlgebra.Ray` | package Mathlib | Two vectors are in the same ray if either one of them is zero or some positive multiples of them are equal (in the typical case over a field, this means one of them is a nonnegative multiple of the other).
- `Space.Direction` | module `Physlib.SpaceAndTime.Space.Module` | package PhysLean | Notion of direction where `unit` returns a unit vector in the direction specified.
- `AffineSubspace.direction` | module `Mathlib.LinearAlgebra.AffineSpace.AffineSubspace.Defs` | package Mathlib | The direction of an affine subspace is the submodule spanned by the pairwise differences of points. (Except in the case of an empty affine subspace, where the direction is the zero submodule, every vector in the direc...

### Query: `Optical Region`
- `Set.Ioi` | module `Mathlib.Order.Interval.Set.Defs` | package Mathlib | `Ioi a` is the left-open right-infinite interval $(a, ∞)$.
- `regionBetween` | module `Mathlib.MeasureTheory.Measure.Lebesgue.Basic` | package Mathlib | The region between two real-valued functions on an arbitrary set.
- `regionBetween_subset` | module `Mathlib.MeasureTheory.Measure.Lebesgue.Basic` | package Mathlib | **Subset Property of the Region Between Two Functions.** For any two real-valued functions $f$ and $g$ defined on a set $\alpha$ and any subset $s \subseteq \alpha$, the region between $f$ and $g$ over $s$ is a subset...

### Query: `Plate Face`
- `BoxIntegral.Box.face` | module `Mathlib.Analysis.BoxIntegral.Box.Basic` | package Mathlib | Face of a box in `ℝⁿ⁺¹ = Fin (n + 1) → ℝ`: the box in `ℝⁿ = Fin n → ℝ` with corners at `I.lower ∘ Fin.succAbove i` and `I.upper ∘ Fin.succAbove i`.
- `CategoryTheory.SimplicialObject.δ` | module `Mathlib.AlgebraicTopology.SimplicialObject.Basic` | package Mathlib | Face maps for a simplicial object.
- `PointedCone.IsFaceOf.isFaceOf_iff_le` | module `Mathlib.Geometry.Convex.Cone.Face.Basic` | package Mathlib | A face of a cone is a face of another if and only if they are contained in each other.

### Query: `Ray Segment`
- `segment` | module `Mathlib.Analysis.Convex.Segment` | package Mathlib | Segments in a vector space. Denoted as `[x -[𝕜] y]` within the `Convex` namespace.
- `sameRay_of_mem_segment` | module `Mathlib.Analysis.Convex.Segment` | package Mathlib | **Same Ray Property for Points on a Segment.** If a point $x$ lies on the closed line segment connecting two points $y$ and $z$ in a module over a strictly ordered commutative ring, then the vectors $x - y$ and $z - x...
- `mem_segment_iff_sameRay` | module `Mathlib.Analysis.Convex.Segment` | package Mathlib | **Characterization of Segments via Same Ray.** A point $x$ belongs to the closed segment $[y, z]$ if and only if the vectors $x - y$ and $z - x$ lie on the same ray.

## Grounded Mathlib/PhysLean names

- `Path.target` (Mathlib)
- `semiformal_result` (PhysLean)
- `stereographic_target` (Mathlib)
- `Order.LTSeries.length_le_krullDim` (Mathlib)
- `Dimension.L𝓭_mass` (PhysLean)
- `Order.krullDim_eq_iSup_length` (Mathlib)
- `UnitChoices` (PhysLean)
- `IsUnit` (Mathlib)
- `LengthUnit.centimeters` (PhysLean)
- `LengthUnit.centimeters` (PhysLean)
- `JoinedIn` (Mathlib)
- `AbsoluteValue` (Mathlib)
- `Real.Angle.toReal` (Mathlib)
- `MvPolynomial.degrees` (Mathlib)
- `MvPolynomial.degrees_C` (Mathlib)
- `Complex.slitPlane` (Mathlib)
- `LightDiagram'` (Mathlib)
- `Sym2.IsDiag` (Mathlib)
- `SameRay` (Mathlib)
- `Space.Direction` (PhysLean)
- `AffineSubspace.direction` (Mathlib)
- `Set.Ioi` (Mathlib)
- `regionBetween` (Mathlib)
- `regionBetween_subset` (Mathlib)
- `BoxIntegral.Box.face` (Mathlib)
- `CategoryTheory.SimplicialObject.δ` (Mathlib)
- `PointedCone.IsFaceOf.isFaceOf_iff_le` (Mathlib)
- `segment` (Mathlib)
- `sameRay_of_mem_segment` (Mathlib)
- `mem_segment_iff_sameRay` (Mathlib)

## Local abstractions introduced

- `PhyXMiniProblems.ProblemPhyXMini0102.AnswerChoice`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMiniProblems.ProblemPhyXMini0102.DiagramPlane`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMiniProblems.ProblemPhyXMini0102.DimLength`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMiniProblems.ProblemPhyXMini0102.FigurePoint`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMiniProblems.ProblemPhyXMini0102.HasPhysicalOpticalParameters`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMiniProblems.ProblemPhyXMini0102.IsPhysicalAcuteAngle`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMiniProblems.ProblemPhyXMini0102.MatchesAnswerToNearestHundredthCentimeter`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMiniProblems.ProblemPhyXMini0102.MatchesProblemData`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMiniProblems.ProblemPhyXMini0102.ObeysSnellsLaw`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMiniProblems.ProblemPhyXMini0102.OpticalRegion`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMiniProblems.ProblemPhyXMini0102.ParallelGlassPlateSetup`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMiniProblems.ProblemPhyXMini0102.PlateFace`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMiniProblems.ProblemPhyXMini0102.RayDirection`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMiniProblems.ProblemPhyXMini0102.RaySegment`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMiniProblems.ProblemPhyXMini0102.SatisfiesParallelPlateGeometry`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMiniProblems.ProblemPhyXMini0102.SatisfiesSnellsLawAt`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.

## Grounding gaps

- No unresolved LeanExplore grounding gaps were recorded by this preflight.
