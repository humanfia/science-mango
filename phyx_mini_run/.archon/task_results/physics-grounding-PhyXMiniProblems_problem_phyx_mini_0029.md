# Physics LeanExplore Grounding Log

- Target Lean file: `PhyXMiniProblems/problem_phyx_mini_0029.lean`
- Blueprint chapter: `blueprint/src/chapters/PhyXMiniProblems_problem_phyx_mini_0029.tex`
- Grounding status: complete
- Search backend: local
- Input fingerprint: sha256:06c489bd0caf819e30f990fbc2f26663a9e1a1033c7021ff5f34a4205453142b
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

### Query: `Dim Optical Power`
- `PowerBasis.dim_pos` | module `Mathlib.RingTheory.PowerBasis` | package Mathlib | **Positivity of Power Basis Dimension.** If $S$ is a nontrivial algebra over a commutative ring $R$, then the dimension of any power basis of $S$ is strictly positive.
- `dimH` | module `Mathlib.Topology.MetricSpace.HausdorffDimension` | package Mathlib | Hausdorff dimension of a set in an (e)metric space.
- `Dimension.instPowRat` | module `Physlib.Units.Dimension` | package PhysLean | **Rational Power of a Physical Dimension.** For any physical dimension $d$ and any rational number $n$, the power $d^n$ is defined as the dimension whose fundamental components—length, time, mass, charge, and temperat...

### Query: `length In Meters`
- `LengthUnit.meters` | module `Physlib.SpaceAndTime.Space.LengthUnit` | package PhysLean | The definition of a length unit of meters.
- `LengthUnit.links` | module `Physlib.SpaceAndTime.Space.LengthUnit` | package PhysLean | The length unit of link (0.201168 meters).
- `LengthUnit.rods` | module `Physlib.SpaceAndTime.Space.LengthUnit` | package PhysLean | The length unit of a rod (5.0292 meters)

### Query: `power In Diopters`
- `EuclideanGeometry.Sphere.power` | module `Mathlib.Geometry.Euclidean.Sphere.Power` | package Mathlib | The power of a point with respect to a sphere. For a point and a sphere, this is defined as the square of the distance from the point to the center minus the square of the radius. This value is positive if the point i...
- `PowerSeries` | module `Mathlib.RingTheory.PowerSeries.Basic` | package Mathlib | Formal power series over a coefficient type `R`
- `JoinedIn.joined` | module `Mathlib.Topology.Connected.PathConnected` | package Mathlib | **Path Connectivity in a Subset Implies Path Connectivity.** If two points $x$ and $y$ in a topological space are joined by a path contained within a subset $F$, then they are joined by a path in the space.

### Query: `Bifocal Segment`
- `segment` | module `Mathlib.Analysis.Convex.Segment` | package Mathlib | Segments in a vector space. Denoted as `[x -[𝕜] y]` within the `Convex` namespace.
- `PrincipalSeg` | module `Mathlib.Order.InitialSeg` | package Mathlib | If `r` is a relation on `α` and `s` in a relation on `β`, then `f : r ≺i s` is an initial segment embedding whose range is `Set.Iio x` for some element `x`. If `β` is a well order, this is equivalent to the embedding...
- `affineSegment` | module `Mathlib.Analysis.Convex.Between` | package Mathlib | The segment of points weakly between `x` and `y`. When convexity is refactored to support abstract affine combination spaces, this will no longer need to be a separate definition from `segment`. However, lemmas involv...

### Query: `Vision Role`
- `HahnSeries.orderTop` | module `Mathlib.RingTheory.HahnSeries.Basic` | package Mathlib | The orderTop of a Hahn series `x` is a minimal element of `WithTop Γ` where `x` has a nonzero coefficient if `x ≠ 0`, and is `⊤` when `x = 0`.
- `HahnSeries.single` | module `Mathlib.RingTheory.HahnSeries.Basic` | package Mathlib | `single a r` is the Hahn series which has coefficient `r` at `a` and zero otherwise.
- `HahnSeries.support` | module `Mathlib.RingTheory.HahnSeries.Basic` | package Mathlib | The support of a Hahn series is just the set of indices whose coefficients are nonzero. Notably, it is well-founded.

### Query: `Clear Vision Range`
- `Set.range` | module `Mathlib.Data.Set.Operations` | package Mathlib | Range of a function. This function is more flexible than `f '' univ`, as the image requires that the domain is in Type and not an arbitrary Sort.
- `Mathlib.Tactic.clear!` | module `Mathlib.Tactic.ClearExclamation` | package Mathlib | A variant of `clear` which clears not only the given hypotheses but also any other hypotheses depending on them
- `Mathlib.Tactic.clear_` | module `Mathlib.Tactic.Clear_` | package Mathlib | Clear all hypotheses starting with `_`, like `_match` and `_let_match`.

### Query: `Thin Corrective Lens`
- `CategoryTheory.ThinSkeleton.lowerAdjunction` | module `Mathlib.CategoryTheory.Skeletal` | package Mathlib | An adjunction between thin categories gives an adjunction between their thin skeletons.
- `HahnSeries.orderTop` | module `Mathlib.RingTheory.HahnSeries.Basic` | package Mathlib | The orderTop of a Hahn series `x` is a minimal element of `WithTop Γ` where `x` has a nonzero coefficient if `x ≠ 0`, and is `⊤` when `x = 0`.
- `YoungDiagram.rowLens` | module `Mathlib.Combinatorics.Young.YoungDiagram` | package Mathlib | List of row lengths of a Young diagram

### Query: `Bifocal Fitting`
- `LieModule.posFittingComp` | module `Mathlib.Algebra.Lie.Weights.Basic` | package Mathlib | If `M` is a representation of a nilpotent Lie algebra `L` with coefficients in `R`, then `posFittingComp R L M` is the span of the positive Fitting components of the action of `x` on `M`, as `x` ranges over `L`. It is...
- `HahnSeries.orderTop` | module `Mathlib.RingTheory.HahnSeries.Basic` | package Mathlib | The orderTop of a Hahn series `x` is a minimal element of `WithTop Γ` where `x` has a nonzero coefficient if `x ≠ 0`, and is `⊤` when `x = 0`.
- `CategoryTheory.Functor.mapBicone_pt` | module `Mathlib.CategoryTheory.Limits.Preserves.Shapes.Biproducts` | package Mathlib | **The Apex of a Functorial Bicone.** Given a functor $F: \mathcal{C} \to \mathcal{D}$ and a bicone $b$ over a family of objects $f$ in $\mathcal{C}$, the apex of the image bicone $F(b)$ is defined as the image of the...

## Grounded Mathlib/PhysLean names

- `Path.target` (Mathlib)
- `semiformal_result` (PhysLean)
- `stereographic_target` (Mathlib)
- `Order.LTSeries.length_le_krullDim` (Mathlib)
- `Dimension.L𝓭_mass` (PhysLean)
- `Order.krullDim_eq_iSup_length` (Mathlib)
- `PowerBasis.dim_pos` (Mathlib)
- `dimH` (Mathlib)
- `Dimension.instPowRat` (PhysLean)
- `LengthUnit.meters` (PhysLean)
- `LengthUnit.links` (PhysLean)
- `LengthUnit.rods` (PhysLean)
- `EuclideanGeometry.Sphere.power` (Mathlib)
- `PowerSeries` (Mathlib)
- `JoinedIn.joined` (Mathlib)
- `segment` (Mathlib)
- `PrincipalSeg` (Mathlib)
- `affineSegment` (Mathlib)
- `HahnSeries.orderTop` (Mathlib)
- `HahnSeries.single` (Mathlib)
- `HahnSeries.support` (Mathlib)
- `Set.range` (Mathlib)
- `Mathlib.Tactic.clear!` (Mathlib)
- `Mathlib.Tactic.clear_` (Mathlib)
- `CategoryTheory.ThinSkeleton.lowerAdjunction` (Mathlib)
- `HahnSeries.orderTop` (Mathlib)
- `YoungDiagram.rowLens` (Mathlib)
- `LieModule.posFittingComp` (Mathlib)
- `HahnSeries.orderTop` (Mathlib)
- `CategoryTheory.Functor.mapBicone_pt` (Mathlib)

## Local abstractions introduced

- `PhyXMiniProblems.ProblemPhyXMini0029.AnswerChoice`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMiniProblems.ProblemPhyXMini0029.BifocalFitting`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMiniProblems.ProblemPhyXMini0029.BifocalSegment`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMiniProblems.ProblemPhyXMini0029.ClearVisionRange`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMiniProblems.ProblemPhyXMini0029.DimLength`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMiniProblems.ProblemPhyXMini0029.DimOpticalPower`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMiniProblems.ProblemPhyXMini0029.FormsVirtualImageAtUnaidedNearPoint`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMiniProblems.ProblemPhyXMini0029.HasPhysicalDistanceOrdering`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMiniProblems.ProblemPhyXMini0029.HasStatedDistanceReadouts`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMiniProblems.ProblemPhyXMini0029.IsNearestThousandthReadout`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMiniProblems.ProblemPhyXMini0029.MatchesBifocalFigure`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMiniProblems.ProblemPhyXMini0029.ObeysOpticalPowerLaw`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMiniProblems.ProblemPhyXMini0029.ObeysThinLensEquation`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMiniProblems.ProblemPhyXMini0029.ThinCorrectiveLens`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMiniProblems.ProblemPhyXMini0029.UsesEyePlaneLensApproximation`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMiniProblems.ProblemPhyXMini0029.VisionRole`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.

## Grounding gaps

- No unresolved LeanExplore grounding gaps were recorded by this preflight.
