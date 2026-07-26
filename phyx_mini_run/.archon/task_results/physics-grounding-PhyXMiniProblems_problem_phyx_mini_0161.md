# Physics LeanExplore Grounding Log

- Target Lean file: `PhyXMiniProblems/problem_phyx_mini_0161.lean`
- Blueprint chapter: `blueprint/src/chapters/PhyXMiniProblems_problem_phyx_mini_0161.tex`
- Grounding status: complete
- Search backend: local
- Input fingerprint: sha256:a952dc47c3da768f3549aaf722778fffc92c33be8b0e5a3572594d7df6a7d8bc
- Packages searched: Mathlib, Physlib

## LeanExplore queries/candidates actually used

### Query: `Physics formalization target`
- `Path.target` | module `Mathlib.Topology.Path` | package Mathlib | **Target of a Path.** For a path $\gamma$ from $x$ to $y$ in a topological space, the value of the path at the endpoint of the unit interval, $\gamma(1)$, is equal to $y$.
- `semiformal_result` | module `Physlib.Meta.Informal.SemiFormal` | package PhysLean | A semiformal result is either a - definition in which the type is given but not the definition. - proof in which the proposition is given but not the proof. Semiformal results cannot be used in further code. They are...
- `stereographic_target` | module `Mathlib.Geometry.Manifold.Instances.Sphere` | package Mathlib | **Target of the Stereographic Projection.** For any unit vector $v$ in an inner product space, the target of the stereographic projection associated with $v$ is the entire codomain (the orthogonal complement of the su...

### Query: `Optical Length`
- `Computation.length` | module `Mathlib.Data.Seq.Computation` | package Mathlib | `length s` gets the number of steps of a terminating computation
- `LengthUnit.lightYears` | module `Physlib.SpaceAndTime.Space.LengthUnit` | package PhysLean | The length unit of a light year (9,460,730,472,580,800 meters).
- `LengthUnit` | module `Physlib.SpaceAndTime.Space.LengthUnit` | package PhysLean | The choices of translationally-invariant metrics on the space-manifold. Such a choice corresponds to a choice of units for length.

### Query: `length Readout`
- `Computation.length` | module `Mathlib.Data.Seq.Computation` | package Mathlib | `length s` gets the number of steps of a terminating computation
- `LengthUnit.rods` | module `Physlib.SpaceAndTime.Space.LengthUnit` | package PhysLean | The length unit of a rod (5.0292 meters)
- `Cycle.length` | module `Mathlib.Data.List.Cycle` | package Mathlib | The length of the `s : Cycle α`, which is the number of elements, counting duplicates.

### Query: `length In Centimeters`
- `LengthUnit.centimeters` | module `Physlib.SpaceAndTime.Space.LengthUnit` | package PhysLean | The length unit of centimeters (10⁻² of a meter).
- `LengthUnit.links` | module `Physlib.SpaceAndTime.Space.LengthUnit` | package PhysLean | The length unit of link (0.201168 meters).
- `LengthUnit.rods` | module `Physlib.SpaceAndTime.Space.LengthUnit` | package PhysLean | The length unit of a rod (5.0292 meters)

### Query: `Optical Medium`
- `HahnSeries.orderTop` | module `Mathlib.RingTheory.HahnSeries.Basic` | package Mathlib | The orderTop of a Hahn series `x` is a minimal element of `WithTop Γ` where `x` has a nonzero coefficient if `x ≠ 0`, and is `⊤` when `x = 0`.
- `HahnSeries.order_abs` | module `Mathlib.RingTheory.HahnSeries.Lex` | package Mathlib | **Order of the Absolute Value of a Hahn Series.** For any Hahn series $x$ in a lexicographically ordered Hahn series ring, the order of its absolute value $|x|$ is equal to the order of $x$.
- `HahnSeries.single` | module `Mathlib.RingTheory.HahnSeries.Basic` | package Mathlib | `single a r` is the Hahn series which has coefficient `r` at `a` and zero otherwise.

### Query: `Source Model`
- `ModelWithCorners.prod_source` | module `Mathlib.Geometry.Manifold.IsManifold.Basic` | package Mathlib | **Domain of the Product Model with Corners.** Given two models with corners $I$ (mapping a topological space $H$ to a normed space $E$) and $I'$ (mapping $H'$ to $E'$), the domain of the product model with corners $I...
- `ModelWithCorners.extendCoordChange_source` | module `Mathlib.Geometry.Manifold.IsManifold.ExtChartAt` | package Mathlib | **Source of the Extended Coordinate Change.** For a model with corners $I$ and two local homeomorphisms $e$ and $e'$, the source of the extended coordinate change map between them is equal to the image under $I$ of th...
- `ModelWithCorners.uniqueDiffOn_preimage_source` | module `Mathlib.Geometry.Manifold.IsManifold.Basic` | package Mathlib | **Unique Differentiability of the Preimage of a Chart Source.** Given a model with corners $I$ from a space $H$ to a vector space $E$, and an open partial homeomorphism $e$ on $H$, the set formed by the intersection o...

### Query: `Bottom Mirror Model`
- `Polynomial.mirror` | module `Mathlib.Algebra.Polynomial.Mirror` | package Mathlib | mirror of a polynomial: reverses the coefficients while preserving `Polynomial.natDegree`
- `WithBot` | module `Mathlib.Order.TypeTags` | package Mathlib | Attach `⊥` to a type.
- `WithBot.instOrderBot` | module `Mathlib.Order.WithBot` | package Mathlib | **Bottom Element of WithBot.** The type formed by adjoining a bottom element to a type $\alpha$ is a bottom-ordered set, where the adjoined element $\bot$ is the least element of the order.

### Query: `Viewing Regime`
- `HahnSeries.orderTop` | module `Mathlib.RingTheory.HahnSeries.Basic` | package Mathlib | The orderTop of a Hahn series `x` is a minimal element of `WithTop Γ` where `x` has a nonzero coefficient if `x ≠ 0`, and is `⊤` when `x = 0`.
- `HahnSeries.single` | module `Mathlib.RingTheory.HahnSeries.Basic` | package Mathlib | `single a r` is the Hahn series which has coefficient `r` at `a` and zero otherwise.
- `HahnSeries.order_lt_order_of_eq_add_single` | module `Mathlib.RingTheory.HahnSeries.Addition` | package Mathlib | **Order Comparison for Hahn Series Sums.** For a Hahn series $x$ and a non-zero Hahn series $y$ over a linearly ordered set $\Gamma$ and a cancellative commutative monoid $R$, if $x$ is equal to the sum of $y$ and the...

### Query: `Image Nature`
- `Set.image` | module `Mathlib.Data.Set.Defs` | package Mathlib | The image of `s : Set α` by `f : α → β`, written `f '' s`, is the set of `b : β` such that `f a = b` for some `a ∈ s`.
- `Finset.image` | module `Mathlib.Data.Finset.Image` | package Mathlib | `image f s` is the forward image of `s` under `f`.
- `Fin.finsetImage_val_Ico` | module `Mathlib.Order.Interval.Finset.Fin` | package Mathlib | **Image of a Finite Interval of Bounded Natural Numbers.** The image of the left-closed, right-open interval $[a, b)$ in the type of natural numbers less than $n$ under the natural inclusion map into $\mathbb{N}$ is e...

### Query: `Observer Side`
- `AffineSubspace.WOppSide` | module `Mathlib.Analysis.Convex.Side` | package Mathlib | The points `x` and `y` are weakly on opposite sides of `s`.
- `AffineSubspace.WSameSide` | module `Mathlib.Analysis.Convex.Side` | package Mathlib | The points `x` and `y` are weakly on the same side of `s`.
- `similar_of_side_side` | module `Mathlib.Topology.MetricSpace.Similarity` | package Mathlib | **Alias** of `similar_of_dist_mul_eq_dist_mul_eq`. --- If two triangles have two pairs of proportional adjacent sides, then the triangles are similar.

## Grounded Mathlib/PhysLean names

- `Path.target` (Mathlib)
- `semiformal_result` (PhysLean)
- `stereographic_target` (Mathlib)
- `Computation.length` (Mathlib)
- `LengthUnit.lightYears` (PhysLean)
- `LengthUnit` (PhysLean)
- `Computation.length` (Mathlib)
- `LengthUnit.rods` (PhysLean)
- `Cycle.length` (Mathlib)
- `LengthUnit.centimeters` (PhysLean)
- `LengthUnit.links` (PhysLean)
- `LengthUnit.rods` (PhysLean)
- `HahnSeries.orderTop` (Mathlib)
- `HahnSeries.order_abs` (Mathlib)
- `HahnSeries.single` (Mathlib)
- `ModelWithCorners.prod_source` (Mathlib)
- `ModelWithCorners.extendCoordChange_source` (Mathlib)
- `ModelWithCorners.uniqueDiffOn_preimage_source` (Mathlib)
- `Polynomial.mirror` (Mathlib)
- `WithBot` (Mathlib)
- `WithBot.instOrderBot` (Mathlib)
- `HahnSeries.orderTop` (Mathlib)
- `HahnSeries.single` (Mathlib)
- `HahnSeries.order_lt_order_of_eq_add_single` (Mathlib)
- `Set.image` (Mathlib)
- `Finset.image` (Mathlib)
- `Fin.finsetImage_val_Ico` (Mathlib)
- `AffineSubspace.WOppSide` (Mathlib)
- `AffineSubspace.WSameSide` (Mathlib)
- `similar_of_side_side` (Mathlib)

## Local abstractions introduced

- `PhyXMiniProblems.ProblemPhyXMini0161.AnswerChoice`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMiniProblems.ProblemPhyXMini0161.BottomMirrorModel`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMiniProblems.ProblemPhyXMini0161.HasPhysicalPoolMirrorParameters`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMiniProblems.ProblemPhyXMini0161.ImageNature`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMiniProblems.ProblemPhyXMini0161.IsUniqueClosestAnswer`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMiniProblems.ProblemPhyXMini0161.MatchesAnswerToNearestCentimeter`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMiniProblems.ProblemPhyXMini0161.MatchesStatedPoolMirrorProblem`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMiniProblems.ProblemPhyXMini0161.ObserverSide`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMiniProblems.ProblemPhyXMini0161.OpticalLength`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMiniProblems.ProblemPhyXMini0161.OpticalMedium`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMiniProblems.ProblemPhyXMini0161.PoolMirrorDiagram`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMiniProblems.ProblemPhyXMini0161.SatisfiesParaxialPoolMirrorOptics`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMiniProblems.ProblemPhyXMini0161.SourceModel`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMiniProblems.ProblemPhyXMini0161.UsesStandardAirWaterIndices`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMiniProblems.ProblemPhyXMini0161.ViewingRegime`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.

## Grounding gaps

- No unresolved LeanExplore grounding gaps were recorded by this preflight.
