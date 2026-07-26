# Physics LeanExplore Grounding Log

- Target Lean file: `PhyXMiniProblems/problem_phyx_mini_0070.lean`
- Blueprint chapter: `blueprint/src/chapters/PhyXMiniProblems_problem_phyx_mini_0070.tex`
- Grounding status: complete
- Search backend: local
- Input fingerprint: sha256:7b6036401b757c6480f7e8f88a7a6d90bb738aa3a405b21a6fc824de362a6493
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

### Query: `length In Centimeters`
- `LengthUnit.centimeters` | module `Physlib.SpaceAndTime.Space.LengthUnit` | package PhysLean | The length unit of centimeters (10⁻² of a meter).
- `LengthUnit.links` | module `Physlib.SpaceAndTime.Space.LengthUnit` | package PhysLean | The length unit of link (0.201168 meters).
- `LengthUnit.rods` | module `Physlib.SpaceAndTime.Space.LengthUnit` | package PhysLean | The length unit of a rod (5.0292 meters)

### Query: `Tank Contents`
- `MvPFunctor.appendContents` | module `Mathlib.Data.PFunctor.Multivariate.Basic` | package Mathlib | append arrows of a polynomial functor application
- `HahnSeries.orderTop` | module `Mathlib.RingTheory.HahnSeries.Basic` | package Mathlib | The orderTop of a Hahn series `x` is a minimal element of `WithTop Γ` where `x` has a nonzero coefficient if `x ≠ 0`, and is `⊤` when `x = 0`.
- `MvPFunctor.M.corecContents` | module `Mathlib.Data.PFunctor.Multivariate.M` | package Mathlib | Using corecursion, construct the contents of an M-type

### Query: `Tank Corner`
- `IsCorner` | module `Mathlib.Combinatorics.Additive.Corner.Defs` | package Mathlib | A **corner** of a set `A` in an abelian group is a triple of points of the form `(x, y), (x + d, y), (x, y + d)`. It is **nontrivial** if `d ≠ 0`. Here we define it as triples `(x₁, y₁), (x₂, y₁), (x₁, y₂)` where `x₁...
- `HahnSeries.orderTop` | module `Mathlib.RingTheory.HahnSeries.Basic` | package Mathlib | The orderTop of a Hahn series `x` is a minimal element of `WithTop Γ` where `x` has a nonzero coefficient if `x ≠ 0`, and is `⊤` when `x = 0`.
- `ModelWithCorners.tangent` | module `Mathlib.Geometry.Manifold.IsManifold.Basic` | package Mathlib | Special case of product model with corners, which is trivial on the second factor. This shows up as the model to tangent bundles.

### Query: `Meter Stick Placement`
- `DimArea.squareMeter` | module `Physlib.Units.WithDim.Area` | package PhysLean | The dimensional area corresponding to 1 square meter.
- `HahnSeries.orderTop` | module `Mathlib.RingTheory.HahnSeries.Basic` | package Mathlib | The orderTop of a Hahn series `x` is a minimal element of `WithTop Γ` where `x` has a nonzero coefficient if `x ≠ 0`, and is `⊤` when `x = 0`.
- `LengthUnit.yards` | module `Physlib.SpaceAndTime.Space.LengthUnit` | package PhysLean | The length unit of a yard (0.9144 meters)

### Query: `Angle Reference`
- `EuclideanGeometry.angle` | module `Mathlib.Geometry.Euclidean.Angle.Unoriented.Affine` | package Mathlib | The undirected angle at `p₂` between the line segments to `p₁` and `p₃`. If either of those points equals `p₂`, this is π/2. Use `open scoped EuclideanGeometry` to access the `∠ p₁ p₂ p₃` notation.
- `Real.Angle.coe_toReal` | module `Mathlib.Analysis.SpecialFunctions.Trigonometric.Angle` | package Mathlib | **Angle Coercion of the Real Representative.** For any angle $\theta$, the angle formed by taking its unique real representative in the interval $(-\pi, \pi]$ is equal to $\theta$ itself.
- `Real.Angle.toReal_neg_iff_sign_neg` | module `Mathlib.Analysis.SpecialFunctions.Trigonometric.Angle` | package Mathlib | **Sign of an Angle and its Real Representative.** For any angle $\theta$, the unique representative of $\theta$ in the interval $(-\pi, \pi]$ is strictly negative if and only if the sign of $\theta$ is equal to $-1$.

### Query: `Empty Tank Meter Stick Setup`
- `DimArea.squareMeter` | module `Physlib.Units.WithDim.Area` | package PhysLean | The dimensional area corresponding to 1 square meter.
- `Mathlib.Notation3.setupLCtx` | module `Mathlib.Util.Notation3` | package Mathlib | Adds all the names in `boundNames` to the local context with types that are fresh metavariables. This is used for example when initializing `p` in `(scoped p => ...)` when elaborating `...`.
- `DimArea.squareMeter_in_SI` | module `Physlib.Units.WithDim.Area` | package PhysLean | **Value of a Square Meter in SI Units.** In the International System of Units (SI), the magnitude of one square meter is exactly equal to one.

### Query: `Matches Problem And Primary Figure`
- `Ideal.primaryComponent` | module `Mathlib.Algebra.Module.Torsion.PrimaryComponent` | package Mathlib | The `I`-primaryComponent component of a module `M` where `I` is an ideal of `A`.
- `Ideal.IsPrimary` | module `Mathlib.RingTheory.Ideal.IsPrimary` | package Mathlib | A proper ideal `I` is primary as a submodule.
- `Submodule.IsPrimary` | module `Mathlib.RingTheory.IsPrimary` | package Mathlib | A proper submodule `S : Submodule R M` is primary iff `r • x ∈ S` implies `x ∈ S` or `∃ n : ℕ, r ^ n • (⊤ : Submodule R M) ≤ S`. This generalizes `Ideal.IsPrimary`.

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
- `LengthUnit.centimeters` (PhysLean)
- `LengthUnit.links` (PhysLean)
- `LengthUnit.rods` (PhysLean)
- `MvPFunctor.appendContents` (Mathlib)
- `HahnSeries.orderTop` (Mathlib)
- `MvPFunctor.M.corecContents` (Mathlib)
- `IsCorner` (Mathlib)
- `HahnSeries.orderTop` (Mathlib)
- `ModelWithCorners.tangent` (Mathlib)
- `DimArea.squareMeter` (PhysLean)
- `HahnSeries.orderTop` (Mathlib)
- `LengthUnit.yards` (PhysLean)
- `EuclideanGeometry.angle` (Mathlib)
- `Real.Angle.coe_toReal` (Mathlib)
- `Real.Angle.toReal_neg_iff_sign_neg` (Mathlib)
- `DimArea.squareMeter` (PhysLean)
- `Mathlib.Notation3.setupLCtx` (Mathlib)
- `DimArea.squareMeter_in_SI` (PhysLean)
- `Ideal.primaryComponent` (Mathlib)
- `Ideal.IsPrimary` (Mathlib)
- `Submodule.IsPrimary` (Mathlib)

## Local abstractions introduced

- `PhyXMiniProblems.ProblemPhyXMini0070.AngleReference`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMiniProblems.ProblemPhyXMini0070.AnswerChoice`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMiniProblems.ProblemPhyXMini0070.EmptyTankMeterStickSetup`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMiniProblems.ProblemPhyXMini0070.HasDepictedPhysicalConfiguration`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMiniProblems.ProblemPhyXMini0070.LengthQuantity`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMiniProblems.ProblemPhyXMini0070.MatchesAnswerChoice`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMiniProblems.ProblemPhyXMini0070.MatchesProblemAndPrimaryFigure`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMiniProblems.ProblemPhyXMini0070.MeterStickPlacement`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMiniProblems.ProblemPhyXMini0070.ObeysStraightSightlineGeometry`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMiniProblems.ProblemPhyXMini0070.RoundsToWholeCentimeterMark`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMiniProblems.ProblemPhyXMini0070.TankContents`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMiniProblems.ProblemPhyXMini0070.TankCorner`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.

## Grounding gaps

- No unresolved LeanExplore grounding gaps were recorded by this preflight.
