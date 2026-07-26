# Physics LeanExplore Grounding Log

- Target Lean file: `PhyXMiniProblems/problem_phyx_mini_0018.lean`
- Blueprint chapter: `blueprint/src/chapters/PhyXMiniProblems_problem_phyx_mini_0018.tex`
- Grounding status: complete
- Search backend: local
- Input fingerprint: sha256:e81a92a4920953cad1029231f7c544e32a654002289a4d08d816a1f86febfcca
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

### Query: `length In Meters`
- `LengthUnit.meters` | module `Physlib.SpaceAndTime.Space.LengthUnit` | package PhysLean | The definition of a length unit of meters.
- `LengthUnit.links` | module `Physlib.SpaceAndTime.Space.LengthUnit` | package PhysLean | The length unit of link (0.201168 meters).
- `LengthUnit.rods` | module `Physlib.SpaceAndTime.Space.LengthUnit` | package PhysLean | The length unit of a rod (5.0292 meters)

### Query: `Optical Medium`
- `HahnSeries.orderTop` | module `Mathlib.RingTheory.HahnSeries.Basic` | package Mathlib | The orderTop of a Hahn series `x` is a minimal element of `WithTop Γ` where `x` has a nonzero coefficient if `x ≠ 0`, and is `⊤` when `x = 0`.
- `HahnSeries.order_abs` | module `Mathlib.RingTheory.HahnSeries.Lex` | package Mathlib | **Order of the Absolute Value of a Hahn Series.** For any Hahn series $x$ in a lexicographically ordered Hahn series ring, the order of its absolute value $|x|$ is equal to the order of $x$.
- `HahnSeries.single` | module `Mathlib.RingTheory.HahnSeries.Basic` | package Mathlib | `single a r` is the Hahn series which has coefficient `r` at `a` and zero otherwise.

### Query: `Optical Interface`
- `HahnSeries.orderTop` | module `Mathlib.RingTheory.HahnSeries.Basic` | package Mathlib | The orderTop of a Hahn series `x` is a minimal element of `WithTop Γ` where `x` has a nonzero coefficient if `x ≠ 0`, and is `⊤` when `x = 0`.
- `HahnSeries.single` | module `Mathlib.RingTheory.HahnSeries.Basic` | package Mathlib | `single a r` is the Hahn series which has coefficient `r` at `a` and zero otherwise.
- `Mathlib.Tactic.LibraryRewrite.RewriteInterface` | module `Mathlib.Tactic.Widget.LibraryRewrite` | package Mathlib | The structure with all data necessary for rendering a rewrite suggestion

### Query: `Quarter Circle Refraction Setup`
- `circleMap` | module `Mathlib.Analysis.SpecialFunctions.Complex.CircleMap` | package Mathlib | The exponential map $θ ↦ c + R e^{θi}$. The range of this map is the circle in `ℂ` with center `c` and radius `|R|`.
- `EuclideanGeometry.Sphere.isDiameter_iff_left_mem_and_pointReflection_center_left` | module `Mathlib.Geometry.Euclidean.Sphere.Basic` | package Mathlib | **Characterization of a Sphere's Diameter via Point Reflection.** Two points $p_1$ and $p_2$ form a diameter of a sphere $s$ if and only if $p_1$ lies on the sphere and $p_2$ is the image of $p_1$ under a point reflec...
- `EuclideanGeometry.Sphere.IsDiameter.pointReflection_center_right` | module `Mathlib.Geometry.Euclidean.Sphere.Basic` | package Mathlib | **Point Reflection of a Diameter Endpoint.** If two points $p_1$ and $p_2$ form a diameter of a sphere $s$, then the reflection of $p_2$ across the center of $s$ is equal to $p_1$.

### Query: `Has Physical Parameters`
- `CanonicalEnsemble.physicalProbability` | module `Physlib.StatisticalMechanics.CanonicalEnsemble.Basic` | package PhysLean | The dimensionless physical probability density. This is is the probability density w.r.t. the measure, obtained by dividing the phase space measure by the fundamental unit `h^dof`, making the probability density `ρ_ph...
- `HasSum` | module `Mathlib.Topology.Algebra.InfiniteSum.Defs` | package Mathlib | `HasSum f a L` means that the (potentially infinite) sum of the `f b` for `b : β` converges to `a` along the SummationFilter `L`. By default `L` is the `unconditional` one, corresponding to the limit of all finite set...
- `Dimension` | module `Physlib.Units.Dimension` | package PhysLean | The foundational dimensions. Defined in the order ⟨length, time, mass, charge, temperature⟩

### Query: `Has Physical Ray Angles`
- `SameRay` | module `Mathlib.LinearAlgebra.Ray` | package Mathlib | Two vectors are in the same ray if either one of them is zero or some positive multiples of them are equal (in the typical case over a field, this means one of them is a nonnegative multiple of the other).
- `EuclideanGeometry.angle_add_angle_eq_of_sbtw_of_sameRay` | module `Mathlib.Geometry.Euclidean.Triangle` | package Mathlib | If `B` lies on the same ray from `P` as a point `X` strictly between `A` and `C`, then `∠ A P B + ∠ B P C = ∠ A P C`.
- `CanonicalEnsemble.physicalProbability` | module `Physlib.StatisticalMechanics.CanonicalEnsemble.Basic` | package PhysLean | The dimensionless physical probability density. This is is the probability density w.r.t. the measure, obtained by dividing the phase space measure by the fundamental unit `h^dof`, making the probability density `ρ_ph...

### Query: `Obeys Quarter Circle Geometry`
- `EuclideanGeometry.oangle` | module `Mathlib.Geometry.Euclidean.Angle.Oriented.Affine` | package Mathlib | The oriented angle at `p₂` between the line segments to `p₁` and `p₃`, modulo `2 * π`. If either of those points equals `p₂`, this is 0. See `EuclideanGeometry.angle` for the corresponding unoriented angle definition.
- `EuclideanGeometry.Sphere.two_zsmul_oangle_eq` | module `Mathlib.Geometry.Euclidean.Angle.Sphere` | package Mathlib | Oriented angle version of "angles in same segment are equal" and "opposite angles of a cyclic quadrilateral add to π", for oriented angles mod π (for which those are the same result), represented here as equality of t...
- `quarter_mem_cantorSet` | module `Mathlib.Topology.Instances.CantorSet` | package Mathlib | **Membership of 1/4 in the Cantor Set.** The real number $1/4$ is an element of the Cantor set.

### Query: `Satisfies Snell Law At`
- `Sat.Valuation.satisfies_fmla` | module `Mathlib.Tactic.Sat.FromLRAT` | package Mathlib | `v.satisfies_fmla f` asserts that formula `f` is satisfied by the valuation. A formula is satisfied if all clauses in it are satisfied.
- `ProbabilityTheory.HasGaussianLaw` | module `Mathlib.Probability.Distributions.Gaussian.HasGaussianLaw.Def` | package Mathlib | The predicate `HasGaussianLaw X P` means that under the measure `P`, `X` has a Gaussian distribution.
- `Sat.Valuation.satisfies` | module `Mathlib.Tactic.Sat.FromLRAT` | package Mathlib | `v.satisfies c` asserts that clause `c` satisfied by the valuation. It is written in a negative way: A clause like `a ∨ ¬b ∨ c` is rewritten as `¬a → b → ¬c → False`, so we are asserting that it is not the case that a...

## Grounded Mathlib/PhysLean names

- `Path.target` (Mathlib)
- `semiformal_result` (PhysLean)
- `stereographic_target` (Mathlib)
- `Order.LTSeries.length_le_krullDim` (Mathlib)
- `Dimension.L𝓭_mass` (PhysLean)
- `Order.krullDim_eq_iSup_length` (Mathlib)
- `LengthUnit.meters` (PhysLean)
- `LengthUnit.links` (PhysLean)
- `LengthUnit.rods` (PhysLean)
- `HahnSeries.orderTop` (Mathlib)
- `HahnSeries.order_abs` (Mathlib)
- `HahnSeries.single` (Mathlib)
- `HahnSeries.orderTop` (Mathlib)
- `HahnSeries.single` (Mathlib)
- `Mathlib.Tactic.LibraryRewrite.RewriteInterface` (Mathlib)
- `circleMap` (Mathlib)
- `EuclideanGeometry.Sphere.isDiameter_iff_left_mem_and_pointReflection_center_left` (Mathlib)
- `EuclideanGeometry.Sphere.IsDiameter.pointReflection_center_right` (Mathlib)
- `CanonicalEnsemble.physicalProbability` (PhysLean)
- `HasSum` (Mathlib)
- `Dimension` (PhysLean)
- `SameRay` (Mathlib)
- `EuclideanGeometry.angle_add_angle_eq_of_sbtw_of_sameRay` (Mathlib)
- `CanonicalEnsemble.physicalProbability` (PhysLean)
- `EuclideanGeometry.oangle` (Mathlib)
- `EuclideanGeometry.Sphere.two_zsmul_oangle_eq` (Mathlib)
- `quarter_mem_cantorSet` (Mathlib)
- `Sat.Valuation.satisfies_fmla` (Mathlib)
- `ProbabilityTheory.HasGaussianLaw` (Mathlib)
- `Sat.Valuation.satisfies` (Mathlib)

## Local abstractions introduced

- `PhyXMiniProblems.ProblemPhyXMini0018.DimLength`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMiniProblems.ProblemPhyXMini0018.HasPhysicalParameters`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMiniProblems.ProblemPhyXMini0018.HasPhysicalRayAngles`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMiniProblems.ProblemPhyXMini0018.ObeysQuarterCircleGeometry`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMiniProblems.ProblemPhyXMini0018.OpticalInterface`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMiniProblems.ProblemPhyXMini0018.OpticalMedium`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMiniProblems.ProblemPhyXMini0018.QuarterCircleRefractionSetup`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMiniProblems.ProblemPhyXMini0018.SatisfiesSnellLawAt`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.

## Grounding gaps

- No unresolved LeanExplore grounding gaps were recorded by this preflight.
