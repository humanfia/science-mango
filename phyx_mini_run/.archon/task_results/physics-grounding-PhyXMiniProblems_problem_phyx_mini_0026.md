# Physics LeanExplore Grounding Log

- Target Lean file: `PhyXMiniProblems/problem_phyx_mini_0026.lean`
- Blueprint chapter: `blueprint/src/chapters/PhyXMiniProblems_problem_phyx_mini_0026.tex`
- Grounding status: complete
- Search backend: local
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

### Query: `Space`
- `Space` | module `Physlib.SpaceAndTime.Space.Basic` | package PhysLean | The type `Space d` is the world-volume which corresponds to `d` dimensional (flat) Euclidean space with a given (but arbitrary) choice of length unit, and a given (but arbitrary) choice of zero. The default value of `...
- `Space.«termΔᵈ»` | module `Physlib.SpaceAndTime.Space.Derivatives.Laplacian` | package PhysLean | The distributional `distLaplacian` operator.
- `Space.«term∂[_]»` | module `Physlib.SpaceAndTime.Space.Derivatives.Basic` | package PhysLean | Given a function `f : Space d → M` the derivative of `f` in direction `μ`.

### Query: `Length Quantity`
- `LengthUnit` | module `Physlib.SpaceAndTime.Space.LengthUnit` | package PhysLean | The choices of translationally-invariant metrics on the space-manifold. Such a choice corresponds to a choice of units for length.
- `Computation.length` | module `Mathlib.Data.Seq.Computation` | package Mathlib | `length s` gets the number of steps of a terminating computation
- `LengthUnit.links` | module `Physlib.SpaceAndTime.Space.LengthUnit` | package PhysLean | The length unit of link (0.201168 meters).

### Query: `metres`
- `LengthUnit` | module `Physlib.SpaceAndTime.Space.LengthUnit` | package PhysLean | The choices of translationally-invariant metrics on the space-manifold. Such a choice corresponds to a choice of units for length.
- `LengthUnit.meters` | module `Physlib.SpaceAndTime.Space.LengthUnit` | package PhysLean | The definition of a length unit of meters.
- `MetricSpace` | module `Mathlib.Topology.MetricSpace.Defs` | package Mathlib | A metric space is a type endowed with a `ℝ`-valued distance `dist` satisfying `dist x y = 0 ↔ x = y`, commutativity `dist x y = dist y x`, and the triangle inequality `dist x z ≤ dist x y + dist y z`. See pseudometric...

### Query: `si Metres`
- `UnitChoices.SI_length` | module `Physlib.Units.Basic` | package PhysLean | **SI Length Unit.** In the International System of Units (SI), the fundamental unit of length is defined to be the meter.
- `HahnSeries.orderTop` | module `Mathlib.RingTheory.HahnSeries.Basic` | package Mathlib | The orderTop of a Hahn series `x` is a minimal element of `WithTop Γ` where `x` has a nonzero coefficient if `x ≠ 0`, and is `⊤` when `x = 0`.
- `UnitChoices.SI` | module `Physlib.Units.Basic` | package PhysLean | The choice of units corresponding to SI units, that is - meters, - seconds, - kilograms, - coulombs, - kelvin.

### Query: `physical Distance`
- `HahnSeries.orderTop` | module `Mathlib.RingTheory.HahnSeries.Basic` | package Mathlib | The orderTop of a Hahn series `x` is a minimal element of `WithTop Γ` where `x` has a nonzero coefficient if `x ≠ 0`, and is `⊤` when `x = 0`.
- `Nat.instDist` | module `Mathlib.Topology.Instances.Nat` | package Mathlib | **Distance on Natural Numbers.** The distance between two natural numbers $x$ and $y$ is defined as the standard distance between them when they are considered as real numbers, denoted by $\text{dist}(x, y)$.
- `CanonicalEnsemble.physicalProbability` | module `Physlib.StatisticalMechanics.CanonicalEnsemble.Basic` | package PhysLean | The dimensionless physical probability density. This is is the probability density w.r.t. the measure, obtained by dividing the phase space measure by the fundamental unit `h^dof`, making the probability density `ρ_ph...

### Query: `Plane Mirror`
- `Polynomial.mirror_smul` | module `Mathlib.Algebra.Polynomial.Mirror` | package Mathlib | **Scalar Multiplication of Mirror Polynomials.** For any scalar $a$ and polynomial $p$ over a domain $R$, the mirror of the scalar product $a \cdot p$ is equal to the scalar product of $a$ and the mirror of $p$.
- `UpperHalfPlane` | module `Mathlib.Analysis.Complex.UpperHalfPlane.Basic` | package Mathlib | The open upper half plane, denoted as `ℍ` within the `UpperHalfPlane` namespace
- `Polynomial.mirror` | module `Mathlib.Algebra.Polynomial.Mirror` | package Mathlib | mirror of a polynomial: reverses the coefficients while preserving `Polynomial.natDegree`

### Query: `reflect Point`
- `Equiv.pointReflection` | module `Mathlib.Algebra.Torsor.Defs` | package Mathlib | Point reflection in `x` as a permutation.
- `Polynomial.reflect` | module `Mathlib.Algebra.Polynomial.Reverse` | package Mathlib | `reflect N f` is the polynomial such that `(reflect N f).coeff i = f.coeff (revAt N i)`. In other words, the terms with exponent `[0, ..., N]` now have exponent `[N, ..., 0]`. In practice, `reflect` is only used when...
- `ContinuousAffineEquiv.pointReflection_apply` | module `Mathlib.Topology.Algebra.ContinuousAffineEquiv` | package Mathlib | **Point Reflection Formula.** For any points $x$ and $y$ in an affine space over a topological ring $k$, the reflection of $y$ across the center $x$ is given by the point $(x - y) + x$.

### Query: `Periscope Setup`
- `HahnSeries.orderTop` | module `Mathlib.RingTheory.HahnSeries.Basic` | package Mathlib | The orderTop of a Hahn series `x` is a minimal element of `WithTop Γ` where `x` has a nonzero coefficient if `x ≠ 0`, and is `⊤` when `x = 0`.
- `Mathlib.Notation3.setupLCtx` | module `Mathlib.Util.Notation3` | package Mathlib | Adds all the names in `boundNames` to the local context with types that are fresh metavariables. This is used for example when initializing `p` in `(scoped p => ...)` when elaborating `...`.
- `HahnSeries.single` | module `Mathlib.RingTheory.HahnSeries.Basic` | package Mathlib | `single a r` is the Hahn series which has coefficient `r` at `a` and zero otherwise.

## Grounded Mathlib/PhysLean names

- `EuclideanSpace` (Mathlib)
- `Space.fderiv_space_components` (PhysLean)
- `Lorentz.ContrMod.toSpace` (PhysLean)
- `Path.target` (Mathlib)
- `semiformal_result` (PhysLean)
- `stereographic_target` (Mathlib)
- `Space` (PhysLean)
- `Space.«termΔᵈ»` (PhysLean)
- `Space.«term∂[_]»` (PhysLean)
- `LengthUnit` (PhysLean)
- `Computation.length` (Mathlib)
- `LengthUnit.links` (PhysLean)
- `LengthUnit` (PhysLean)
- `LengthUnit.meters` (PhysLean)
- `MetricSpace` (Mathlib)
- `UnitChoices.SI_length` (PhysLean)
- `HahnSeries.orderTop` (Mathlib)
- `UnitChoices.SI` (PhysLean)
- `HahnSeries.orderTop` (Mathlib)
- `Nat.instDist` (Mathlib)
- `CanonicalEnsemble.physicalProbability` (PhysLean)
- `Polynomial.mirror_smul` (Mathlib)
- `UpperHalfPlane` (Mathlib)
- `Polynomial.mirror` (Mathlib)
- `Equiv.pointReflection` (Mathlib)
- `Polynomial.reflect` (Mathlib)
- `ContinuousAffineEquiv.pointReflection_apply` (Mathlib)
- `HahnSeries.orderTop` (Mathlib)
- `Mathlib.Notation3.setupLCtx` (Mathlib)
- `HahnSeries.single` (Mathlib)

## Local abstractions introduced

- `PhyXMiniProblems.ProblemPhyXMini0026.AnswerChoice`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMiniProblems.ProblemPhyXMini0026.FinalImageMatchesChoice`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMiniProblems.ProblemPhyXMini0026.HasFortyFiveDegreeMirrorGeometry`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMiniProblems.ProblemPhyXMini0026.HasPositiveFigureLengths`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMiniProblems.ProblemPhyXMini0026.LengthQuantity`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMiniProblems.ProblemPhyXMini0026.MatchesPeriscopeFigure`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMiniProblems.ProblemPhyXMini0026.PeriscopeSetup`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMiniProblems.ProblemPhyXMini0026.PlaneMirror`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMiniProblems.ProblemPhyXMini0026.SatisfiesPlaneMirrorImageFormation`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMiniProblems.ProblemPhyXMini0026.Space`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.

## Grounding gaps

- No unresolved LeanExplore grounding gaps were recorded by this preflight.
