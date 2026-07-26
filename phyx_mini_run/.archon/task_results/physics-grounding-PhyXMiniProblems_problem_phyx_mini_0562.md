# Physics LeanExplore Grounding Log

- Target Lean file: `PhyXMiniProblems/problem_phyx_mini_0562.lean`
- Blueprint chapter: `blueprint/src/chapters/PhyXMiniProblems_problem_phyx_mini_0562.tex`
- Grounding status: complete
- Search backend: local
- Input fingerprint: sha256:cb16e75ada3d3d73fa1f4372e5c51b6feecf7cb4da59756d70cf505b41651b94
- Packages searched: Mathlib, Physlib

## LeanExplore queries/candidates actually used

### Query: `Physics formalization target`
- `Path.target` | module `Mathlib.Topology.Path` | package Mathlib | **Target of a Path.** For a path $\gamma$ from $x$ to $y$ in a topological space, the value of the path at the endpoint of the unit interval, $\gamma(1)$, is equal to $y$.
- `semiformal_result` | module `Physlib.Meta.Informal.SemiFormal` | package PhysLean | A semiformal result is either a - definition in which the type is given but not the definition. - proof in which the proposition is given but not the proof. Semiformal results cannot be used in further code. They are...
- `stereographic_target` | module `Mathlib.Geometry.Manifold.Instances.Sphere` | package Mathlib | **Target of the Stereographic Projection.** For any unit vector $v$ in an inner product space, the target of the stereographic projection associated with $v$ is the entire codomain (the orthogonal complement of the su...

### Query: `Length Magnitude`
- `List.Vector.length` | module `Mathlib.Data.Vector.Defs` | package Mathlib | The length of a vector.
- `Computation.length` | module `Mathlib.Data.Seq.Computation` | package Mathlib | `length s` gets the number of steps of a terminating computation
- `LengthUnit` | module `Physlib.SpaceAndTime.Space.LengthUnit` | package PhysLean | The choices of translationally-invariant metrics on the space-manifold. Such a choice corresponds to a choice of units for length.

### Query: `Area Magnitude`
- `DimArea` | module `Physlib.Units.WithDim.Area` | package PhysLean | The type of areas in the absence of a choice of unit.
- `HahnSeries.orderTop` | module `Mathlib.RingTheory.HahnSeries.Basic` | package Mathlib | The orderTop of a Hahn series `x` is a minimal element of `WithTop Γ` where `x` has a nonzero coefficient if `x ≠ 0`, and is `⊤` when `x = 0`.
- `DimArea.are` | module `Physlib.Units.WithDim.Area` | package PhysLean | The dimensional area corresponding to 1 are (100 square meters).

### Query: `Particle Intensity`
- `ClassicalMechanics.FreeParticle` | module `Physlib.ClassicalMechanics.FreeParticle.Basic` | package PhysLean | A classical free particle with positive mass. A free particle is a mechanical system evolving in the absence of external forces. The dynamics are therefore entirely determined by Newton's second law with zero force. T...
- `HahnSeries.orderTop` | module `Mathlib.RingTheory.HahnSeries.Basic` | package Mathlib | The orderTop of a Hahn series `x` is a minimal element of `WithTop Γ` where `x` has a nonzero coefficient if `x ≠ 0`, and is `⊤` when `x = 0`.
- `Real.integral_rpowIntegrand₀₁_one_pos` | module `Mathlib.Analysis.SpecialFunctions.ContinuousFunctionalCalculus.Rpow.IntegralRepresentation` | package Mathlib | **Positivity of the Fractional Power Integrand Integral.** For any $p$ in the open interval $(0, 1)$, the integral over the interval $(0, \infty)$ of the integrand $t^p \left( \frac{1}{t} - \frac{1}{t + 1} \right)$ is...

### Query: `Particle Rate`
- `HahnSeries.orderTop` | module `Mathlib.RingTheory.HahnSeries.Basic` | package Mathlib | The orderTop of a Hahn series `x` is a minimal element of `WithTop Γ` where `x` has a nonzero coefficient if `x ≠ 0`, and is `⊤` when `x = 0`.
- `ProbabilityTheory.«termPo(_)»` | module `Mathlib.Probability.Distributions.Poisson.Basic` | package Mathlib | The Poisson probability distribution with rate `r`.
- `ProbabilityTheory.poissonPMFReal` | module `Mathlib.Probability.Distributions.Poisson.Basic` | package Mathlib | The pmf of the Poisson distribution depending on its rate, as a function to ℝ

### Query: `Cross Section Normalization`
- `crossProduct` | module `Mathlib.LinearAlgebra.CrossProduct` | package Mathlib | The cross product of two vectors in $R^3$ for $R$ a commutative ring.
- `cross_cross` | module `Mathlib.LinearAlgebra.CrossProduct` | package Mathlib | **Vector Triple Product Identity.** For any three vectors $u, v, w \in R^3$ over a commutative ring $R$, the iterated cross product satisfies the identity $u \times (v \times w) = u \times (v \times w) - v \times (u \...
- `jacobi_cross` | module `Mathlib.LinearAlgebra.CrossProduct` | package Mathlib | **Jacobi identity**: For a cross product of three vectors, their sum over the three even permutations is equal to the zero vector.

### Query: `cross Section Normalization Factor`
- `cross_cross` | module `Mathlib.LinearAlgebra.CrossProduct` | package Mathlib | **Vector Triple Product Identity.** For any three vectors $u, v, w \in R^3$ over a commutative ring $R$, the iterated cross product satisfies the identity $u \times (v \times w) = u \times (v \times w) - v \times (u \...
- `UniqueFactorizationMonoid.normalizedFactors` | module `Mathlib.RingTheory.UniqueFactorizationDomain.NormalizedFactors` | package Mathlib | Noncomputably determines the multiset of prime factors.
- `UniqueFactorizationMonoid.prod_normalizedFactors_eq` | module `Mathlib.RingTheory.UniqueFactorizationDomain.NormalizedFactors` | package Mathlib | **Product of Normalized Factors.** In a unique factorization monoid with strong normalization, the product of the multiset of normalized prime factors of a non-zero element $a$ is equal to the normalization of $a$.

### Query: `length Readout`
- `Computation.length` | module `Mathlib.Data.Seq.Computation` | package Mathlib | `length s` gets the number of steps of a terminating computation
- `LengthUnit.rods` | module `Physlib.SpaceAndTime.Space.LengthUnit` | package PhysLean | The length unit of a rod (5.0292 meters)
- `Cycle.length` | module `Mathlib.Data.List.Cycle` | package Mathlib | The length of the `s : Cycle α`, which is the number of elements, counting duplicates.

### Query: `area Readout`
- `DimArea` | module `Physlib.Units.WithDim.Area` | package PhysLean | The type of areas in the absence of a choice of unit.
- `HahnSeries.orderTop` | module `Mathlib.RingTheory.HahnSeries.Basic` | package Mathlib | The orderTop of a Hahn series `x` is a minimal element of `WithTop Γ` where `x` has a nonzero coefficient if `x ≠ 0`, and is `⊤` when `x = 0`.
- `DimArea.are` | module `Physlib.Units.WithDim.Area` | package PhysLean | The dimensional area corresponding to 1 are (100 square meters).

### Query: `particle Intensity Readout`
- `ClassicalMechanics.FreeParticle` | module `Physlib.ClassicalMechanics.FreeParticle.Basic` | package PhysLean | A classical free particle with positive mass. A free particle is a mechanical system evolving in the absence of external forces. The dynamics are therefore entirely determined by Newton's second law with zero force. T...
- `HahnSeries.orderTop` | module `Mathlib.RingTheory.HahnSeries.Basic` | package Mathlib | The orderTop of a Hahn series `x` is a minimal element of `WithTop Γ` where `x` has a nonzero coefficient if `x ≠ 0`, and is `⊤` when `x = 0`.
- `ClassicalMechanics.FreeParticle.velocity` | module `Physlib.ClassicalMechanics.FreeParticle.Basic` | package PhysLean | The velocity of a trajectory at a given time. This is defined as the time derivative of the position function.

## Grounded Mathlib/PhysLean names

- `Path.target` (Mathlib)
- `semiformal_result` (PhysLean)
- `stereographic_target` (Mathlib)
- `List.Vector.length` (Mathlib)
- `Computation.length` (Mathlib)
- `LengthUnit` (PhysLean)
- `DimArea` (PhysLean)
- `HahnSeries.orderTop` (Mathlib)
- `DimArea.are` (PhysLean)
- `ClassicalMechanics.FreeParticle` (PhysLean)
- `HahnSeries.orderTop` (Mathlib)
- `Real.integral_rpowIntegrand₀₁_one_pos` (Mathlib)
- `HahnSeries.orderTop` (Mathlib)
- `ProbabilityTheory.«termPo(_)»` (Mathlib)
- `ProbabilityTheory.poissonPMFReal` (Mathlib)
- `crossProduct` (Mathlib)
- `cross_cross` (Mathlib)
- `jacobi_cross` (Mathlib)
- `cross_cross` (Mathlib)
- `UniqueFactorizationMonoid.normalizedFactors` (Mathlib)
- `UniqueFactorizationMonoid.prod_normalizedFactors_eq` (Mathlib)
- `Computation.length` (Mathlib)
- `LengthUnit.rods` (PhysLean)
- `Cycle.length` (Mathlib)
- `DimArea` (PhysLean)
- `HahnSeries.orderTop` (Mathlib)
- `DimArea.are` (PhysLean)
- `ClassicalMechanics.FreeParticle` (PhysLean)
- `HahnSeries.orderTop` (Mathlib)
- `ClassicalMechanics.FreeParticle.velocity` (PhysLean)

## Local abstractions introduced

- `PhyXMiniProblems.ProblemPhyXMini0562.AnswerChoice`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMiniProblems.ProblemPhyXMini0562.AreaMagnitude`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMiniProblems.ProblemPhyXMini0562.CrossSectionNormalization`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMiniProblems.ProblemPhyXMini0562.FigureAngleLabel`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMiniProblems.ProblemPhyXMini0562.FigureLengthLabel`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMiniProblems.ProblemPhyXMini0562.FigureRay`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMiniProblems.ProblemPhyXMini0562.HardSphereScatteringFigure`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMiniProblems.ProblemPhyXMini0562.HardSphereScatteringSetup`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMiniProblems.ProblemPhyXMini0562.HasPhysicalHardSphereParameters`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMiniProblems.ProblemPhyXMini0562.LengthMagnitude`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMiniProblems.ProblemPhyXMini0562.MatchesAnswerChoice`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMiniProblems.ProblemPhyXMini0562.MatchesHardSphereScatteringScenario`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMiniProblems.ProblemPhyXMini0562.MatchesPrimaryFigure`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMiniProblems.ProblemPhyXMini0562.ParticleIntensity`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMiniProblems.ProblemPhyXMini0562.ParticleRate`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMiniProblems.ProblemPhyXMini0562.SatisfiesHardSphereContactGeometry`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMiniProblems.ProblemPhyXMini0562.SatisfiesHardSphereCrossSectionLaw`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMiniProblems.ProblemPhyXMini0562.SatisfiesSpecularReflectionLaw`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMiniProblems.ProblemPhyXMini0562.SatisfiesUniformBeamCountingLaw`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.

## Grounding gaps

- No unresolved LeanExplore grounding gaps were recorded by this preflight.
