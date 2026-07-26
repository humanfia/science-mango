# Physics LeanExplore Grounding Log

- Target Lean file: `PhyXMiniProblems/problem_phyx_mini_0378.lean`
- Blueprint chapter: `blueprint/src/chapters/PhyXMiniProblems_problem_phyx_mini_0378.tex`
- Grounding status: complete
- Search backend: local
- Input fingerprint: sha256:ef3021d74d096c9797eb2932c394a2e9c5fae885f616586d928556a7852b05e5
- Packages searched: Mathlib, Physlib

## LeanExplore queries/candidates actually used

### Query: `Physics formalization target`
- `Path.target` | module `Mathlib.Topology.Path` | package Mathlib | **Target of a Path.** For a path $\gamma$ from $x$ to $y$ in a topological space, the value of the path at the endpoint of the unit interval, $\gamma(1)$, is equal to $y$.
- `semiformal_result` | module `Physlib.Meta.Informal.SemiFormal` | package PhysLean | A semiformal result is either a - definition in which the type is given but not the definition. - proof in which the proposition is given but not the proof. Semiformal results cannot be used in further code. They are...
- `stereographic_target` | module `Mathlib.Geometry.Manifold.Instances.Sphere` | package Mathlib | **Target of the Stereographic Projection.** For any unit vector $v$ in an inner product space, the target of the stereographic projection associated with $v$ is the entire codomain (the orthogonal complement of the su...

### Query: `Speed Quantity`
- `DimSpeed` | module `Physlib.Units.WithDim.Speed` | package PhysLean | The type of speeds in the absence of a choice of unit.
- `HahnSeries.orderTop` | module `Mathlib.RingTheory.HahnSeries.Basic` | package Mathlib | The orderTop of a Hahn series `x` is a minimal element of `WithTop Γ` where `x` has a nonzero coefficient if `x ≠ 0`, and is `⊤` when `x = 0`.
- `UnitExamples.SpeedEq` | module `Physlib.Units.Examples` | package PhysLean | An example of dimensions corresponding to `s = d/t` using `WithDim`.

### Query: `speed Readout`
- `UnitExamples.SpeedEq` | module `Physlib.Units.Examples` | package PhysLean | An example of dimensions corresponding to `s = d/t` using `WithDim`.
- `HahnSeries.orderTop` | module `Mathlib.RingTheory.HahnSeries.Basic` | package Mathlib | The orderTop of a Hahn series `x` is a minimal element of `WithTop Γ` where `x` has a nonzero coefficient if `x ≠ 0`, and is `⊤` when `x = 0`.
- `DimSpeed` | module `Physlib.Units.WithDim.Speed` | package PhysLean | The type of speeds in the absence of a choice of unit.

### Query: `speed In Meters Per Second`
- `SecondCountableTopology` | module `Mathlib.Topology.Bases` | package Mathlib | A second-countable space is one with a countable basis.
- `DimSpeed.oneMeterPerSecond` | module `Physlib.Units.WithDim.Speed` | package PhysLean | The dimensional speed corresponding to 1 meter per second.
- `DimSpeed.oneMeterPerSecond_in_SI` | module `Physlib.Units.WithDim.Speed` | package PhysLean | **One Meter per Second in SI Units.** In the International System of Units (SI), the value of the dimensional speed defined as one meter per second is equal to 1.

### Query: `Histogram Axis`
- `HahnSeries.orderTop` | module `Mathlib.RingTheory.HahnSeries.Basic` | package Mathlib | The orderTop of a Hahn series `x` is a minimal element of `WithTop Γ` where `x` has a nonzero coefficient if `x ≠ 0`, and is `⊤` when `x = 0`.
- `RigidBody.intermediate_axis_instability` | module `Physlib.ClassicalMechanics.RigidBody.Basic` | package PhysLean | Rotations about the largest and smallest principal axes are stable under small perturbations; rotation about the intermediate axis is unstable (tennis-racket effect).
- `BoxIntegral.Box.splitUpper_eq_bot` | module `Mathlib.Analysis.BoxIntegral.Partition.Split` | package Mathlib | **Upper Split of a Box is Empty.** For a rectangular box $I$, a dimension $i$, and a coordinate $x$, the upper split of $I$ at $x$ along the $i$-th axis is empty if and only if the $i$-th coordinate of the upper bound...

### Query: `Histogram Axis Quantity`
- `HahnSeries.orderTop` | module `Mathlib.RingTheory.HahnSeries.Basic` | package Mathlib | The orderTop of a Hahn series `x` is a minimal element of `WithTop Γ` where `x` has a nonzero coefficient if `x ≠ 0`, and is `⊤` when `x = 0`.
- `RigidBody.intermediate_axis_instability` | module `Physlib.ClassicalMechanics.RigidBody.Basic` | package PhysLean | Rotations about the largest and smallest principal axes are stable under small perturbations; rotation about the intermediate axis is unstable (tennis-racket effect).
- `HahnSeries.single` | module `Mathlib.RingTheory.HahnSeries.Basic` | package Mathlib | `single a r` is the Hahn series which has coefficient `r` at `a` and zero otherwise.

### Query: `Speed Bin`
- `DimSpeed` | module `Physlib.Units.WithDim.Speed` | package PhysLean | The type of speeds in the absence of a choice of unit.
- `HahnSeries.orderTop` | module `Mathlib.RingTheory.HahnSeries.Basic` | package Mathlib | The orderTop of a Hahn series `x` is a minimal element of `WithTop Γ` where `x` has a nonzero coefficient if `x ≠ 0`, and is `⊤` when `x = 0`.
- `SpeedOfLight` | module `Physlib.Relativity.SpeedOfLight` | package PhysLean | The speed of light in a vacuum. An element of this type should be thought of as the speed of light in some chosen but arbitrary system of units.

### Query: `Bar Shade`
- `Rep.barComplex` | module `Mathlib.RepresentationTheory.Homological.Resolution` | package Mathlib | The projective resolution of `k` as a trivial `k`-linear `G`-representation with `n`th differential `(Gⁿ⁺¹ →₀ k[G]) → (Gⁿ →₀ k[G])` sending `(g₀, ..., gₙ)` to `g₀·(g₁, ..., gₙ) + ∑ (-1)ʲ⁺¹·(g₀, ..., gⱼgⱼ₊₁, ..., gₙ) +...
- `HahnSeries.orderTop` | module `Mathlib.RingTheory.HahnSeries.Basic` | package Mathlib | The orderTop of a Hahn series `x` is a minimal element of `WithTop Γ` where `x` has a nonzero coefficient if `x ≠ 0`, and is `⊤` when `x = 0`.
- `Rep.barResolution` | module `Mathlib.RepresentationTheory.Homological.Resolution` | package Mathlib | The chain complex `barComplex k G` as a projective resolution of `k` as a trivial `k`-linear `G`-representation.

### Query: `Molecular Speed Histogram`
- `HahnSeries.orderTop` | module `Mathlib.RingTheory.HahnSeries.Basic` | package Mathlib | The orderTop of a Hahn series `x` is a minimal element of `WithTop Γ` where `x` has a nonzero coefficient if `x ≠ 0`, and is `⊤` when `x = 0`.
- `DimSpeed` | module `Physlib.Units.WithDim.Speed` | package PhysLean | The type of speeds in the absence of a choice of unit.
- `HahnSeries.single` | module `Mathlib.RingTheory.HahnSeries.Basic` | package Mathlib | `single a r` is the Hahn series which has coefficient `r` at `a` and zero otherwise.

### Query: `Gas Sample Size`
- `IdealGas` | module `Physlib.StatisticalMechanics.MicroCanonicalEnsemble.IdealGas` | package PhysLean | The Hamiltonian for an ideal gas: particles live in a cube of volume V^(1/3), and each contributes an energy p^2/2. The per-particle mass is normalized to 1.
- `IdealGas.ideal_gas_law` | module `Physlib.StatisticalMechanics.MicroCanonicalEnsemble.IdealGas` | package PhysLean | The ideal gas law: PV = nRT. In our unitsless system, R = 1.
- `IdealGas.ZIntegrable` | module `Physlib.StatisticalMechanics.MicroCanonicalEnsemble.IdealGas` | package PhysLean | **Integrability of the Ideal Gas Partition Function.** For a system of $n$ particles in a volume $V > 0$ at an inverse temperature $\beta > 0$, the ideal gas Hamiltonian is $Z$-integrable. This means that the Boltzman...

## Grounded Mathlib/PhysLean names

- `Path.target` (Mathlib)
- `semiformal_result` (PhysLean)
- `stereographic_target` (Mathlib)
- `DimSpeed` (PhysLean)
- `HahnSeries.orderTop` (Mathlib)
- `UnitExamples.SpeedEq` (PhysLean)
- `UnitExamples.SpeedEq` (PhysLean)
- `HahnSeries.orderTop` (Mathlib)
- `DimSpeed` (PhysLean)
- `SecondCountableTopology` (Mathlib)
- `DimSpeed.oneMeterPerSecond` (PhysLean)
- `DimSpeed.oneMeterPerSecond_in_SI` (PhysLean)
- `HahnSeries.orderTop` (Mathlib)
- `RigidBody.intermediate_axis_instability` (PhysLean)
- `BoxIntegral.Box.splitUpper_eq_bot` (Mathlib)
- `HahnSeries.orderTop` (Mathlib)
- `RigidBody.intermediate_axis_instability` (PhysLean)
- `HahnSeries.single` (Mathlib)
- `DimSpeed` (PhysLean)
- `HahnSeries.orderTop` (Mathlib)
- `SpeedOfLight` (PhysLean)
- `Rep.barComplex` (Mathlib)
- `HahnSeries.orderTop` (Mathlib)
- `Rep.barResolution` (Mathlib)
- `HahnSeries.orderTop` (Mathlib)
- `DimSpeed` (PhysLean)
- `HahnSeries.single` (Mathlib)
- `IdealGas` (PhysLean)
- `IdealGas.ideal_gas_law` (PhysLean)
- `IdealGas.ZIntegrable` (PhysLean)

## Local abstractions introduced

- `PhyXMiniProblems.ProblemPhyXMini0378.AnswerChoice`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMiniProblems.ProblemPhyXMini0378.BarShade`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMiniProblems.ProblemPhyXMini0378.GasSampleSize`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMiniProblems.ProblemPhyXMini0378.HasNonemptyMolecularSample`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMiniProblems.ProblemPhyXMini0378.HistogramAxis`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMiniProblems.ProblemPhyXMini0378.HistogramAxisQuantity`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMiniProblems.ProblemPhyXMini0378.MatchesDisplayedChoice`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMiniProblems.ProblemPhyXMini0378.MatchesPrimaryMolecularSpeedHistogram`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMiniProblems.ProblemPhyXMini0378.MolecularGasSample`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMiniProblems.ProblemPhyXMini0378.MolecularSpeedHistogram`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMiniProblems.ProblemPhyXMini0378.SatisfiesDiscreteMolecularRmsLaw`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMiniProblems.ProblemPhyXMini0378.SpeedBin`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMiniProblems.ProblemPhyXMini0378.SpeedQuantity`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.

## Grounding gaps

- No unresolved LeanExplore grounding gaps were recorded by this preflight.
