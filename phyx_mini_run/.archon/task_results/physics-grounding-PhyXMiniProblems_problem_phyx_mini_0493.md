# Physics LeanExplore Grounding Log

- Target Lean file: `PhyXMiniProblems/problem_phyx_mini_0493.lean`
- Blueprint chapter: `blueprint/src/chapters/PhyXMiniProblems_problem_phyx_mini_0493.tex`
- Grounding status: complete
- Search backend: local
- Input fingerprint: sha256:f97ad16253bf014a27800698eb639e58fd199db17510141cae8f7dfbd6dcd4db
- Packages searched: Mathlib, Physlib

## LeanExplore queries/candidates actually used

### Query: `Physics formalization target`
- `Path.target` | module `Mathlib.Topology.Path` | package Mathlib | **Target of a Path.** For a path $\gamma$ from $x$ to $y$ in a topological space, the value of the path at the endpoint of the unit interval, $\gamma(1)$, is equal to $y$.
- `semiformal_result` | module `Physlib.Meta.Informal.SemiFormal` | package PhysLean | A semiformal result is either a - definition in which the type is given but not the definition. - proof in which the proposition is given but not the proof. Semiformal results cannot be used in further code. They are...
- `stereographic_target` | module `Mathlib.Geometry.Manifold.Instances.Sphere` | package Mathlib | **Target of the Stereographic Projection.** For any unit vector $v$ in an inner product space, the target of the stereographic projection associated with $v$ is the entire codomain (the orthogonal complement of the su...

### Query: `Absolute Temperature Quantity`
- `TemperatureUnit.absoluteFahrenheit` | module `Physlib.Thermodynamics.Temperature.TemperatureUnits` | package PhysLean | The temperature unit of degrees fahrenheit ((5/9) of a kelvin). Note, this is fahrenheit starting at `0` absolute temperature.
- `Temperature` | module `Physlib.Thermodynamics.Temperature.Basic` | package PhysLean | The type `Temperature` represents the temperature in a given (but arbitrary) set of units (preserving zero). It currently wraps `ℝ≥0`, i.e., absolute temperature in nonnegative reals.
- `TemperatureUnit` | module `Physlib.Thermodynamics.Temperature.TemperatureUnits` | package PhysLean | The choices of translationally-invariant metrics on the temperature-manifold. Such a choice corresponds to a choice of units for temperature.

### Query: `temperature In Kelvins`
- `Temperature` | module `Physlib.Thermodynamics.Temperature.Basic` | package PhysLean | The type `Temperature` represents the temperature in a given (but arbitrary) set of units (preserving zero). It currently wraps `ℝ≥0`, i.e., absolute temperature in nonnegative reals.
- `Constants.kB` | module `Physlib.StatisticalMechanics.BoltzmannConstant` | package PhysLean | The Boltzmann constant in a given but arbitrary set of units. Boltzman's constant has dimension equivalent to `Energy/Temperature`.
- `UnitChoices.SI_temperature` | module `Physlib.Units.Basic` | package PhysLean | **SI Temperature Unit.** In the International System of Units (SI), the designated unit for temperature is the kelvin.

### Query: `Thermodynamic Device Role`
- `CanonicalEnsemble.thermodynamicEntropy_def` | module `Physlib.StatisticalMechanics.CanonicalEnsemble.Basic` | package PhysLean | **Definition of Thermodynamic Entropy.** For a canonical ensemble $\mathcal{C}$ at temperature $T$, the thermodynamic entropy is defined as the product of the negative Boltzmann constant $-k_B$ and the integral of the...
- `HahnSeries.orderTop` | module `Mathlib.RingTheory.HahnSeries.Basic` | package Mathlib | The orderTop of a Hahn series `x` is a minimal element of `WithTop Γ` where `x` has a nonzero coefficient if `x ≠ 0`, and is `⊤` when `x = 0`.
- `CanonicalEnsemble.thermodynamicEntropy` | module `Physlib.StatisticalMechanics.CanonicalEnsemble.Basic` | package PhysLean | The absolute thermodynamic entropy, defined from its statistical mechanical foundation as the Gibbs-Shannon entropy of the dimensionless physical probability distribution. This corresponds to Landau & Lifshitz, Statis...

### Query: `Heat Engine Model`
- `CanonicalEnsemble.heatCapacity` | module `Physlib.StatisticalMechanics.CanonicalEnsemble.Lemmas` | package PhysLean | The heat capacity (at constant volume) C_V = ∂U/∂T (as a derivWithin on T > 0).
- `modelWithCornersSelf` | module `Mathlib.Geometry.Manifold.IsManifold.Basic` | package Mathlib | A vector space is a model with corners, denoted as `𝓘(𝕜, E)` within the `Manifold` namespace.
- `CanonicalEnsemble.heatCapacity_eq_deriv_meanEnergyBeta` | module `Physlib.StatisticalMechanics.CanonicalEnsemble.Lemmas` | package PhysLean | Relates C_V = dU/dT to dU/dβ. C_V = dU/dβ * (-1/(kB T²)).

### Query: `Reservoir`
- `εNFA.εClosure` | module `Mathlib.Computability.EpsilonNFA` | package Mathlib | The `εClosure` of a set is the set of states which can be reached by taking a finite string of ε-transitions from an element of the set.
- `εNFA.IsPath` | module `Mathlib.Computability.EpsilonNFA` | package Mathlib | `M.IsPath` represents a traversal in `M` from a start state to an end state by following a list of transitions in order.
- `ValuativeRel.«term𝓀[_]»` | module `Mathlib.Topology.Algebra.Valued.ValuativeRel` | package Mathlib | The residue field of a local ring is the quotient of the ring by its maximal ideal.

### Query: `Reservoir Substance`
- `Mathlib.Tactic.Widget.StringDiagram.addConstructor` | module `Mathlib.Tactic.Widget.StringDiagram` | package Mathlib | Add constructor `tp v := nm (vs)` to the substance program.
- `IsLocalRing.ResidueField` | module `Mathlib.RingTheory.LocalRing.ResidueField.Defs` | package Mathlib | The residue field of a local ring is the quotient of the ring by its maximal ideal.
- `εNFA.εClosure` | module `Mathlib.Computability.EpsilonNFA` | package Mathlib | The `εClosure` of a set is the set of states which can be reached by taking a finite string of ε-transitions from an element of the set.

### Query: `Cryogenic Vessel Mark`
- `HahnSeries.orderTop` | module `Mathlib.RingTheory.HahnSeries.Basic` | package Mathlib | The orderTop of a Hahn series `x` is a minimal element of `WithTop Γ` where `x` has a nonzero coefficient if `x ≠ 0`, and is `⊤` when `x = 0`.
- `HahnSeries.single` | module `Mathlib.RingTheory.HahnSeries.Basic` | package Mathlib | `single a r` is the Hahn series which has coefficient `r` at `a` and zero otherwise.
- `HahnSeries.order` | module `Mathlib.RingTheory.HahnSeries.Basic` | package Mathlib | The order of a nonzero Hahn series `x` is a minimal element of `Γ` where `x` has a nonzero coefficient, the order of 0 is 0.

### Query: `Cryogenic Facility Figure`
- `Mathlib.Tactic.Widget.mkCommDiag` | module `Mathlib.Tactic.Widget.CommDiag` | package Mathlib | Construct a commutative diagram from a Penrose `sub`stance program and expressions `embeds` to display as labels in the diagram.
- `εNFA.εClosure` | module `Mathlib.Computability.EpsilonNFA` | package Mathlib | The `εClosure` of a set is the set of states which can be reached by taking a finite string of ε-transitions from an element of the set.
- `εNFA.IsPath` | module `Mathlib.Computability.EpsilonNFA` | package Mathlib | `M.IsPath` represents a traversal in `M` from a start state to an end state by following a list of transitions in order.

### Query: `Ambient Nitrogen Carnot Setup`
- `HahnSeries.orderTop` | module `Mathlib.RingTheory.HahnSeries.Basic` | package Mathlib | The orderTop of a Hahn series `x` is a minimal element of `WithTop Γ` where `x` has a nonzero coefficient if `x ≠ 0`, and is `⊤` when `x = 0`.
- `Mathlib.Notation3.setupLCtx` | module `Mathlib.Util.Notation3` | package Mathlib | Adds all the names in `boundNames` to the local context with types that are fresh metavariables. This is used for example when initializing `p` in `(scoped p => ...)` when elaborating `...`.
- `HahnSeries.single` | module `Mathlib.RingTheory.HahnSeries.Basic` | package Mathlib | `single a r` is the Hahn series which has coefficient `r` at `a` and zero otherwise.

## Grounded Mathlib/PhysLean names

- `Path.target` (Mathlib)
- `semiformal_result` (PhysLean)
- `stereographic_target` (Mathlib)
- `TemperatureUnit.absoluteFahrenheit` (PhysLean)
- `Temperature` (PhysLean)
- `TemperatureUnit` (PhysLean)
- `Temperature` (PhysLean)
- `Constants.kB` (PhysLean)
- `UnitChoices.SI_temperature` (PhysLean)
- `CanonicalEnsemble.thermodynamicEntropy_def` (PhysLean)
- `HahnSeries.orderTop` (Mathlib)
- `CanonicalEnsemble.thermodynamicEntropy` (PhysLean)
- `CanonicalEnsemble.heatCapacity` (PhysLean)
- `modelWithCornersSelf` (Mathlib)
- `CanonicalEnsemble.heatCapacity_eq_deriv_meanEnergyBeta` (PhysLean)
- `εNFA.εClosure` (Mathlib)
- `εNFA.IsPath` (Mathlib)
- `ValuativeRel.«term𝓀[_]»` (Mathlib)
- `Mathlib.Tactic.Widget.StringDiagram.addConstructor` (Mathlib)
- `IsLocalRing.ResidueField` (Mathlib)
- `εNFA.εClosure` (Mathlib)
- `HahnSeries.orderTop` (Mathlib)
- `HahnSeries.single` (Mathlib)
- `HahnSeries.order` (Mathlib)
- `Mathlib.Tactic.Widget.mkCommDiag` (Mathlib)
- `εNFA.εClosure` (Mathlib)
- `εNFA.IsPath` (Mathlib)
- `HahnSeries.orderTop` (Mathlib)
- `Mathlib.Notation3.setupLCtx` (Mathlib)
- `HahnSeries.single` (Mathlib)

## Local abstractions introduced

- `PhyXMiniProblems.ProblemPhyXMini0493.AbsoluteTemperatureQuantity`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMiniProblems.ProblemPhyXMini0493.AmbientNitrogenCarnotSetup`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMiniProblems.ProblemPhyXMini0493.AnswerChoice`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMiniProblems.ProblemPhyXMini0493.CryogenicFacilityFigure`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMiniProblems.ProblemPhyXMini0493.CryogenicVesselMark`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMiniProblems.ProblemPhyXMini0493.HasPhysicalCarnotParameters`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMiniProblems.ProblemPhyXMini0493.HeatEngineModel`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMiniProblems.ProblemPhyXMini0493.MatchesPrimaryCryogenicFigure`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMiniProblems.ProblemPhyXMini0493.MatchesProblemStatement`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMiniProblems.ProblemPhyXMini0493.Reservoir`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMiniProblems.ProblemPhyXMini0493.ReservoirSubstance`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMiniProblems.ProblemPhyXMini0493.SatisfiesCarnotEfficiencyLaw`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMiniProblems.ProblemPhyXMini0493.ThermodynamicDeviceRole`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.

## Grounding gaps

- No unresolved LeanExplore grounding gaps were recorded by this preflight.
