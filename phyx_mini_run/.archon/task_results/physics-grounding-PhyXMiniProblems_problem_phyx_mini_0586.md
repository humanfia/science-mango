# Physics LeanExplore Grounding Log

- Target Lean file: `PhyXMiniProblems/problem_phyx_mini_0586.lean`
- Blueprint chapter: `blueprint/src/chapters/PhyXMiniProblems_problem_phyx_mini_0586.tex`
- Grounding status: complete
- Search backend: local
- Input fingerprint: sha256:9d6de68d1852e1dcac1a70912fb2fa4076236a76dcc8856214bbf409b342c1c3
- Packages searched: Mathlib, Physlib

## LeanExplore queries/candidates actually used

### Query: `Physics formalization target`
- `Path.target` | module `Mathlib.Topology.Path` | package Mathlib | **Target of a Path.** For a path $\gamma$ from $x$ to $y$ in a topological space, the value of the path at the endpoint of the unit interval, $\gamma(1)$, is equal to $y$.
- `semiformal_result` | module `Physlib.Meta.Informal.SemiFormal` | package PhysLean | A semiformal result is either a - definition in which the type is given but not the definition. - proof in which the proposition is given but not the proof. Semiformal results cannot be used in further code. They are...
- `stereographic_target` | module `Mathlib.Geometry.Manifold.Instances.Sphere` | package Mathlib | **Target of the Stereographic Projection.** For any unit vector $v$ in an inner product space, the target of the stereographic projection associated with $v$ is the entire codomain (the orthogonal complement of the su...

### Query: `Energy Quantity`
- `DimEnergy` | module `Physlib.Units.WithDim.Energy` | package PhysLean | Energy as a dimensional quantity with dimension `MLT⁻2`..
- `HahnSeries.orderTop` | module `Mathlib.RingTheory.HahnSeries.Basic` | package Mathlib | The orderTop of a Hahn series `x` is a minimal element of `WithTop Γ` where `x` has a nonzero coefficient if `x ≠ 0`, and is `⊤` when `x = 0`.
- `Finpartition.energy` | module `Mathlib.Combinatorics.SimpleGraph.Regularity.Energy` | package Mathlib | The energy of a partition, also known as index. Auxiliary quantity for Szemerédi's regularity lemma.

### Query: `Wavelength Quantity`
- `QuantumMechanics.OneDimension.HarmonicOscillator.one_over_ξ_sq` | module `Physlib.QuantumMechanics.HarmonicOscillator.OneDimension.Basic` | package PhysLean | **Inverse Square of the Characteristic Length.** For a quantum harmonic oscillator with mass $m$, angular frequency $\omega$, and characteristic length $\xi$, the square of the reciprocal of the characteristic length...
- `LengthUnit` | module `Physlib.SpaceAndTime.Space.LengthUnit` | package PhysLean | The choices of translationally-invariant metrics on the space-manifold. Such a choice corresponds to a choice of units for length.
- `Dimension` | module `Physlib.Units.Dimension` | package PhysLean | The foundational dimensions. Defined in the order ⟨length, time, mass, charge, temperature⟩

### Query: `energy In Electron Volts`
- `DimEnergy.electronVolt` | module `Physlib.Units.WithDim.Energy` | package PhysLean | The dimensional energy corresponding to 1 electron volt, 1.602176634×10−19 J.
- `Electromagnetism.ElectromagneticPotential.electricField` | module `Physlib.Electromagnetism.Kinematics.ElectricField` | package PhysLean | The electric field from the electromagnetic potential.
- `DimEnergy` | module `Physlib.Units.WithDim.Energy` | package PhysLean | Energy as a dimensional quantity with dimension `MLT⁻2`..

### Query: `wavelength Readout`
- `εNFA.εClosure` | module `Mathlib.Computability.EpsilonNFA` | package Mathlib | The `εClosure` of a set is the set of states which can be reached by taking a finite string of ε-transitions from an element of the set.
- `εNFA.IsPath` | module `Mathlib.Computability.EpsilonNFA` | package Mathlib | `M.IsPath` represents a traversal in `M` from a start state to an end state by following a list of transitions in order.
- `Turing.TM1to1.supportsStmt_read` | module `Mathlib.Computability.TuringMachine.PostTuringMachine` | package Mathlib | **Support of the Read Statement.** A finite set of labels $S$ supports a `read` statement if, for every possible symbol $a$ that can be read from the tape, the set $S$ supports the statement $f(a)$ that is executed af...

### Query: `wavelength In Nanometers`
- `LengthUnit.nanometers` | module `Physlib.SpaceAndTime.Space.LengthUnit` | package PhysLean | The length unit of nanometers (10⁻⁹ of a meter).
- `ComputableIn` | module `Mathlib.Computability.RecursiveIn` | package Mathlib | A total function is computable in `O` if its constant lift is recursive in `O`.
- `JoinedIn` | module `Mathlib.Topology.Connected.PathConnected` | package Mathlib | The relation "being joined by a path in `F`". Not quite an equivalence relation since it's not reflexive for points that do not belong to `F`.

### Query: `photon Energy Wavelength Constant Ev Nm`
- `DimEnergy` | module `Physlib.Units.WithDim.Energy` | package PhysLean | Energy as a dimensional quantity with dimension `MLT⁻2`..
- `LocallyConstant` | module `Mathlib.Topology.LocallyConstant.Basic` | package Mathlib | A (bundled) locally constant function from a topological space `X` to a type `Y`.
- `DimSpeed.speedOfLight` | module `Physlib.Units.WithDim.Speed` | package PhysLean | The dimensionful speed of light corresponding to 299792458 meters per second.

### Query: `Particle Species`
- `TensorSpecies.Tensor` | module `Physlib.Relativity.Tensors.Basic` | package PhysLean | The tensors associated with a list of indices of a given color `c : Fin n → C`.
- `SMCharges.toSpecies_apply_eq` | module `Physlib.Particles.StandardModel.AnomalyCancellation.Basic` | package PhysLean | **Standard Model Charge Species Component.** For any index $i \in \{0, \dots, 4\}$ and any set of charges $S$ in the Standard Model with $n$ generations, the $i$-th species of charges in $S$ is equal to the function m...
- `ClassicalMechanics.FreeParticle` | module `Physlib.ClassicalMechanics.FreeParticle.Basic` | package PhysLean | A classical free particle with positive mass. A free particle is a mechanical system evolving in the absence of external forces. The dynamics are therefore entirely determined by Newton's second law with zero force. T...

### Query: `Well Dimension`
- `Dimension` | module `Physlib.Units.Dimension` | package PhysLean | The foundational dimensions. Defined in the order ⟨length, time, mass, charge, temperature⟩
- `HasDim` | module `Physlib.Units.Basic` | package PhysLean | This typeclass indicates that there is a dimension `dim M : Dimension` associated with the type `M`.
- `Order.krullDim` | module `Mathlib.Order.KrullDimension` | package Mathlib | The **Krull dimension** of a preorder `α` is the supremum of the rightmost index of all relation series of `α` ordered by `<`. If there is no series `a₀ < a₁ < ... < aₙ` in `α`, then its Krull dimension is defined to...

### Query: `Well Depth Kind`
- `WType.depth_pos` | module `Mathlib.Data.W.Basic` | package Mathlib | **Positivity of Tree Depth.** For any well-founded tree $t$ in a $W$-type, the depth of $t$ is strictly greater than zero.
- `WellFoundedLT` | module `Mathlib.Order.RelClasses` | package Mathlib | A class for a well-founded relation `<`.
- `WType.depth` | module `Mathlib.Data.W.Basic` | package Mathlib | The depth of a finitely branching tree.

## Grounded Mathlib/PhysLean names

- `Path.target` (Mathlib)
- `semiformal_result` (PhysLean)
- `stereographic_target` (Mathlib)
- `DimEnergy` (PhysLean)
- `HahnSeries.orderTop` (Mathlib)
- `Finpartition.energy` (Mathlib)
- `QuantumMechanics.OneDimension.HarmonicOscillator.one_over_ξ_sq` (PhysLean)
- `LengthUnit` (PhysLean)
- `Dimension` (PhysLean)
- `DimEnergy.electronVolt` (PhysLean)
- `Electromagnetism.ElectromagneticPotential.electricField` (PhysLean)
- `DimEnergy` (PhysLean)
- `εNFA.εClosure` (Mathlib)
- `εNFA.IsPath` (Mathlib)
- `Turing.TM1to1.supportsStmt_read` (Mathlib)
- `LengthUnit.nanometers` (PhysLean)
- `ComputableIn` (Mathlib)
- `JoinedIn` (Mathlib)
- `DimEnergy` (PhysLean)
- `LocallyConstant` (Mathlib)
- `DimSpeed.speedOfLight` (PhysLean)
- `TensorSpecies.Tensor` (PhysLean)
- `SMCharges.toSpecies_apply_eq` (PhysLean)
- `ClassicalMechanics.FreeParticle` (PhysLean)
- `Dimension` (PhysLean)
- `HasDim` (PhysLean)
- `Order.krullDim` (Mathlib)
- `WType.depth_pos` (Mathlib)
- `WellFoundedLT` (Mathlib)
- `WType.depth` (Mathlib)

## Local abstractions introduced

- `PhyXMiniProblems.ProblemPhyXMini0586.AbsorptionFeature`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMiniProblems.ProblemPhyXMini0586.AnswerChoice`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMiniProblems.ProblemPhyXMini0586.EnergyLevelFigure`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMiniProblems.ProblemPhyXMini0586.EnergyLevelLabel`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMiniProblems.ProblemPhyXMini0586.EnergyQuantity`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMiniProblems.ProblemPhyXMini0586.FiniteWellAbsorptionSetup`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMiniProblems.ProblemPhyXMini0586.HasPhysicalFiniteWellParameters`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMiniProblems.ProblemPhyXMini0586.IsUniqueMatchingFirstExcitedEnergy`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMiniProblems.ProblemPhyXMini0586.MatchesDisplayedFirstExcitedEnergy`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMiniProblems.ProblemPhyXMini0586.MatchesFiniteOneDimensionalWellScenario`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMiniProblems.ProblemPhyXMini0586.MatchesPrimaryEnergyLevelFigure`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMiniProblems.ProblemPhyXMini0586.MatchesProblemReadouts`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMiniProblems.ProblemPhyXMini0586.ParticleSpecies`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMiniProblems.ProblemPhyXMini0586.RoundsToNearestElectronVolt`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMiniProblems.ProblemPhyXMini0586.SatisfiesFiniteWellPhotonAbsorptionLaws`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMiniProblems.ProblemPhyXMini0586.SpectralRegionKind`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMiniProblems.ProblemPhyXMini0586.WavelengthQuantity`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMiniProblems.ProblemPhyXMini0586.WellDepthKind`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMiniProblems.ProblemPhyXMini0586.WellDimension`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.

## Grounding gaps

- No unresolved LeanExplore grounding gaps were recorded by this preflight.
