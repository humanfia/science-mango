# Physics LeanExplore Grounding Log

- Target Lean file: `PhyXMiniProblems/problem_phyx_mini_0637.lean`
- Blueprint chapter: `blueprint/src/chapters/PhyXMiniProblems_problem_phyx_mini_0637.tex`
- Grounding status: complete
- Search backend: local
- Input fingerprint: sha256:ab9bb05bed4dad5e0b7cfd0a729c0286d6ee4e14e06de275a98dfed4e9236476
- Packages searched: Mathlib, Physlib

## LeanExplore queries/candidates actually used

### Query: `Physics formalization target`
- `Path.target` | module `Mathlib.Topology.Path` | package Mathlib | **Target of a Path.** For a path $\gamma$ from $x$ to $y$ in a topological space, the value of the path at the endpoint of the unit interval, $\gamma(1)$, is equal to $y$.
- `semiformal_result` | module `Physlib.Meta.Informal.SemiFormal` | package PhysLean | A semiformal result is either a - definition in which the type is given but not the definition. - proof in which the proposition is given but not the proof. Semiformal results cannot be used in further code. They are...
- `stereographic_target` | module `Mathlib.Geometry.Manifold.Instances.Sphere` | package Mathlib | **Target of the Stereographic Projection.** For any unit vector $v$ in an inner product space, the target of the stereographic projection associated with $v$ is the entire codomain (the orthogonal complement of the su...

### Query: `Wavelength Quantity`
- `QuantumMechanics.OneDimension.HarmonicOscillator.one_over_ξ_sq` | module `Physlib.QuantumMechanics.HarmonicOscillator.OneDimension.Basic` | package PhysLean | **Inverse Square of the Characteristic Length.** For a quantum harmonic oscillator with mass $m$, angular frequency $\omega$, and characteristic length $\xi$, the square of the reciprocal of the characteristic length...
- `LengthUnit` | module `Physlib.SpaceAndTime.Space.LengthUnit` | package PhysLean | The choices of translationally-invariant metrics on the space-manifold. Such a choice corresponds to a choice of units for length.
- `Dimension` | module `Physlib.Units.Dimension` | package PhysLean | The foundational dimensions. Defined in the order ⟨length, time, mass, charge, temperature⟩

### Query: `energy In Joules`
- `Finset.mulEnergy` | module `Mathlib.Combinatorics.Additive.Energy` | package Mathlib | The multiplicative energy `Eₘ[s, t]` of two finsets `s` and `t` in a group is the number of quadruples `(a₁, a₂, b₁, b₂) ∈ s × s × t × t` such that `a₁ * b₁ = a₂ * b₂`. The notation `Eₘ[s, t]` is available in scope `C...
- `Finset.addEnergy` | module `Mathlib.Combinatorics.Additive.Energy` | package Mathlib | The additive energy `E[s, t]` of two finsets `s` and `t` in a group is the number of quadruples `(a₁, a₂, b₁, b₂) ∈ s × s × t × t` such that `a₁ + b₁ = a₂ + b₂`. The notation `E[s, t]` is available in scope `Combinato...
- `DimEnergy.joule` | module `Physlib.Units.WithDim.Energy` | package PhysLean | The dimensional energy corresponding to 1 joule, J.

### Query: `energy In Electron Volts`
- `DimEnergy.electronVolt` | module `Physlib.Units.WithDim.Energy` | package PhysLean | The dimensional energy corresponding to 1 electron volt, 1.602176634×10−19 J.
- `Electromagnetism.ElectromagneticPotential.electricField` | module `Physlib.Electromagnetism.Kinematics.ElectricField` | package PhysLean | The electric field from the electromagnetic potential.
- `DimEnergy` | module `Physlib.Units.WithDim.Energy` | package PhysLean | Energy as a dimensional quantity with dimension `MLT⁻2`..

### Query: `wavelength Readout`
- `εNFA.εClosure` | module `Mathlib.Computability.EpsilonNFA` | package Mathlib | The `εClosure` of a set is the set of states which can be reached by taking a finite string of ε-transitions from an element of the set.
- `εNFA.IsPath` | module `Mathlib.Computability.EpsilonNFA` | package Mathlib | `M.IsPath` represents a traversal in `M` from a start state to an end state by following a list of transitions in order.
- `Turing.TM1to1.supportsStmt_read` | module `Mathlib.Computability.TuringMachine.PostTuringMachine` | package Mathlib | **Support of the Read Statement.** A finite set of labels $S$ supports a `read` statement if, for every possible symbol $a$ that can be read from the tape, the set $S$ supports the statement $f(a)$ that is executed af...

### Query: `wavelength In Meters`
- `LengthUnit.meters` | module `Physlib.SpaceAndTime.Space.LengthUnit` | package PhysLean | The definition of a length unit of meters.
- `LengthUnit` | module `Physlib.SpaceAndTime.Space.LengthUnit` | package PhysLean | The choices of translationally-invariant metrics on the space-manifold. Such a choice corresponds to a choice of units for length.
- `LengthUnit.lightYears` | module `Physlib.SpaceAndTime.Space.LengthUnit` | package PhysLean | The length unit of a light year (9,460,730,472,580,800 meters).

### Query: `wavelength In Nanometers`
- `LengthUnit.nanometers` | module `Physlib.SpaceAndTime.Space.LengthUnit` | package PhysLean | The length unit of nanometers (10⁻⁹ of a meter).
- `ComputableIn` | module `Mathlib.Computability.RecursiveIn` | package Mathlib | A total function is computable in `O` if its constant lift is recursive in `O`.
- `JoinedIn` | module `Mathlib.Topology.Connected.PathConnected` | package Mathlib | The relation "being joined by a path in `F`". Not quite an equivalence relation since it's not reflexive for points that do not belong to `F`.

### Query: `planck Times Light In Electron Volt Nanometers`
- `LightProfinite` | module `Mathlib.Topology.Category.LightProfinite.Basic` | package Mathlib | `LightProfinite` is the category of second countable profinite spaces.
- `DimEnergy.electronVolt` | module `Physlib.Units.WithDim.Energy` | package PhysLean | The dimensional energy corresponding to 1 electron volt, 1.602176634×10−19 J.
- `Constants.ℏ` | module `Physlib.QuantumMechanics.PlanckConstant` | package PhysLean | The value of the reduced Planck's constant in units of J.s.

### Query: `Figure Text Label`
- `MonadCont.Label` | module `Mathlib.Control.Monad.Cont` | package Mathlib | **Continuation Label.** A continuation label is a structure that encapsulates a function mapping values of type $\alpha$ to computations in a monad $m$ that produce values of type $\beta$.
- `StateT.mkLabel` | module `Mathlib.Control.Monad.Cont` | package Mathlib | **State Monad Transformer Label Mapping.** Given a continuation label that maps a pair consisting of a value and a state to a computation in a base monad, this construction defines a corresponding label for the state...
- `WriterT.mkLabel` | module `Mathlib.Control.Monad.Cont` | package Mathlib | **Writer Monad Transformer Label Mapping.** Given a type $\omega$ with an empty collection element, a continuation label for computations in a monad $m$ that accepts a pair $(a, w) \in \alpha \times \omega$ can be tra...

### Query: `Transition Arrow`
- `StateTransition.FRespects` | module `Mathlib.Computability.StateTransition` | package Mathlib | A simpler version of `Respects` when the state transition relation `tr` is a function.
- `CategoryTheory.Arrow` | module `Mathlib.CategoryTheory.Comma.Arrow` | package Mathlib | The arrow category of `T` has as objects all morphisms in `T` and as morphisms commutative squares in `T`.
- `StateTransition.Reaches` | module `Mathlib.Computability.StateTransition` | package Mathlib | The reflexive transitive closure of a state transition function. `Reaches f a b` means there is a finite sequence of steps `f a = some a₁`, `f a₁ = some a₂`, ... such that `aₙ = b`. This relation permits zero steps of...

## Grounded Mathlib/PhysLean names

- `Path.target` (Mathlib)
- `semiformal_result` (PhysLean)
- `stereographic_target` (Mathlib)
- `QuantumMechanics.OneDimension.HarmonicOscillator.one_over_ξ_sq` (PhysLean)
- `LengthUnit` (PhysLean)
- `Dimension` (PhysLean)
- `Finset.mulEnergy` (Mathlib)
- `Finset.addEnergy` (Mathlib)
- `DimEnergy.joule` (PhysLean)
- `DimEnergy.electronVolt` (PhysLean)
- `Electromagnetism.ElectromagneticPotential.electricField` (PhysLean)
- `DimEnergy` (PhysLean)
- `εNFA.εClosure` (Mathlib)
- `εNFA.IsPath` (Mathlib)
- `Turing.TM1to1.supportsStmt_read` (Mathlib)
- `LengthUnit.meters` (PhysLean)
- `LengthUnit` (PhysLean)
- `LengthUnit.lightYears` (PhysLean)
- `LengthUnit.nanometers` (PhysLean)
- `ComputableIn` (Mathlib)
- `JoinedIn` (Mathlib)
- `LightProfinite` (Mathlib)
- `DimEnergy.electronVolt` (PhysLean)
- `Constants.ℏ` (PhysLean)
- `MonadCont.Label` (Mathlib)
- `StateT.mkLabel` (Mathlib)
- `WriterT.mkLabel` (Mathlib)
- `StateTransition.FRespects` (Mathlib)
- `CategoryTheory.Arrow` (Mathlib)
- `StateTransition.Reaches` (Mathlib)

## Local abstractions introduced

- `PhyXMiniProblems.ProblemPhyXMini0637.AnswerChoice`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMiniProblems.ProblemPhyXMini0637.FigureTextLabel`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMiniProblems.ProblemPhyXMini0637.HasPhysicalHydrogenFluorescenceParameters`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMiniProblems.ProblemPhyXMini0637.HydrogenFluorescenceFigure`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMiniProblems.ProblemPhyXMini0637.HydrogenFluorescenceSetup`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMiniProblems.ProblemPhyXMini0637.IsUniqueClosestDisplayedWavelength`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMiniProblems.ProblemPhyXMini0637.IsUniqueClosestPostAbsorptionLevel`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMiniProblems.ProblemPhyXMini0637.MatchesAbsorbedPhotonMeasurement`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMiniProblems.ProblemPhyXMini0637.MatchesHydrogenFluorescenceScenario`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMiniProblems.ProblemPhyXMini0637.MatchesSuppliedFluorescenceFigure`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMiniProblems.ProblemPhyXMini0637.RoundsToDisplayedWavelength`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMiniProblems.ProblemPhyXMini0637.SatisfiesHydrogenFluorescenceLaws`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMiniProblems.ProblemPhyXMini0637.TransitionArrow`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMiniProblems.ProblemPhyXMini0637.UsesRoundedAbsorptionLevelIdentification`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMiniProblems.ProblemPhyXMini0637.UsesStandardHydrogenReferenceData`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMiniProblems.ProblemPhyXMini0637.WavelengthQuantity`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.

## Grounding gaps

- No unresolved LeanExplore grounding gaps were recorded by this preflight.
