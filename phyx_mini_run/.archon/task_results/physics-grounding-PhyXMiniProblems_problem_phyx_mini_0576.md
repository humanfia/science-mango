# Physics LeanExplore Grounding Log

- Target Lean file: `PhyXMiniProblems/problem_phyx_mini_0576.lean`
- Blueprint chapter: `blueprint/src/chapters/PhyXMiniProblems_problem_phyx_mini_0576.tex`
- Grounding status: complete
- Search backend: local
- Input fingerprint: sha256:ef36f1bc9e00e3bb0e1ffb2e30b3eabb2c72f7559e723d7315e725d965c927a6
- Packages searched: Mathlib, Physlib

## LeanExplore queries/candidates actually used

### Query: `Physics formalization target`
- `Path.target` | module `Mathlib.Topology.Path` | package Mathlib | **Target of a Path.** For a path $\gamma$ from $x$ to $y$ in a topological space, the value of the path at the endpoint of the unit interval, $\gamma(1)$, is equal to $y$.
- `semiformal_result` | module `Physlib.Meta.Informal.SemiFormal` | package PhysLean | A semiformal result is either a - definition in which the type is given but not the definition. - proof in which the proposition is given but not the proof. Semiformal results cannot be used in further code. They are...
- `stereographic_target` | module `Mathlib.Geometry.Manifold.Instances.Sphere` | package Mathlib | **Target of the Stereographic Projection.** For any unit vector $v$ in an inner product space, the target of the stereographic projection associated with $v$ is the entire codomain (the orthogonal complement of the su...

### Query: `Time Quantity`
- `Time` | module `Physlib.SpaceAndTime.Time.Basic` | package PhysLean | The type `Time` represents the time in a given (but arbitrary) set of units, and with a given (but arbitrary) choice of origin.
- `TimeUnit` | module `Physlib.SpaceAndTime.Time.TimeUnit` | package PhysLean | The choices of translationally-invariant metrics on the manifold `TimeTransMan`. Such a choice corresponds to a choice of units for time.
- `Time.eq_one_smul` | module `Physlib.SpaceAndTime.Time.Basic` | package PhysLean | **Time Representation as Scalar Multiplication.** Any element $t$ of the type `Time` is equal to the scalar multiplication of its underlying numerical value $t.val$ by the unit element $1$.

### Query: `Decay Constant Quantity`
- `LocallyConstant` | module `Mathlib.Topology.LocallyConstant.Basic` | package Mathlib | A (bundled) locally constant function from a topological space `X` to a type `Y`.
- `ClassicalMechanics.DampedHarmonicOscillator.decayRate` | module `Physlib.ClassicalMechanics.DampedHarmonicOscillator.Basic` | package PhysLean | The exponential decay rate `γ / (2 * m)`.
- `Asymptotics.SuperpolynomialDecay` | module `Mathlib.Analysis.Asymptotics.SuperpolynomialDecay` | package Mathlib | `f` has superpolynomial decay in parameter `k` along filter `l` if `k ^ n * f` tends to zero at `l` for all naturals `n`

### Query: `Activity Quantity`
- `εNFA.εClosure` | module `Mathlib.Computability.EpsilonNFA` | package Mathlib | The `εClosure` of a set is the set of states which can be reached by taking a finite string of ε-transitions from an element of the set.
- `εNFA.IsPath` | module `Mathlib.Computability.EpsilonNFA` | package Mathlib | `M.IsPath` represents a traversal in `M` from a start state to an end state by following a list of transitions in order.
- `instMulActionNNRealDimensionful` | module `Physlib.Units.Basic` | package PhysLean | **Scalar Action on Dimensionful Quantities.** For any type $M$ that carries a dimension, the set of dimensionful quantities of $M$ inherits a multiplicative action by the nonnegative real numbers $\mathbb{R}_{\ge 0}$....

### Query: `time Readout`
- `Time` | module `Physlib.SpaceAndTime.Time.Basic` | package PhysLean | The type `Time` represents the time in a given (but arbitrary) set of units, and with a given (but arbitrary) choice of origin.
- `TimeMan` | module `Physlib.SpaceAndTime.Time.TimeMan` | package PhysLean | The type `TimeMan` represents the time manifold. Mathematically `TimeMan` is a manifold diffeomorphic to `ℝ` with an orientation but no additional structure.
- `TimeUnit` | module `Physlib.SpaceAndTime.Time.TimeUnit` | package PhysLean | The choices of translationally-invariant metrics on the manifold `TimeTransMan`. Such a choice corresponds to a choice of units for time.

### Query: `decay Constant Readout`
- `LocallyConstant` | module `Mathlib.Topology.LocallyConstant.Basic` | package Mathlib | A (bundled) locally constant function from a topological space `X` to a type `Y`.
- `ClassicalMechanics.DampedHarmonicOscillator.decayRate` | module `Physlib.ClassicalMechanics.DampedHarmonicOscillator.Basic` | package PhysLean | The exponential decay rate `γ / (2 * m)`.
- `Asymptotics.SuperpolynomialDecay` | module `Mathlib.Analysis.Asymptotics.SuperpolynomialDecay` | package Mathlib | `f` has superpolynomial decay in parameter `k` along filter `l` if `k ^ n * f` tends to zero at `l` for all naturals `n`

### Query: `activity Readout`
- `ωCPO.omegaCompletePartialOrderEqualizer` | module `Mathlib.Order.Category.OmegaCompletePartialOrder` | package Mathlib | **$\omega$-Complete Partial Order on Equalizers.** Given two $\omega$-complete partial orders $\alpha$ and $\beta$ and two continuous functions $f, g: \alpha \to \beta$, the equalizer $\{ a \in \alpha \mid f(a) = g(a)...
- `ωCPO.instLargeCategory` | module `Mathlib.Order.Category.OmegaCompletePartialOrder` | package Mathlib | **The Category of $\omega$-Complete Partial Orders.** The collection of $\omega$-complete partial orders forms a large category where the morphisms between two objects are the continuous functions between them, the id...
- `ωCPO.instInhabited` | module `Mathlib.Order.Category.OmegaCompletePartialOrder` | package Mathlib | **Inhabited Category of $\omega$-Complete Partial Orders.** The type of all $\omega$-complete partial orders is inhabited, as the unit type $PUnit$ (equipped with its unique partial order) serves as an example of an $...

### Query: `time In Seconds`
- `TimeUnit.seconds` | module `Physlib.SpaceAndTime.Time.TimeUnit` | package PhysLean | The definition of a time unit of seconds.
- `Time` | module `Physlib.SpaceAndTime.Time.Basic` | package PhysLean | The type `Time` represents the time in a given (but arbitrary) set of units, and with a given (but arbitrary) choice of origin.
- `TimeUnit.hours_div_seconds` | module `Physlib.SpaceAndTime.Time.TimeUnit` | package PhysLean | **Ratio of Hours to Seconds.** The ratio of the time unit representing one hour to the time unit representing one second is equal to the non-negative real number $3600$.

### Query: `decay Constant In Per Second`
- `ClassicalMechanics.DampedHarmonicOscillator.decayRate` | module `Physlib.ClassicalMechanics.DampedHarmonicOscillator.Basic` | package PhysLean | The exponential decay rate `γ / (2 * m)`.
- `SecondCountableTopology` | module `Mathlib.Topology.Bases` | package Mathlib | A second-countable space is one with a countable basis.
- `DimSpeed.oneMeterPerSecond_in_SI` | module `Physlib.Units.WithDim.Speed` | package PhysLean | **One Meter per Second in SI Units.** In the International System of Units (SI), the value of the dimensional speed defined as one meter per second is equal to 1.

### Query: `activity In Becquerels`
- `RecursiveIn` | module `Mathlib.Computability.RecursiveIn` | package Mathlib | A partial function `f : α →. σ` between `Primcodable` types is recursive in a set of oracles `O` if its encoding as a function `ℕ →. ℕ` is `Nat.RecursiveIn O`.
- `JoinedIn` | module `Mathlib.Topology.Connected.PathConnected` | package Mathlib | The relation "being joined by a path in `F`". Not quite an equivalence relation since it's not reflexive for points that do not belong to `F`.
- `Colex.instVAdd` | module `Mathlib.Algebra.Order.Group.Synonym` | package Mathlib | **Colexicographical Power.** If there is a power operation $a^b$ defined for elements $a \in \alpha$ and $b \in \beta$, then a corresponding power operation is defined for the colexicographical transformation of $\alp...

## Grounded Mathlib/PhysLean names

- `Path.target` (Mathlib)
- `semiformal_result` (PhysLean)
- `stereographic_target` (Mathlib)
- `Time` (PhysLean)
- `TimeUnit` (PhysLean)
- `Time.eq_one_smul` (PhysLean)
- `LocallyConstant` (Mathlib)
- `ClassicalMechanics.DampedHarmonicOscillator.decayRate` (PhysLean)
- `Asymptotics.SuperpolynomialDecay` (Mathlib)
- `εNFA.εClosure` (Mathlib)
- `εNFA.IsPath` (Mathlib)
- `instMulActionNNRealDimensionful` (PhysLean)
- `Time` (PhysLean)
- `TimeMan` (PhysLean)
- `TimeUnit` (PhysLean)
- `LocallyConstant` (Mathlib)
- `ClassicalMechanics.DampedHarmonicOscillator.decayRate` (PhysLean)
- `Asymptotics.SuperpolynomialDecay` (Mathlib)
- `ωCPO.omegaCompletePartialOrderEqualizer` (Mathlib)
- `ωCPO.instLargeCategory` (Mathlib)
- `ωCPO.instInhabited` (Mathlib)
- `TimeUnit.seconds` (PhysLean)
- `Time` (PhysLean)
- `TimeUnit.hours_div_seconds` (PhysLean)
- `ClassicalMechanics.DampedHarmonicOscillator.decayRate` (PhysLean)
- `SecondCountableTopology` (Mathlib)
- `DimSpeed.oneMeterPerSecond_in_SI` (PhysLean)
- `RecursiveIn` (Mathlib)
- `JoinedIn` (Mathlib)
- `Colex.instVAdd` (Mathlib)

## Local abstractions introduced

- `PhyXMiniProblems.ProblemPhyXMini0576.ActivityQuantity`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMiniProblems.ProblemPhyXMini0576.AnswerChoice`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMiniProblems.ProblemPhyXMini0576.DecayConstantQuantity`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMiniProblems.ProblemPhyXMini0576.DecayCurveColor`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMiniProblems.ProblemPhyXMini0576.DecayCurveShape`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMiniProblems.ProblemPhyXMini0576.DecayCurveTrend`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMiniProblems.ProblemPhyXMini0576.HasPhysicalRadioactiveParameters`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMiniProblems.ProblemPhyXMini0576.IsCorrectRoundedAnswerChoice`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMiniProblems.ProblemPhyXMini0576.MatchesProblemReadouts`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMiniProblems.ProblemPhyXMini0576.MatchesSuppliedParentDecayFigure`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMiniProblems.ProblemPhyXMini0576.ParentDecayFigure`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMiniProblems.ProblemPhyXMini0576.RadioactiveDecaySetup`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMiniProblems.ProblemPhyXMini0576.RadioactiveSample`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMiniProblems.ProblemPhyXMini0576.SatisfiesRadioactiveDecayLaws`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMiniProblems.ProblemPhyXMini0576.TimeQuantity`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.

## Grounding gaps

- No unresolved LeanExplore grounding gaps were recorded by this preflight.
