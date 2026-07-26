# Physics LeanExplore Grounding Log

- Target Lean file: `PhyXMiniProblems/problem_phyx_mini_0877.lean`
- Blueprint chapter: `blueprint/src/chapters/PhyXMiniProblems_problem_phyx_mini_0877.tex`
- Grounding status: complete
- Search backend: local
- Input fingerprint: sha256:0598659bc7b10d69696e500c84e22eb311211e09fa0f4cb8fa29fbba7c0456d3
- Packages searched: Mathlib, Physlib

## LeanExplore queries/candidates actually used

### Query: `Physics formalization target`
- `Path.target` | module `Mathlib.Topology.Path` | package Mathlib | **Target of a Path.** For a path $\gamma$ from $x$ to $y$ in a topological space, the value of the path at the endpoint of the unit interval, $\gamma(1)$, is equal to $y$.
- `semiformal_result` | module `Physlib.Meta.Informal.SemiFormal` | package PhysLean | A semiformal result is either a - definition in which the type is given but not the definition. - proof in which the proposition is given but not the proof. Semiformal results cannot be used in further code. They are...
- `stereographic_target` | module `Mathlib.Geometry.Manifold.Instances.Sphere` | package Mathlib | **Target of the Stereographic Projection.** For any unit vector $v$ in an inner product space, the target of the stereographic projection associated with $v$ is the entire codomain (the orthogonal complement of the su...

### Query: `potential Difference Dimension`
- `Electromagnetism.ElectromagneticPotential.instSub` | module `Physlib.Electromagnetism.Kinematics.EMPotential` | package PhysLean | **Subtraction of Electromagnetic Potentials.** For a given dimension $d$, the difference between two electromagnetic potentials $A$ and $B$ is defined pointwise, such that $(A - B)(x) = A(x) - B(x)$ for all $x$.
- `Electromagnetism.ElectromagneticPotential.vectorPotential` | module `Physlib.Electromagnetism.Kinematics.VectorPotential` | package PhysLean | The vector potential from the electromagnetic potential.
- `QuantumMechanics.OneDimension.ReflectionlessPotential.reflectionlessPotential` | module `Physlib.QuantumMechanics.ReflectionlessPotential.Basic` | package PhysLean | Define the reflectionless potential as V(x) = - (ℏ^2 * κ^2 * N * (N + 1)) / (2 * m * (cosh (κ * x)) ^ 2) -

### Query: `capacitance Dimension`
- `Dimension` | module `Physlib.Units.Dimension` | package PhysLean | The foundational dimensions. Defined in the order ⟨length, time, mass, charge, temperature⟩
- `SSet.HasDimensionLT` | module `Mathlib.AlgebraicTopology.SimplicialSet.Dimension` | package Mathlib | A simplicial set `X` has dimension `< d` iff for any `n : ℕ` such that `d ≤ n`, all `n`-simplices are degenerate.
- `Dimension.C𝓭` | module `Physlib.Units.Dimension` | package PhysLean | The dimension corresponding to charge.

### Query: `Capacitance Quantity`
- `ACCSystemCharges.Charges` | module `Physlib.QFT.AnomalyCancellation.Basic` | package PhysLean | The charges as functions from `Fin χ.numberCharges → ℚ`.
- `εNFA.εClosure` | module `Mathlib.Computability.EpsilonNFA` | package Mathlib | The `εClosure` of a set is the set of states which can be reached by taking a finite string of ε-transitions from an element of the set.
- `Dimension.div_charge` | module `Physlib.Units.Dimension` | package PhysLean | **Charge of a Quotient of Dimensions.** The electric charge of the quotient of two dimensions is equal to the difference between the electric charge of the numerator and the electric charge of the denominator.

### Query: `capacitance Readout`
- `εNFA.εClosure` | module `Mathlib.Computability.EpsilonNFA` | package Mathlib | The `εClosure` of a set is the set of states which can be reached by taking a finite string of ε-transitions from an element of the set.
- `εNFA.IsPath` | module `Mathlib.Computability.EpsilonNFA` | package Mathlib | `M.IsPath` represents a traversal in `M` from a start state to an end state by following a list of transitions in order.
- `εNFA.evalFrom` | module `Mathlib.Computability.EpsilonNFA` | package Mathlib | `M.evalFrom S x` computes all possible paths through `M` with input `x` starting at an element of `S`.

### Query: `capacitance In Farads`
- `RecursiveIn` | module `Mathlib.Computability.RecursiveIn` | package Mathlib | A partial function `f : α →. σ` between `Primcodable` types is recursive in a set of oracles `O` if its encoding as a function `ℕ →. ℕ` is `Nat.RecursiveIn O`.
- `Electromagnetism.FreeSpace.c` | module `Physlib.Electromagnetism.Dynamics.Basic` | package PhysLean | The speed of light in free space.
- `Electromagnetism.EMSystem.coulombConstant` | module `Physlib.Electromagnetism.Basic` | package PhysLean | Coulomb's constant.

### Query: `capacitance In Microfarads`
- `RecursiveIn` | module `Mathlib.Computability.RecursiveIn` | package Mathlib | A partial function `f : α →. σ` between `Primcodable` types is recursive in a set of oracles `O` if its encoding as a function `ℕ →. ℕ` is `Nat.RecursiveIn O`.
- `JoinedIn` | module `Mathlib.Topology.Connected.PathConnected` | package Mathlib | The relation "being joined by a path in `F`". Not quite an equivalence relation since it's not reflexive for points that do not belong to `F`.
- `TimeUnit.microseconds` | module `Physlib.SpaceAndTime.Time.TimeUnit` | package PhysLean | The time unit of microseconds (10⁻⁶ of a second).

### Query: `Capacitor Label`
- `HahnSeries.orderTop` | module `Mathlib.RingTheory.HahnSeries.Basic` | package Mathlib | The orderTop of a Hahn series `x` is a minimal element of `WithTop Γ` where `x` has a nonzero coefficient if `x ≠ 0`, and is `⊤` when `x = 0`.
- `MonadCont.Label` | module `Mathlib.Control.Monad.Cont` | package Mathlib | **Continuation Label.** A continuation label is a structure that encapsulates a function mapping values of type $\alpha$ to computations in a monad $m$ that produce values of type $\beta$.
- `Quiver.Labelling` | module `Mathlib.Combinatorics.Quiver.Subquiver` | package Mathlib | An `L`-labelling of a quiver assigns to every arrow an element of `L`.

### Query: `Circuit Node`
- `Matroid.IsCircuit` | module `Mathlib.Combinatorics.Matroid.Circuit` | package Mathlib | `M.IsCircuit C` means that `C` is a minimal dependent set in `M`.
- `Tree.node` | module `Mathlib.Data.Tree.Basic` | package Mathlib | **Alias** of `BinaryTree.node`.
- `Ordnode.node'` | module `Mathlib.Data.Ordmap.Ordnode` | package Mathlib | **Internal use only** O(1). Construct a node with the correct size information, without rebalancing.

### Query: `Battery Terminal`
- `Symbol.terminal` | module `Mathlib.Computability.Language` | package Mathlib | Terminal symbols (of the same type as the language)
- `CategoryTheory.Limits.IsTerminal` | module `Mathlib.CategoryTheory.Limits.Shapes.IsTerminal` | package Mathlib | `X` is terminal if the cone it induces on the empty diagram is limiting.
- `CategoryTheory.Limits.terminal` | module `Mathlib.CategoryTheory.Limits.Shapes.Terminal` | package Mathlib | An arbitrary choice of terminal object, if one exists. You can use the notation `⊤_ C`. This object is characterized by having a unique morphism from any object.

## Grounded Mathlib/PhysLean names

- `Path.target` (Mathlib)
- `semiformal_result` (PhysLean)
- `stereographic_target` (Mathlib)
- `Electromagnetism.ElectromagneticPotential.instSub` (PhysLean)
- `Electromagnetism.ElectromagneticPotential.vectorPotential` (PhysLean)
- `QuantumMechanics.OneDimension.ReflectionlessPotential.reflectionlessPotential` (PhysLean)
- `Dimension` (PhysLean)
- `SSet.HasDimensionLT` (Mathlib)
- `Dimension.C𝓭` (PhysLean)
- `ACCSystemCharges.Charges` (PhysLean)
- `εNFA.εClosure` (Mathlib)
- `Dimension.div_charge` (PhysLean)
- `εNFA.εClosure` (Mathlib)
- `εNFA.IsPath` (Mathlib)
- `εNFA.evalFrom` (Mathlib)
- `RecursiveIn` (Mathlib)
- `Electromagnetism.FreeSpace.c` (PhysLean)
- `Electromagnetism.EMSystem.coulombConstant` (PhysLean)
- `RecursiveIn` (Mathlib)
- `JoinedIn` (Mathlib)
- `TimeUnit.microseconds` (PhysLean)
- `HahnSeries.orderTop` (Mathlib)
- `MonadCont.Label` (Mathlib)
- `Quiver.Labelling` (Mathlib)
- `Matroid.IsCircuit` (Mathlib)
- `Tree.node` (Mathlib)
- `Ordnode.node'` (Mathlib)
- `Symbol.terminal` (Mathlib)
- `CategoryTheory.Limits.IsTerminal` (Mathlib)
- `CategoryTheory.Limits.terminal` (Mathlib)

## Local abstractions introduced

- `PhyXMiniProblems.ProblemPhyXMini0877.AnswerChoice`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMiniProblems.ProblemPhyXMini0877.AnswerMatchesEquivalentCapacitance`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMiniProblems.ProblemPhyXMini0877.BatteryTerminal`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMiniProblems.ProblemPhyXMini0877.CapacitanceQuantity`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMiniProblems.ProblemPhyXMini0877.CapacitorLabel`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMiniProblems.ProblemPhyXMini0877.CapacitorModel`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMiniProblems.ProblemPhyXMini0877.CircuitNode`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMiniProblems.ProblemPhyXMini0877.HasPositiveCircuitCapacitances`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMiniProblems.ProblemPhyXMini0877.MatchesIdealThreeCapacitorScenario`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMiniProblems.ProblemPhyXMini0877.MatchesSeriesParallelTopology`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMiniProblems.ProblemPhyXMini0877.MatchesSuppliedThreeCapacitorFigure`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMiniProblems.ProblemPhyXMini0877.SatisfiesIdealCapacitorCombinationLaws`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMiniProblems.ProblemPhyXMini0877.ThreeCapacitorCircuitFigure`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMiniProblems.ProblemPhyXMini0877.ThreeCapacitorCircuitSetup`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMiniProblems.ProblemPhyXMini0877.VoltageSourceModel`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.

## Grounding gaps

- No unresolved LeanExplore grounding gaps were recorded by this preflight.
