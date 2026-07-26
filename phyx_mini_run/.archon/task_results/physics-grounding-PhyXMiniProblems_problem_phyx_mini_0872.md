# Physics LeanExplore Grounding Log

- Target Lean file: `PhyXMiniProblems/problem_phyx_mini_0872.lean`
- Blueprint chapter: `blueprint/src/chapters/PhyXMiniProblems_problem_phyx_mini_0872.tex`
- Grounding status: complete
- Search backend: local
- Input fingerprint: sha256:23415ff18b500db9447d06c24559d933873c187fc8c2d2540b43ec607a603aca
- Packages searched: Mathlib, Physlib

## LeanExplore queries/candidates actually used

### Query: `electric charge`
- `Electromagnetism.ElectromagneticPotential.electricField` | module `Physlib.Electromagnetism.Kinematics.ElectricField` | package PhysLean | The electric field from the electromagnetic potential.
- `ChargeUnit.elementaryCharge` | module `Physlib.Electromagnetism.Charge.ChargeUnit` | package PhysLean | The charge unit of a elementryCharge (1.602176634×10−19 coulomb).
- `Electromagnetism.ElectricField` | module `Physlib.Electromagnetism.Basic` | package PhysLean | The electric field is a map from `d`+1 dimensional spacetime to the vector space `ℝ^d`.

### Query: `Physics formalization target`
- `Path.target` | module `Mathlib.Topology.Path` | package Mathlib | **Target of a Path.** For a path $\gamma$ from $x$ to $y$ in a topological space, the value of the path at the endpoint of the unit interval, $\gamma(1)$, is equal to $y$.
- `semiformal_result` | module `Physlib.Meta.Informal.SemiFormal` | package PhysLean | A semiformal result is either a - definition in which the type is given but not the definition. - proof in which the proposition is given but not the proof. Semiformal results cannot be used in further code. They are...
- `stereographic_target` | module `Mathlib.Geometry.Manifold.Instances.Sphere` | package Mathlib | **Target of the Stereographic Projection.** For any unit vector $v$ in an inner product space, the target of the stereographic projection associated with $v$ is the entire codomain (the orthogonal complement of the su...

### Query: `energy Dimension`
- `Finset.mulEnergy` | module `Mathlib.Combinatorics.Additive.Energy` | package Mathlib | The multiplicative energy `Eₘ[s, t]` of two finsets `s` and `t` in a group is the number of quadruples `(a₁, a₂, b₁, b₂) ∈ s × s × t × t` such that `a₁ * b₁ = a₂ * b₂`. The notation `Eₘ[s, t]` is available in scope `C...
- `Finset.addEnergy` | module `Mathlib.Combinatorics.Additive.Energy` | package Mathlib | The additive energy `E[s, t]` of two finsets `s` and `t` in a group is the number of quadruples `(a₁, a₂, b₁, b₂) ∈ s × s × t × t` such that `a₁ + b₁ = a₂ + b₂`. The notation `E[s, t]` is available in scope `Combinato...
- `DimEnergy` | module `Physlib.Units.WithDim.Energy` | package PhysLean | Energy as a dimensional quantity with dimension `MLT⁻2`..

### Query: `electric Potential Difference Dimension`
- `Electromagnetism.ElectromagneticPotential.electricField` | module `Physlib.Electromagnetism.Kinematics.ElectricField` | package PhysLean | The electric field from the electromagnetic potential.
- `Dimension.C𝓭` | module `Physlib.Units.Dimension` | package PhysLean | The dimension corresponding to charge.
- `Electromagnetism.ElectromagneticPotential.electricField_eq` | module `Physlib.Electromagnetism.Kinematics.ElectricField` | package PhysLean | **Electric Field in Terms of Potentials.** For an electromagnetic potential $A$ in $d$ spatial dimensions and a given speed of light $c$, the associated electric field at time $t$ and position $x$ is equal to the nega...

### Query: `Electric Potential Difference Quantity`
- `Electromagnetism.ElectromagneticPotential.electricField` | module `Physlib.Electromagnetism.Kinematics.ElectricField` | package PhysLean | The electric field from the electromagnetic potential.
- `Electromagnetism.ElectromagneticPotential.sub_val` | module `Physlib.Electromagnetism.Kinematics.EMPotential` | package PhysLean | **Subtraction of Electromagnetic Potentials.** The value of the difference between two electromagnetic potentials is equal to the difference of their individual values.
- `Electromagnetism.ElectromagneticPotential.electricField_differentiable` | module `Physlib.Electromagnetism.Kinematics.ElectricField` | package PhysLean | **Differentiability of the Electric Field.** If an electromagnetic potential $A$ is of class $C^2$, then its associated electric field is differentiable.

### Query: `potential Difference In Volts`
- `Electromagnetism.ElectromagneticPotential.vectorPotential` | module `Physlib.Electromagnetism.Kinematics.VectorPotential` | package PhysLean | The vector potential from the electromagnetic potential.
- `Electromagnetism.ElectromagneticPotential.sub_val` | module `Physlib.Electromagnetism.Kinematics.EMPotential` | package PhysLean | **Subtraction of Electromagnetic Potentials.** The value of the difference between two electromagnetic potentials is equal to the difference of their individual values.
- `CovariantDerivative.difference` | module `Mathlib.Geometry.Manifold.VectorBundle.CovariantDerivative.Basic` | package Mathlib | The difference of two covariant derivatives, as a one-form taking values in the endomorphisms of `V`.

### Query: `Circuit Node`
- `Matroid.IsCircuit` | module `Mathlib.Combinatorics.Matroid.Circuit` | package Mathlib | `M.IsCircuit C` means that `C` is a minimal dependent set in `M`.
- `Tree.node` | module `Mathlib.Data.Tree.Basic` | package Mathlib | **Alias** of `BinaryTree.node`.
- `Ordnode.node'` | module `Mathlib.Data.Ordmap.Ordnode` | package Mathlib | **Internal use only** O(1). Construct a node with the correct size information, without rebalancing.

### Query: `Directed Voltage Edge`
- `DirectedOn` | module `Mathlib.Order.Directed` | package Mathlib | A subset of `α` is directed if there is an element of the set `≼`-above any pair of elements in the set.
- `Directed` | module `Mathlib.Order.Directed` | package Mathlib | A family of elements of `α` is directed (with respect to a relation `≼` on `α`) if there is a member of the family `≼`-above any pair in the family.
- `Mathlib.Tactic.Order.Edge` | module `Mathlib.Tactic.Order.Graph.Basic` | package Mathlib | An edge in a graph. In the `order` tactic, the `proof` field stores the of `atoms[src] ≤ atoms[dst]`.

### Query: `initial Node`
- `Ordinal.isInitial_zero` | module `Mathlib.SetTheory.Cardinal.Aleph` | package Mathlib | **The Initiality of Zero.** The ordinal $0$ is an initial ordinal.
- `CategoryTheory.Limits.IsInitial` | module `Mathlib.CategoryTheory.Limits.Shapes.IsTerminal` | package Mathlib | `X` is initial if the cocone it induces on the empty diagram is colimiting.
- `Ordnode.node` | module `Mathlib.Data.Ordmap.Ordnode` | package Mathlib | **Ordered Tree Node.** An internal node of an ordered tree structure, consisting of a natural number representing the total size of the subtree, a left subtree, a central value of type $\alpha$, and a right subtree.

### Query: `final Node`
- `CategoryTheory.Functor.Final` | module `Mathlib.CategoryTheory.Limits.Final` | package Mathlib | A functor `F : C ⥤ D` is final if for every `d : D`, the comma category of morphisms `d ⟶ F.obj c` is connected.
- `Ordnode.node'` | module `Mathlib.Data.Ordmap.Ordnode` | package Mathlib | **Internal use only** O(1). Construct a node with the correct size information, without rebalancing.
- `Ordnode.node` | module `Mathlib.Data.Ordmap.Ordnode` | package Mathlib | **Ordered Tree Node.** An internal node of an ordered tree structure, consisting of a natural number representing the total size of the subtree, a left subtree, a central value of type $\alpha$, and a right subtree.

## Grounded Mathlib/PhysLean names

- `Electromagnetism.ElectromagneticPotential.electricField` (PhysLean)
- `ChargeUnit.elementaryCharge` (PhysLean)
- `Electromagnetism.ElectricField` (PhysLean)
- `Path.target` (Mathlib)
- `semiformal_result` (PhysLean)
- `stereographic_target` (Mathlib)
- `Finset.mulEnergy` (Mathlib)
- `Finset.addEnergy` (Mathlib)
- `DimEnergy` (PhysLean)
- `Electromagnetism.ElectromagneticPotential.electricField` (PhysLean)
- `Dimension.C𝓭` (PhysLean)
- `Electromagnetism.ElectromagneticPotential.electricField_eq` (PhysLean)
- `Electromagnetism.ElectromagneticPotential.electricField` (PhysLean)
- `Electromagnetism.ElectromagneticPotential.sub_val` (PhysLean)
- `Electromagnetism.ElectromagneticPotential.electricField_differentiable` (PhysLean)
- `Electromagnetism.ElectromagneticPotential.vectorPotential` (PhysLean)
- `Electromagnetism.ElectromagneticPotential.sub_val` (PhysLean)
- `CovariantDerivative.difference` (Mathlib)
- `Matroid.IsCircuit` (Mathlib)
- `Tree.node` (Mathlib)
- `Ordnode.node'` (Mathlib)
- `DirectedOn` (Mathlib)
- `Directed` (Mathlib)
- `Mathlib.Tactic.Order.Edge` (Mathlib)
- `Ordinal.isInitial_zero` (Mathlib)
- `CategoryTheory.Limits.IsInitial` (Mathlib)
- `Ordnode.node` (Mathlib)
- `CategoryTheory.Functor.Final` (Mathlib)
- `Ordnode.node'` (Mathlib)
- `Ordnode.node` (Mathlib)

## Local abstractions introduced

- `PhyXMiniProblems.ProblemPhyXMini0872.AnswerChoice`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMiniProblems.ProblemPhyXMini0872.CircuitNode`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMiniProblems.ProblemPhyXMini0872.DirectedVoltageEdge`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMiniProblems.ProblemPhyXMini0872.DirectedVoltageLoopFigure`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMiniProblems.ProblemPhyXMini0872.DirectedVoltageLoopSetup`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMiniProblems.ProblemPhyXMini0872.ElectricPotentialDifferenceQuantity`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMiniProblems.ProblemPhyXMini0872.FigureNodePlacement`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMiniProblems.ProblemPhyXMini0872.MatchesSuppliedDirectedVoltageFigure`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMiniProblems.ProblemPhyXMini0872.SatisfiesClosedLoopVoltageLaw`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.

## Grounding gaps

- No unresolved LeanExplore grounding gaps were recorded by this preflight.
