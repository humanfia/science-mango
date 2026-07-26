# Physics LeanExplore Grounding Log

- Target Lean file: `PhyXMiniProblems/problem_phyx_mini_0531.lean`
- Blueprint chapter: `blueprint/src/chapters/PhyXMiniProblems_problem_phyx_mini_0531.tex`
- Grounding status: complete
- Search backend: local
- Input fingerprint: sha256:17b3c34386d1a8e2afa7b1a789730a9bd3cc60f727556f07a7a226103f37af5b
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

### Query: `Plane Momentum`
- `QuantumMechanics.OneDimension.planeWaveFunctional_generalized_eigenvector_momentumOperatorUnbounded` | module `Physlib.QuantumMechanics.Operators.OneDimension.Momentum` | package PhysLean | **Generalized Eigenvector of the Momentum Operator.** For any real number $k$, the plane wave functional associated with $k$ is a generalized eigenvector of the unbounded momentum operator with corresponding eigenvalu...
- `UpperHalfPlane` | module `Mathlib.Analysis.Complex.UpperHalfPlane.Basic` | package Mathlib | The open upper half plane, denoted as `ℍ` within the `UpperHalfPlane` namespace
- `Momentum` | module `Physlib.Units.WithDim.Momentum` | package PhysLean | Momentum in `d`-dimensional space in an arbitrary, but given, set of units. In `(3+1)d` space time this corresponds to `3`-momentum not `4`-momentum.

### Query: `Diagram Axis`
- `Mathlib.Tactic.Widget.elabStringDiagramCmd` | module `Mathlib.Tactic.Widget.StringDiagram` | package Mathlib | Display the string diagram for a given term. Example usage: ``` /- String diagram for the equality theorem. -/ #string_diagram MonoidalCategory.whisker_exchange /- String diagram for the morphism. -/ variable {C : Typ...
- `Sym2.IsDiag` | module `Mathlib.Data.Sym.Sym2` | package Mathlib | A predicate for testing whether an element of `Sym2 α` is on the diagonal.
- `RigidBody.intermediate_axis_instability` | module `Physlib.ClassicalMechanics.RigidBody.Basic` | package PhysLean | Rotations about the largest and smallest principal axes are stable under small perturbations; rotation about the intermediate axis is unstable (tennis-racket effect).

### Query: `to Fin`
- `finsetStx` | module `Mathlib.Data.Fintype.Sets` | package Mathlib | `finset% t` elaborates `t` as a `Finset`. If `t` is a `Set`, then inserts `Set.toFinset`. Does not make use of the expected type; useful for big operators over finsets. ``` #check finset% Finset.range 2 -- Finset Nat...
- `Finsupp.onFinset` | module `Mathlib.Data.Finsupp.Defs` | package Mathlib | `Finsupp.onFinset s f hf` is the finsupp function representing `f` restricted to the finset `s`. The function must be `0` outside of `s`. Use this when the set needs to be filtered anyways, otherwise a better set repr...
- `Set.Finite.toFinset` | module `Mathlib.Data.Set.Finite.Basic` | package Mathlib | Using choice, get the `Finset` that represents this `Set`.

### Query: `momentum Component In SI`
- `QuantumMechanics.momentumCLM` | module `Physlib.QuantumMechanics.Operators.Momentum` | package PhysLean | Component `i` of the momentum operator is the continuous linear map from `𝓢(Space d, ℂ)` to itself which maps `ψ` to `-iℏ ∂ᵢψ`.
- `Momentum` | module `Physlib.Units.WithDim.Momentum` | package PhysLean | Momentum in `d`-dimensional space in an arbitrary, but given, set of units. In `(3+1)d` space time this corresponds to `3`-momentum not `4`-momentum.
- `connectedComponentIn` | module `Mathlib.Topology.Connected.Basic` | package Mathlib | Given a set `F` in a topological space `α` and a point `x : α`, the connected component of `x` in `F` is the connected component of `x` in the subtype `F` seen as a set in `α`. This definition does not make sense if `...

### Query: `momentum Magnitude In SI`
- `Momentum` | module `Physlib.Units.WithDim.Momentum` | package PhysLean | Momentum in `d`-dimensional space in an arbitrary, but given, set of units. In `(3+1)d` space time this corresponds to `3`-momentum not `4`-momentum.
- `QuantumMechanics.momentumCLM` | module `Physlib.QuantumMechanics.Operators.Momentum` | package PhysLean | Component `i` of the momentum operator is the continuous linear map from `𝓢(Space d, ℂ)` to itself which maps `ψ` to `-iℏ ∂ᵢψ`.
- `DimArea.acre_in_SI` | module `Physlib.Units.WithDim.Area` | package PhysLean | **The Value of an Acre in SI Units.** In the International System of Units (SI), the area of one acre is defined as exactly $4046.8564224$ square meters.

### Query: `energy In Joules`
- `Finset.mulEnergy` | module `Mathlib.Combinatorics.Additive.Energy` | package Mathlib | The multiplicative energy `Eₘ[s, t]` of two finsets `s` and `t` in a group is the number of quadruples `(a₁, a₂, b₁, b₂) ∈ s × s × t × t` such that `a₁ * b₁ = a₂ * b₂`. The notation `Eₘ[s, t]` is available in scope `C...
- `Finset.addEnergy` | module `Mathlib.Combinatorics.Additive.Energy` | package Mathlib | The additive energy `E[s, t]` of two finsets `s` and `t` in a group is the number of quadruples `(a₁, a₂, b₁, b₂) ∈ s × s × t × t` such that `a₁ + b₁ = a₂ + b₂`. The notation `E[s, t]` is available in scope `Combinato...
- `DimEnergy.joule` | module `Physlib.Units.WithDim.Energy` | package PhysLean | The dimensional energy corresponding to 1 joule, J.

### Query: `energy In Mega Electron Volts`
- `DimEnergy.electronVolt` | module `Physlib.Units.WithDim.Energy` | package PhysLean | The dimensional energy corresponding to 1 electron volt, 1.602176634×10−19 J.
- `Electromagnetism.ElectromagneticPotential.electricField` | module `Physlib.Electromagnetism.Kinematics.ElectricField` | package PhysLean | The electric field from the electromagnetic potential.
- `DimEnergy` | module `Physlib.Units.WithDim.Energy` | package PhysLean | Energy as a dimensional quantity with dimension `MLT⁻2`..

### Query: `speed Of Light In Meters Per Second`
- `DimSpeed.speedOfLight_in_SI` | module `Physlib.Units.WithDim.Speed` | package PhysLean | **Value of the Speed of Light in SI Units.** The speed of light, when expressed in the International System of Units (SI), is exactly $299,792,458$.
- `SecondCountableTopology` | module `Mathlib.Topology.Bases` | package Mathlib | A second-countable space is one with a countable basis.
- `DimSpeed.oneMeterPerSecond_in_SI` | module `Physlib.Units.WithDim.Speed` | package PhysLean | **One Meter per Second in SI Units.** In the International System of Units (SI), the value of the dimensional speed defined as one meter per second is equal to 1.

## Grounded Mathlib/PhysLean names

- `EuclideanSpace` (Mathlib)
- `Space.fderiv_space_components` (PhysLean)
- `Lorentz.ContrMod.toSpace` (PhysLean)
- `Path.target` (Mathlib)
- `semiformal_result` (PhysLean)
- `stereographic_target` (Mathlib)
- `QuantumMechanics.OneDimension.planeWaveFunctional_generalized_eigenvector_momentumOperatorUnbounded` (PhysLean)
- `UpperHalfPlane` (Mathlib)
- `Momentum` (PhysLean)
- `Mathlib.Tactic.Widget.elabStringDiagramCmd` (Mathlib)
- `Sym2.IsDiag` (Mathlib)
- `RigidBody.intermediate_axis_instability` (PhysLean)
- `finsetStx` (Mathlib)
- `Finsupp.onFinset` (Mathlib)
- `Set.Finite.toFinset` (Mathlib)
- `QuantumMechanics.momentumCLM` (PhysLean)
- `Momentum` (PhysLean)
- `connectedComponentIn` (Mathlib)
- `Momentum` (PhysLean)
- `QuantumMechanics.momentumCLM` (PhysLean)
- `DimArea.acre_in_SI` (PhysLean)
- `Finset.mulEnergy` (Mathlib)
- `Finset.addEnergy` (Mathlib)
- `DimEnergy.joule` (PhysLean)
- `DimEnergy.electronVolt` (PhysLean)
- `Electromagnetism.ElectromagneticPotential.electricField` (PhysLean)
- `DimEnergy` (PhysLean)
- `DimSpeed.speedOfLight_in_SI` (PhysLean)
- `SecondCountableTopology` (Mathlib)
- `DimSpeed.oneMeterPerSecond_in_SI` (PhysLean)

## Local abstractions introduced

- `PhyXMiniProblems.ProblemPhyXMini0531.AnswerChoice`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMiniProblems.ProblemPhyXMini0531.ComptonProblemData`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMiniProblems.ProblemPhyXMini0531.ComptonScatteringSetup`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMiniProblems.ProblemPhyXMini0531.DiagramAxis`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMiniProblems.ProblemPhyXMini0531.EqualAngleComptonFigure`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMiniProblems.ProblemPhyXMini0531.FigureReadout`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMiniProblems.ProblemPhyXMini0531.IsClosestAnswerChoice`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMiniProblems.ProblemPhyXMini0531.PlaneMomentum`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMiniProblems.ProblemPhyXMini0531.SatisfiesComptonScatteringLaws`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.

## Grounding gaps

- No unresolved LeanExplore grounding gaps were recorded by this preflight.
