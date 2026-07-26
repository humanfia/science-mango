# Physics LeanExplore Grounding Log

- Target Lean file: `PhyXMiniProblems/problem_phyx_mini_0542.lean`
- Blueprint chapter: `blueprint/src/chapters/PhyXMiniProblems_problem_phyx_mini_0542.tex`
- Grounding status: complete
- Search backend: local
- Input fingerprint: sha256:f3d5a3c021ce51aa16af19a4a108c9af4cabeff0466601be0df2b202b916606b
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

### Query: `Spin Outcome`
- `HahnSeries.orderTop` | module `Mathlib.RingTheory.HahnSeries.Basic` | package Mathlib | The orderTop of a Hahn series `x` is a minimal element of `WithTop Γ` where `x` has a nonzero coefficient if `x ≠ 0`, and is `⊤` when `x = 0`.
- `spinGroup.mem_even` | module `Mathlib.LinearAlgebra.CliffordAlgebra.SpinGroup` | package Mathlib | **Elements of the Spin Group are Even.** Every element of the spin group associated with a quadratic form $Q$ is contained within the even subalgebra of the corresponding Clifford algebra.
- `spinGroup` | module `Mathlib.LinearAlgebra.CliffordAlgebra.SpinGroup` | package Mathlib | `spinGroup Q` is defined as the infimum of `pinGroup Q` and `CliffordAlgebra.even Q`. See `mem_iff`.

### Query: `opposite`
- `MulOpposite` | module `Mathlib.Algebra.Opposites` | package Mathlib | Multiplicative opposite of a type. This type inherits all additive structures on `α` and reverses left and right in multiplication.
- `Opposite` | module `Mathlib.Data.Opposite` | package Mathlib | The type of objects of the opposite of `α`; used to define the opposite category. Now that Lean 4 supports definitional eta equality for records, both `unop (op X) = X` and `op (unop X) = X` are definitional equalities.
- `Set.unop_op` | module `Mathlib.Data.Set.Opposite` | package Mathlib | **Opposite of the Unopposite Set.** For any set $s$ of elements in the opposite type $\alpha^{\text{op}}$, taking the opposite of its corresponding set in $\alpha$ (the "unopposite" set) returns the original set $s$.

### Query: `Particle Spin`
- `spinGroup.mem_pin` | module `Mathlib.LinearAlgebra.CliffordAlgebra.SpinGroup` | package Mathlib | **Inclusion of the Spin Group in the Pin Group.** Every element of the spin group of a quadratic form $Q$ is also an element of the corresponding pin group.
- `HahnSeries.orderTop` | module `Mathlib.RingTheory.HahnSeries.Basic` | package Mathlib | The orderTop of a Hahn series `x` is a minimal element of `WithTop Γ` where `x` has a nonzero coefficient if `x ≠ 0`, and is `⊤` when `x = 0`.
- `spinGroup` | module `Mathlib.LinearAlgebra.CliffordAlgebra.SpinGroup` | package Mathlib | `spinGroup Q` is defined as the infimum of `pinGroup Q` and `CliffordAlgebra.even Q`. See `mem_iff`.

### Query: `Spin Axis`
- `spinGroup.star_mem_iff` | module `Mathlib.LinearAlgebra.CliffordAlgebra.SpinGroup` | package Mathlib | An element is in `spinGroup Q` if and only if `star x` is in `spinGroup Q`. See `star_mem` for only one direction.
- `Orientation.rotation` | module `Mathlib.Geometry.Euclidean.Angle.Oriented.Rotation` | package Mathlib | A rotation by the oriented angle `θ`.
- `spinGroup` | module `Mathlib.LinearAlgebra.CliffordAlgebra.SpinGroup` | package Mathlib | `spinGroup Q` is defined as the infimum of `pinGroup Q` and `CliffordAlgebra.even Q`. See `mem_iff`.

### Query: `dimensionless Pauli Observable`
- `PauliMatrix.pauliMatrix` | module `Physlib.Relativity.PauliMatrices.Basic` | package PhysLean | The Pauli matrices.
- `PauliMatrix.pauliCo_eq_ofRat` | module `Physlib.Relativity.PauliMatrices.ToTensor` | package PhysLean | **Pauli Matrix Tensor Components.** The components of the Pauli matrix tensor $\sigma_{\mu \alpha \dot{\beta}}$ are given by the rational complex numbers defined as follows: if the index $\mu = 0$, the component is $1...
- `PauliMatrix.toTensor_eq_ofRat` | module `Physlib.Relativity.PauliMatrices.ToTensor` | package PhysLean | **Tensor Representation of Pauli Matrices.** The tensor representation of the Pauli matrices $\sigma$ is given by the rational-valued function of its indices $b$ defined as follows: * If $b_0 = 0$ and $b_1 = b_2$, the...

### Query: `Analyzer Axis Label`
- `RigidBody.intermediate_axis_instability` | module `Physlib.ClassicalMechanics.RigidBody.Basic` | package PhysLean | Rotations about the largest and smallest principal axes are stable under small perturbations; rotation about the intermediate axis is unstable (tennis-racket effect).
- `HahnSeries.orderTop` | module `Mathlib.RingTheory.HahnSeries.Basic` | package Mathlib | The orderTop of a Hahn series `x` is a minimal element of `WithTop Γ` where `x` has a nonzero coefficient if `x ≠ 0`, and is `⊤` when `x = 0`.
- `RigidBody.parallel_axis_theorem` | module `Physlib.ClassicalMechanics.RigidBody.Basic` | package PhysLean | If I_O is the inertia tensor about a point O, then the inertia tensor about a parallel point O' displaced by a is I_{O'} = I_O + M(|a|² 1 − a ⊗ a). This is the parallel-axis theorem.

### Query: `Stern Gerlach Analyzer`
- `εNFA.εClosure` | module `Mathlib.Computability.EpsilonNFA` | package Mathlib | The `εClosure` of a set is the set of states which can be reached by taking a finite string of ε-transitions from an element of the set.
- `εNFA.IsPath` | module `Mathlib.Computability.EpsilonNFA` | package Mathlib | `M.IsPath` represents a traversal in `M` from a start state to an end state by following a list of transitions in order.
- `ACCSystemCharges.Charges` | module `Physlib.QFT.AnomalyCancellation.Basic` | package PhysLean | The charges as functions from `Fin χ.numberCharges → ℚ`.

### Query: `Stern Gerlach Experiment`
- `εNFA.εClosure` | module `Mathlib.Computability.EpsilonNFA` | package Mathlib | The `εClosure` of a set is the set of states which can be reached by taking a finite string of ε-transitions from an element of the set.
- `Stirling.stirlingSeq_one` | module `Mathlib.Analysis.SpecialFunctions.Stirling` | package Mathlib | **First Term of the Stirling Sequence.** The first term of the Stirling sequence, $stirlingSeq(1)$, is equal to $e / \sqrt{2}$.
- `εNFA.IsPath` | module `Mathlib.Computability.EpsilonNFA` | package Mathlib | `M.IsPath` represents a traversal in `M` from a start state to an end state by following a list of transitions in order.

## Grounded Mathlib/PhysLean names

- `EuclideanSpace` (Mathlib)
- `Space.fderiv_space_components` (PhysLean)
- `Lorentz.ContrMod.toSpace` (PhysLean)
- `Path.target` (Mathlib)
- `semiformal_result` (PhysLean)
- `stereographic_target` (Mathlib)
- `HahnSeries.orderTop` (Mathlib)
- `spinGroup.mem_even` (Mathlib)
- `spinGroup` (Mathlib)
- `MulOpposite` (Mathlib)
- `Opposite` (Mathlib)
- `Set.unop_op` (Mathlib)
- `spinGroup.mem_pin` (Mathlib)
- `HahnSeries.orderTop` (Mathlib)
- `spinGroup` (Mathlib)
- `spinGroup.star_mem_iff` (Mathlib)
- `Orientation.rotation` (Mathlib)
- `spinGroup` (Mathlib)
- `PauliMatrix.pauliMatrix` (PhysLean)
- `PauliMatrix.pauliCo_eq_ofRat` (PhysLean)
- `PauliMatrix.toTensor_eq_ofRat` (PhysLean)
- `RigidBody.intermediate_axis_instability` (PhysLean)
- `HahnSeries.orderTop` (Mathlib)
- `RigidBody.parallel_axis_theorem` (PhysLean)
- `εNFA.εClosure` (Mathlib)
- `εNFA.IsPath` (Mathlib)
- `ACCSystemCharges.Charges` (PhysLean)
- `εNFA.εClosure` (Mathlib)
- `Stirling.stirlingSeq_one` (Mathlib)
- `εNFA.IsPath` (Mathlib)

## Local abstractions introduced

- `PhyXMiniProblems.ProblemPhyXMini0542.AnalyzerAxisLabel`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMiniProblems.ProblemPhyXMini0542.AnswerChoice`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMiniProblems.ProblemPhyXMini0542.IsCorrectAnswer`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMiniProblems.ProblemPhyXMini0542.MatchesSpinHalfScenario`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMiniProblems.ProblemPhyXMini0542.MatchesSuppliedThreeAnalyzerFigure`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMiniProblems.ProblemPhyXMini0542.ParticleSpin`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMiniProblems.ProblemPhyXMini0542.SatisfiesSequentialFilteringLaw`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMiniProblems.ProblemPhyXMini0542.SecondAnalyzerGeometry`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMiniProblems.ProblemPhyXMini0542.SpinAxis`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMiniProblems.ProblemPhyXMini0542.SpinHalfBornRule`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMiniProblems.ProblemPhyXMini0542.SpinOutcome`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMiniProblems.ProblemPhyXMini0542.SternGerlachAnalyzer`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `PhyXMiniProblems.ProblemPhyXMini0542.SternGerlachExperiment`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.

## Grounding gaps

- No unresolved LeanExplore grounding gaps were recorded by this preflight.
