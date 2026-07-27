# Physics LeanExplore Grounding Log

- Target Lean file: `IPhO2026Problems/problem_IPhO_2026_3_C_5.lean`
- Blueprint chapter: `blueprint/src/chapters/IPhO2026Problems_problem_IPhO_2026_3_C_5.tex`
- Grounding status: complete
- Search backend: local
- Input fingerprint: sha256:0823507d82cd6ef207b6fd6577d119dc0ee6f12761b5afecd4e1b56def3dc45b
- Packages searched: Mathlib, Physlib

## LeanExplore queries/candidates actually used

### Query: `CycleState`
- `Stream'.cycleG` | module `Mathlib.Data.Stream.Defs` | package Mathlib | An auxiliary definition for `Stream'.cycle` corecursive def
- `Equiv.Perm.SameCycle` | module `Mathlib.GroupTheory.Perm.Cycle.Basic` | package Mathlib | The equivalence relation indicating that two points are in the same cycle of a permutation.
- `Cycle` | module `Mathlib.Data.List.Cycle` | package Mathlib | `Cycle α` is the quotient of `List α` by cyclic permutation. Duplicates are allowed.

### Query: `CycleLeg`
- `Equiv.Perm.SameCycle` | module `Mathlib.GroupTheory.Perm.Cycle.Basic` | package Mathlib | The equivalence relation indicating that two points are in the same cycle of a permutation.
- `SimpleGraph.cycleGraph.isCycle_cycle` | module `Mathlib.Combinatorics.SimpleGraph.CycleGraph` | package Mathlib | **The Cycle Graph is a Cycle.** For any natural number $n$, the standard walk representing the cycle in the cycle graph $C_n$ satisfies the properties of a cycle; specifically, it is a closed walk where the initial se...
- `Equiv.Perm.cycleType_def` | module `Mathlib.GroupTheory.Perm.Cycle.Type` | package Mathlib | **Definition of Cycle Type.** The cycle type of a permutation $\sigma$ is defined as the multiset of the cardinalities of the supports of its disjoint cycle factors.

### Query: `CycleLeg.startState`
- `Stream'.cycleG` | module `Mathlib.Data.Stream.Defs` | package Mathlib | An auxiliary definition for `Stream'.cycle` corecursive def
- `SimpleGraph.cycleGraph.isCycle_cycle` | module `Mathlib.Combinatorics.SimpleGraph.CycleGraph` | package Mathlib | **The Cycle Graph is a Cycle.** For any natural number $n$, the standard walk representing the cycle in the cycle graph $C_n$ satisfies the properties of a cycle; specifically, it is a closed walk where the initial se...
- `Cycle` | module `Mathlib.Data.List.Cycle` | package Mathlib | `Cycle α` is the quotient of `List α` by cyclic permutation. Duplicates are allowed.

### Query: `CycleLeg.endState`
- `Stream'.cycleG` | module `Mathlib.Data.Stream.Defs` | package Mathlib | An auxiliary definition for `Stream'.cycle` corecursive def
- `Equiv.Perm.IsCycle` | module `Mathlib.GroupTheory.Perm.Cycle.Basic` | package Mathlib | A cycle is a non-identity permutation where any two nonfixed points of the permutation are related by repeated application of the permutation.
- `SimpleGraph.cycleGraph.isCycle_cycle` | module `Mathlib.Combinatorics.SimpleGraph.CycleGraph` | package Mathlib | **The Cycle Graph is a Cycle.** For any natural number $n$, the standard walk representing the cycle in the cycle graph $C_n$ satisfies the properties of a cycle; specifically, it is a closed walk where the initial se...

### Query: `MagneticCarnotCycle`
- `Electromagnetism.MagneticField` | module `Physlib.Electromagnetism.Basic` | package PhysLean | The magnetic field is a map from `d+1` dimensional spacetime to the vector space `ℝ^d`.
- `Electromagnetism.ElectromagneticPotential.magneticFieldMatrix` | module `Physlib.Electromagnetism.Kinematics.MagneticField` | package PhysLean | The matrix corresponding to the magnetic field in general dimensions. In `3` space-dimensions this reduces to a vector.
- `MagmaCat.instCoeSortType` | module `Mathlib.Algebra.Category.Semigrp.Basic` | package Mathlib | **Coercion from MagmaCat to Type.** There is a natural coercion from the category of magmas to the category of types, which maps each magma object to its underlying carrier set.

### Query: `FollowsFigureThreeB`
- `Cubic.b_eq_three_roots` | module `Mathlib.Algebra.CubicDiscriminant` | package Mathlib | **Vieta's Formula for the Second Coefficient of a Cubic.** Let $P$ be a cubic polynomial with coefficients $a, b, c, d$. If the leading coefficient $a$ is non-zero and the image of $P$ under a ring homomorphism $\phi$...
- `ThreeGPFree` | module `Mathlib.Combinatorics.Additive.AP.Three.Defs` | package Mathlib | A set is **3GP-free** if it does not contain any non-trivial geometric progression of length three.
- `ThreeAPFree` | module `Mathlib.Combinatorics.Additive.AP.Three.Defs` | package Mathlib | A set is **3AP-free** if it does not contain any non-trivial arithmetic progression of length three. This is also sometimes called a **non-averaging set** or **Salem-Spencer set**.

### Query: `SatisfiesParamagneticEquationOfState`
- `MSSMACC.AnomalyFreePerp.NotInLineEqSol` | module `Physlib.Particles.SuperSymmetry.MSSMNu.AnomalyCancellation.OrthogY3B3.ToSols` | package PhysLean | Those solutions which do not satisfy the condition `lineEqPropSol`.
- `adiabatic_relation_UaUbVaVb` | module `Physlib.Thermodynamics.IdealGas.Basic` | package PhysLean | Adiabatic relation in product form: If S(Ua,Va,N) = S(Ub,Vb,N) with N fixed, then (Ua/Ub)^c * (Va/Vb) = 1.
- `adiabatic_relation_log` | module `Physlib.Thermodynamics.IdealGas.Basic` | package PhysLean | Adiabatic relation in logarithmic form: If S(Ua,Va,N) = S(Ub,Vb,N) with N fixed, then c * log (Ua/Ub) + log (Va/Vb) = 0.

### Query: `SatisfiesIsothermalHeatRelation`
- `CanonicalEnsemble.heatCapacity` | module `Physlib.StatisticalMechanics.CanonicalEnsemble.Lemmas` | package PhysLean | The heat capacity (at constant volume) C_V = ∂U/∂T (as a derivWithin on T > 0).
- `adiabatic_relation_UaUbVaVb` | module `Physlib.Thermodynamics.IdealGas.Basic` | package PhysLean | Adiabatic relation in product form: If S(Ua,Va,N) = S(Ub,Vb,N) with N fixed, then (Ua/Ub)^c * (Va/Vb) = 1.
- `adiabatic_relation_log` | module `Physlib.Thermodynamics.IdealGas.Basic` | package PhysLean | Adiabatic relation in logarithmic form: If S(Ua,Va,N) = S(Ub,Vb,N) with N fixed, then c * log (Ua/Ub) + log (Va/Vb) = 0.

### Query: `HasPhysicalCycleParameters`
- `Equiv.Perm.SameCycle` | module `Mathlib.GroupTheory.Perm.Cycle.Basic` | package Mathlib | The equivalence relation indicating that two points are in the same cycle of a permutation.
- `Equiv.Perm.OnCycleFactors.cycleType_kerParam_apply_apply` | module `Mathlib.GroupTheory.Perm.Centralizer` | package Mathlib | **Cycle Type of the Kernel Parameterization.** For a permutation $g$ of a finite set, the cycle type of the image of a pair $(k, v)$ under the kernel parameterization map $\text{kerParam}$ is equal to the cycle type o...
- `CanonicalEnsemble.physicalProbability` | module `Physlib.StatisticalMechanics.CanonicalEnsemble.Basic` | package PhysLean | The dimensionless physical probability density. This is is the probability density w.r.t. the measure, obtained by dividing the phase space measure by the fundamental unit `h^dof`, making the probability density `ρ_ph...

### Query: `CoolingRun`
- `Computation.run` | module `Mathlib.Data.Seq.Computation` | package Mathlib | `run c` is an unsound meta function that runs `c` to completion, possibly resulting in an infinite loop in the VM.
- `ContT.run` | module `Mathlib.Control.Monad.Cont` | package Mathlib | Run a `ContT` with a provided callback.
- `WriterT.run` | module `Mathlib.Control.Monad.Writer` | package Mathlib | **Writer Transformer Execution.** The execution of a writer monad transformer action, which transforms a computation of type `WriterT ω M α` into an action in the underlying monad `M` that returns a pair consisting of...

## Grounded Mathlib/PhysLean names

- `Stream'.cycleG` (Mathlib)
- `Equiv.Perm.SameCycle` (Mathlib)
- `Cycle` (Mathlib)
- `Equiv.Perm.SameCycle` (Mathlib)
- `SimpleGraph.cycleGraph.isCycle_cycle` (Mathlib)
- `Equiv.Perm.cycleType_def` (Mathlib)
- `Stream'.cycleG` (Mathlib)
- `SimpleGraph.cycleGraph.isCycle_cycle` (Mathlib)
- `Cycle` (Mathlib)
- `Stream'.cycleG` (Mathlib)
- `Equiv.Perm.IsCycle` (Mathlib)
- `SimpleGraph.cycleGraph.isCycle_cycle` (Mathlib)
- `Electromagnetism.MagneticField` (PhysLean)
- `Electromagnetism.ElectromagneticPotential.magneticFieldMatrix` (PhysLean)
- `MagmaCat.instCoeSortType` (Mathlib)
- `Cubic.b_eq_three_roots` (Mathlib)
- `ThreeGPFree` (Mathlib)
- `ThreeAPFree` (Mathlib)
- `MSSMACC.AnomalyFreePerp.NotInLineEqSol` (PhysLean)
- `adiabatic_relation_UaUbVaVb` (PhysLean)
- `adiabatic_relation_log` (PhysLean)
- `CanonicalEnsemble.heatCapacity` (PhysLean)
- `adiabatic_relation_UaUbVaVb` (PhysLean)
- `adiabatic_relation_log` (PhysLean)
- `Equiv.Perm.SameCycle` (Mathlib)
- `Equiv.Perm.OnCycleFactors.cycleType_kerParam_apply_apply` (Mathlib)
- `CanonicalEnsemble.physicalProbability` (PhysLean)
- `Computation.run` (Mathlib)
- `ContT.run` (Mathlib)
- `WriterT.run` (Mathlib)

## Local abstractions introduced

- `IPhO2026Problems.IPhO2026_3_C_5.CoolingRun`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `IPhO2026Problems.IPhO2026_3_C_5.CycleLeg`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `IPhO2026Problems.IPhO2026_3_C_5.CycleState`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `IPhO2026Problems.IPhO2026_3_C_5.FollowsFigureThreeB`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `IPhO2026Problems.IPhO2026_3_C_5.HasPhysicalCycleParameters`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `IPhO2026Problems.IPhO2026_3_C_5.MagneticCarnotCycle`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `IPhO2026Problems.IPhO2026_3_C_5.SatisfiesIsothermalHeatRelation`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `IPhO2026Problems.IPhO2026_3_C_5.SatisfiesParamagneticEquationOfState`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.

## Grounding gaps

- No unresolved LeanExplore grounding gaps were recorded by this preflight.
