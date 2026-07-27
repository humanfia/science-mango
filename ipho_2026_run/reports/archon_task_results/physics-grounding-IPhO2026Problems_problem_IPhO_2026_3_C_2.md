# Physics LeanExplore Grounding Log

- Target Lean file: `IPhO2026Problems/problem_IPhO_2026_3_C_2.lean`
- Blueprint chapter: `blueprint/src/chapters/IPhO2026Problems_problem_IPhO_2026_3_C_2.tex`
- Grounding status: complete
- Search backend: local
- Input fingerprint: sha256:ae607dfb350b60ab66157488de0243f5235e6b9e4e345ad9a81680eb863bc934
- Packages searched: Mathlib, Physlib

## LeanExplore queries/candidates actually used

### Query: `Real.sqrt square root`
- `Real.sqrt` | module `Mathlib.Analysis.Real.Sqrt` | package Mathlib | The square root of a real number. This returns 0 for negative inputs. This has notation `√x`. Note that `√x⁻¹` is parsed as `√(x⁻¹)`.
- `Real.coe_sqrt` | module `Mathlib.Analysis.Real.Sqrt` | package Mathlib | **Square Root of Nonnegative Reals.** For any nonnegative real number $x$, the real-valued square root of $x$ is equal to the square root of $x$ computed in the nonnegative real numbers and then cast to a real number.
- `Real.sqrt_lt'` | module `Mathlib.Analysis.Real.Sqrt` | package Mathlib | **Strict Monotonicity of the Square Root.** For any real number $x$ and any positive real number $y$, the square root of $x$ is strictly less than $y$ if and only if $x$ is strictly less than $y^2$.

### Query: `PhysicalQuantityTypes`
- `CanonicalEnsemble.physicalProbability` | module `Physlib.StatisticalMechanics.CanonicalEnsemble.Basic` | package PhysLean | The dimensionless physical probability density. This is is the probability density w.r.t. the measure, obtained by dividing the phase space measure by the fundamental unit `h^dof`, making the probability density `ρ_ph...
- `Dimension` | module `Physlib.Units.Dimension` | package PhysLean | The foundational dimensions. Defined in the order ⟨length, time, mass, charge, temperature⟩
- `CanonicalEnsemble.physicalProbability_pos` | module `Physlib.StatisticalMechanics.CanonicalEnsemble.Basic` | package PhysLean | **Positivity of the Physical Probability in a Canonical Ensemble.** For a canonical ensemble with a non-zero underlying measure, if the Boltzmann measure at a given temperature $T$ is finite, then the physical probabi...

### Query: `SIReadout`
- `εNFA.εClosure` | module `Mathlib.Computability.EpsilonNFA` | package Mathlib | The `εClosure` of a set is the set of states which can be reached by taking a finite string of ε-transitions from an element of the set.
- `εNFA.IsPath` | module `Mathlib.Computability.EpsilonNFA` | package Mathlib | `M.IsPath` represents a traversal in `M` from a start state to an end state by following a list of transitions in order.
- `Turing.TM1to1.supportsStmt_read` | module `Mathlib.Computability.TuringMachine.PostTuringMachine` | package Mathlib | **Support of the Read Statement.** A finite set of labels $S$ supports a `read` statement if, for every possible symbol $a$ that can be read from the tape, the set $S$ supports the statement $f(a)$ that is executed af...

### Query: `TorusState`
- `torusIntegral` | module `Mathlib.MeasureTheory.Integral.TorusIntegral` | package Mathlib | The integral over a generalized torus with center `c ∈ ℂⁿ` and radius `R ∈ ℝⁿ`, defined as the `•`-product of the derivative of `torusMap` and `f (torusMap c R θ)`
- `TorusIntegrable` | module `Mathlib.MeasureTheory.Integral.TorusIntegral` | package Mathlib | A function `f : ℂⁿ → E` is integrable on the generalized torus if the function `f ∘ torusMap c R θ` is integrable on `Icc (0 : ℝⁿ) (fun _ ↦ 2 * π)`.
- `Turing.TM2to1.Λ'.ret` | module `Mathlib.Computability.TuringMachine.StackTuringMachine` | package Mathlib | **Return State of the TM2 Emulator.** The return state is a state in the Turing machine emulating a multi-stack machine, parameterized by a specific statement from the original machine's program. It signifies the phas...

### Query: `CycleLeg`
- `Equiv.Perm.SameCycle` | module `Mathlib.GroupTheory.Perm.Cycle.Basic` | package Mathlib | The equivalence relation indicating that two points are in the same cycle of a permutation.
- `SimpleGraph.cycleGraph.isCycle_cycle` | module `Mathlib.Combinatorics.SimpleGraph.CycleGraph` | package Mathlib | **The Cycle Graph is a Cycle.** For any natural number $n$, the standard walk representing the cycle in the cycle graph $C_n$ satisfies the properties of a cycle; specifically, it is a closed walk where the initial se...
- `Equiv.Perm.cycleType_def` | module `Mathlib.GroupTheory.Perm.Cycle.Type` | package Mathlib | **Definition of Cycle Type.** The cycle type of a permutation $\sigma$ is defined as the multiset of the cardinalities of the supports of its disjoint cycle factors.

### Query: `ProcessKind`
- `MeasureTheory.stoppedProcess` | module `Mathlib.Probability.Process.Stopping` | package Mathlib | Given a map `u : ι → Ω → E`, the stopped process with respect to `τ` is `u i ω` if `i ≤ τ ω`, and `u (τ ω) ω` otherwise. Intuitively, the stopped process stops evolving once the stopping time has occurred.
- `ProbabilityTheory.Kernel.densityProcess` | module `Mathlib.Probability.Kernel.Disintegration.Density` | package Mathlib | An `ℕ`-indexed martingale that is a density for `κ` with respect to `ν` on the sets in `countablePartition γ n`. Used to define its limit `ProbabilityTheory.Kernel.density`, which is a density for those kernels for al...
- `Mathlib.Tactic.Widget.StringDiagram.Kind` | module `Mathlib.Tactic.Widget.StringDiagram` | package Mathlib | The kind of the context.

### Query: `CarnotCycle`
- `Equiv.Perm.SameCycle` | module `Mathlib.GroupTheory.Perm.Cycle.Basic` | package Mathlib | The equivalence relation indicating that two points are in the same cycle of a permutation.
- `Cycle` | module `Mathlib.Data.List.Cycle` | package Mathlib | `Cycle α` is the quotient of `List α` by cyclic permutation. Duplicates are allowed.
- `SimpleGraph.cycleGraph_EulerianCircuit` | module `Mathlib.Combinatorics.SimpleGraph.CycleGraph` | package Mathlib | **Alias** of `SimpleGraph.cycleGraph.cycle`. --- The Eulerian cycle of `cycleGraph (n + 3)`

### Query: `Figure3bReadout`
- `εNFA.εClosure` | module `Mathlib.Computability.EpsilonNFA` | package Mathlib | The `εClosure` of a set is the set of states which can be reached by taking a finite string of ε-transitions from an element of the set.
- `εNFA.IsPath` | module `Mathlib.Computability.EpsilonNFA` | package Mathlib | `M.IsPath` represents a traversal in `M` from a start state to an end state by following a list of transitions in order.
- `ACCSystemCharges.Charges` | module `Physlib.QFT.AnomalyCancellation.Basic` | package PhysLean | The charges as functions from `Fin χ.numberCharges → ℚ`.

### Query: `SatisfiesParamagneticEquationOfState`
- `MSSMACC.AnomalyFreePerp.NotInLineEqSol` | module `Physlib.Particles.SuperSymmetry.MSSMNu.AnomalyCancellation.OrthogY3B3.ToSols` | package PhysLean | Those solutions which do not satisfy the condition `lineEqPropSol`.
- `adiabatic_relation_UaUbVaVb` | module `Physlib.Thermodynamics.IdealGas.Basic` | package PhysLean | Adiabatic relation in product form: If S(Ua,Va,N) = S(Ub,Vb,N) with N fixed, then (Ua/Ub)^c * (Va/Vb) = 1.
- `adiabatic_relation_log` | module `Physlib.Thermodynamics.IdealGas.Basic` | package PhysLean | Adiabatic relation in logarithmic form: If S(Ua,Va,N) = S(Ub,Vb,N) with N fixed, then c * log (Ua/Ub) + log (Va/Vb) = 0.

### Query: `SatisfiesIsothermalHeatLaw`
- `CanonicalEnsemble.heatCapacity` | module `Physlib.StatisticalMechanics.CanonicalEnsemble.Lemmas` | package PhysLean | The heat capacity (at constant volume) C_V = ∂U/∂T (as a derivWithin on T > 0).
- `ProbabilityTheory.HasGaussianLaw` | module `Mathlib.Probability.Distributions.Gaussian.HasGaussianLaw.Def` | package Mathlib | The predicate `HasGaussianLaw X P` means that under the measure `P`, `X` has a Gaussian distribution.
- `adiabatic_relation_UaUbVaVb` | module `Physlib.Thermodynamics.IdealGas.Basic` | package PhysLean | Adiabatic relation in product form: If S(Ua,Va,N) = S(Ub,Vb,N) with N fixed, then (Ua/Ub)^c * (Va/Vb) = 1.

## Grounded Mathlib/PhysLean names

- `Real.sqrt` (Mathlib)
- `Real.coe_sqrt` (Mathlib)
- `Real.sqrt_lt'` (Mathlib)
- `CanonicalEnsemble.physicalProbability` (PhysLean)
- `Dimension` (PhysLean)
- `CanonicalEnsemble.physicalProbability_pos` (PhysLean)
- `εNFA.εClosure` (Mathlib)
- `εNFA.IsPath` (Mathlib)
- `Turing.TM1to1.supportsStmt_read` (Mathlib)
- `torusIntegral` (Mathlib)
- `TorusIntegrable` (Mathlib)
- `Turing.TM2to1.Λ'.ret` (Mathlib)
- `Equiv.Perm.SameCycle` (Mathlib)
- `SimpleGraph.cycleGraph.isCycle_cycle` (Mathlib)
- `Equiv.Perm.cycleType_def` (Mathlib)
- `MeasureTheory.stoppedProcess` (Mathlib)
- `ProbabilityTheory.Kernel.densityProcess` (Mathlib)
- `Mathlib.Tactic.Widget.StringDiagram.Kind` (Mathlib)
- `Equiv.Perm.SameCycle` (Mathlib)
- `Cycle` (Mathlib)
- `SimpleGraph.cycleGraph_EulerianCircuit` (Mathlib)
- `εNFA.εClosure` (Mathlib)
- `εNFA.IsPath` (Mathlib)
- `ACCSystemCharges.Charges` (PhysLean)
- `MSSMACC.AnomalyFreePerp.NotInLineEqSol` (PhysLean)
- `adiabatic_relation_UaUbVaVb` (PhysLean)
- `adiabatic_relation_log` (PhysLean)
- `CanonicalEnsemble.heatCapacity` (PhysLean)
- `ProbabilityTheory.HasGaussianLaw` (Mathlib)
- `adiabatic_relation_UaUbVaVb` (PhysLean)

## Local abstractions introduced

- `IPhO2026Problems.IPhO2026_3_C_2.CarnotCycle`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `IPhO2026Problems.IPhO2026_3_C_2.CycleLeg`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `IPhO2026Problems.IPhO2026_3_C_2.EquationOfStateAtVertices`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `IPhO2026Problems.IPhO2026_3_C_2.Figure3bReadout`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `IPhO2026Problems.IPhO2026_3_C_2.PhysicalQuantityTypes`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `IPhO2026Problems.IPhO2026_3_C_2.ProcessKind`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `IPhO2026Problems.IPhO2026_3_C_2.SIReadout`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `IPhO2026Problems.IPhO2026_3_C_2.SatisfiesIsothermalHeatLaw`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `IPhO2026Problems.IPhO2026_3_C_2.SatisfiesParamagneticEquationOfState`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `IPhO2026Problems.IPhO2026_3_C_2.SatisfiesReversibleCarnotHeatBalance`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.
- `IPhO2026Problems.IPhO2026_3_C_2.TorusState`: blueprint-local physics/modeling abstraction; must preserve the physical role instead of erasing it to a bare scalar.

## Grounding gaps

- No unresolved LeanExplore grounding gaps were recorded by this preflight.
