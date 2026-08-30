import ArchonPhysics.PhyslibFPUTArbitraryClusterDecoherencePropagation
import ArchonPhysics.PhyslibFPUTHigherOrderSourceDefectDecomposition

/-!
# Arbitrary-cluster FPUT closure from resolved source/moment correlations

This module combines the arbitrary many-cluster telescope with the exact
nonlinear-source decomposition.  The resulting premise is the quantitative
higher-order RPA statement that is actually needed: at every prefix split,
both mixed correlations containing one full alpha-beta Hamiltonian source
insertion must be small throughout the time interval.

Pairwise mode decoherence is not among the premises and would not suffice.
All clusters live on the same coherent Hamiltonian trajectories.
-/

namespace ArchonPhysics.PhyslibFPUTArbitraryClusterSourceMomentClosure

open ArchonPhysics
open ArchonPhysics.CoerciveHamiltonianPhyslib
open ArchonPhysics.FinitePhaseMonomials
open ArchonPhysics.MassWeightedHamiltonianDynamics
open ArchonPhysics.ModalPhaseMismatch
open ArchonPhysics.PhyslibFPUTArbitraryClusterDecoherencePropagation
open ArchonPhysics.PhyslibFPUTCoercivePositiveTimeCumulantHierarchy
open ArchonPhysics.PhyslibFPUTHigherOrderClusterFactorizationPropagation
open ArchonPhysics.PhyslibFPUTHigherOrderSourceDefectDecomposition
open ArchonPhysics.PhyslibFPUTPositiveTimeCumulantHierarchy

noncomputable section

variable {I Omega : Type*}
  [Fintype I] [DecidableEq I] [Nonempty I]
  [Fintype Omega] [DecidableEq Omega]

/-- Full alpha-beta arbitrary-order propagation bound stated only in terms
of the two resolved source/moment correlation errors at every prefix split.
The error budget remains recursive so non-unit balanced cluster moments are
retained rather than normalized away. -/
theorem norm_actualFiniteCoerciveOrderedClusterFactorizationDefect_le_of_sourceMoment
    {N : Nat} [NeZero N]
    (weight : Omega → Real)
    (mass : Omega → Lattice.PositiveMassConfig N)
    (kappa beta g : Real)
    (entry : I → PhaseSign × Lattice.Site N)
    (p q : Omega → Time → HilbertConfiguration N)
    (hp : ∀ omega, Differentiable Real (p omega))
    (hq : ∀ omega, Differentiable Real (q omega))
    (hHamilton : ∀ omega,
      SatisfiesHamiltonEquations (mass omega) kappa beta g
        (p omega) (q omega))
    (homega : ∀ omega i,
      0 < modeFrequency (mass omega) (entry i).2)
    (cluster : Nat → Finset I)
    (hindex : ∀ n,
      Disjoint (orderedClusterUnion cluster n) (cluster n))
    (hzero : ∀ n,
      actualFiniteCoerciveClusterFactorizationDefect
        weight mass entry p q
          (orderedClusterUnion cluster n) (cluster n) 0 = 0)
    (time : Real) (leftEpsilon rightEpsilon : Nat → Real)
    (hleft : ∀ n, ∀ s ∈ Set.uIcc 0 time,
      ‖leftSourceMomentFactorizationDefect weight
          (actualFiniteCubicEnsemblePath mass entry p q)
          (actualFiniteCoerciveEnsembleSource
            mass kappa beta g entry q)
          (orderedClusterUnion cluster n) (cluster n) s‖ ≤
        leftEpsilon n)
    (hright : ∀ n, ∀ s ∈ Set.uIcc 0 time,
      ‖rightMomentSourceFactorizationDefect weight
          (actualFiniteCubicEnsemblePath mass entry p q)
          (actualFiniteCoerciveEnsembleSource
            mass kappa beta g entry q)
          (orderedClusterUnion cluster n) (cluster n) s‖ ≤
        rightEpsilon n)
    (count : Nat) :
    ‖actualFiniteCoerciveOrderedClusterFactorizationDefect
        weight mass entry p q cluster count time‖ ≤
      orderedClusterFactorizationErrorBound
        (actualFiniteCubicEnsembleBlockMoment weight mass entry p q)
        cluster (fun n ↦ leftEpsilon n + rightEpsilon n)
        time count := by
  apply norm_actualFiniteCoerciveOrderedClusterFactorizationDefect_le
    weight mass kappa beta g entry p q hp hq hHamilton homega
      cluster hzero time (fun n ↦ leftEpsilon n + rightEpsilon n)
  intro n s hs
  calc
    ‖actualFiniteCoerciveClusterFactorizationDefectSource
        weight mass kappa beta g entry p q
          (orderedClusterUnion cluster n) (cluster n) s‖
        ≤ ‖leftSourceMomentFactorizationDefect weight
              (actualFiniteCubicEnsemblePath mass entry p q)
              (actualFiniteCoerciveEnsembleSource
                mass kappa beta g entry q)
              (orderedClusterUnion cluster n) (cluster n) s‖ +
            ‖rightMomentSourceFactorizationDefect weight
              (actualFiniteCubicEnsemblePath mass entry p q)
              (actualFiniteCoerciveEnsembleSource
                mass kappa beta g entry q)
              (orderedClusterUnion cluster n) (cluster n) s‖ :=
      norm_actualFiniteCoerciveClusterFactorizationDefectSource_le
        weight mass kappa beta g entry p q hp hq hHamilton homega
          (hindex n) s
    _ ≤ leftEpsilon n + rightEpsilon n :=
      add_le_add (hleft n s hs) (hright n s hs)

/-- Summed fixed-order form for normalized observables.  It displays the
precise quantitative approximate-RPA requirement: the total high-order
decoherence error is the time length times the sum of all resolved prefix
source/moment errors. -/
theorem norm_actualFiniteCoerciveOrderedClusterFactorizationDefect_le_sum_of_sourceMoment
    {N : Nat} [NeZero N]
    (weight : Omega → Real)
    (mass : Omega → Lattice.PositiveMassConfig N)
    (kappa beta g : Real)
    (entry : I → PhaseSign × Lattice.Site N)
    (p q : Omega → Time → HilbertConfiguration N)
    (hp : ∀ omega, Differentiable Real (p omega))
    (hq : ∀ omega, Differentiable Real (q omega))
    (hHamilton : ∀ omega,
      SatisfiesHamiltonEquations (mass omega) kappa beta g
        (p omega) (q omega))
    (homega : ∀ omega i,
      0 < modeFrequency (mass omega) (entry i).2)
    (cluster : Nat → Finset I)
    (hindex : ∀ n,
      Disjoint (orderedClusterUnion cluster n) (cluster n))
    (hzero : ∀ n,
      actualFiniteCoerciveClusterFactorizationDefect
        weight mass entry p q
          (orderedClusterUnion cluster n) (cluster n) 0 = 0)
    (time : Real) (leftEpsilon rightEpsilon : Nat → Real)
    (hleft : ∀ n, ∀ s ∈ Set.uIcc 0 time,
      ‖leftSourceMomentFactorizationDefect weight
          (actualFiniteCubicEnsemblePath mass entry p q)
          (actualFiniteCoerciveEnsembleSource
            mass kappa beta g entry q)
          (orderedClusterUnion cluster n) (cluster n) s‖ ≤
        leftEpsilon n)
    (hright : ∀ n, ∀ s ∈ Set.uIcc 0 time,
      ‖rightMomentSourceFactorizationDefect weight
          (actualFiniteCubicEnsemblePath mass entry p q)
          (actualFiniteCoerciveEnsembleSource
            mass kappa beta g entry q)
          (orderedClusterUnion cluster n) (cluster n) s‖ ≤
        rightEpsilon n)
    (hempty : actualFiniteCubicEnsembleBlockMoment
      weight mass entry p q ∅ time = 1)
    (hmoment : ∀ n,
      ‖actualFiniteCubicEnsembleBlockMoment
        weight mass entry p q (cluster n) time‖ ≤ 1)
    (hleftNonneg : ∀ n, 0 ≤ leftEpsilon n)
    (hrightNonneg : ∀ n, 0 ≤ rightEpsilon n)
    (count : Nat) :
    ‖actualFiniteCoerciveOrderedClusterFactorizationDefect
        weight mass entry p q cluster count time‖ ≤
      (∑ n ∈ Finset.range count,
        (leftEpsilon n + rightEpsilon n)) * |time| := by
  apply le_trans
    (norm_actualFiniteCoerciveOrderedClusterFactorizationDefect_le_of_sourceMoment
      weight mass kappa beta g entry p q hp hq hHamilton homega
        cluster hindex hzero time leftEpsilon rightEpsilon
        hleft hright count)
  exact orderedClusterFactorizationErrorBound_le_sum
    (actualFiniteCubicEnsembleBlockMoment weight mass entry p q)
      cluster (fun n ↦ leftEpsilon n + rightEpsilon n) time
      hempty hmoment
      (fun n ↦ add_nonneg (hleftNonneg n) (hrightNonneg n)) count

end

end ArchonPhysics.PhyslibFPUTArbitraryClusterSourceMomentClosure
