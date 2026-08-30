import ArchonPhysics.PhyslibFPUTArbitraryClusterSourceMomentClosure
import ArchonPhysics.PhyslibFPUTSourceInsertionClusterExpansion

/-!
# Actual coercive FPUT cluster closure resolved by nonlinear source slots

The exact higher-order source defect of a cluster split can be resolved one
step further than a mixed source/moment correlation: it is the sum of the
ordinary factorization defects obtained by inserting the verified full
alpha-beta Hamiltonian source in one displayed slot.

The final theorem propagates arbitrary many-cluster factorization from bounds
on those individual slot defects.  Thus the remaining long-time input is no
longer an abstract RPA error.  It is a finite family of concrete correlations
on the same Hamiltonian trajectories, suitable for a garden/recollision
expansion.  No independence, re-Haarization, Markov approximation, decay, or
kinetic limit is assumed here.
-/

namespace ArchonPhysics.PhyslibFPUTActualClusterSourceSlotClosure

open ArchonPhysics
open ArchonPhysics.CoerciveHamiltonianPhyslib
open ArchonPhysics.FinitePhaseMonomials
open ArchonPhysics.MassWeightedHamiltonianDynamics
open ArchonPhysics.ModalPhaseMismatch
open ArchonPhysics.PhyslibFPUTArbitraryClusterDecoherencePropagation
open ArchonPhysics.PhyslibFPUTArbitraryClusterSourceMomentClosure
open ArchonPhysics.PhyslibFPUTCoercivePositiveTimeCumulantHierarchy
open ArchonPhysics.PhyslibFPUTHigherOrderClusterFactorizationPropagation
open ArchonPhysics.PhyslibFPUTHigherOrderSourceDefectDecomposition
open ArchonPhysics.PhyslibFPUTPositiveTimeCumulantHierarchy
open ArchonPhysics.PhyslibFPUTSourceInsertionClusterExpansion

noncomputable section

variable {I Omega : Type*}
  [Fintype I] [DecidableEq I] [Nonempty I]
  [Fintype Omega] [DecidableEq Omega]

/-- One actual left-source slot against the ordinary right block. -/
def actualLeftSourceSlotFactorizationDefect
    {N : Nat} [NeZero N]
    (weight : Omega → Real)
    (mass : Omega → Lattice.PositiveMassConfig N)
    (kappa beta g : Real)
    (entry : I → PhaseSign × Lattice.Site N)
    (p q : Omega → Time → HilbertConfiguration N)
    (left right : Finset I) (slot : I) (time : Real) : Complex :=
  finiteWeightedObservableFactorizationDefect weight
    (sourceInsertedBlockObservable
      (actualFiniteCubicEnsemblePath mass entry p q)
      (actualFiniteCoerciveEnsembleSource mass kappa beta g entry q)
      left slot time)
    (pathBlockObservable
      (actualFiniteCubicEnsemblePath mass entry p q) right time)

/-- One ordinary left block against an actual right-source slot. -/
def actualRightSourceSlotFactorizationDefect
    {N : Nat} [NeZero N]
    (weight : Omega → Real)
    (mass : Omega → Lattice.PositiveMassConfig N)
    (kappa beta g : Real)
    (entry : I → PhaseSign × Lattice.Site N)
    (p q : Omega → Time → HilbertConfiguration N)
    (left right : Finset I) (slot : I) (time : Real) : Complex :=
  finiteWeightedObservableFactorizationDefect weight
    (pathBlockObservable
      (actualFiniteCubicEnsemblePath mass entry p q) left time)
    (sourceInsertedBlockObservable
      (actualFiniteCubicEnsemblePath mass entry p q)
      (actualFiniteCoerciveEnsembleSource mass kappa beta g entry q)
      right slot time)

/-- Exact actual alpha-beta source defect as the sum of all resolved
left- and right-source-slot factorization defects. -/
theorem actualFiniteCoerciveClusterFactorizationDefectSource_eq_slotSums
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
    {left right : Finset I} (hindex : Disjoint left right)
    (time : Real) :
    actualFiniteCoerciveClusterFactorizationDefectSource
        weight mass kappa beta g entry p q left right time =
      (∑ slot ∈ left,
        actualLeftSourceSlotFactorizationDefect
          weight mass kappa beta g entry p q left right slot time) +
      ∑ slot ∈ right,
        actualRightSourceSlotFactorizationDefect
          weight mass kappa beta g entry p q left right slot time := by
  rw [actualFiniteCoerciveClusterFactorizationDefectSource_eq_sum
    weight mass kappa beta g entry p q hp hq hHamilton homega hindex time]
  rw [leftSourceMomentFactorizationDefect_eq_sum_slotDefects,
    rightMomentSourceFactorizationDefect_eq_sum_slotDefects]
  rfl

/-- Norm bound resolving the actual full-potential source defect into every
individual nonlinear source slot. -/
theorem norm_actualFiniteCoerciveClusterFactorizationDefectSource_le_slotSums
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
    {left right : Finset I} (hindex : Disjoint left right)
    (time : Real) :
    ‖actualFiniteCoerciveClusterFactorizationDefectSource
        weight mass kappa beta g entry p q left right time‖ ≤
      (∑ slot ∈ left,
        ‖actualLeftSourceSlotFactorizationDefect
          weight mass kappa beta g entry p q left right slot time‖) +
      ∑ slot ∈ right,
        ‖actualRightSourceSlotFactorizationDefect
          weight mass kappa beta g entry p q left right slot time‖ := by
  rw [actualFiniteCoerciveClusterFactorizationDefectSource_eq_slotSums
    weight mass kappa beta g entry p q hp hq hHamilton homega hindex time]
  exact (norm_add_le _ _).trans
    (add_le_add (norm_sum_le _ _) (norm_sum_le _ _))

/-- Arbitrary many-cluster propagation from bounds on every concrete
source-inserted slot correlation.  This is the slot-resolved quantitative
approximate-RPA criterion for the actual coercive alpha-beta flow. -/
theorem norm_actualFiniteCoerciveOrderedClusterFactorizationDefect_le_slotErrors
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
    (time : Real)
    (leftSlotEpsilon rightSlotEpsilon : Nat → I → Real)
    (hleft : ∀ n, ∀ s ∈ Set.uIcc 0 time,
      ∀ slot ∈ orderedClusterUnion cluster n,
        ‖actualLeftSourceSlotFactorizationDefect
          weight mass kappa beta g entry p q
            (orderedClusterUnion cluster n) (cluster n) slot s‖ ≤
          leftSlotEpsilon n slot)
    (hright : ∀ n, ∀ s ∈ Set.uIcc 0 time,
      ∀ slot ∈ cluster n,
        ‖actualRightSourceSlotFactorizationDefect
          weight mass kappa beta g entry p q
            (orderedClusterUnion cluster n) (cluster n) slot s‖ ≤
          rightSlotEpsilon n slot)
    (hempty : actualFiniteCubicEnsembleBlockMoment
      weight mass entry p q ∅ time = 1)
    (hmoment : ∀ n,
      ‖actualFiniteCubicEnsembleBlockMoment
        weight mass entry p q (cluster n) time‖ ≤ 1)
    (hleftNonneg : ∀ n slot, 0 ≤ leftSlotEpsilon n slot)
    (hrightNonneg : ∀ n slot, 0 ≤ rightSlotEpsilon n slot)
    (count : Nat) :
    ‖actualFiniteCoerciveOrderedClusterFactorizationDefect
        weight mass entry p q cluster count time‖ ≤
      (∑ n ∈ Finset.range count,
        ((∑ slot ∈ orderedClusterUnion cluster n,
            leftSlotEpsilon n slot) +
          ∑ slot ∈ cluster n, rightSlotEpsilon n slot)) * |time| := by
  apply norm_actualFiniteCoerciveOrderedClusterFactorizationDefect_le_sum_of_sourceMoment
    weight mass kappa beta g entry p q hp hq hHamilton homega
      cluster hindex hzero time
      (fun n ↦ ∑ slot ∈ orderedClusterUnion cluster n,
        leftSlotEpsilon n slot)
      (fun n ↦ ∑ slot ∈ cluster n, rightSlotEpsilon n slot)
  · intro n s hs
    apply (norm_leftSourceMomentFactorizationDefect_le_sum_slotDefects
      weight
        (actualFiniteCubicEnsemblePath mass entry p q)
        (actualFiniteCoerciveEnsembleSource mass kappa beta g entry q)
        (orderedClusterUnion cluster n) (cluster n) s).trans
    exact Finset.sum_le_sum fun slot hslot ↦ hleft n s hs slot hslot
  · intro n s hs
    apply (norm_rightMomentSourceFactorizationDefect_le_sum_slotDefects
      weight
        (actualFiniteCubicEnsemblePath mass entry p q)
        (actualFiniteCoerciveEnsembleSource mass kappa beta g entry q)
        (orderedClusterUnion cluster n) (cluster n) s).trans
    exact Finset.sum_le_sum fun slot hslot ↦ hright n s hs slot hslot
  · exact hempty
  · exact hmoment
  · intro n
    exact Finset.sum_nonneg fun slot _ ↦ hleftNonneg n slot
  · intro n
    exact Finset.sum_nonneg fun slot _ ↦ hrightNonneg n slot

end

end ArchonPhysics.PhyslibFPUTActualClusterSourceSlotClosure
