import ArchonPhysics.FreeFPUTObservedChildGlobalFeedbackClosure

/-!
# Consumer: global observed-child feedback closure

This consumer exposes the two proved global reindices.  The carrier-observed
fiber has four placements.  The free-observed tadpole part cancels inside its
own stratum, while the surviving channel-five fiber has two placements after
the inner-placement collapse.
-/

namespace ArchonPhysicsConsumers.Thermalization

open ArchonPhysics
open ArchonPhysics.FreeFPUTNonAllDistinctFeedbackTreePartition
open ArchonPhysics.FreeFPUTObservedChildGlobalFeedbackClosure
open ArchonPhysics.FreeFPUTPositiveDegenerateRepresentativeA1Partition
open ArchonPhysics.FreeFPUTTensorPhaseExpansion
open ArchonPhysics.ModalPhaseMismatch
open ArchonPhysics.PhyslibFPUTSecondOrderExplicitReturnFeedback

noncomputable section

def problem_positiveObservedCarrier_global_equiv
    {N : Nat} [NeZero N] (m : Lattice.PositiveMassConfig N)
    (observed : Lattice.Site N) :
    PositiveObservedCarrierParameter N m observed ≃
      FullyPositiveObservedCarrierTerm N m observed :=
  positiveObservedCarrierEquiv m observed

theorem problem_freeObserved_tadpole_sum_eq_zero
    {N : Nat} [NeZero N]
    (m : Lattice.PositiveMassConfig N) (kappa time : Real)
    (energy : Lattice.Site N → Real) (observed : Lattice.Site N) :
    (∑ term ∈ positiveInnerObservedOnlyAtFreeTadpoleTerms m observed,
      observedChildPhysicalFeedbackWeight
        m kappa time energy observed term.1) = 0 :=
  freeObservedTadpoleFeedbackSum_eq_zero
    m kappa time energy observed

def problem_positiveObservedFree_connected_global_equiv
    {N : Nat} [NeZero N] (m : Lattice.PositiveMassConfig N)
    (observed : Lattice.Site N)
    (hObserved : 0 < modeFrequency m observed) :
    PositiveObservedFreeConnectedParameter N m observed ≃
      ObservedFreeConnectedTerm N m observed :=
  positiveObservedFreeConnectedEquiv m observed hObserved

theorem problem_observedChildA1_add_feedback_eq_resolved
    {N : Nat} [NeZero N]
    (m : Lattice.PositiveMassConfig N) (kappa time : Real)
    (energy : Lattice.Site N → Real) (observed : Lattice.Site N)
    (hObserved : 0 < modeFrequency m observed)
    (hEnergy : ∀ mode, 0 ≤ energy mode) :
    positiveObservedOnlyAtChildZeroRepresentativeA1Gain
          m kappa time energy observed +
        positiveObservedOnlyAtChildOneRepresentativeA1Gain
          m kappa time energy observed +
        positiveInnerObservedOnlyAtCarrierFeedbackRemainder m kappa time
          (phaseEnergyRadius energy (modeFrequency m)) observed +
        positiveInnerObservedOnlyAtFreeFeedbackRemainder m kappa time
          (phaseEnergyRadius energy (modeFrequency m)) observed =
      positiveObservedOnlyAtChildZeroRepresentativeA1Gain
          m kappa time energy observed +
        positiveObservedOnlyAtChildOneRepresentativeA1Gain
          m kappa time energy observed +
        observedCarrierSignedKernelSum m kappa time energy observed +
        observedFreeCollapsedKernelSum m kappa time energy observed :=
  observedChildA1_add_feedback_eq_resolved
    m kappa time energy observed hObserved hEnergy

#print axioms problem_positiveObservedCarrier_global_equiv
#print axioms problem_freeObserved_tadpole_sum_eq_zero
#print axioms problem_positiveObservedFree_connected_global_equiv
#print axioms problem_observedChildA1_add_feedback_eq_resolved

end

end ArchonPhysicsConsumers.Thermalization
