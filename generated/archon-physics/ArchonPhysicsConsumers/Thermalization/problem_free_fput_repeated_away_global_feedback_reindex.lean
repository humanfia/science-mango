import ArchonPhysics.FreeFPUTRepeatedAwayGlobalFeedbackReindex

namespace ArchonPhysicsConsumers.Thermalization

open ArchonPhysics
open ArchonPhysics.FreeFPUTEnergyCollisionWeightBridge
open ArchonPhysics.FreeFPUTNonAllDistinctFeedbackTreePartition
open ArchonPhysics.FreeFPUTPositiveDegenerateRepresentativeA1Partition
open ArchonPhysics.FreeFPUTRepeatedAwayGlobalFeedbackReindex
open ArchonPhysics.FreeFPUTRepeatedChildOppositeSignCorrection
open ArchonPhysics.FreeFPUTRepeatedChildSameSignCorrection
open ArchonPhysics.FreeFPUTTensorPhaseExpansion
open ArchonPhysics.ModalPhaseMismatch

noncomputable section

/-- Consumer check for the exact canonical union covering the same-sign
repeated-away matched-tree stratum. -/
theorem problem_positiveInnerCarrierFreeRepeatedAwaySameSignReturnTerms_eq_biUnion
    {N : Nat} [NeZero N]
    (m : Lattice.PositiveMassConfig N) (observed : Lattice.Site N)
    (hObserved : 0 < modeFrequency m observed) :
    positiveInnerCarrierFreeRepeatedAwaySameSignReturnTerms m observed =
      positiveRepeatedChildSameSignConnectedReturnImages m observed :=
  positiveInnerCarrierFreeRepeatedAwaySameSignReturnTerms_eq_biUnion
    m observed hObserved

/-- Consumer check for the exact canonical union covering the opposite-sign
repeated-away matched-tree stratum. -/
theorem problem_positiveInnerCarrierFreeRepeatedAwayOppositeSignReturnTerms_eq_biUnion
    {N : Nat} [NeZero N]
    (m : Lattice.PositiveMassConfig N) (observed : Lattice.Site N)
    (hObserved : 0 < modeFrequency m observed) :
    positiveInnerCarrierFreeRepeatedAwayOppositeSignReturnTerms m observed =
      positiveRepeatedChildOppositeSignConnectedReturnImages m observed :=
  positiveInnerCarrierFreeRepeatedAwayOppositeSignReturnTerms_eq_biUnion
    m observed hObserved

/-- Consumer check for the global tree-level physical feedback reindex. -/
theorem problem_positiveInnerCarrierFreeRepeatedAwayFeedbackRemainder_eq_local
    {N : Nat} [NeZero N]
    (m : Lattice.PositiveMassConfig N) (kappa time : Real)
    (energy : Lattice.Site N → Real) (observed : Lattice.Site N)
    (hObserved : 0 < modeFrequency m observed) :
    positiveInnerCarrierFreeRepeatedAwayFeedbackRemainder m kappa time
        (phaseEnergyRadius energy (modeFrequency m)) observed =
      (∑ q ∈ positiveRepeatedChildSameSignRepresentatives N m observed,
        repeatedChildConnectedReturnFeedbackSum
          m kappa time energy observed q) +
      ∑ q ∈ positiveRepeatedChildOppositeSignRepresentatives
          N m observed,
        repeatedChildOppositeSignConnectedReturnFeedbackSum
          m kappa time energy observed q :=
  positiveInnerCarrierFreeRepeatedAwayFeedbackRemainder_eq_local
    m kappa time energy observed hObserved

/-- Consumer check that the global physical reindex composes with both
existing local correction theorems. -/
theorem problem_repeatedAwayRepresentativeA1Gain_add_feedback_eq_signedFlux
    {N : Nat} [NeZero N]
    (m : Lattice.PositiveMassConfig N) (kappa time : Real)
    (energy : Lattice.Site N → Real) (observed : Lattice.Site N)
    (hObserved : 0 < modeFrequency m observed)
    (hEnergy : ∀ mode, 0 ≤ energy mode) :
    positiveRepeatedChildSameSignRepresentativeA1Gain
          m kappa time energy observed +
        positiveRepeatedChildOppositeSignRepresentativeA1Gain
          m kappa time energy observed +
        positiveInnerCarrierFreeRepeatedAwayFeedbackRemainder m kappa time
          (phaseEnergyRadius energy (modeFrequency m)) observed =
      (∑ q ∈ positiveRepeatedChildSameSignRepresentatives N m observed,
        repeatedChildSameSignSignedFluxWithCorrection
          m kappa time energy observed q) +
      ∑ q ∈ positiveRepeatedChildOppositeSignRepresentatives
          N m observed,
        repeatedChildOppositeSignFourSignedFlux
          m kappa time energy observed q :=
  repeatedAwayRepresentativeA1Gain_add_feedback_eq_signedFlux
    m kappa time energy observed hObserved hEnergy

#print axioms
  problem_positiveInnerCarrierFreeRepeatedAwaySameSignReturnTerms_eq_biUnion
#print axioms
  problem_positiveInnerCarrierFreeRepeatedAwayOppositeSignReturnTerms_eq_biUnion
#print axioms
  problem_positiveInnerCarrierFreeRepeatedAwayFeedbackRemainder_eq_local
#print axioms
  problem_repeatedAwayRepresentativeA1Gain_add_feedback_eq_signedFlux

end

end ArchonPhysicsConsumers.Thermalization
