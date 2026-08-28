import ArchonPhysics.FreeFPUTObservedChildQLevelGainLossClosure

namespace ArchonPhysicsConsumers.Thermalization

open ArchonPhysics
open ArchonPhysics.FreeFPUTNonAllDistinctFeedbackTreePartition
open ArchonPhysics.FreeFPUTObservedChildQLevelGainLossClosure
open ArchonPhysics.FreeFPUTPositiveDegenerateRepresentativeA1Partition
open ArchonPhysics.FreeFPUTTensorPhaseExpansion
open ArchonPhysics.ModalPhaseMismatch

noncomputable section

/-- Consumer for the exact join between the two A1 representative strata and
the unique observed-input selector. -/
theorem problem_observedChildRepresentativeA1Gain_eq_selectorSum
    {N : Nat} [NeZero N]
    (m : Lattice.PositiveMassConfig N) (kappa time : Real)
    (energy : Lattice.Site N → Real) (observed : Lattice.Site N) :
    positiveObservedOnlyAtChildZeroRepresentativeA1Gain
          m kappa time energy observed +
        positiveObservedOnlyAtChildOneRepresentativeA1Gain
          m kappa time energy observed =
      ∑ selector : PositiveObservedChildSelector N m observed,
        ArchonPhysics.FreeFPUTAllDistinctLocalSignedGainLoss.allDistinctLocalA1Gain
          m kappa time energy observed selector.q :=
  observedChildRepresentativeA1Gain_eq_selectorSum
    m kappa time energy observed

/-- Consumer for the fully joined q-level signed-flux formula with its exact
sign-one placement correction. -/
theorem problem_observedChildA1_add_feedback_eq_fourSignedFlux_add_correction
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
      observedChildFourSignedFluxSum m kappa time energy observed +
        observedChildPlacementCorrection m kappa time energy observed :=
  observedChildA1_add_feedback_eq_fourSignedFlux_add_correction
    m kappa time energy observed hObserved hEnergy

#print axioms problem_observedChildRepresentativeA1Gain_eq_selectorSum
#print axioms
  problem_observedChildA1_add_feedback_eq_fourSignedFlux_add_correction

end

end ArchonPhysicsConsumers.Thermalization
