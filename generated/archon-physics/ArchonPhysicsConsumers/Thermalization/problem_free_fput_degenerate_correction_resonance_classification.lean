import ArchonPhysics.FreeFPUTDegenerateCorrectionResonanceClassification

/-!
# Consumer: resonance classification of degenerate FPUT corrections

These endpoints expose the exact dangerous/off-resonant partitions left by
the repeated-away, observed-child, and all-equal global closures.  Every
inverse-time constant is a literal fixed-volume finite sum; none is asserted
to be uniform in the lattice size.
-/

namespace ArchonPhysicsConsumers.Thermalization

open ArchonPhysics
open ArchonPhysics.FreeFPUTAllEqualGlobalSelectorMultiplicity
open ArchonPhysics.FreeFPUTCollisionMismatchBridge
open ArchonPhysics.FreeFPUTDegenerateCorrectionResonanceClassification
open ArchonPhysics.FreeFPUTObservedChildGlobalFeedbackClosure
open ArchonPhysics.FreeFPUTTensorPhaseExpansion
open ArchonPhysics.MicroscopicFiniteTimeCollisionPolynomial
open ArchonPhysics.ModalPhaseMismatch
open ArchonPhysics.PhyslibFPUTIteratedQuadraticSecondPicardCharacterFamily
open ArchonPhysics.ThreeSignedChargeCancellationClassification

noncomputable section

/-- The repeated-away two-copy correction is exactly the sum of its possible
`omega_observed = 2 omega_child` sector and its all-plus complement. -/
theorem problem_repeatedAwayCorrection_eq_potential_add_counterrotating
    {N : Nat} [NeZero N]
    (m : Lattice.PositiveMassConfig N) (kappa time : Real)
    (energy : Lattice.Site N → Real) (observed : Lattice.Site N) :
    repeatedAwaySameSignTwoCopyCorrectionSum
        m kappa time energy observed =
      repeatedAwayPotentiallyResonantCorrectionSum
          m kappa time energy observed +
        repeatedAwayCounterrotatingCorrectionSum
          m kappa time energy observed :=
  repeatedAwaySameSignTwoCopyCorrectionSum_eq_potential_add_counterrotating
    m kappa time energy observed

/-- Exact resonance criterion in the retained repeated-away dangerous
sector. -/
theorem problem_isResonant_repeatedAwayPotentiallyResonant_iff
    {N : Nat} [NeZero N] (m : Lattice.PositiveMassConfig N)
    (observed : Lattice.Site N) (q : QuadraticPhaseTerm N)
    (hq : q ∈ repeatedAwayPotentiallyResonantSameSignRepresentatives
      N m observed) :
    IsResonant m (quadraticCollisionSign q)
        (quadraticCollisionModes observed q) ↔
      modeFrequency m observed = 2 * modeFrequency m (q.1 0) :=
  isResonant_repeatedAwayPotentiallyResonant_iff m observed q hq

/-- Fixed-volume inverse-time bound on the repeated-away all-plus part. -/
theorem problem_abs_repeatedAwayCounterrotatingCorrectionSum_le_inverseTime
    {N : Nat} [NeZero N]
    (m : Lattice.PositiveMassConfig N) (kappa : Real)
    (energy : Lattice.Site N → Real) (observed : Lattice.Site N)
    {time : Real} (htime : 0 < time)
    (hObserved : 0 < modeFrequency m observed) :
    |repeatedAwayCounterrotatingCorrectionSum
        m kappa time energy observed| ≤
      repeatedAwayCounterrotatingStaticMass
        m kappa energy observed / time :=
  abs_repeatedAwayCounterrotatingCorrectionSum_le_inverseTime
    m kappa energy observed htime hObserved

/-- Exact potentially-resonant/off-resonant partition of the carrier sum. -/
theorem problem_observedCarrierSignedKernelSum_eq_potential_add_offResonant
    {N : Nat} [NeZero N]
    (m : Lattice.PositiveMassConfig N) (kappa time : Real)
    (energy : Lattice.Site N → Real) (observed : Lattice.Site N) :
    observedCarrierSignedKernelSum m kappa time energy observed =
      observedCarrierPotentiallyResonantSum
          m kappa time energy observed +
        observedCarrierOffResonantSum
          m kappa time energy observed :=
  observedCarrierSignedKernelSum_eq_potential_add_offResonant
    m kappa time energy observed

/-- Exact resonance criterion in the retained carrier-observed dangerous
sector. -/
theorem problem_isResonant_observedCarrierPotentiallyResonant_iff
    {N : Nat} [NeZero N] (m : Lattice.PositiveMassConfig N)
    (observed : Lattice.Site N)
    (parameter : PositiveObservedCarrierParameter N m observed)
    (hParameter : parameter ∈
      observedCarrierPotentiallyResonantParameters m observed) :
    IsResonant m (quadraticCollisionSign parameter.q)
        (quadraticCollisionModes observed parameter.q) ↔
      modeFrequency m
          (parameter.q.1 (otherQuadraticSlot parameter.selected)) =
        2 * modeFrequency m observed :=
  isResonant_observedCarrierPotentiallyResonant_iff
    m observed parameter hParameter

/-- Fixed-volume inverse-time bound on the full carrier complement. -/
theorem problem_abs_observedCarrierOffResonantSum_le_inverseTime
    {N : Nat} [NeZero N]
    (m : Lattice.PositiveMassConfig N) (kappa : Real)
    (energy : Lattice.Site N → Real) (observed : Lattice.Site N)
    {time : Real} (htime : 0 < time)
    (hObserved : 0 < modeFrequency m observed) :
    |observedCarrierOffResonantSum
        m kappa time energy observed| ≤
      observedCarrierOffResonantStaticMass
        m kappa energy observed / time :=
  abs_observedCarrierOffResonantSum_le_inverseTime
    m kappa energy observed htime hObserved

/-- Exact potentially-resonant/all-plus partition of the free-observed
collapsed sum. -/
theorem problem_observedFreeCollapsedKernelSum_eq_potential_add_counterrotating
    {N : Nat} [NeZero N]
    (m : Lattice.PositiveMassConfig N) (kappa time : Real)
    (energy : Lattice.Site N → Real) (observed : Lattice.Site N) :
    observedFreeCollapsedKernelSum m kappa time energy observed =
      observedFreePotentiallyResonantSum m kappa time energy observed +
        observedFreeCounterrotatingSum m kappa time energy observed :=
  observedFreeCollapsedKernelSum_eq_potential_add_counterrotating
    m kappa time energy observed

/-- Exact resonance criterion in the retained free-observed dangerous
sector. -/
theorem problem_isResonant_observedFreePotentiallyResonant_iff
    {N : Nat} [NeZero N] (m : Lattice.PositiveMassConfig N)
    (observed : Lattice.Site N)
    (parameter : PositiveObservedFreeConnectedParameter N m observed)
    (hParameter : parameter ∈
      observedFreePotentiallyResonantParameters m observed) :
    IsResonant m (quadraticCollisionSign parameter.q)
        (quadraticCollisionModes observed parameter.q) ↔
      modeFrequency m (parameter.q.1 parameter.selected) =
        2 * modeFrequency m observed :=
  isResonant_observedFreePotentiallyResonant_iff
    m observed parameter hParameter

/-- Fixed-volume inverse-time bound on the free-observed all-plus part. -/
theorem problem_abs_observedFreeCounterrotatingSum_le_inverseTime
    {N : Nat} [NeZero N]
    (m : Lattice.PositiveMassConfig N) (kappa : Real)
    (energy : Lattice.Site N → Real) (observed : Lattice.Site N)
    {time : Real} (htime : 0 < time)
    (hObserved : 0 < modeFrequency m observed) :
    |observedFreeCounterrotatingSum m kappa time energy observed| ≤
      observedFreeCounterrotatingStaticMass
        m kappa energy observed / time :=
  abs_observedFreeCounterrotatingSum_le_inverseTime
    m kappa energy observed htime hObserved

/-- Every all-equal channel-five parameter has mismatch exactly
`omega_observed` or `3 omega_observed`. -/
theorem problem_phaseMismatch_allEqualChannelFive
    {N : Nat} [NeZero N] (m : Lattice.PositiveMassConfig N)
    (observed : Lattice.Site N)
    (parameter : QuadraticPhaseTerm N × (Fin 2 × Fin 2))
    (hParameter : parameter ∈
      positiveAllEqualChannelFiveParameters N m observed) :
    phaseMismatch m (quadraticCollisionSign parameter.1)
        (quadraticCollisionModes observed parameter.1) =
      if quadraticPhaseTermBinarySign parameter.1 parameter.2.1 = 0 then
        modeFrequency m observed
      else 3 * modeFrequency m observed :=
  phaseMismatch_allEqualChannelFive m observed parameter hParameter

/-- Fixed-volume inverse-time bound for the entire all-equal channel-five
correction. -/
theorem problem_abs_allEqualChannelFiveCorrectionSum_le_inverseTime
    {N : Nat} [NeZero N]
    (m : Lattice.PositiveMassConfig N) (kappa : Real)
    (energy : Lattice.Site N → Real) (observed : Lattice.Site N)
    {time : Real} (htime : 0 < time)
    (hObserved : 0 < modeFrequency m observed) :
    |allEqualChannelFiveCorrectionSum
        m kappa time energy observed| ≤
      allEqualChannelFiveStaticMass m kappa energy observed / time :=
  abs_allEqualChannelFiveCorrectionSum_le_inverseTime
    m kappa energy observed htime hObserved

#print axioms
  problem_repeatedAwayCorrection_eq_potential_add_counterrotating
#print axioms
  problem_isResonant_repeatedAwayPotentiallyResonant_iff
#print axioms
  problem_abs_repeatedAwayCounterrotatingCorrectionSum_le_inverseTime
#print axioms
  problem_observedCarrierSignedKernelSum_eq_potential_add_offResonant
#print axioms
  problem_isResonant_observedCarrierPotentiallyResonant_iff
#print axioms
  problem_abs_observedCarrierOffResonantSum_le_inverseTime
#print axioms
  problem_observedFreeCollapsedKernelSum_eq_potential_add_counterrotating
#print axioms
  problem_isResonant_observedFreePotentiallyResonant_iff
#print axioms
  problem_abs_observedFreeCounterrotatingSum_le_inverseTime
#print axioms problem_phaseMismatch_allEqualChannelFive
#print axioms
  problem_abs_allEqualChannelFiveCorrectionSum_le_inverseTime

end

end ArchonPhysicsConsumers.Thermalization
