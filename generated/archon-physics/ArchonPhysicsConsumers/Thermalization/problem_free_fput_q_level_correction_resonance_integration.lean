import ArchonPhysics.FreeFPUTQLevelCorrectionResonanceIntegration

/-!
# Consumer: q-level correction resonance integration

The three correction names appearing in the q-level unified closure are
connected to their exact sign-sector decompositions.  Potential resonances
remain explicit, and every inverse-time mass is a literal fixed-volume sum.
-/

namespace ArchonPhysicsConsumers.Thermalization

open ArchonPhysics
open ArchonPhysics.FreeFPUTCollisionMismatchBridge
open ArchonPhysics.FreeFPUTCounterrotatingFiniteTimeDecay
open ArchonPhysics.FreeFPUTDegenerateCorrectionResonanceClassification
open ArchonPhysics.FreeFPUTObservedChildQLevelGainLossClosure
open ArchonPhysics.FreeFPUTQLevelCorrectionResonanceIntegration
open ArchonPhysics.FreeFPUTTensorPhaseExpansion
open ArchonPhysics.MicroscopicFiniteTimeCollisionPolynomial
open ArchonPhysics.ModalPhaseMismatch
open ArchonPhysics.PhyslibFPUTIteratedQuadraticSecondPicardCharacterFamily
open ArchonPhysics.PhyslibFPUTSecondOrderUnifiedDegenerateClosure

noncomputable section

/-- Named bridge from the q-level repeated correction to the classified
two-copy sum. -/
theorem problem_repeatedAwayFixedPointCorrection_eq_repeatedAwaySameSignTwoCopyCorrectionSum
    {N : Nat} [NeZero N]
    (m : Lattice.PositiveMassConfig N) (kappa time : Real)
    (energy : Lattice.Site N → Real) (observed : Lattice.Site N) :
    repeatedAwayFixedPointCorrection m kappa time energy observed =
      repeatedAwaySameSignTwoCopyCorrectionSum
        m kappa time energy observed :=
  repeatedAwayFixedPointCorrection_eq_repeatedAwaySameSignTwoCopyCorrectionSum
    m kappa time energy observed

/-- Named bridge from the q-level all-equal correction to its classified
channel-five sum. -/
theorem problem_allEqualChannelFiveCorrection_eq_allEqualChannelFiveCorrectionSum
    {N : Nat} [NeZero N]
    (m : Lattice.PositiveMassConfig N) (kappa time : Real)
    (energy : Lattice.Site N → Real) (observed : Lattice.Site N) :
    allEqualChannelFiveCorrection m kappa time energy observed =
      allEqualChannelFiveCorrectionSum m kappa time energy observed :=
  allEqualChannelFiveCorrection_eq_allEqualChannelFiveCorrectionSum
    m kappa time energy observed

/-- Direct q-level selector calculation: sign zero has net multiplicity
`-4`, while sign one has net multiplicity `-2`. -/
theorem problem_observedChildPlacementCorrection_eq_signZero_add_signOne
    {N : Nat} [NeZero N]
    (m : Lattice.PositiveMassConfig N) (kappa time : Real)
    (energy : Lattice.Site N → Real) (observed : Lattice.Site N) :
    observedChildPlacementCorrection m kappa time energy observed =
      observedChildSignZeroNetCorrectionSum
          m kappa time energy observed +
        observedChildSignOneNetCorrectionSum
          m kappa time energy observed :=
  observedChildPlacementCorrection_eq_signZero_add_signOne
    m kappa time energy observed

/-- Complete direct selector split into sign-zero, dangerous sign-one, and
all-plus sign-one sectors. -/
theorem problem_observedChildPlacementCorrection_eq_three_signSectors
    {N : Nat} [NeZero N]
    (m : Lattice.PositiveMassConfig N) (kappa time : Real)
    (energy : Lattice.Site N → Real) (observed : Lattice.Site N) :
    observedChildPlacementCorrection m kappa time energy observed =
      observedChildSignZeroNetCorrectionSum
          m kappa time energy observed +
        observedChildPotentiallyResonantCorrectionSum
          m kappa time energy observed +
        observedChildCounterrotatingCorrectionSum
          m kappa time energy observed :=
  observedChildPlacementCorrection_eq_signZero_add_potential_add_counterrotating
    m kappa time energy observed

/-- Exact resonance criterion in the retained dangerous selector sector. -/
theorem problem_isResonant_observedChildPotentiallyResonant_iff
    {N : Nat} [NeZero N] (m : Lattice.PositiveMassConfig N)
    (observed : Lattice.Site N)
    (selector : PositiveObservedChildSelector N m observed)
    (hSelector : selector ∈
      observedChildPotentiallyResonantSelectors m observed) :
    IsResonant m (quadraticCollisionSign selector.q)
        (quadraticCollisionModes observed selector.q) ↔
      modeFrequency m
          (selector.q.1 (otherQuadraticSlot selector.observedSlot)) =
        2 * modeFrequency m observed :=
  isResonant_observedChildPotentiallyResonant_iff
    m observed selector hSelector

/-- On observed-sign zero the exact mismatch gap is the other-mode
frequency. -/
theorem problem_abs_phaseMismatch_observedChildSignZero_eq_otherFrequency
    {N : Nat} [NeZero N] (m : Lattice.PositiveMassConfig N)
    (observed : Lattice.Site N)
    (selector : PositiveObservedChildSelector N m observed)
    (hSelector : selector ∈ observedChildSignZeroSelectors m observed) :
    |phaseMismatch m (quadraticCollisionSign selector.q)
        (quadraticCollisionModes observed selector.q)| =
      modeFrequency m
        (selector.q.1 (otherQuadraticSlot selector.observedSlot)) :=
  abs_phaseMismatch_observedChildSignZero_eq_otherFrequency
    m observed selector hSelector

/-- The non-dangerous observed-sign-one selector sector is exactly all
plus. -/
theorem problem_quadraticCollisionSign_observedChildCounterrotating
    {N : Nat} [NeZero N] (m : Lattice.PositiveMassConfig N)
    (observed : Lattice.Site N)
    (selector : PositiveObservedChildSelector N m observed)
    (hSelector : selector ∈ observedChildCounterrotatingSelectors m observed) :
    quadraticCollisionSign selector.q = counterrotatingThreeWaveSign :=
  quadraticCollisionSign_observedChildCounterrotating
    m observed selector hSelector

/-- Exact potential/off-resonant split of the original placement correction. -/
theorem problem_observedChildPlacementCorrection_eq_potential_add_offResonant
    {N : Nat} [NeZero N]
    (m : Lattice.PositiveMassConfig N) (kappa time : Real)
    (energy : Lattice.Site N → Real) (observed : Lattice.Site N) :
    observedChildPlacementCorrection m kappa time energy observed =
      observedChildPotentiallyResonantCorrectionSum
          m kappa time energy observed +
        observedChildOffResonantPlacementCorrection
          m kappa time energy observed :=
  observedChildPlacementCorrection_eq_potential_add_offResonant
    m kappa time energy observed

/-- Fixed-volume inverse-time bound for the complete non-dangerous placement
correction. -/
theorem problem_abs_observedChildOffResonantPlacementCorrection_le_inverseTime
    {N : Nat} [NeZero N]
    (m : Lattice.PositiveMassConfig N) (kappa : Real)
    (energy : Lattice.Site N → Real) (observed : Lattice.Site N)
    {time : Real} (htime : 0 < time)
    (hObserved : 0 < modeFrequency m observed) :
    |observedChildOffResonantPlacementCorrection
        m kappa time energy observed| ≤
      observedChildOffResonantStaticMass
        m kappa energy observed / time :=
  abs_observedChildOffResonantPlacementCorrection_le_inverseTime
    m kappa energy observed htime hObserved

/-- Consumer-ready exact decomposition of all three q-level correction
names. -/
theorem problem_qLevelThreeCorrections_eq_potential_add_offResonant
    {N : Nat} [NeZero N]
    (m : Lattice.PositiveMassConfig N) (kappa time : Real)
    (energy : Lattice.Site N → Real) (observed : Lattice.Site N) :
    repeatedAwayFixedPointCorrection m kappa time energy observed +
        observedChildPlacementCorrection m kappa time energy observed +
        allEqualChannelFiveCorrection m kappa time energy observed =
      qLevelPotentiallyResonantCorrectionSum
          m kappa time energy observed +
        qLevelOffResonantCorrectionSum
          m kappa time energy observed :=
  qLevelThreeCorrections_eq_potential_add_offResonant
    m kappa time energy observed

/-- Fixed-volume inverse-time bound for all non-dangerous pieces of the three
q-level corrections. -/
theorem problem_abs_qLevelOffResonantCorrectionSum_le_inverseTime
    {N : Nat} [NeZero N]
    (m : Lattice.PositiveMassConfig N) (kappa : Real)
    (energy : Lattice.Site N → Real) (observed : Lattice.Site N)
    {time : Real} (htime : 0 < time)
    (hObserved : 0 < modeFrequency m observed) :
    |qLevelOffResonantCorrectionSum m kappa time energy observed| ≤
      qLevelOffResonantCorrectionStaticMass
        m kappa energy observed / time :=
  abs_qLevelOffResonantCorrectionSum_le_inverseTime
    m kappa energy observed htime hObserved

#print axioms
  problem_repeatedAwayFixedPointCorrection_eq_repeatedAwaySameSignTwoCopyCorrectionSum
#print axioms
  problem_allEqualChannelFiveCorrection_eq_allEqualChannelFiveCorrectionSum
#print axioms
  problem_observedChildPlacementCorrection_eq_signZero_add_signOne
#print axioms
  problem_observedChildPlacementCorrection_eq_three_signSectors
#print axioms
  problem_isResonant_observedChildPotentiallyResonant_iff
#print axioms
  problem_abs_phaseMismatch_observedChildSignZero_eq_otherFrequency
#print axioms
  problem_quadraticCollisionSign_observedChildCounterrotating
#print axioms
  problem_observedChildPlacementCorrection_eq_potential_add_offResonant
#print axioms
  problem_abs_observedChildOffResonantPlacementCorrection_le_inverseTime
#print axioms
  problem_qLevelThreeCorrections_eq_potential_add_offResonant
#print axioms
  problem_abs_qLevelOffResonantCorrectionSum_le_inverseTime

end

end ArchonPhysicsConsumers.Thermalization
