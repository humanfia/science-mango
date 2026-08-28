import ArchonPhysics.FreeFPUTDegenerateCorrectionResonanceClassification
import ArchonPhysics.PhyslibFPUTSecondOrderQLevelUnifiedClosure

/-!
# Q-level integration of the three explicit FPUT corrections

This module connects the correction names in the q-level unified closure to
their resolved sign-sector sums.  The observed-child placement correction is
classified directly on `PositiveObservedChildSelector`: observed-sign zero
has net multiplicity `-4`, while observed-sign one has net multiplicity `-2`.

Potentially resonant sectors remain explicit.  Every inverse-time constant is
a literal finite sum at fixed volume; no `N`-uniform acoustic gap is asserted.
-/

namespace ArchonPhysics.FreeFPUTQLevelCorrectionResonanceIntegration

open ArchonPhysics
open ArchonPhysics.FreeFPUTAllEqualGlobalSelectorMultiplicity
open ArchonPhysics.FreeFPUTCollisionMismatchBridge
open ArchonPhysics.FreeFPUTCounterrotatingFiniteTimeDecay
open ArchonPhysics.FreeFPUTDegenerateCorrectionResonanceClassification
open ArchonPhysics.FreeFPUTEnergyCollisionWeightBridge
open ArchonPhysics.FreeFPUTObservedChildGlobalFeedbackClosure
open ArchonPhysics.FreeFPUTObservedChildQLevelGainLossClosure
open ArchonPhysics.FreeFPUTPositiveDegenerateRepresentativeA1Partition
open ArchonPhysics.FreeFPUTTensorPhaseExpansion
open ArchonPhysics.MicroscopicFiniteTimeCollisionPolynomial
open ArchonPhysics.ModalPhaseMismatch
open ArchonPhysics.NormalizedModeCoupling
open ArchonPhysics.PhyslibFPUTIteratedQuadraticSecondPicardCharacterFamily
open ArchonPhysics.PhyslibFPUTSecondOrderA1CollisionGainDecomposition
open ArchonPhysics.PhyslibFPUTSecondOrderQLevelUnifiedClosure
open ArchonPhysics.PhyslibFPUTSecondOrderUnifiedDegenerateClosure
open ArchonPhysics.ThreeSignedChargeCancellationClassification

noncomputable section

/-! ## Equality bridges to the q-level closure names -/

/-- The q-level fixed-point correction is exactly the previously classified
same-sign two-copy correction sum. -/
theorem repeatedAwayFixedPointCorrection_eq_repeatedAwaySameSignTwoCopyCorrectionSum
    {N : Nat} [NeZero N]
    (m : Lattice.PositiveMassConfig N) (kappa time : Real)
    (energy : Lattice.Site N → Real) (observed : Lattice.Site N) :
    repeatedAwayFixedPointCorrection m kappa time energy observed =
      repeatedAwaySameSignTwoCopyCorrectionSum
        m kappa time energy observed := by
  classical
  unfold repeatedAwayFixedPointCorrection
    repeatedAwaySameSignTwoCopyCorrectionSum
    repeatedAwaySameSignTwoCopyWeight
  apply Finset.sum_congr rfl
  intro q _hq
  ring

/-- The q-level channel-five correction is definitionally the previously
classified all-equal correction sum. -/
theorem allEqualChannelFiveCorrection_eq_allEqualChannelFiveCorrectionSum
    {N : Nat} [NeZero N]
    (m : Lattice.PositiveMassConfig N) (kappa time : Real)
    (energy : Lattice.Site N → Real) (observed : Lattice.Site N) :
    allEqualChannelFiveCorrection m kappa time energy observed =
      allEqualChannelFiveCorrectionSum m kappa time energy observed := by
  rfl

/-! ## Intrinsic selector sign sectors -/

/-- Observed-child selectors whose observed input is a phase character. -/
def observedChildSignZeroSelectors
    {N : Nat} [NeZero N] (m : Lattice.PositiveMassConfig N)
    (observed : Lattice.Site N) :
    Finset (PositiveObservedChildSelector N m observed) := by
  classical
  exact Finset.univ.filter fun selector ↦
    quadraticPhaseTermBinarySign selector.q selector.observedSlot = 0

/-- Complementary observed-child selectors.  Binary nonzero is equivalently
sign one. -/
def observedChildSignOneSelectors
    {N : Nat} [NeZero N] (m : Lattice.PositiveMassConfig N)
    (observed : Lattice.Site N) :
    Finset (PositiveObservedChildSelector N m observed) := by
  classical
  exact Finset.univ.filter fun selector ↦
    quadraticPhaseTermBinarySign selector.q selector.observedSlot ≠ 0

@[simp] theorem mem_observedChildSignZeroSelectors_iff
    {N : Nat} [NeZero N] (m : Lattice.PositiveMassConfig N)
    (observed : Lattice.Site N)
    (selector : PositiveObservedChildSelector N m observed) :
    selector ∈ observedChildSignZeroSelectors m observed ↔
      quadraticPhaseTermBinarySign selector.q selector.observedSlot = 0 := by
  classical
  simp [observedChildSignZeroSelectors]

@[simp] theorem mem_observedChildSignOneSelectors_iff
    {N : Nat} [NeZero N] (m : Lattice.PositiveMassConfig N)
    (observed : Lattice.Site N)
    (selector : PositiveObservedChildSelector N m observed) :
    selector ∈ observedChildSignOneSelectors m observed ↔
      quadraticPhaseTermBinarySign selector.q selector.observedSlot = 1 := by
  classical
  simp only [observedChildSignOneSelectors, Finset.mem_filter,
    Finset.mem_univ, true_and]
  constructor
  · intro hne
    omega
  · intro hone
    omega

/-- Within observed-sign one, a phase other input can satisfy
`2 omega_observed = omega_other` and is therefore retained as dangerous. -/
def observedChildPotentiallyResonantSelectors
    {N : Nat} [NeZero N] (m : Lattice.PositiveMassConfig N)
    (observed : Lattice.Site N) :
    Finset (PositiveObservedChildSelector N m observed) := by
  classical
  exact (observedChildSignOneSelectors m observed).filter fun selector ↦
    quadraticPhaseTermBinarySign selector.q
      (otherQuadraticSlot selector.observedSlot) = 0

/-- The complementary observed-sign-one selectors have two conjugate inputs
and are all plus. -/
def observedChildCounterrotatingSelectors
    {N : Nat} [NeZero N] (m : Lattice.PositiveMassConfig N)
    (observed : Lattice.Site N) :
    Finset (PositiveObservedChildSelector N m observed) := by
  classical
  exact (observedChildSignOneSelectors m observed).filter fun selector ↦
    quadraticPhaseTermBinarySign selector.q
      (otherQuadraticSlot selector.observedSlot) ≠ 0

/-! ## Exact net multiplicities -/

/-- Net sign-zero placement correction.  There is no restricted `+2` term,
so the multiplicity remains exactly `-4`. -/
def observedChildSignZeroNetCorrectionSum
    {N : Nat} [NeZero N]
    (m : Lattice.PositiveMassConfig N) (kappa time : Real)
    (energy : Lattice.Site N → Real) (observed : Lattice.Site N) : Real :=
  ∑ selector ∈ observedChildSignZeroSelectors m observed,
    (-4 : Real) * observedChildOtherInputLossKernel
      m kappa time energy observed selector

/-- Net sign-one placement correction.  Restricted `+2` minus universal
`4` gives exactly `-2`, not a cancellation. -/
def observedChildSignOneNetCorrectionSum
    {N : Nat} [NeZero N]
    (m : Lattice.PositiveMassConfig N) (kappa time : Real)
    (energy : Lattice.Site N → Real) (observed : Lattice.Site N) : Real :=
  ∑ selector ∈ observedChildSignOneSelectors m observed,
    (-2 : Real) * observedChildOtherInputLossKernel
      m kappa time energy observed selector

/-- Dangerous part of the net sign-one correction, retaining multiplicity
`-2`. -/
def observedChildPotentiallyResonantCorrectionSum
    {N : Nat} [NeZero N]
    (m : Lattice.PositiveMassConfig N) (kappa time : Real)
    (energy : Lattice.Site N → Real) (observed : Lattice.Site N) : Real :=
  ∑ selector ∈ observedChildPotentiallyResonantSelectors m observed,
    (-2 : Real) * observedChildOtherInputLossKernel
      m kappa time energy observed selector

/-- All-plus part of the net sign-one correction, also with multiplicity
`-2`. -/
def observedChildCounterrotatingCorrectionSum
    {N : Nat} [NeZero N]
    (m : Lattice.PositiveMassConfig N) (kappa time : Real)
    (energy : Lattice.Site N → Real) (observed : Lattice.Site N) : Real :=
  ∑ selector ∈ observedChildCounterrotatingSelectors m observed,
    (-2 : Real) * observedChildOtherInputLossKernel
      m kappa time energy observed selector

/-- Direct q-level calculation of the net `-4` and `-2` multiplicities. -/
theorem observedChildPlacementCorrection_eq_signZero_add_signOne
    {N : Nat} [NeZero N]
    (m : Lattice.PositiveMassConfig N) (kappa time : Real)
    (energy : Lattice.Site N → Real) (observed : Lattice.Site N) :
    observedChildPlacementCorrection m kappa time energy observed =
      observedChildSignZeroNetCorrectionSum
          m kappa time energy observed +
        observedChildSignOneNetCorrectionSum
          m kappa time energy observed := by
  classical
  have hSubtype :
      (∑ selector : PositiveObservedChildFreeCorrectionSelector N m observed,
        2 * observedChildOtherInputLossKernel
          m kappa time energy observed selector.1) =
        ∑ selector ∈ observedChildSignOneSelectors m observed,
          2 * observedChildOtherInputLossKernel
            m kappa time energy observed selector := by
    rw [Finset.sum_subtype
      (observedChildSignOneSelectors m observed)
      (fun selector ↦
        mem_observedChildSignOneSelectors_iff m observed selector)
      (fun selector ↦ 2 * observedChildOtherInputLossKernel
        m kappa time energy observed selector)]
  have hAll :
      (∑ selector : PositiveObservedChildSelector N m observed,
        4 * observedChildOtherInputLossKernel
          m kappa time energy observed selector) =
        (∑ selector ∈ observedChildSignZeroSelectors m observed,
          4 * observedChildOtherInputLossKernel
            m kappa time energy observed selector) +
        ∑ selector ∈ observedChildSignOneSelectors m observed,
          4 * observedChildOtherInputLossKernel
            m kappa time energy observed selector := by
    unfold observedChildSignZeroSelectors observedChildSignOneSelectors
    exact (Finset.sum_filter_add_sum_filter_not Finset.univ
      (fun selector : PositiveObservedChildSelector N m observed ↦
        quadraticPhaseTermBinarySign selector.q selector.observedSlot = 0)
      (fun selector ↦ 4 * observedChildOtherInputLossKernel
        m kappa time energy observed selector)).symm
  have hZero :
      (∑ selector ∈ observedChildSignZeroSelectors m observed,
        (-4 : Real) * observedChildOtherInputLossKernel
          m kappa time energy observed selector) =
        -(∑ selector ∈ observedChildSignZeroSelectors m observed,
          4 * observedChildOtherInputLossKernel
            m kappa time energy observed selector) := by
    rw [← Finset.sum_neg_distrib]
    apply Finset.sum_congr rfl
    intro selector _hselector
    ring
  have hOne :
      (∑ selector ∈ observedChildSignOneSelectors m observed,
        (-2 : Real) * observedChildOtherInputLossKernel
          m kappa time energy observed selector) =
        (∑ selector ∈ observedChildSignOneSelectors m observed,
          2 * observedChildOtherInputLossKernel
            m kappa time energy observed selector) -
        ∑ selector ∈ observedChildSignOneSelectors m observed,
          4 * observedChildOtherInputLossKernel
            m kappa time energy observed selector := by
    rw [← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro selector _hselector
    ring
  unfold observedChildPlacementCorrection
    observedChildSignZeroNetCorrectionSum
    observedChildSignOneNetCorrectionSum
  rw [hSubtype, hAll, hZero, hOne]
  ring

/-- Exact dangerous/all-plus split of the net sign-one correction. -/
theorem observedChildSignOneNetCorrectionSum_eq_potential_add_counterrotating
    {N : Nat} [NeZero N]
    (m : Lattice.PositiveMassConfig N) (kappa time : Real)
    (energy : Lattice.Site N → Real) (observed : Lattice.Site N) :
    observedChildSignOneNetCorrectionSum
        m kappa time energy observed =
      observedChildPotentiallyResonantCorrectionSum
          m kappa time energy observed +
        observedChildCounterrotatingCorrectionSum
          m kappa time energy observed := by
  classical
  unfold observedChildSignOneNetCorrectionSum
    observedChildPotentiallyResonantCorrectionSum
    observedChildCounterrotatingCorrectionSum
    observedChildPotentiallyResonantSelectors
    observedChildCounterrotatingSelectors
  exact (Finset.sum_filter_add_sum_filter_not
    (observedChildSignOneSelectors m observed)
    (fun selector ↦ quadraticPhaseTermBinarySign selector.q
      (otherQuadraticSlot selector.observedSlot) = 0)
    (fun selector ↦ (-2 : Real) * observedChildOtherInputLossKernel
      m kappa time energy observed selector)).symm

/-- Full exact q-level placement partition, with dangerous sector explicit. -/
theorem observedChildPlacementCorrection_eq_signZero_add_potential_add_counterrotating
    {N : Nat} [NeZero N]
    (m : Lattice.PositiveMassConfig N) (kappa time : Real)
    (energy : Lattice.Site N → Real) (observed : Lattice.Site N) :
    observedChildPlacementCorrection m kappa time energy observed =
      observedChildSignZeroNetCorrectionSum
          m kappa time energy observed +
        observedChildPotentiallyResonantCorrectionSum
          m kappa time energy observed +
        observedChildCounterrotatingCorrectionSum
          m kappa time energy observed := by
  rw [observedChildPlacementCorrection_eq_signZero_add_signOne,
    observedChildSignOneNetCorrectionSum_eq_potential_add_counterrotating]
  ring

/-! ## Selector mismatch classification -/

@[simp] theorem mem_observedChildPotentiallyResonantSelectors_iff
    {N : Nat} [NeZero N] (m : Lattice.PositiveMassConfig N)
    (observed : Lattice.Site N)
    (selector : PositiveObservedChildSelector N m observed) :
    selector ∈ observedChildPotentiallyResonantSelectors m observed ↔
      quadraticPhaseTermBinarySign selector.q selector.observedSlot = 1 ∧
        quadraticPhaseTermBinarySign selector.q
          (otherQuadraticSlot selector.observedSlot) = 0 := by
  classical
  simp [observedChildPotentiallyResonantSelectors]

@[simp] theorem mem_observedChildCounterrotatingSelectors_iff
    {N : Nat} [NeZero N] (m : Lattice.PositiveMassConfig N)
    (observed : Lattice.Site N)
    (selector : PositiveObservedChildSelector N m observed) :
    selector ∈ observedChildCounterrotatingSelectors m observed ↔
      quadraticPhaseTermBinarySign selector.q selector.observedSlot = 1 ∧
        quadraticPhaseTermBinarySign selector.q
          (otherQuadraticSlot selector.observedSlot) = 1 := by
  classical
  simp only [observedChildCounterrotatingSelectors, Finset.mem_filter,
    mem_observedChildSignOneSelectors_iff]
  constructor
  · rintro ⟨hObservedSign, hOtherNe⟩
    refine ⟨hObservedSign, ?_⟩
    omega
  · rintro ⟨hObservedSign, hOtherSign⟩
    refine ⟨hObservedSign, ?_⟩
    omega

/-- On observed-sign zero, output and observed-input frequencies cancel.  The
absolute mismatch is exactly the positive other-input frequency. -/
theorem abs_phaseMismatch_observedChildSignZero_eq_otherFrequency
    {N : Nat} [NeZero N] (m : Lattice.PositiveMassConfig N)
    (observed : Lattice.Site N)
    (selector : PositiveObservedChildSelector N m observed)
    (hSelector : selector ∈ observedChildSignZeroSelectors m observed) :
    |phaseMismatch m (quadraticCollisionSign selector.q)
        (quadraticCollisionModes observed selector.q)| =
      modeFrequency m
        (selector.q.1 (otherQuadraticSlot selector.observedSlot)) := by
  exact abs_phaseMismatch_selectedPhase_observed_eq_freeFrequency
    m observed selector.q selector.observedSlot selector.observed_only.1
      ((mem_observedChildSignZeroSelectors_iff
        m observed selector).1 hSelector)

/-- The q-level dangerous observed-child sector has exact mismatch
`2 omega_observed - omega_other`. -/
theorem phaseMismatch_observedChildPotentiallyResonant
    {N : Nat} [NeZero N] (m : Lattice.PositiveMassConfig N)
    (observed : Lattice.Site N)
    (selector : PositiveObservedChildSelector N m observed)
    (hSelector : selector ∈
      observedChildPotentiallyResonantSelectors m observed) :
    phaseMismatch m (quadraticCollisionSign selector.q)
        (quadraticCollisionModes observed selector.q) =
      2 * modeFrequency m observed -
        modeFrequency m
          (selector.q.1 (otherQuadraticSlot selector.observedSlot)) := by
  have hsign :=
    (mem_observedChildPotentiallyResonantSelectors_iff
      m observed selector).1 hSelector
  exact phaseMismatch_selectedConjugate_otherPhase_observed
    m observed selector.q selector.observedSlot selector.observed_only.1
      hsign.1 hsign.2

/-- Exact resonance is possible in the dangerous q-level selector sector
precisely when `omega_other = 2 omega_observed`. -/
theorem isResonant_observedChildPotentiallyResonant_iff
    {N : Nat} [NeZero N] (m : Lattice.PositiveMassConfig N)
    (observed : Lattice.Site N)
    (selector : PositiveObservedChildSelector N m observed)
    (hSelector : selector ∈
      observedChildPotentiallyResonantSelectors m observed) :
    IsResonant m (quadraticCollisionSign selector.q)
        (quadraticCollisionModes observed selector.q) ↔
      modeFrequency m
          (selector.q.1 (otherQuadraticSlot selector.observedSlot)) =
        2 * modeFrequency m observed := by
  unfold IsResonant
  rw [phaseMismatch_observedChildPotentiallyResonant
    m observed selector hSelector]
  constructor <;> intro h <;> linarith

/-- The remaining sign-one q-level selectors are exactly all plus. -/
theorem quadraticCollisionSign_observedChildCounterrotating
    {N : Nat} [NeZero N] (m : Lattice.PositiveMassConfig N)
    (observed : Lattice.Site N)
    (selector : PositiveObservedChildSelector N m observed)
    (hSelector : selector ∈ observedChildCounterrotatingSelectors m observed) :
    quadraticCollisionSign selector.q = counterrotatingThreeWaveSign := by
  have hsign :=
    (mem_observedChildCounterrotatingSelectors_iff
      m observed selector).1 hSelector
  exact quadraticCollisionSign_eq_counterrotating_of_selected_bothConjugate
    selector.q selector.observedSlot hsign.1 hsign.2

/-! ## Fixed-volume bounds for the non-dangerous placement sectors -/

/-- Kernel-factored net weight on observed-sign zero; the `-4` is retained
literally. -/
def observedChildSignZeroNetWeight
    {N : Nat} [NeZero N] (m : Lattice.PositiveMassConfig N)
    (energy : Lattice.Site N → Real) (observed : Lattice.Site N)
    (selector : PositiveObservedChildSelector N m observed) : Real :=
  (-4 : Real) *
    (quadraticInputInteractionSign selector.q
      (otherQuadraticSlot selector.observedSlot)).coefficient *
    (modeAction energy (modeFrequency m) observed *
      modeAction energy (modeFrequency m) observed)

/-- Kernel-factored net weight on observed-sign one; the `-2` is retained
literally. -/
def observedChildSignOneNetWeight
    {N : Nat} [NeZero N] (m : Lattice.PositiveMassConfig N)
    (energy : Lattice.Site N → Real) (observed : Lattice.Site N)
    (selector : PositiveObservedChildSelector N m observed) : Real :=
  (-2 : Real) *
    (quadraticInputInteractionSign selector.q
      (otherQuadraticSlot selector.observedSlot)).coefficient *
    (modeAction energy (modeFrequency m) observed *
      modeAction energy (modeFrequency m) observed)

/-- Literal static mass for the entire observed-sign-zero correction. -/
def observedChildSignZeroStaticMass
    {N : Nat} [NeZero N]
    (m : Lattice.PositiveMassConfig N) (kappa : Real)
    (energy : Lattice.Site N → Real) (observed : Lattice.Site N) : Real :=
  ∑ selector ∈ observedChildSignZeroSelectors m observed,
    |observedChildSignZeroNetWeight m energy observed selector| *
      (kappa ^ 2 * normalizedInteractionWeight m
        (quadraticCollisionModes observed selector.q)) *
      (2 / modeFrequency m
        (selector.q.1 (otherQuadraticSlot selector.observedSlot))) ^ 2

/-- Literal static mass for the all-plus part of observed-sign one. -/
def observedChildCounterrotatingStaticMass
    {N : Nat} [NeZero N]
    (m : Lattice.PositiveMassConfig N) (kappa : Real)
    (energy : Lattice.Site N → Real) (observed : Lattice.Site N) : Real :=
  ∑ selector ∈ observedChildCounterrotatingSelectors m observed,
    |observedChildSignOneNetWeight m energy observed selector| *
      (kappa ^ 2 * normalizedInteractionWeight m
        (quadraticCollisionModes observed selector.q)) *
      (2 / modeFrequency m observed) ^ 2

theorem otherFrequency_pos_of_observedChildSelector
    {N : Nat} [NeZero N] (m : Lattice.PositiveMassConfig N)
    (observed : Lattice.Site N)
    (selector : PositiveObservedChildSelector N m observed) :
    0 < modeFrequency m
      (selector.q.1 (otherQuadraticSlot selector.observedSlot)) := by
  classical
  have hPositive : PositiveModeTuple m
      (quadraticCollisionModes observed selector.q) := by
    simpa [positiveQuadraticSwapOrbitRepresentatives] using
      (Finset.mem_filter.mp selector.q_mem).2
  simpa [quadraticCollisionModes] using
    hPositive (Fin.succ (otherQuadraticSlot selector.observedSlot))

/-- Fixed-volume inverse-time bound for all observed-sign-zero selectors. -/
theorem abs_observedChildSignZeroNetCorrectionSum_le_inverseTime
    {N : Nat} [NeZero N]
    (m : Lattice.PositiveMassConfig N) (kappa : Real)
    (energy : Lattice.Site N → Real) (observed : Lattice.Site N)
    {time : Real} (htime : 0 < time) :
    |observedChildSignZeroNetCorrectionSum
        m kappa time energy observed| ≤
      observedChildSignZeroStaticMass m kappa energy observed / time := by
  classical
  unfold observedChildSignZeroNetCorrectionSum
    observedChildOtherInputLossKernel observedChildSignZeroStaticMass
    observedChildSignZeroNetWeight
  simpa only [mul_assoc, mul_left_comm, mul_comm] using
    (abs_weightedQuadraticKernelSum_le_inverseTime
      m kappa observed (observedChildSignZeroSelectors m observed)
      (fun selector ↦ selector.q)
      (fun selector ↦
        (-4 : Real) *
          (quadraticInputInteractionSign selector.q
            (otherQuadraticSlot selector.observedSlot)).coefficient *
          (modeAction energy (modeFrequency m) observed *
            modeAction energy (modeFrequency m) observed))
      (fun selector ↦ modeFrequency m
        (selector.q.1 (otherQuadraticSlot selector.observedSlot))) htime
      (fun selector _hSelector ↦
        otherFrequency_pos_of_observedChildSelector m observed selector)
      (fun selector hSelector ↦ by
        rw [abs_phaseMismatch_observedChildSignZero_eq_otherFrequency
          m observed selector hSelector]))

/-- Fixed-volume inverse-time bound for the q-level all-plus selector sector. -/
theorem abs_observedChildCounterrotatingCorrectionSum_le_inverseTime
    {N : Nat} [NeZero N]
    (m : Lattice.PositiveMassConfig N) (kappa : Real)
    (energy : Lattice.Site N → Real) (observed : Lattice.Site N)
    {time : Real} (htime : 0 < time)
    (hObserved : 0 < modeFrequency m observed) :
    |observedChildCounterrotatingCorrectionSum
        m kappa time energy observed| ≤
      observedChildCounterrotatingStaticMass
        m kappa energy observed / time := by
  classical
  unfold observedChildCounterrotatingCorrectionSum
    observedChildOtherInputLossKernel observedChildCounterrotatingStaticMass
    observedChildSignOneNetWeight
  simpa only [mul_assoc, mul_left_comm, mul_comm] using
    (abs_weightedQuadraticKernelSum_le_inverseTime
      m kappa observed (observedChildCounterrotatingSelectors m observed)
      (fun selector ↦ selector.q)
      (fun selector ↦
        (-2 : Real) *
          (quadraticInputInteractionSign selector.q
            (otherQuadraticSlot selector.observedSlot)).coefficient *
          (modeAction energy (modeFrequency m) observed *
            modeAction energy (modeFrequency m) observed))
      (fun _selector ↦ modeFrequency m observed) htime
      (fun _selector _hSelector ↦ hObserved)
      (fun selector hSelector ↦ by
        rw [quadraticCollisionSign_observedChildCounterrotating
          m observed selector hSelector]
        exact modeFrequency_le_abs_phaseMismatch_counterrotating
          m (quadraticCollisionModes observed selector.q)))

/-- Full algebraically off-resonant part of the q-level placement correction. -/
def observedChildOffResonantPlacementCorrection
    {N : Nat} [NeZero N]
    (m : Lattice.PositiveMassConfig N) (kappa time : Real)
    (energy : Lattice.Site N → Real) (observed : Lattice.Site N) : Real :=
  observedChildSignZeroNetCorrectionSum m kappa time energy observed +
    observedChildCounterrotatingCorrectionSum
      m kappa time energy observed

/-- Literal fixed-volume mass for both non-dangerous selector sectors. -/
def observedChildOffResonantStaticMass
    {N : Nat} [NeZero N]
    (m : Lattice.PositiveMassConfig N) (kappa : Real)
    (energy : Lattice.Site N → Real) (observed : Lattice.Site N) : Real :=
  observedChildSignZeroStaticMass m kappa energy observed +
    observedChildCounterrotatingStaticMass m kappa energy observed

/-- Exact potential/off-resonant decomposition of the original q-level
placement correction. -/
theorem observedChildPlacementCorrection_eq_potential_add_offResonant
    {N : Nat} [NeZero N]
    (m : Lattice.PositiveMassConfig N) (kappa time : Real)
    (energy : Lattice.Site N → Real) (observed : Lattice.Site N) :
    observedChildPlacementCorrection m kappa time energy observed =
      observedChildPotentiallyResonantCorrectionSum
          m kappa time energy observed +
        observedChildOffResonantPlacementCorrection
          m kappa time energy observed := by
  rw [observedChildPlacementCorrection_eq_signZero_add_potential_add_counterrotating]
  unfold observedChildOffResonantPlacementCorrection
  ring

/-- Fixed-volume `C_N / T` bound for the full non-dangerous placement
correction. -/
theorem abs_observedChildOffResonantPlacementCorrection_le_inverseTime
    {N : Nat} [NeZero N]
    (m : Lattice.PositiveMassConfig N) (kappa : Real)
    (energy : Lattice.Site N → Real) (observed : Lattice.Site N)
    {time : Real} (htime : 0 < time)
    (hObserved : 0 < modeFrequency m observed) :
    |observedChildOffResonantPlacementCorrection
        m kappa time energy observed| ≤
      observedChildOffResonantStaticMass
        m kappa energy observed / time := by
  have hZero := abs_observedChildSignZeroNetCorrectionSum_le_inverseTime
    m kappa energy observed htime
  have hCounter :=
    abs_observedChildCounterrotatingCorrectionSum_le_inverseTime
      m kappa energy observed htime hObserved
  unfold observedChildOffResonantPlacementCorrection
    observedChildOffResonantStaticMass
  calc
    |observedChildSignZeroNetCorrectionSum m kappa time energy observed +
        observedChildCounterrotatingCorrectionSum
          m kappa time energy observed| ≤
      |observedChildSignZeroNetCorrectionSum
          m kappa time energy observed| +
        |observedChildCounterrotatingCorrectionSum
          m kappa time energy observed| := abs_add_le _ _
    _ ≤ observedChildSignZeroStaticMass m kappa energy observed / time +
        observedChildCounterrotatingStaticMass
          m kappa energy observed / time := add_le_add hZero hCounter
    _ = (observedChildSignZeroStaticMass m kappa energy observed +
        observedChildCounterrotatingStaticMass
          m kappa energy observed) / time := by ring

/-! ## Unified q-level correction decomposition -/

/-- The two genuinely potentially resonant q-level correction sectors. -/
def qLevelPotentiallyResonantCorrectionSum
    {N : Nat} [NeZero N]
    (m : Lattice.PositiveMassConfig N) (kappa time : Real)
    (energy : Lattice.Site N → Real) (observed : Lattice.Site N) : Real :=
  repeatedAwayPotentiallyResonantCorrectionSum
      m kappa time energy observed +
    observedChildPotentiallyResonantCorrectionSum
      m kappa time energy observed

/-- All algebraically off-resonant parts of the three q-level corrections. -/
def qLevelOffResonantCorrectionSum
    {N : Nat} [NeZero N]
    (m : Lattice.PositiveMassConfig N) (kappa time : Real)
    (energy : Lattice.Site N → Real) (observed : Lattice.Site N) : Real :=
  repeatedAwayCounterrotatingCorrectionSum
      m kappa time energy observed +
    observedChildOffResonantPlacementCorrection
      m kappa time energy observed +
    allEqualChannelFiveCorrectionSum m kappa time energy observed

/-- Literal fixed-volume mass for the complete off-resonant q-level
correction list. -/
def qLevelOffResonantCorrectionStaticMass
    {N : Nat} [NeZero N]
    (m : Lattice.PositiveMassConfig N) (kappa : Real)
    (energy : Lattice.Site N → Real) (observed : Lattice.Site N) : Real :=
  repeatedAwayCounterrotatingStaticMass m kappa energy observed +
    observedChildOffResonantStaticMass m kappa energy observed +
    allEqualChannelFiveStaticMass m kappa energy observed

/-- Consumer-ready exact decomposition of the three correction names in the
q-level unified closure. -/
theorem qLevelThreeCorrections_eq_potential_add_offResonant
    {N : Nat} [NeZero N]
    (m : Lattice.PositiveMassConfig N) (kappa time : Real)
    (energy : Lattice.Site N → Real) (observed : Lattice.Site N) :
    repeatedAwayFixedPointCorrection m kappa time energy observed +
        observedChildPlacementCorrection m kappa time energy observed +
        allEqualChannelFiveCorrection m kappa time energy observed =
      qLevelPotentiallyResonantCorrectionSum
          m kappa time energy observed +
        qLevelOffResonantCorrectionSum
          m kappa time energy observed := by
  rw [repeatedAwayFixedPointCorrection_eq_repeatedAwaySameSignTwoCopyCorrectionSum,
    repeatedAwaySameSignTwoCopyCorrectionSum_eq_potential_add_counterrotating,
    observedChildPlacementCorrection_eq_potential_add_offResonant,
    allEqualChannelFiveCorrection_eq_allEqualChannelFiveCorrectionSum]
  unfold qLevelPotentiallyResonantCorrectionSum
    qLevelOffResonantCorrectionSum
  ring

/-- Fixed-volume inverse-time bound for every non-dangerous part of the three
q-level corrections.  No uniformity in `N` is claimed. -/
theorem abs_qLevelOffResonantCorrectionSum_le_inverseTime
    {N : Nat} [NeZero N]
    (m : Lattice.PositiveMassConfig N) (kappa : Real)
    (energy : Lattice.Site N → Real) (observed : Lattice.Site N)
    {time : Real} (htime : 0 < time)
    (hObserved : 0 < modeFrequency m observed) :
    |qLevelOffResonantCorrectionSum m kappa time energy observed| ≤
      qLevelOffResonantCorrectionStaticMass
        m kappa energy observed / time := by
  have hRepeated :=
    abs_repeatedAwayCounterrotatingCorrectionSum_le_inverseTime
      m kappa energy observed htime hObserved
  have hObservedChild :=
    abs_observedChildOffResonantPlacementCorrection_le_inverseTime
      m kappa energy observed htime hObserved
  have hAllEqual := abs_allEqualChannelFiveCorrectionSum_le_inverseTime
    m kappa energy observed htime hObserved
  unfold qLevelOffResonantCorrectionSum
    qLevelOffResonantCorrectionStaticMass
  calc
    |repeatedAwayCounterrotatingCorrectionSum
          m kappa time energy observed +
        observedChildOffResonantPlacementCorrection
          m kappa time energy observed +
        allEqualChannelFiveCorrectionSum
          m kappa time energy observed| ≤
      |repeatedAwayCounterrotatingCorrectionSum
          m kappa time energy observed| +
        |observedChildOffResonantPlacementCorrection
          m kappa time energy observed| +
      |allEqualChannelFiveCorrectionSum
          m kappa time energy observed| := by
      exact (abs_add_le _ _).trans
        (add_le_add (abs_add_le _ _) (le_refl _))
    _ ≤ repeatedAwayCounterrotatingStaticMass
          m kappa energy observed / time +
        observedChildOffResonantStaticMass
          m kappa energy observed / time +
        allEqualChannelFiveStaticMass
          m kappa energy observed / time := by
      exact add_le_add (add_le_add hRepeated hObservedChild) hAllEqual
    _ = (repeatedAwayCounterrotatingStaticMass
          m kappa energy observed +
        observedChildOffResonantStaticMass
          m kappa energy observed +
        allEqualChannelFiveStaticMass
          m kappa energy observed) / time := by ring

end

end ArchonPhysics.FreeFPUTQLevelCorrectionResonanceIntegration
