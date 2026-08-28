import ArchonPhysics.FreeFPUTObservedChildGlobalFeedbackClosure

/-!
# Q-level gain--loss closure for the observed-child FPUT strata

The tree-level carrier and free-observed feedbacks have already been globally
reindexed.  This module joins those two parameter bases to the canonical
quadratic representatives carrying exactly one observed child.  It keeps the
input-swap orbit cardinality and both placement multiplicities explicit.

For every canonical observed-child selector, the coherent A1 gain and the
four carrier-observed placements give four copies of the signed collision
flux, except for the loss at the other input.  The surviving free-observed
fiber restores two copies of that loss precisely when the observed/free input
has binary sign one.  The remaining multiplicity correction is therefore
stated as a literal restricted-selector sum minus the four-copy loss sum; no
cross-stratum cancellation is assumed.
-/

namespace ArchonPhysics.FreeFPUTObservedChildQLevelGainLossClosure

open ArchonPhysics
open ArchonPhysics.FreeFPUTAllDistinctLocalSignedGainLoss
open ArchonPhysics.FreeFPUTCollisionMismatchBridge
open ArchonPhysics.FreeFPUTEnergyCollisionWeightBridge
open ArchonPhysics.FreeFPUTNonAllDistinctFeedbackTreePartition
open ArchonPhysics.FreeFPUTObservedChildDegeneracyPartition
open ArchonPhysics.FreeFPUTObservedChildGlobalFeedbackClosure
open ArchonPhysics.FreeFPUTPositiveDegenerateRepresentativeA1Partition
open ArchonPhysics.FreeFPUTQuadraticTermSwapSymmetry
open ArchonPhysics.FreeFPUTTensorPhaseExpansion
open ArchonPhysics.MicroscopicFiniteTimeCollisionPolynomial
open ArchonPhysics.ModalPhaseMismatch
open ArchonPhysics.PhyslibFPUTIteratedQuadraticSecondPicardCharacterFamily
open ArchonPhysics.PhyslibFPUTSecondOrderA1CollisionGainDecomposition
open ArchonPhysics.SignedThreeWaveCollisionFlux
open ArchonPhysics.ThreeSignedChargeCancellationClassification

noncomputable section

/-! ## One canonical q-level selector -/

/-- A positive canonical quadratic representative together with its unique
observed input.  No placement index is retained at this level. -/
structure PositiveObservedChildSelector
    (N : Nat) [NeZero N] (m : Lattice.PositiveMassConfig N)
    (observed : Lattice.Site N) where
  q : QuadraticPhaseTerm N
  observedSlot : Fin 2
  q_mem : q ∈ positiveQuadraticSwapOrbitRepresentatives N m observed
  observed_only : ObservedAtSelectedOnly observed q observedSlot

abbrev PositiveObservedOnlyAtChildZeroRepresentative
    (N : Nat) [NeZero N] (m : Lattice.PositiveMassConfig N)
    (observed : Lattice.Site N) :=
  {q : QuadraticPhaseTerm N //
    q ∈ positiveObservedOnlyAtChildZeroRepresentatives N m observed}

abbrev PositiveObservedOnlyAtChildOneRepresentative
    (N : Nat) [NeZero N] (m : Lattice.PositiveMassConfig N)
    (observed : Lattice.Site N) :=
  {q : QuadraticPhaseTerm N //
    q ∈ positiveObservedOnlyAtChildOneRepresentatives N m observed}

/-- The selected-input description is exactly the disjoint sum of the
child-zero-only and child-one-only representative strata. -/
def positiveObservedChildSelectorEquivSum
    {N : Nat} [NeZero N] (m : Lattice.PositiveMassConfig N)
    (observed : Lattice.Site N) :
    PositiveObservedChildSelector N m observed ≃
      Sum (PositiveObservedOnlyAtChildZeroRepresentative N m observed)
        (PositiveObservedOnlyAtChildOneRepresentative N m observed) where
  toFun selector := by
    classical
    by_cases hslot : selector.observedSlot = 0
    · exact Sum.inl ⟨selector.q, by
        unfold positiveObservedOnlyAtChildZeroRepresentatives
          observedOnlyAtChildZeroTerms
        apply Finset.mem_filter.mpr
        refine ⟨selector.q_mem, ?_⟩
        simpa [ObservedAtSelectedOnly, ObservedOnlyAtChildZero,
          hslot, otherQuadraticSlot] using selector.observed_only⟩
    · have hslotOne : selector.observedSlot = 1 :=
        Fin.eq_one_of_ne_zero selector.observedSlot hslot
      exact Sum.inr ⟨selector.q, by
        unfold positiveObservedOnlyAtChildOneRepresentatives
          observedOnlyAtChildOneTerms
        apply Finset.mem_filter.mpr
        refine ⟨selector.q_mem, ?_⟩
        simpa [ObservedAtSelectedOnly, ObservedOnlyAtChildOne,
          hslotOne, otherQuadraticSlot] using selector.observed_only⟩
  invFun entry := by
    classical
    rcases entry with zero | one
    · have hmem := Finset.mem_filter.mp zero.2
      exact ⟨zero.1, 0, hmem.1, by
        simpa [ObservedAtSelectedOnly, ObservedOnlyAtChildZero,
          otherQuadraticSlot] using hmem.2⟩
    · have hmem := Finset.mem_filter.mp one.2
      exact ⟨one.1, 1, hmem.1, by
        simpa [ObservedAtSelectedOnly, ObservedOnlyAtChildOne,
          otherQuadraticSlot] using hmem.2⟩
  left_inv selector := by
    rcases selector with ⟨q, selected, hmem, hselected⟩
    fin_cases selected <;> rfl
  right_inv entry := by
    rcases entry with ⟨q, hq⟩ | ⟨q, hq⟩ <;> rfl

noncomputable instance instFintypePositiveObservedChildSelector
    {N : Nat} [NeZero N] (m : Lattice.PositiveMassConfig N)
    (observed : Lattice.Site N) :
    Fintype (PositiveObservedChildSelector N m observed) := by
  classical
  exact Fintype.ofEquiv
    (Sum (PositiveObservedOnlyAtChildZeroRepresentative N m observed)
      (PositiveObservedOnlyAtChildOneRepresentative N m observed))
    (positiveObservedChildSelectorEquivSum m observed).symm

/-! ## Exact joins with the two placement parameter bases -/

/-- The carrier parameter is one q-level selector times two outer and two
inner placements. -/
def positiveObservedCarrierParameterEquivSelectorPlacements
    {N : Nat} [NeZero N] (m : Lattice.PositiveMassConfig N)
    (observed : Lattice.Site N) :
    PositiveObservedCarrierParameter N m observed ≃
      PositiveObservedChildSelector N m observed × (Fin 2 × Fin 2) where
  toFun parameter :=
    (⟨parameter.q, parameter.selected, parameter.q_mem,
      parameter.observed_selected⟩,
      (parameter.outerSlot, parameter.innerSlot))
  invFun data :=
    ⟨data.1.q, data.1.observedSlot, data.2.1, data.2.2,
      data.1.q_mem, data.1.observed_only⟩
  left_inv parameter := by cases parameter; rfl
  right_inv data := by rcases data with ⟨selector, placement⟩; rfl

/-- Q-level selectors for which the observed input is the conjugate/free-sign
one input.  This is the exact boundary on which the two-placement surviving
free-observed correction exists. -/
abbrev PositiveObservedChildFreeCorrectionSelector
    (N : Nat) [NeZero N] (m : Lattice.PositiveMassConfig N)
    (observed : Lattice.Site N) :=
  {selector : PositiveObservedChildSelector N m observed //
    quadraticPhaseTermBinarySign selector.q selector.observedSlot = 1}

/-- The surviving free-observed parameter is a sign-one q-level selector
times its two outer placements.  Its distinguished input is the nonobserved
input, hence the `otherQuadraticSlot` in both directions. -/
def positiveObservedFreeParameterEquivCorrectionPlacements
    {N : Nat} [NeZero N] (m : Lattice.PositiveMassConfig N)
    (observed : Lattice.Site N) :
    PositiveObservedFreeConnectedParameter N m observed ≃
      PositiveObservedChildFreeCorrectionSelector N m observed × Fin 2 where
  toFun parameter :=
    (⟨⟨parameter.q, otherQuadraticSlot parameter.selected,
        parameter.q_mem, by
          simpa [ObservedAtSelectedOnly, ObservedAtOtherOnly] using
            parameter.observed_free⟩,
      parameter.free_sign⟩,
      parameter.outerSlot)
  invFun data :=
    ⟨data.1.1.q, otherQuadraticSlot data.1.1.observedSlot, data.2,
      data.1.1.q_mem, by
        simpa [ObservedAtSelectedOnly, ObservedAtOtherOnly] using
          data.1.1.observed_only,
      by simpa using data.1.2⟩
  left_inv parameter := by
    rcases parameter with ⟨q, selected, outer, hmem, hfree, hsign⟩
    fin_cases selected <;> rfl
  right_inv data := by
    rcases data with ⟨⟨⟨q, selected, hmem, hfree⟩, hsign⟩, outer⟩
    fin_cases selected <;> rfl

/-! ## Q-level kernels and exact placement factors -/

def observedChildCarrierKernel
    {N : Nat} [NeZero N]
    (m : Lattice.PositiveMassConfig N) (kappa time : Real)
    (energy : Lattice.Site N → Real) (observed : Lattice.Site N)
    (selector : PositiveObservedChildSelector N m observed) : Real :=
  (quadraticInputInteractionSign selector.q
      selector.observedSlot).coefficient *
    (finiteTimeCollisionKernel m kappa
        (quadraticCollisionSign selector.q) time
        (quadraticCollisionModes observed selector.q) *
      modeAction energy (modeFrequency m) observed *
      modeAction energy (modeFrequency m)
        (selector.q.1 (otherQuadraticSlot selector.observedSlot)))

def observedChildOtherInputLossKernel
    {N : Nat} [NeZero N]
    (m : Lattice.PositiveMassConfig N) (kappa time : Real)
    (energy : Lattice.Site N → Real) (observed : Lattice.Site N)
    (selector : PositiveObservedChildSelector N m observed) : Real :=
  (quadraticInputInteractionSign selector.q
      (otherQuadraticSlot selector.observedSlot)).coefficient *
    (finiteTimeCollisionKernel m kappa
        (quadraticCollisionSign selector.q) time
        (quadraticCollisionModes observed selector.q) *
      modeAction energy (modeFrequency m) observed *
      modeAction energy (modeFrequency m) observed)

def observedChildFourSignedFluxKernel
    {N : Nat} [NeZero N]
    (m : Lattice.PositiveMassConfig N) (kappa time : Real)
    (energy : Lattice.Site N → Real) (observed : Lattice.Site N)
    (selector : PositiveObservedChildSelector N m observed) : Real :=
  4 * finiteTimeCollisionKernel m kappa
        (quadraticCollisionSign selector.q) time
        (quadraticCollisionModes observed selector.q) *
      quadraticSignedCollisionFlux selector.q
        (modeAction energy (modeFrequency m)) observed

/-- The two ordered input modes are distinct on every observed-only selector,
so the deduplicated swap orbit retains both elements. -/
theorem card_quadraticSwapOrbit_eq_two_of_observedChildSelector
    {N : Nat} [NeZero N] (m : Lattice.PositiveMassConfig N)
    (observed : Lattice.Site N)
    (selector : PositiveObservedChildSelector N m observed) :
    (quadraticSwapOrbit selector.q).card = 2 := by
  apply card_quadraticSwapOrbit_eq_two_of_ne
  intro hfixed
  have hmodes : selector.q.1 0 = selector.q.1 1 :=
    ((swapQuadraticPhaseTerm_eq_self_iff selector.q).1 hfixed).1
  generalize hslot : selector.observedSlot = slot
  fin_cases slot
  · exact (selected_ne_other_of_observedAtSelectedOnly
      observed selector.q 0 (by simpa [hslot] using selector.observed_only)) hmodes
  · exact (selected_ne_other_of_observedAtSelectedOnly
      observed selector.q 1 (by simpa [hslot] using selector.observed_only)) hmodes.symm

/-- Exact join of the two original A1 representative strata with the unique
q-level observed-child selector. -/
theorem observedChildRepresentativeA1Gain_eq_selectorSum
    {N : Nat} [NeZero N]
    (m : Lattice.PositiveMassConfig N) (kappa time : Real)
    (energy : Lattice.Site N → Real) (observed : Lattice.Site N) :
    positiveObservedOnlyAtChildZeroRepresentativeA1Gain
          m kappa time energy observed +
        positiveObservedOnlyAtChildOneRepresentativeA1Gain
          m kappa time energy observed =
      ∑ selector : PositiveObservedChildSelector N m observed,
        allDistinctLocalA1Gain
          m kappa time energy observed selector.q := by
  classical
  unfold positiveObservedOnlyAtChildZeroRepresentativeA1Gain
    positiveObservedOnlyAtChildOneRepresentativeA1Gain
  rw [Finset.sum_subtype
      (positiveObservedOnlyAtChildZeroRepresentatives N m observed)
      (fun _ ↦ Iff.rfl) _,
    Finset.sum_subtype
      (positiveObservedOnlyAtChildOneRepresentatives N m observed)
      (fun _ ↦ Iff.rfl) _]
  calc
    (∑ q : PositiveObservedOnlyAtChildZeroRepresentative N m observed,
          allDistinctLocalA1Gain m kappa time energy observed q.1) +
        ∑ q : PositiveObservedOnlyAtChildOneRepresentative N m observed,
          allDistinctLocalA1Gain m kappa time energy observed q.1 =
      ∑ entry : Sum
          (PositiveObservedOnlyAtChildZeroRepresentative N m observed)
          (PositiveObservedOnlyAtChildOneRepresentative N m observed),
        match entry with
        | Sum.inl q => allDistinctLocalA1Gain
            m kappa time energy observed q.1
        | Sum.inr q => allDistinctLocalA1Gain
            m kappa time energy observed q.1 := by
          rw [Fintype.sum_sum_type]
    _ = ∑ selector : PositiveObservedChildSelector N m observed,
        allDistinctLocalA1Gain
          m kappa time energy observed selector.q := by
      simpa [positiveObservedChildSelectorEquivSum] using
        (Equiv.sum_comp
          (positiveObservedChildSelectorEquivSum m observed).symm
          (fun selector : PositiveObservedChildSelector N m observed ↦
            allDistinctLocalA1Gain
              m kappa time energy observed selector.q))

/-- The carrier parameter sum is exactly four copies of its q-level selected
input loss. -/
theorem observedCarrierSignedKernelSum_eq_four_selectorSum
    {N : Nat} [NeZero N]
    (m : Lattice.PositiveMassConfig N) (kappa time : Real)
    (energy : Lattice.Site N → Real) (observed : Lattice.Site N) :
    observedCarrierSignedKernelSum m kappa time energy observed =
      ∑ selector : PositiveObservedChildSelector N m observed,
        4 * observedChildCarrierKernel
          m kappa time energy observed selector := by
  classical
  unfold observedCarrierSignedKernelSum observedChildCarrierKernel
  have hreindex := Equiv.sum_comp
    (positiveObservedCarrierParameterEquivSelectorPlacements m observed)
    (fun data : PositiveObservedChildSelector N m observed × (Fin 2 × Fin 2) ↦
      (quadraticInputInteractionSign data.1.q
          data.1.observedSlot).coefficient *
        (finiteTimeCollisionKernel m kappa
            (quadraticCollisionSign data.1.q) time
            (quadraticCollisionModes observed data.1.q) *
          modeAction energy (modeFrequency m) observed *
          modeAction energy (modeFrequency m)
            (data.1.q.1 (otherQuadraticSlot data.1.observedSlot))))
  have hreindex' :
      (∑ parameter : PositiveObservedCarrierParameter N m observed,
        (quadraticInputInteractionSign parameter.q
            parameter.selected).coefficient *
          (finiteTimeCollisionKernel m kappa
              (quadraticCollisionSign parameter.q) time
              (quadraticCollisionModes observed parameter.q) *
            modeAction energy (modeFrequency m) observed *
            modeAction energy (modeFrequency m)
              (parameter.q.1 (otherQuadraticSlot parameter.selected)))) =
        ∑ data : PositiveObservedChildSelector N m observed × (Fin 2 × Fin 2),
          (quadraticInputInteractionSign data.1.q
              data.1.observedSlot).coefficient *
            (finiteTimeCollisionKernel m kappa
                (quadraticCollisionSign data.1.q) time
                (quadraticCollisionModes observed data.1.q) *
              modeAction energy (modeFrequency m) observed *
              modeAction energy (modeFrequency m)
                (data.1.q.1 (otherQuadraticSlot data.1.observedSlot))) := by
    simpa [positiveObservedCarrierParameterEquivSelectorPlacements] using hreindex
  rw [hreindex']
  simp only [Fintype.sum_prod_type, Fin.sum_univ_two]
  apply Finset.sum_congr rfl
  intro selector _hselector
  ring

/-- The surviving free-observed parameter sum is two copies of the other-input
loss, restricted exactly to selectors whose observed input has sign one. -/
theorem observedFreeCollapsedKernelSum_eq_two_correctionSelectorSum
    {N : Nat} [NeZero N]
    (m : Lattice.PositiveMassConfig N) (kappa time : Real)
    (energy : Lattice.Site N → Real) (observed : Lattice.Site N) :
    observedFreeCollapsedKernelSum m kappa time energy observed =
      ∑ selector : PositiveObservedChildFreeCorrectionSelector N m observed,
        2 * observedChildOtherInputLossKernel
          m kappa time energy observed selector.1 := by
  classical
  unfold observedFreeCollapsedKernelSum observedChildOtherInputLossKernel
  have hreindex := Equiv.sum_comp
    (positiveObservedFreeParameterEquivCorrectionPlacements m observed)
    (fun data : PositiveObservedChildFreeCorrectionSelector N m observed × Fin 2 ↦
      (quadraticInputInteractionSign data.1.1.q
          (otherQuadraticSlot data.1.1.observedSlot)).coefficient *
        (finiteTimeCollisionKernel m kappa
            (quadraticCollisionSign data.1.1.q) time
            (quadraticCollisionModes observed data.1.1.q) *
          modeAction energy (modeFrequency m) observed *
          modeAction energy (modeFrequency m) observed))
  have hreindex' :
      (∑ parameter : PositiveObservedFreeConnectedParameter N m observed,
        (quadraticInputInteractionSign parameter.q
            parameter.selected).coefficient *
          (finiteTimeCollisionKernel m kappa
              (quadraticCollisionSign parameter.q) time
              (quadraticCollisionModes observed parameter.q) *
            modeAction energy (modeFrequency m) observed *
            modeAction energy (modeFrequency m) observed)) =
        ∑ data : PositiveObservedChildFreeCorrectionSelector N m observed × Fin 2,
          (quadraticInputInteractionSign data.1.1.q
              (otherQuadraticSlot data.1.1.observedSlot)).coefficient *
            (finiteTimeCollisionKernel m kappa
                (quadraticCollisionSign data.1.1.q) time
                (quadraticCollisionModes observed data.1.1.q) *
              modeAction energy (modeFrequency m) observed *
              modeAction energy (modeFrequency m) observed) := by
    simpa [positiveObservedFreeParameterEquivCorrectionPlacements] using hreindex
  rw [hreindex']
  simp only [Fintype.sum_prod_type, Fin.sum_univ_two]
  apply Finset.sum_congr rfl
  intro selector _hselector
  ring

/-! ## Signed flux plus the exact placement correction -/

/-- At one q-level selector, the orbit-square A1 gain and four carrier
placements form four signed-flux copies minus the absent four-copy loss at the
other input. -/
theorem observedChildA1_add_fourCarrier_eq_flux_sub_otherLoss
    {N : Nat} [NeZero N]
    (m : Lattice.PositiveMassConfig N) (kappa time : Real)
    (energy : Lattice.Site N → Real) (observed : Lattice.Site N)
    (selector : PositiveObservedChildSelector N m observed) :
    allDistinctLocalA1Gain m kappa time energy observed selector.q +
        4 * observedChildCarrierKernel
          m kappa time energy observed selector =
      observedChildFourSignedFluxKernel
          m kappa time energy observed selector -
        4 * observedChildOtherInputLossKernel
          m kappa time energy observed selector := by
  unfold allDistinctLocalA1Gain observedChildCarrierKernel
    observedChildFourSignedFluxKernel observedChildOtherInputLossKernel
    quadraticSignedCollisionFlux signedThreeWaveCollisionFlux
  rw [card_quadraticSwapOrbit_eq_two_of_observedChildSelector
    m observed selector]
  simp only [Nat.cast_ofNat, Fin.prod_univ_two]
  by_cases hslot : selector.observedSlot = 0
  · have hSelected : observed = selector.q.1 0 := by
      simpa [hslot] using selector.observed_only.1
    simp only [hslot, otherQuadraticSlot_zero]
    rw [← hSelected]
    ring
  · have hslotOne : selector.observedSlot = 1 :=
      Fin.eq_one_of_ne_zero selector.observedSlot hslot
    have hSelected : observed = selector.q.1 1 := by
      simpa [hslotOne] using selector.observed_only.1
    simp only [hslotOne, otherQuadraticSlot_one]
    rw [← hSelected]
    ring

/-- Four signed-flux copies over every observed-child representative. -/
def observedChildFourSignedFluxSum
    {N : Nat} [NeZero N]
    (m : Lattice.PositiveMassConfig N) (kappa time : Real)
    (energy : Lattice.Site N → Real) (observed : Lattice.Site N) : Real :=
  ∑ selector : PositiveObservedChildSelector N m observed,
    observedChildFourSignedFluxKernel
      m kappa time energy observed selector

/-- Exact transparent placement correction.  The first sum restores two
other-input losses only on sign-one observed/free selectors; the second sum
subtracts the four-copy loss that would be needed for a full signed flux on
every observed-child selector. -/
def observedChildPlacementCorrection
    {N : Nat} [NeZero N]
    (m : Lattice.PositiveMassConfig N) (kappa time : Real)
    (energy : Lattice.Site N → Real) (observed : Lattice.Site N) : Real :=
  (∑ selector : PositiveObservedChildFreeCorrectionSelector N m observed,
      2 * observedChildOtherInputLossKernel
        m kappa time energy observed selector.1) -
    ∑ selector : PositiveObservedChildSelector N m observed,
      4 * observedChildOtherInputLossKernel
        m kappa time energy observed selector

/-- Complete q-level observed-child gain--loss closure.  The fixed two-element
swap orbit, four carrier placements, and sign-one two-placement free correction
are all retained explicitly; no cancellation between the two tree strata is
assumed. -/
theorem observedChildA1_add_feedback_eq_fourSignedFlux_add_correction
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
        observedChildPlacementCorrection m kappa time energy observed := by
  rw [observedChildRepresentativeA1Gain_eq_selectorSum,
    carrierFeedback_eq_signedKernelSum
      m kappa time energy observed hObserved hEnergy,
    freeFeedback_eq_collapsedKernelSum
      m kappa time energy observed hObserved hEnergy,
    observedCarrierSignedKernelSum_eq_four_selectorSum,
    observedFreeCollapsedKernelSum_eq_two_correctionSelectorSum]
  unfold observedChildFourSignedFluxSum observedChildPlacementCorrection
  have hlocal :
      (∑ selector : PositiveObservedChildSelector N m observed,
        (allDistinctLocalA1Gain
            m kappa time energy observed selector.q +
          4 * observedChildCarrierKernel
            m kappa time energy observed selector)) =
        ∑ selector : PositiveObservedChildSelector N m observed,
          (observedChildFourSignedFluxKernel
              m kappa time energy observed selector -
            4 * observedChildOtherInputLossKernel
              m kappa time energy observed selector) := by
    apply Finset.sum_congr rfl
    intro selector _hselector
    exact observedChildA1_add_fourCarrier_eq_flux_sub_otherLoss
      m kappa time energy observed selector
  calc
    (∑ selector : PositiveObservedChildSelector N m observed,
          allDistinctLocalA1Gain
            m kappa time energy observed selector.q) +
        (∑ selector : PositiveObservedChildSelector N m observed,
          4 * observedChildCarrierKernel
            m kappa time energy observed selector) +
        ∑ selector : PositiveObservedChildFreeCorrectionSelector N m observed,
          2 * observedChildOtherInputLossKernel
            m kappa time energy observed selector.1 =
      (∑ selector : PositiveObservedChildSelector N m observed,
        (allDistinctLocalA1Gain
            m kappa time energy observed selector.q +
          4 * observedChildCarrierKernel
            m kappa time energy observed selector)) +
        ∑ selector : PositiveObservedChildFreeCorrectionSelector N m observed,
          2 * observedChildOtherInputLossKernel
            m kappa time energy observed selector.1 := by
        rw [Finset.sum_add_distrib]
    _ = (∑ selector : PositiveObservedChildSelector N m observed,
          (observedChildFourSignedFluxKernel
              m kappa time energy observed selector -
            4 * observedChildOtherInputLossKernel
              m kappa time energy observed selector)) +
        ∑ selector : PositiveObservedChildFreeCorrectionSelector N m observed,
          2 * observedChildOtherInputLossKernel
            m kappa time energy observed selector.1 := by rw [hlocal]
    _ = (∑ selector : PositiveObservedChildSelector N m observed,
          observedChildFourSignedFluxKernel
            m kappa time energy observed selector) +
        ((∑ selector : PositiveObservedChildFreeCorrectionSelector N m observed,
            2 * observedChildOtherInputLossKernel
              m kappa time energy observed selector.1) -
          ∑ selector : PositiveObservedChildSelector N m observed,
            4 * observedChildOtherInputLossKernel
              m kappa time energy observed selector) := by
        rw [Finset.sum_sub_distrib]
        ring

end

end ArchonPhysics.FreeFPUTObservedChildQLevelGainLossClosure
