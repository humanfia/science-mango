import ArchonPhysics.FreeFPUTNonAllDistinctFeedbackTreePartition
import ArchonPhysics.FreeFPUTPositiveDegenerateRepresentativeA1Partition
import ArchonPhysics.FreeFPUTTadpoleFeedbackCancellation
import ArchonPhysics.FreeFPUTZeroFrequencyConnectedFeedbackBridge

/-!
# Global closure of the two observed-child feedback strata

The positive-inner non-all-distinct feedback has two strata in which exactly
one outer mode is the observed mode.  They have different global geometry.

* If the first-Picard carrier is observed, the free mode is separated from it.
  Hence no tadpole channel is possible and the four outer/inner placements are
  globally parametrized by a positive canonical quadratic representative.
* If the free outer mode is observed, the two canonical tadpole fibers cancel
  inside this stratum.  The surviving connected fiber has negative free sign;
  its two inner placements coincide, leaving exactly two outer placements.

This module proves the corresponding global equivalences and transports the
physical feedback weight.  In particular, it does not identify a fixed-`q`
constructor image with an original tree fiber before proving global
surjectivity and cross-representative injectivity.
-/

namespace ArchonPhysics.FreeFPUTObservedChildGlobalFeedbackClosure

open ArchonPhysics
open ArchonPhysics.FiniteTimeResonanceWeight
open ArchonPhysics.FreeFPUTA0IteratedQuadraticFeedbackIdentity
open ArchonPhysics.FreeFPUTAllDistinctCanonicalConnectedFiber
open ArchonPhysics.FreeFPUTAllDistinctConnectedReturnSurjectivity
open ArchonPhysics.FreeFPUTAllDistinctLocalSignedGainLoss
open ArchonPhysics.FreeFPUTCanonicalConnectedReturnTree
open ArchonPhysics.FreeFPUTCollisionMismatchBridge
open ArchonPhysics.FreeFPUTConnectedReturnCollisionKernelBridge
open ArchonPhysics.FreeFPUTEnergyCollisionWeightBridge
open ArchonPhysics.FreeFPUTNonAllDistinctFeedbackTreePartition
open ArchonPhysics.FreeFPUTObservedChildDegeneracyPartition
open ArchonPhysics.FreeFPUTPositiveDegenerateRepresentativeA1Partition
open ArchonPhysics.FreeFPUTQuadraticTermSwapSymmetry
open ArchonPhysics.FreeFPUTSwapOrbitCollisionCorrection
open ArchonPhysics.FreeFPUTSwapOrbitRepresentativeReindex
open ArchonPhysics.FreeFPUTTadpoleFeedbackCancellation
open ArchonPhysics.FreeFPUTTensorPhaseExpansion
open ArchonPhysics.FreeFPUTZeroFrequencyConnectedFeedbackBridge
open ArchonPhysics.MatchedIteratedQuadraticCanonicalReturnChannel
open ArchonPhysics.MatchedIteratedQuadraticReturnChannelClassification
open ArchonPhysics.MicroscopicFiniteTimeCollisionPolynomial
open ArchonPhysics.ModalPhaseMismatch
open ArchonPhysics.NormalizedModeCoupling
open ArchonPhysics.PhyslibFPUTIteratedQuadraticSecondPicardCharacterFamily
open ArchonPhysics.PhyslibFPUTSecondOrderA1CollisionGainDecomposition
open ArchonPhysics.PhyslibFPUTSecondOrderExplicitReturnFeedback
open ArchonPhysics.ResonanceWeightSinc
open ArchonPhysics.ThreeSignedChargeCancellationClassification

noncomputable section

/-! ## Canonical observed-child parameters -/

/-- A selected quadratic input is the unique input at the observed mode. -/
def ObservedAtSelectedOnly
    {N : Nat} [NeZero N] (observed : Lattice.Site N)
    (q : QuadraticPhaseTerm N) (selected : Fin 2) : Prop :=
  observed = q.1 selected ∧
    observed ≠ q.1 (otherQuadraticSlot selected)

/-- The selected and opposite inputs are different on the observed-only
stratum. -/
theorem selected_ne_other_of_observedAtSelectedOnly
    {N : Nat} [NeZero N] (observed : Lattice.Site N)
    (q : QuadraticPhaseTerm N) (selected : Fin 2)
    (hSelected : ObservedAtSelectedOnly observed q selected) :
    q.1 selected ≠ q.1 (otherQuadraticSlot selected) := by
  intro hEq
  exact hSelected.2 (hSelected.1.trans hEq)

/-- Swapping the ordered inputs and the distinguished input preserves the
observed-only condition. -/
theorem observedAtSelectedOnly_swap_other
    {N : Nat} [NeZero N] (observed : Lattice.Site N)
    (q : QuadraticPhaseTerm N) (selected : Fin 2)
    (hSelected : ObservedAtSelectedOnly observed q selected) :
    ObservedAtSelectedOnly observed (swapQuadraticPhaseTerm q)
      (otherQuadraticSlot selected) := by
  unfold ObservedAtSelectedOnly at hSelected ⊢
  fin_cases selected <;> simpa using hSelected

/-- Four-placement canonical parameter for the carrier-observed layer. -/
structure PositiveObservedCarrierParameter
    (N : Nat) [NeZero N] (m : Lattice.PositiveMassConfig N)
    (observed : Lattice.Site N) where
  q : QuadraticPhaseTerm N
  selected : Fin 2
  outerSlot : Fin 2
  innerSlot : Fin 2
  q_mem : q ∈ positiveQuadraticSwapOrbitRepresentatives N m observed
  observed_selected : ObservedAtSelectedOnly observed q selected

/-- Fully positive part of the original carrier-observed tree stratum. -/
abbrev FullyPositiveObservedCarrierTerm
    (N : Nat) [NeZero N] (m : Lattice.PositiveMassConfig N)
    (observed : Lattice.Site N) :=
  {term : FreeInitialMatchedIteratedQuadraticTerm N observed //
    term ∈ positiveInnerObservedOnlyAtCarrierReturnTerms m observed ∧
      0 < modeFrequency m (iteratedQuadraticFreeMode term.1)}

/-- The global constructor into the carrier-observed physical tree fiber. -/
def positiveObservedCarrierMap
    {N : Nat} [NeZero N] (m : Lattice.PositiveMassConfig N)
    (observed : Lattice.Site N) :
    PositiveObservedCarrierParameter N m observed →
      FullyPositiveObservedCarrierTerm N m observed := by
  classical
  intro parameter
  let term := matchedConnectedReturnTree observed parameter.q
    parameter.selected parameter.outerSlot parameter.innerSlot
  have hPositive : PositiveModeTuple m
      (quadraticCollisionModes observed parameter.q) := by
    simpa [positiveQuadraticSwapOrbitRepresentatives] using
      (Finset.mem_filter.mp parameter.q_mem).2
  have hCarrierPositive :
      0 < modeFrequency m (parameter.q.1 parameter.selected) := by
    simpa [quadraticCollisionModes] using hPositive (Fin.succ parameter.selected)
  have hFreePositive :
      0 < modeFrequency m
        (parameter.q.1 (otherQuadraticSlot parameter.selected)) := by
    have := hPositive (Fin.succ (otherQuadraticSlot parameter.selected))
    simpa [quadraticCollisionModes] using this
  refine ⟨term, ?_, ?_⟩
  · unfold positiveInnerObservedOnlyAtCarrierReturnTerms
      returnObservedOnlyAtCarrierTerms
    apply Finset.mem_filter.mpr
    refine ⟨?_, ?_⟩
    · unfold positiveInnerMatchedIteratedQuadraticTerms
      apply Finset.mem_filter.mpr
      refine ⟨Finset.mem_univ _, ?_⟩
      simpa only [term, matchedConnectedReturnTree,
        connectedReturnTree_firstPicardMode] using hCarrierPositive
    · unfold ReturnObservedOnlyAtCarrier
      simpa only [ObservedAtSelectedOnly, term, matchedConnectedReturnTree,
        connectedReturnTree_firstPicardMode,
        connectedReturnTree_freeMode] using parameter.observed_selected
  · simpa only [term, matchedConnectedReturnTree,
      connectedReturnTree_freeMode] using hFreePositive

@[simp] theorem positiveObservedCarrierMap_val
    {N : Nat} [NeZero N] (m : Lattice.PositiveMassConfig N)
    (observed : Lattice.Site N)
    (parameter : PositiveObservedCarrierParameter N m observed) :
    (positiveObservedCarrierMap m observed parameter).1.1 =
      connectedReturnTree observed parameter.q parameter.selected
        parameter.outerSlot parameter.innerSlot := rfl

/-! ## Structural bijectivity of the carrier-observed constructor -/

theorem positiveObservedCarrierMap_injective
    {N : Nat} [NeZero N] (m : Lattice.PositiveMassConfig N)
    (observed : Lattice.Site N) :
    Function.Injective (positiveObservedCarrierMap m observed) := by
  classical
  rintro ⟨leftQ, leftSelected, leftOuter, leftInner,
      leftMem, leftObserved⟩
    ⟨rightQ, rightSelected, rightOuter, rightInner,
      rightMem, rightObserved⟩ hMap
  have hTree :
      connectedReturnTree observed leftQ leftSelected leftOuter leftInner =
        connectedReturnTree observed rightQ rightSelected rightOuter
          rightInner := by
    exact congrArg (fun term ↦ term.1.1) hMap
  have hCanonical := congrArg
    (fun term ↦ canonicalQuadraticSwapRepresentative
      (returnTreeOuterQuadraticTerm term)) hTree
  rw [canonicalRepresentative_returnTreeOuter_connectedReturnTree,
    canonicalRepresentative_returnTreeOuter_connectedReturnTree,
    (mem_quadraticSwapOrbitRepresentatives_iff leftQ).1
      (Finset.mem_filter.mp leftMem).1,
    (mem_quadraticSwapOrbitRepresentatives_iff rightQ).1
      (Finset.mem_filter.mp rightMem).1] at hCanonical
  subst rightQ
  have hMode : leftQ.1 leftSelected = leftQ.1 rightSelected := by
    simpa using congrArg iteratedQuadraticFirstPicardMode hTree
  have hSelected : leftSelected = rightSelected := by
    fin_cases leftSelected <;> fin_cases rightSelected
    · rfl
    · exact (selected_ne_other_of_observedAtSelectedOnly
        observed leftQ 0 leftObserved hMode).elim
    · exact (selected_ne_other_of_observedAtSelectedOnly
        observed leftQ 1 leftObserved hMode).elim
    · rfl
  subst rightSelected
  have hPlacement : (leftOuter, leftInner) = (rightOuter, rightInner) :=
    connectedReturnTree_placement_injective observed leftQ leftSelected
      leftObserved.2 hTree
  cases hPlacement
  rfl

/-- A carrier-observed matched tree cannot be a tadpole because its free mode
is separated from the observed mode. -/
theorem not_tadpole_of_returnObservedOnlyAtCarrier
    {N : Nat} [NeZero N] (observed : Lattice.Site N)
    (term : IteratedQuadraticSecondPicardCharacterTerm N)
    (hCarrier : ReturnObservedOnlyAtCarrier observed term) :
    ¬ MatchedIteratedQuadraticTadpoleChannel observed term := by
  intro hTadpole
  rcases hTadpole with hTadpole | hTadpole
  · unfold FreeObservedInnerZeroCancelsInnerOne at hTadpole
    exact hCarrier.2 hTadpole.2.2.2.1.symm
  · unfold FreeObservedInnerOneCancelsInnerZero at hTadpole
    exact hCarrier.2 hTadpole.2.2.2.1.symm

/-- Full collision-mode positivity is invariant under input swap. -/
theorem positiveModeTuple_quadraticCollisionModes_swap_iff
    {N : Nat} [NeZero N] (m : Lattice.PositiveMassConfig N)
    (observed : Lattice.Site N) (q : QuadraticPhaseTerm N) :
    PositiveModeTuple m
        (quadraticCollisionModes observed (swapQuadraticPhaseTerm q)) ↔
      PositiveModeTuple m (quadraticCollisionModes observed q) := by
  constructor <;> intro h leg
  · have := h (quadraticCollisionLegSwap leg)
    fin_cases leg <;>
      simpa [quadraticCollisionModes_swap, Function.comp_apply] using this
  · have := h (quadraticCollisionLegSwap leg)
    fin_cases leg <;>
      simpa [quadraticCollisionModes_swap, Function.comp_apply] using this

theorem positiveObservedCarrierMap_surjective
    {N : Nat} [NeZero N] (m : Lattice.PositiveMassConfig N)
    (observed : Lattice.Site N) :
    Function.Surjective (positiveObservedCarrierMap m observed) := by
  classical
  intro target
  let term : FreeInitialMatchedIteratedQuadraticTerm N observed := target.1
  have hTarget := target.2.1
  unfold positiveInnerObservedOnlyAtCarrierReturnTerms
    returnObservedOnlyAtCarrierTerms at hTarget
  have hParts := Finset.mem_filter.mp hTarget
  have hCarrier : ReturnObservedOnlyAtCarrier observed term.1 := hParts.2
  have hBase := hParts.1
  have hInnerPositive :
      0 < modeFrequency m (iteratedQuadraticFirstPicardMode term.1) := by
    simpa [positiveInnerMatchedIteratedQuadraticTerms] using hBase
  have hObserved : 0 < modeFrequency m observed := by
    rw [hCarrier.1]
    exact hInnerPositive
  have hFreePositive :
      0 < modeFrequency m (iteratedQuadraticFreeMode term.1) := target.2.2
  have hConnected : MatchedIteratedQuadraticConnectedChannel observed term.1 := by
    rcases matchedIteratedQuadratic_tadpole_or_connected observed term.1 term.2 with
      hTadpole | hConnected
    · exact (not_tadpole_of_returnObservedOnlyAtCarrier
        observed term.1 hCarrier hTadpole).elim
    · exact hConnected
  obtain ⟨innerSlot, hTree⟩ :=
    exists_innerSlot_connectedReturnTree_eq_of_connectedChannel
      observed term.1 hConnected
  let raw := returnTreeOuterQuadraticTerm term.1
  let q := canonicalQuadraticSwapRepresentative raw
  let selected := iteratedQuadraticFirstPicardSlot term.1
  have hRawPositive :
      PositiveModeTuple m (quadraticCollisionModes observed raw) := by
    apply positiveModeTuple_quadraticCollisionModes_of_selected_other
      m observed raw selected hObserved
    · simpa [raw, selected] using hInnerPositive
    · simpa [raw, selected] using hFreePositive
  have hQRepresentative : q ∈ quadraticSwapOrbitRepresentatives N := by
    exact canonicalQuadraticSwapRepresentative_mem_representatives raw
  have hQOrbit := canonicalQuadraticSwapRepresentative_mem_swapOrbit raw
  rcases (mem_quadraticSwapOrbit_iff q raw).1 hQOrbit with
      hCanonical | hCanonical
  · have hQPositive :
        PositiveModeTuple m (quadraticCollisionModes observed q) := by
      simpa [hCanonical] using hRawPositive
    have hQMem : q ∈
        positiveQuadraticSwapOrbitRepresentatives N m observed := by
      unfold positiveQuadraticSwapOrbitRepresentatives
      exact Finset.mem_filter.mpr ⟨hQRepresentative, hQPositive⟩
    have hSelected : ObservedAtSelectedOnly observed q selected := by
      unfold ObservedAtSelectedOnly
      simpa [ReturnObservedOnlyAtCarrier, q, raw, selected,
        hCanonical] using hCarrier
    let parameter : PositiveObservedCarrierParameter N m observed :=
      ⟨q, selected, selected, innerSlot, hQMem, hSelected⟩
    refine ⟨parameter, ?_⟩
    apply Subtype.ext
    apply Subtype.ext
    change connectedReturnTree observed q selected selected innerSlot = term.1
    rw [hCanonical]
    exact hTree
  · have hQPositive :
        PositiveModeTuple m (quadraticCollisionModes observed q) := by
      rw [hCanonical]
      exact (positiveModeTuple_quadraticCollisionModes_swap_iff
        m observed raw).2 hRawPositive
    have hQMem : q ∈
        positiveQuadraticSwapOrbitRepresentatives N m observed := by
      unfold positiveQuadraticSwapOrbitRepresentatives
      exact Finset.mem_filter.mpr ⟨hQRepresentative, hQPositive⟩
    have hSelected : ObservedAtSelectedOnly observed q
        (otherQuadraticSlot selected) := by
      have hRawSelected : ObservedAtSelectedOnly observed raw selected := by
        unfold ObservedAtSelectedOnly
        simpa [ReturnObservedOnlyAtCarrier, raw, selected] using hCarrier
      rw [hCanonical]
      exact observedAtSelectedOnly_swap_other
        observed raw selected hRawSelected
    let parameter : PositiveObservedCarrierParameter N m observed :=
      ⟨q, otherQuadraticSlot selected, selected, innerSlot,
        hQMem, hSelected⟩
    refine ⟨parameter, ?_⟩
    apply Subtype.ext
    apply Subtype.ext
    change connectedReturnTree observed q (otherQuadraticSlot selected)
        selected innerSlot = term.1
    rw [hCanonical, connectedReturnTree_swap_distinguished]
    exact hTree

/-- Exact global equivalence; unlike a fixed-`q` image statement, this also
proves uniqueness across canonical swap representatives. -/
def positiveObservedCarrierEquiv
    {N : Nat} [NeZero N] (m : Lattice.PositiveMassConfig N)
    (observed : Lattice.Site N) :
    PositiveObservedCarrierParameter N m observed ≃
      FullyPositiveObservedCarrierTerm N m observed :=
  Equiv.ofBijective (positiveObservedCarrierMap m observed)
    ⟨positiveObservedCarrierMap_injective m observed,
      positiveObservedCarrierMap_surjective m observed⟩

/-! ## Carrier-observed weighted sum -/

/-- Literal fully positive filter used by the carrier equivalence. -/
def fullyPositiveObservedCarrierTerms
    {N : Nat} [NeZero N] (m : Lattice.PositiveMassConfig N)
    (observed : Lattice.Site N) :
    Finset (FreeInitialMatchedIteratedQuadraticTerm N observed) := by
  classical
  exact (positiveInnerObservedOnlyAtCarrierReturnTerms m observed).filter
    fun term ↦ 0 < modeFrequency m (iteratedQuadraticFreeMode term.1)

@[simp] theorem mem_fullyPositiveObservedCarrierTerms_iff
    {N : Nat} [NeZero N] (m : Lattice.PositiveMassConfig N)
    (observed : Lattice.Site N)
    (term : FreeInitialMatchedIteratedQuadraticTerm N observed) :
    term ∈ fullyPositiveObservedCarrierTerms m observed ↔
      term ∈ positiveInnerObservedOnlyAtCarrierReturnTerms m observed ∧
        0 < modeFrequency m (iteratedQuadraticFreeMode term.1) := by
  classical
  simp [fullyPositiveObservedCarrierTerms]

/-- Physical finite-time feedback summand, named once for both strata. -/
def observedChildPhysicalFeedbackWeight
    {N : Nat} [NeZero N]
    (m : Lattice.PositiveMassConfig N) (kappa time : Real)
    (energy : Lattice.Site N → Real) (observed : Lattice.Site N)
    (term : IteratedQuadraticSecondPicardCharacterTerm N) : Real :=
  compactIteratedQuadraticStaticFeedbackWeight m kappa
      (phaseEnergyRadius energy (modeFrequency m)) observed term *
    finiteTimeResonanceWeight (iteratedQuadraticInnerMismatch m term) time

/-- Terms with a nonpositive free frequency vanish before any denominator is
cancelled, so the original carrier stratum restricts to the exact target of
the global equivalence. -/
theorem carrierFeedback_eq_fullyPositive
    {N : Nat} [NeZero N]
    (m : Lattice.PositiveMassConfig N) (kappa time : Real)
    (energy : Lattice.Site N → Real) (observed : Lattice.Site N)
    (hObserved : 0 < modeFrequency m observed) :
    positiveInnerObservedOnlyAtCarrierFeedbackRemainder m kappa time
        (phaseEnergyRadius energy (modeFrequency m)) observed =
      ∑ term ∈ fullyPositiveObservedCarrierTerms m observed,
        observedChildPhysicalFeedbackWeight
          m kappa time energy observed term.1 := by
  classical
  unfold positiveInnerObservedOnlyAtCarrierFeedbackRemainder
    fullyPositiveObservedCarrierTerms
    observedChildPhysicalFeedbackWeight
  rw [Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro term hTerm
  have hInner :
      0 < modeFrequency m (iteratedQuadraticFirstPicardMode term.1) := by
    have hBase := (Finset.mem_filter.mp hTerm).1
    simpa [positiveInnerMatchedIteratedQuadraticTerms] using hBase
  by_cases hFree :
      0 < modeFrequency m (iteratedQuadraticFreeMode term.1)
  · rw [if_pos hFree]
  · rw [if_neg hFree,
      compactIteratedQuadraticStaticFeedbackWeight_eq_zero_of_not_freeFrequency_pos
        m kappa (phaseEnergyRadius energy (modeFrequency m)) observed term.1
          hObserved hInner hFree]
    simp

noncomputable instance instFintypePositiveObservedCarrierParameter
    {N : Nat} [NeZero N] (m : Lattice.PositiveMassConfig N)
    (observed : Lattice.Site N) :
    Fintype (PositiveObservedCarrierParameter N m observed) := by
  classical
  exact Fintype.ofEquiv
    (FullyPositiveObservedCarrierTerm N m observed)
    (positiveObservedCarrierEquiv m observed).symm

/-- The fully positive original finset is reindexed by the proved global
equivalence, with every selector and placement retained. -/
theorem sum_fullyPositiveCarrier_eq_parameters
    {N : Nat} [NeZero N] {M : Type*} [AddCommMonoid M]
    (m : Lattice.PositiveMassConfig N) (observed : Lattice.Site N)
    (weight : FreeInitialMatchedIteratedQuadraticTerm N observed → M) :
    (∑ term ∈ fullyPositiveObservedCarrierTerms m observed, weight term) =
      ∑ parameter : PositiveObservedCarrierParameter N m observed,
        weight (positiveObservedCarrierMap m observed parameter).1 := by
  classical
  let equivalence := positiveObservedCarrierEquiv m observed
  apply Finset.sum_bij
    (fun term hTerm ↦ equivalence.symm
      ⟨term, (mem_fullyPositiveObservedCarrierTerms_iff
        m observed term).1 hTerm⟩)
  · intro term hTerm
    simp
  · intro left hLeft right hRight hEq
    have hSubtype :
        (⟨left, (mem_fullyPositiveObservedCarrierTerms_iff
          m observed left).1 hLeft⟩ :
            FullyPositiveObservedCarrierTerm N m observed) =
          ⟨right, (mem_fullyPositiveObservedCarrierTerms_iff
            m observed right).1 hRight⟩ := by
      rw [← equivalence.apply_symm_apply
          (⟨left, (mem_fullyPositiveObservedCarrierTerms_iff
            m observed left).1 hLeft⟩ :
              FullyPositiveObservedCarrierTerm N m observed),
        ← equivalence.apply_symm_apply
          (⟨right, (mem_fullyPositiveObservedCarrierTerms_iff
            m observed right).1 hRight⟩ :
              FullyPositiveObservedCarrierTerm N m observed)]
      exact congrArg equivalence hEq
    exact congrArg Subtype.val hSubtype
  · intro parameter _hParameter
    refine ⟨(positiveObservedCarrierMap m observed parameter).1,
      (mem_fullyPositiveObservedCarrierTerms_iff m observed _).2
        (positiveObservedCarrierMap m observed parameter).2, ?_⟩
    exact equivalence.symm_apply_apply parameter
  · intro term hTerm
    have hApply := equivalence.apply_symm_apply
      (⟨term, (mem_fullyPositiveObservedCarrierTerms_iff
        m observed term).1 hTerm⟩ :
          FullyPositiveObservedCarrierTerm N m observed)
    exact (congrArg (fun candidate ↦ weight candidate.1) hApply).symm

/-- Exact weight transport on one carrier parameter. -/
theorem observedCarrierMap_feedback_eq_signedKernel
    {N : Nat} [NeZero N]
    (m : Lattice.PositiveMassConfig N) (kappa time : Real)
    (energy : Lattice.Site N → Real) (observed : Lattice.Site N)
    (parameter : PositiveObservedCarrierParameter N m observed)
    (hEnergy : ∀ mode, 0 ≤ energy mode) :
    observedChildPhysicalFeedbackWeight m kappa time energy observed
        (positiveObservedCarrierMap m observed parameter).1.1 =
      (quadraticInputInteractionSign parameter.q
          parameter.selected).coefficient *
        (finiteTimeCollisionKernel m kappa
            (quadraticCollisionSign parameter.q) time
            (quadraticCollisionModes observed parameter.q) *
          modeAction energy (modeFrequency m) observed *
          modeAction energy (modeFrequency m)
            (parameter.q.1 (otherQuadraticSlot parameter.selected))) := by
  classical
  have hPositive : PositiveModeTuple m
      (quadraticCollisionModes observed parameter.q) := by
    simpa [positiveQuadraticSwapOrbitRepresentatives] using
      (Finset.mem_filter.mp parameter.q_mem).2
  unfold observedChildPhysicalFeedbackWeight
  rw [positiveObservedCarrierMap_val,
    connectedReturnTree_innerMismatch, finiteTimeResonanceWeight_neg]
  simpa only [quadraticCollisionSign_succ] using
    (connectedReturnTree_feedback_eq_signedKernel_mul_actions
      m kappa time energy observed parameter.q parameter.selected
        parameter.outerSlot parameter.innerSlot hEnergy hPositive)

/-- Exact carrier-observed feedback: four placements of the selected-input
signed loss for every positive canonical observed-child parameter. -/
theorem carrierFeedback_eq_parameterSignedKernel
    {N : Nat} [NeZero N]
    (m : Lattice.PositiveMassConfig N) (kappa time : Real)
    (energy : Lattice.Site N → Real) (observed : Lattice.Site N)
    (hObserved : 0 < modeFrequency m observed)
    (hEnergy : ∀ mode, 0 ≤ energy mode) :
    positiveInnerObservedOnlyAtCarrierFeedbackRemainder m kappa time
        (phaseEnergyRadius energy (modeFrequency m)) observed =
      ∑ parameter : PositiveObservedCarrierParameter N m observed,
        (quadraticInputInteractionSign parameter.q
            parameter.selected).coefficient *
          (finiteTimeCollisionKernel m kappa
              (quadraticCollisionSign parameter.q) time
              (quadraticCollisionModes observed parameter.q) *
            modeAction energy (modeFrequency m) observed *
            modeAction energy (modeFrequency m)
              (parameter.q.1
                (otherQuadraticSlot parameter.selected))) := by
  rw [carrierFeedback_eq_fullyPositive m kappa time energy observed hObserved,
    sum_fullyPositiveCarrier_eq_parameters]
  apply Finset.sum_congr rfl
  intro parameter _hParameter
  exact observedCarrierMap_feedback_eq_signedKernel
    m kappa time energy observed parameter hEnergy

/-! ## Free-observed tadpole cancellation -/

/-- Free-observed trees assigned to one of the four connected selector
labels. -/
def positiveInnerObservedOnlyAtFreeConnectedTerms
    {N : Nat} [NeZero N] (m : Lattice.PositiveMassConfig N)
    (observed : Lattice.Site N) :
    Finset (FreeInitialMatchedIteratedQuadraticTerm N observed) := by
  classical
  exact (positiveInnerObservedOnlyAtFreeReturnTerms m observed).filter
    fun term ↦ canonicalReturnChannel observed term ∈
      canonicalConnectedReturnChannels

/-- Complementary free-observed selector fibers.  These are precisely the
two canonical tadpole labels, but keeping the complement as one finset makes
the cancellation involution literal. -/
def positiveInnerObservedOnlyAtFreeTadpoleTerms
    {N : Nat} [NeZero N] (m : Lattice.PositiveMassConfig N)
    (observed : Lattice.Site N) :
    Finset (FreeInitialMatchedIteratedQuadraticTerm N observed) := by
  classical
  exact (positiveInnerObservedOnlyAtFreeReturnTerms m observed).filter
    fun term ↦ canonicalReturnChannel observed term ∉
      canonicalConnectedReturnChannels

/-- Exact connected/tadpole partition of the original free-observed base. -/
theorem sum_positiveInnerObservedOnlyAtFree_eq_connected_add_tadpole
    {N : Nat} [NeZero N] {M : Type*} [AddCommMonoid M]
    (m : Lattice.PositiveMassConfig N) (observed : Lattice.Site N)
    (weight : FreeInitialMatchedIteratedQuadraticTerm N observed → M) :
    (∑ term ∈ positiveInnerObservedOnlyAtFreeReturnTerms m observed,
        weight term) =
      (∑ term ∈ positiveInnerObservedOnlyAtFreeConnectedTerms m observed,
        weight term) +
      ∑ term ∈ positiveInnerObservedOnlyAtFreeTadpoleTerms m observed,
        weight term := by
  classical
  unfold positiveInnerObservedOnlyAtFreeConnectedTerms
    positiveInnerObservedOnlyAtFreeTadpoleTerms
  exact (Finset.sum_filter_add_sum_filter_not
    (positiveInnerObservedOnlyAtFreeReturnTerms m observed)
    (fun term ↦ canonicalReturnChannel observed term ∈
      canonicalConnectedReturnChannels) weight).symm

/-- The inner-branch flip fixes both outer modes, hence preserves the
free-observed-only stratum. -/
@[simp] theorem mem_positiveInnerObservedOnlyAtFree_flip_iff
    {N : Nat} [NeZero N] (m : Lattice.PositiveMassConfig N)
    (observed : Lattice.Site N)
    (term : FreeInitialMatchedIteratedQuadraticTerm N observed) :
    flipMatchedIteratedQuadraticInnerBranch observed term ∈
        positiveInnerObservedOnlyAtFreeReturnTerms m observed ↔
      term ∈ positiveInnerObservedOnlyAtFreeReturnTerms m observed := by
  classical
  unfold positiveInnerObservedOnlyAtFreeReturnTerms
    returnObservedOnlyAtFreeTerms ReturnObservedOnlyAtFree
  simp only [Finset.mem_filter,
    mem_positiveInnerMatchedIteratedQuadraticTerms_flip_iff,
    flipMatchedIteratedQuadraticInnerBranch_coe,
    flipIteratedQuadraticInnerBranch_freeMode,
    flipIteratedQuadraticInnerBranch_firstPicardMode]

/-- The entire complementary selector part really is tadpole, with no claim
that the underlying raw six predicates are disjoint. -/
theorem tadpole_of_mem_positiveInnerObservedOnlyAtFreeTadpoleTerms
    {N : Nat} [NeZero N] (m : Lattice.PositiveMassConfig N)
    (observed : Lattice.Site N)
    (term : FreeInitialMatchedIteratedQuadraticTerm N observed)
    (hTerm : term ∈
      positiveInnerObservedOnlyAtFreeTadpoleTerms m observed) :
    MatchedIteratedQuadraticTadpoleChannel observed term.1 := by
  classical
  have hNotConnected := (Finset.mem_filter.mp hTerm).2
  have hLabel :
      canonicalReturnChannel observed term =
          .freeObservedInnerZeroCancelsInnerOne ∨
        canonicalReturnChannel observed term =
          .freeObservedInnerOneCancelsInnerZero := by
    by_cases hFirst : canonicalReturnChannel observed term =
        .freeObservedInnerZeroCancelsInnerOne
    · exact Or.inl hFirst
    · right
      by_contra hThird
      exact hNotConnected
        ((mem_canonicalConnectedReturnChannels_iff _).2
          ⟨hFirst, hThird⟩)
  rcases hLabel with hFirst | hThird
  · left
    have hRaw := canonicalReturnChannel_rawHolds observed term
    rw [hFirst] at hRaw
    simpa only [CanonicalReturnChannel.RawHolds] using hRaw
  · right
    have hRaw := canonicalReturnChannel_rawHolds observed term
    rw [hThird] at hRaw
    simpa only [CanonicalReturnChannel.RawHolds] using hRaw

/-- The restricted free-observed tadpole base is invariant under the branch
flip. -/
@[simp] theorem mem_positiveInnerObservedOnlyAtFreeTadpoleTerms_flip_iff
    {N : Nat} [NeZero N] (m : Lattice.PositiveMassConfig N)
    (observed : Lattice.Site N)
    (term : FreeInitialMatchedIteratedQuadraticTerm N observed) :
    flipMatchedIteratedQuadraticInnerBranch observed term ∈
        positiveInnerObservedOnlyAtFreeTadpoleTerms m observed ↔
      term ∈ positiveInnerObservedOnlyAtFreeTadpoleTerms m observed := by
  classical
  unfold positiveInnerObservedOnlyAtFreeTadpoleTerms
  simp only [Finset.mem_filter,
    mem_positiveInnerObservedOnlyAtFree_flip_iff,
    canonicalReturnChannel_flipMatchedIteratedQuadraticInnerBranch]

/-- The tadpole part cancels inside the free-observed stratum itself; no
all-equal or carrier-observed tree is borrowed from another stratum. -/
theorem freeObservedTadpoleFeedbackSum_eq_zero
    {N : Nat} [NeZero N]
    (m : Lattice.PositiveMassConfig N) (kappa time : Real)
    (energy : Lattice.Site N → Real) (observed : Lattice.Site N) :
    (∑ term ∈ positiveInnerObservedOnlyAtFreeTadpoleTerms m observed,
      observedChildPhysicalFeedbackWeight
        m kappa time energy observed term.1) = 0 := by
  classical
  apply Finset.sum_involution
    (fun term _hTerm ↦
      flipMatchedIteratedQuadraticInnerBranch observed term)
  · intro term hTerm
    unfold observedChildPhysicalFeedbackWeight
    change
      compactIteratedQuadraticStaticFeedbackWeight m kappa
            (phaseEnergyRadius energy (modeFrequency m)) observed term.1 *
          finiteTimeResonanceWeight
            (iteratedQuadraticInnerMismatch m term.1) time +
        compactIteratedQuadraticStaticFeedbackWeight m kappa
            (phaseEnergyRadius energy (modeFrequency m)) observed
            (flipIteratedQuadraticInnerBranch term.1) *
          finiteTimeResonanceWeight
            (iteratedQuadraticInnerMismatch m
              (flipIteratedQuadraticInnerBranch term.1)) time = 0
    rw [compactFeedbackSummand_flip_eq_neg_of_tadpole
      m kappa time (phaseEnergyRadius energy (modeFrequency m)) observed
        term.1
        (tadpole_of_mem_positiveInnerObservedOnlyAtFreeTadpoleTerms
          m observed term hTerm)]
    ring
  · intro term _hTerm _hNonzero
    exact flipMatchedIteratedQuadraticInnerBranch_ne observed term
  · intro term hTerm
    exact (mem_positiveInnerObservedOnlyAtFreeTadpoleTerms_flip_iff
      m observed term).2 hTerm
  · intro term _hTerm
    exact flipMatchedIteratedQuadraticInnerBranch_involutive observed term

/-- Consequently the complete free-observed physical remainder is exactly
its connected-selector subfiber. -/
theorem freeFeedback_eq_connected
    {N : Nat} [NeZero N]
    (m : Lattice.PositiveMassConfig N) (kappa time : Real)
    (energy : Lattice.Site N → Real) (observed : Lattice.Site N) :
    positiveInnerObservedOnlyAtFreeFeedbackRemainder m kappa time
        (phaseEnergyRadius energy (modeFrequency m)) observed =
      ∑ term ∈ positiveInnerObservedOnlyAtFreeConnectedTerms m observed,
        observedChildPhysicalFeedbackWeight
          m kappa time energy observed term.1 := by
  unfold positiveInnerObservedOnlyAtFreeFeedbackRemainder
  change
    (∑ term ∈ positiveInnerObservedOnlyAtFreeReturnTerms m observed,
      observedChildPhysicalFeedbackWeight
        m kappa time energy observed term.1) = _
  rw [sum_positiveInnerObservedOnlyAtFree_eq_connected_add_tadpole,
    freeObservedTadpoleFeedbackSum_eq_zero]
  simp

/-! ## Global parametrization of the surviving free-observed fiber -/

/-- On a free-observed-only tree, a connected selector label must be channel
five.  Labels two and four overlap an earlier tadpole predicate, while label
six overlaps channel five, so the first-match priority excludes them. -/
theorem canonicalReturnChannel_eq_fifth_of_freeOnly_connected
    {N : Nat} [NeZero N] (observed : Lattice.Site N)
    (term : FreeInitialMatchedIteratedQuadraticTerm N observed)
    (hFree : ReturnObservedOnlyAtFree observed term.1)
    (hConnectedLabel : canonicalReturnChannel observed term ∈
      canonicalConnectedReturnChannels) :
    canonicalReturnChannel observed term =
      .innerZeroObservedInnerOneCancelsFree := by
  cases hChannel : canonicalReturnChannel observed term
  · simp [hChannel] at hConnectedLabel
  · have hPriority :=
      (canonicalReturnChannel_eq_iff_priorityHolds observed term
        .innerZeroObservedFreeCancelsInnerOne).1 hChannel
    have hEarlier : CanonicalReturnChannel.RawHolds
        .freeObservedInnerZeroCancelsInnerOne observed term.1 := by
      unfold CanonicalReturnChannel.PriorityHolds at hPriority
      unfold CanonicalReturnChannel.RawHolds at hPriority ⊢
      unfold InnerZeroObservedFreeCancelsInnerOne at hPriority
      unfold FreeObservedInnerZeroCancelsInnerOne
      unfold ReturnObservedOnlyAtFree at hFree
      dsimp only at hPriority ⊢
      rcases hPriority.2 with ⟨hFreeSign, hZeroSign, hOneSign,
        hZeroMode, hCancelMode⟩
      have hFreeMode :
          (iteratedQuadraticFreeSignedLeg term.1).mode = observed := by
        change iteratedQuadraticFreeMode term.1 = observed
        exact hFree.1.symm
      exact ⟨hFreeSign, hZeroSign, hOneSign,
        hFreeMode,
        hZeroMode.trans (hFreeMode.symm.trans hCancelMode)⟩
    exact (hPriority.1 hEarlier).elim
  · simp [hChannel] at hConnectedLabel
  · have hPriority :=
      (canonicalReturnChannel_eq_iff_priorityHolds observed term
        .innerOneObservedFreeCancelsInnerZero).1 hChannel
    have hEarlier : CanonicalReturnChannel.RawHolds
        .freeObservedInnerOneCancelsInnerZero observed term.1 := by
      unfold CanonicalReturnChannel.PriorityHolds at hPriority
      unfold CanonicalReturnChannel.RawHolds at hPriority ⊢
      unfold InnerOneObservedFreeCancelsInnerZero at hPriority
      unfold FreeObservedInnerOneCancelsInnerZero
      unfold ReturnObservedOnlyAtFree at hFree
      dsimp only at hPriority ⊢
      rcases hPriority.2.2.2 with ⟨hFreeSign, hZeroSign, hOneSign,
        hOneMode, hCancelMode⟩
      have hFreeMode :
          (iteratedQuadraticFreeSignedLeg term.1).mode = observed := by
        change iteratedQuadraticFreeMode term.1 = observed
        exact hFree.1.symm
      exact ⟨hFreeSign, hZeroSign, hOneSign,
        hFreeMode,
        hOneMode.trans (hFreeMode.symm.trans hCancelMode)⟩
    exact (hPriority.2.2.1 hEarlier).elim
  · rfl
  · have hPriority :=
      (canonicalReturnChannel_eq_iff_priorityHolds observed term
        .innerOneObservedInnerZeroCancelsFree).1 hChannel
    have hEarlier : CanonicalReturnChannel.RawHolds
        .innerZeroObservedInnerOneCancelsFree observed term.1 := by
      unfold CanonicalReturnChannel.PriorityHolds at hPriority
      unfold CanonicalReturnChannel.RawHolds at hPriority ⊢
      unfold InnerOneObservedInnerZeroCancelsFree at hPriority
      unfold InnerZeroObservedInnerOneCancelsFree
      unfold ReturnObservedOnlyAtFree at hFree
      dsimp only at hPriority ⊢
      rcases hPriority.2.2.2.2.2 with
        ⟨hFreeSign, hZeroSign, hOneSign, hOneMode, hCancelMode⟩
      have hFreeMode :
          (iteratedQuadraticFreeSignedLeg term.1).mode = observed := by
        change iteratedQuadraticFreeMode term.1 = observed
        exact hFree.1.symm
      exact ⟨hFreeSign, hZeroSign, hOneSign,
        hCancelMode.trans hFreeMode,
        hOneMode.trans hFreeMode.symm⟩
    exact (hPriority.2.2.2.2.1 hEarlier).elim

/-- Channel five has a conjugate free leg, hence raw binary free sign one. -/
theorem freeSign_eq_one_of_canonicalChannel_fifth
    {N : Nat} [NeZero N] (observed : Lattice.Site N)
    (term : FreeInitialMatchedIteratedQuadraticTerm N observed)
    (hFifth : canonicalReturnChannel observed term =
      .innerZeroObservedInnerOneCancelsFree) :
    iteratedQuadraticFreeSign term.1 = 1 := by
  have hRaw := canonicalReturnChannel_rawHolds observed term
  rw [hFifth] at hRaw
  unfold CanonicalReturnChannel.RawHolds
    InnerZeroObservedInnerOneCancelsFree at hRaw
  have hSign := hRaw.1
  unfold iteratedQuadraticFreeSignedLeg binarySignedMode at hSign
  generalize hValue : iteratedQuadraticFreeSign term.1 = sign at hSign ⊢
  fin_cases sign
  · simp [binaryPhaseSign] at hSign
  · rfl

/-- The input opposite `selected` is the unique observed input. -/
def ObservedAtOtherOnly
    {N : Nat} [NeZero N] (observed : Lattice.Site N)
    (q : QuadraticPhaseTerm N) (selected : Fin 2) : Prop :=
  observed = q.1 (otherQuadraticSlot selected) ∧
    observed ≠ q.1 selected

theorem observedAtOtherOnly_swap_other
    {N : Nat} [NeZero N] (observed : Lattice.Site N)
    (q : QuadraticPhaseTerm N) (selected : Fin 2)
    (hFree : ObservedAtOtherOnly observed q selected) :
    ObservedAtOtherOnly observed (swapQuadraticPhaseTerm q)
      (otherQuadraticSlot selected) := by
  unfold ObservedAtOtherOnly at hFree ⊢
  fin_cases selected <;> simpa using hFree

@[simp] theorem quadraticPhaseTermBinarySign_swap_apply
    {N : Nat} [NeZero N] (q : QuadraticPhaseTerm N) (slot : Fin 2) :
    quadraticPhaseTermBinarySign (swapQuadraticPhaseTerm q) slot =
      quadraticPhaseTermBinarySign q (otherQuadraticSlot slot) := by
  fin_cases slot <;> rfl

/-- Two-placement canonical parameter for the surviving free-observed
connected fiber. -/
structure PositiveObservedFreeConnectedParameter
    (N : Nat) [NeZero N] (m : Lattice.PositiveMassConfig N)
    (observed : Lattice.Site N) where
  q : QuadraticPhaseTerm N
  selected : Fin 2
  outerSlot : Fin 2
  q_mem : q ∈ positiveQuadraticSwapOrbitRepresentatives N m observed
  observed_free : ObservedAtOtherOnly observed q selected
  free_sign : quadraticPhaseTermBinarySign q
    (otherQuadraticSlot selected) = 1

abbrev ObservedFreeConnectedTerm
    (N : Nat) [NeZero N] (m : Lattice.PositiveMassConfig N)
    (observed : Lattice.Site N) :=
  {term : FreeInitialMatchedIteratedQuadraticTerm N observed //
    term ∈ positiveInnerObservedOnlyAtFreeConnectedTerms m observed}

def positiveObservedFreeConnectedMap
    {N : Nat} [NeZero N] (m : Lattice.PositiveMassConfig N)
    (observed : Lattice.Site N) :
    PositiveObservedFreeConnectedParameter N m observed →
      ObservedFreeConnectedTerm N m observed := by
  classical
  intro parameter
  let term := matchedConnectedReturnTree observed parameter.q
    parameter.selected parameter.outerSlot 0
  refine ⟨term, ?_⟩
  unfold positiveInnerObservedOnlyAtFreeConnectedTerms
  apply Finset.mem_filter.mpr
  refine ⟨?_, ?_⟩
  · unfold positiveInnerObservedOnlyAtFreeReturnTerms
      returnObservedOnlyAtFreeTerms
    apply Finset.mem_filter.mpr
    refine ⟨?_, ?_⟩
    · unfold positiveInnerMatchedIteratedQuadraticTerms
      apply Finset.mem_filter.mpr
      refine ⟨Finset.mem_univ _, ?_⟩
      have hPositive : PositiveModeTuple m
          (quadraticCollisionModes observed parameter.q) := by
        simpa [positiveQuadraticSwapOrbitRepresentatives] using
          (Finset.mem_filter.mp parameter.q_mem).2
      simpa only [term, matchedConnectedReturnTree,
        connectedReturnTree_firstPicardMode,
        quadraticCollisionModes_succ] using
        hPositive (Fin.succ parameter.selected)
    · unfold ReturnObservedOnlyAtFree
      simpa only [ObservedAtOtherOnly, term, matchedConnectedReturnTree,
        connectedReturnTree_freeMode,
        connectedReturnTree_firstPicardMode] using parameter.observed_free
  · rw [mem_canonicalConnectedReturnChannels_iff]
    have hLabel :=
      canonicalReturnChannel_connectedReturnTree_allEqual_freeSignOne
        observed parameter.q parameter.selected parameter.outerSlot 0
          parameter.observed_free.1 parameter.free_sign
    rw [show canonicalReturnChannel observed term =
        .innerZeroObservedInnerOneCancelsFree by exact hLabel]
    decide

@[simp] theorem positiveObservedFreeConnectedMap_val
    {N : Nat} [NeZero N] (m : Lattice.PositiveMassConfig N)
    (observed : Lattice.Site N)
    (parameter : PositiveObservedFreeConnectedParameter N m observed) :
    (positiveObservedFreeConnectedMap m observed parameter).1.1 =
      connectedReturnTree observed parameter.q parameter.selected
        parameter.outerSlot 0 := rfl

theorem positiveObservedFreeConnectedMap_injective
    {N : Nat} [NeZero N] (m : Lattice.PositiveMassConfig N)
    (observed : Lattice.Site N) :
    Function.Injective (positiveObservedFreeConnectedMap m observed) := by
  classical
  rintro ⟨leftQ, leftSelected, leftOuter, leftMem, leftFree, leftSign⟩
    ⟨rightQ, rightSelected, rightOuter, rightMem, rightFree, rightSign⟩ hMap
  have hTree :
      connectedReturnTree observed leftQ leftSelected leftOuter 0 =
        connectedReturnTree observed rightQ rightSelected rightOuter 0 :=
    congrArg (fun term ↦ term.1.1) hMap
  have hCanonical := congrArg
    (fun term ↦ canonicalQuadraticSwapRepresentative
      (returnTreeOuterQuadraticTerm term)) hTree
  rw [canonicalRepresentative_returnTreeOuter_connectedReturnTree,
    canonicalRepresentative_returnTreeOuter_connectedReturnTree,
    (mem_quadraticSwapOrbitRepresentatives_iff leftQ).1
      (Finset.mem_filter.mp leftMem).1,
    (mem_quadraticSwapOrbitRepresentatives_iff rightQ).1
      (Finset.mem_filter.mp rightMem).1] at hCanonical
  subst rightQ
  have hMode : leftQ.1 leftSelected = leftQ.1 rightSelected := by
    simpa using congrArg iteratedQuadraticFirstPicardMode hTree
  have hSelected : leftSelected = rightSelected := by
    fin_cases leftSelected <;> fin_cases rightSelected
    · rfl
    · exact (leftFree.2 (leftFree.1.trans hMode.symm)).elim
    · exact (leftFree.2 (leftFree.1.trans hMode.symm)).elim
    · rfl
  subst rightSelected
  have hOuter : leftOuter = rightOuter := by
    simpa using congrArg iteratedQuadraticFirstPicardSlot hTree
  subst rightOuter
  rfl

theorem positiveObservedFreeConnectedMap_surjective
    {N : Nat} [NeZero N] (m : Lattice.PositiveMassConfig N)
    (observed : Lattice.Site N)
    (hObserved : 0 < modeFrequency m observed) :
    Function.Surjective (positiveObservedFreeConnectedMap m observed) := by
  classical
  intro target
  let term : FreeInitialMatchedIteratedQuadraticTerm N observed := target.1
  have hConnectedMem := Finset.mem_filter.mp target.2
  have hFreeMem := hConnectedMem.1
  have hFreeParts := Finset.mem_filter.mp hFreeMem
  have hFree : ReturnObservedOnlyAtFree observed term.1 := hFreeParts.2
  have hBase := hFreeParts.1
  have hCarrierPositive :
      0 < modeFrequency m (iteratedQuadraticFirstPicardMode term.1) := by
    simpa [positiveInnerMatchedIteratedQuadraticTerms] using hBase
  have hFifth := canonicalReturnChannel_eq_fifth_of_freeOnly_connected
    observed term hFree hConnectedMem.2
  have hFreeSign : iteratedQuadraticFreeSign term.1 = 1 :=
    freeSign_eq_one_of_canonicalChannel_fifth observed term hFifth
  have hRawConnected : MatchedIteratedQuadraticConnectedChannel
      observed term.1 := by
    have hRaw := canonicalReturnChannel_rawHolds observed term
    rw [hFifth] at hRaw
    exact Or.inr (Or.inr (Or.inl (by
      simpa only [CanonicalReturnChannel.RawHolds] using hRaw)))
  obtain ⟨innerSlot, hTree⟩ :=
    exists_innerSlot_connectedReturnTree_eq_of_connectedChannel
      observed term.1 hRawConnected
  let raw := returnTreeOuterQuadraticTerm term.1
  let q := canonicalQuadraticSwapRepresentative raw
  let selected := iteratedQuadraticFirstPicardSlot term.1
  have hRawPositive : PositiveModeTuple m
      (quadraticCollisionModes observed raw) := by
    apply positiveModeTuple_quadraticCollisionModes_of_selected_other
      m observed raw selected hObserved
    · simpa [raw, selected] using hCarrierPositive
    · have hFreePositive :
          0 < modeFrequency m (iteratedQuadraticFreeMode term.1) := by
        rw [← hFree.1]
        exact hObserved
      simpa [raw, selected] using hFreePositive
  have hRawFree : ObservedAtOtherOnly observed raw selected := by
    unfold ObservedAtOtherOnly
    simpa [ReturnObservedOnlyAtFree, raw, selected] using hFree
  have hRawSign : quadraticPhaseTermBinarySign raw
      (otherQuadraticSlot selected) = 1 := by
    simpa [raw, selected] using hFreeSign
  have hQRep : q ∈ quadraticSwapOrbitRepresentatives N :=
    canonicalQuadraticSwapRepresentative_mem_representatives raw
  have hQOrbit := canonicalQuadraticSwapRepresentative_mem_swapOrbit raw
  rcases (mem_quadraticSwapOrbit_iff q raw).1 hQOrbit with
      hCanonical | hCanonical
  · have hQPositive : PositiveModeTuple m
        (quadraticCollisionModes observed q) := by
      simpa [hCanonical] using hRawPositive
    have hQMem : q ∈ positiveQuadraticSwapOrbitRepresentatives
        N m observed := Finset.mem_filter.mpr ⟨hQRep, hQPositive⟩
    have hQFree : ObservedAtOtherOnly observed q selected := by
      simpa [hCanonical] using hRawFree
    have hQSign : quadraticPhaseTermBinarySign q
        (otherQuadraticSlot selected) = 1 := by
      simpa [hCanonical] using hRawSign
    let parameter : PositiveObservedFreeConnectedParameter N m observed :=
      ⟨q, selected, selected, hQMem, hQFree, hQSign⟩
    refine ⟨parameter, ?_⟩
    apply Subtype.ext
    apply Subtype.ext
    change connectedReturnTree observed q selected selected 0 = term.1
    rw [← connectedReturnTree_innerPlacement_eq_zero_of_allEqual_freeSignOne
      observed q selected selected innerSlot hQFree.1 hQSign,
      hCanonical]
    exact hTree
  · have hQPositive : PositiveModeTuple m
        (quadraticCollisionModes observed q) := by
      rw [hCanonical]
      exact (positiveModeTuple_quadraticCollisionModes_swap_iff
        m observed raw).2 hRawPositive
    have hQMem : q ∈ positiveQuadraticSwapOrbitRepresentatives
        N m observed := Finset.mem_filter.mpr ⟨hQRep, hQPositive⟩
    have hQFree : ObservedAtOtherOnly observed q
        (otherQuadraticSlot selected) := by
      rw [hCanonical]
      exact observedAtOtherOnly_swap_other observed raw selected hRawFree
    have hQSign : quadraticPhaseTermBinarySign q
        (otherQuadraticSlot (otherQuadraticSlot selected)) = 1 := by
      rw [hCanonical]
      simpa using hRawSign
    let parameter : PositiveObservedFreeConnectedParameter N m observed :=
      ⟨q, otherQuadraticSlot selected, selected,
        hQMem, hQFree, hQSign⟩
    refine ⟨parameter, ?_⟩
    apply Subtype.ext
    apply Subtype.ext
    change connectedReturnTree observed q (otherQuadraticSlot selected)
        selected 0 = term.1
    rw [← connectedReturnTree_innerPlacement_eq_zero_of_allEqual_freeSignOne
      observed q (otherQuadraticSlot selected) selected innerSlot
        hQFree.1 hQSign,
      hCanonical, connectedReturnTree_swap_distinguished]
    exact hTree

/-- Exact global equivalence for the surviving two-placement correction. -/
def positiveObservedFreeConnectedEquiv
    {N : Nat} [NeZero N] (m : Lattice.PositiveMassConfig N)
    (observed : Lattice.Site N)
    (hObserved : 0 < modeFrequency m observed) :
    PositiveObservedFreeConnectedParameter N m observed ≃
      ObservedFreeConnectedTerm N m observed :=
  Equiv.ofBijective (positiveObservedFreeConnectedMap m observed)
    ⟨positiveObservedFreeConnectedMap_injective m observed,
      positiveObservedFreeConnectedMap_surjective m observed hObserved⟩

noncomputable instance instFintypePositiveObservedFreeConnectedParameter
    {N : Nat} [NeZero N] (m : Lattice.PositiveMassConfig N)
    (observed : Lattice.Site N) :
    Fintype (PositiveObservedFreeConnectedParameter N m observed) := by
  classical
  apply Fintype.ofInjective
    (fun parameter : PositiveObservedFreeConnectedParameter N m observed ↦
      (parameter.q, parameter.selected, parameter.outerSlot))
  rintro ⟨leftQ, leftSelected, leftOuter, leftMem, leftFree, leftSign⟩
    ⟨rightQ, rightSelected, rightOuter, rightMem, rightFree, rightSign⟩ h
  cases h
  rfl

/-- Finite-sum form of the free-observed global equivalence. -/
theorem sum_observedFreeConnected_eq_parameters
    {N : Nat} [NeZero N] {M : Type*} [AddCommMonoid M]
    (m : Lattice.PositiveMassConfig N) (observed : Lattice.Site N)
    (hObserved : 0 < modeFrequency m observed)
    (weight : FreeInitialMatchedIteratedQuadraticTerm N observed → M) :
    (∑ term ∈ positiveInnerObservedOnlyAtFreeConnectedTerms m observed,
        weight term) =
      ∑ parameter : PositiveObservedFreeConnectedParameter N m observed,
        weight (positiveObservedFreeConnectedMap m observed parameter).1 := by
  classical
  let equivalence := positiveObservedFreeConnectedEquiv
    m observed hObserved
  apply Finset.sum_bij
    (fun term hTerm ↦ equivalence.symm
      (⟨term, hTerm⟩ : ObservedFreeConnectedTerm N m observed))
  · intro term hTerm
    simp
  · intro left hLeft right hRight hEq
    have hSubtype :
        (⟨left, hLeft⟩ : ObservedFreeConnectedTerm N m observed) =
          ⟨right, hRight⟩ := by
      rw [← equivalence.apply_symm_apply
          (⟨left, hLeft⟩ : ObservedFreeConnectedTerm N m observed),
        ← equivalence.apply_symm_apply
          (⟨right, hRight⟩ : ObservedFreeConnectedTerm N m observed)]
      exact congrArg equivalence hEq
    exact congrArg Subtype.val hSubtype
  · intro parameter _hParameter
    refine ⟨(positiveObservedFreeConnectedMap m observed parameter).1,
      (positiveObservedFreeConnectedMap m observed parameter).2, ?_⟩
    exact equivalence.symm_apply_apply parameter
  · intro term hTerm
    have hApply := equivalence.apply_symm_apply
      (⟨term, hTerm⟩ : ObservedFreeConnectedTerm N m observed)
    exact (congrArg (fun candidate ↦ weight candidate.1) hApply).symm

/-- Every surviving free-observed parameter contributes the carrier-input
sign times two observed actions. -/
theorem observedFreeMap_feedback_eq_collapsedKernel
    {N : Nat} [NeZero N]
    (m : Lattice.PositiveMassConfig N) (kappa time : Real)
    (energy : Lattice.Site N → Real) (observed : Lattice.Site N)
    (parameter : PositiveObservedFreeConnectedParameter N m observed)
    (hEnergy : ∀ mode, 0 ≤ energy mode) :
    observedChildPhysicalFeedbackWeight m kappa time energy observed
        (positiveObservedFreeConnectedMap m observed parameter).1.1 =
      (quadraticInputInteractionSign parameter.q
          parameter.selected).coefficient *
        (finiteTimeCollisionKernel m kappa
            (quadraticCollisionSign parameter.q) time
            (quadraticCollisionModes observed parameter.q) *
          modeAction energy (modeFrequency m) observed *
          modeAction energy (modeFrequency m) observed) := by
  classical
  have hPositive : PositiveModeTuple m
      (quadraticCollisionModes observed parameter.q) := by
    simpa [positiveQuadraticSwapOrbitRepresentatives] using
      (Finset.mem_filter.mp parameter.q_mem).2
  unfold observedChildPhysicalFeedbackWeight
  rw [positiveObservedFreeConnectedMap_val,
    connectedReturnTree_innerMismatch, finiteTimeResonanceWeight_neg]
  have hTerm := connectedReturnTree_feedback_eq_signedKernel_mul_actions
    m kappa time energy observed parameter.q parameter.selected
      parameter.outerSlot 0 hEnergy hPositive
  rw [← parameter.observed_free.1] at hTerm
  simpa only [quadraticCollisionSign_succ] using hTerm

/-- Exact final formula for the original free-observed remainder.  Tadpoles
have cancelled, and the displayed parameter type contains only two outer
placements; the missing inner factor is the proved `4 → 2` collapse. -/
theorem freeFeedback_eq_collapsedParameterKernel
    {N : Nat} [NeZero N]
    (m : Lattice.PositiveMassConfig N) (kappa time : Real)
    (energy : Lattice.Site N → Real) (observed : Lattice.Site N)
    (hObserved : 0 < modeFrequency m observed)
    (hEnergy : ∀ mode, 0 ≤ energy mode) :
    positiveInnerObservedOnlyAtFreeFeedbackRemainder m kappa time
        (phaseEnergyRadius energy (modeFrequency m)) observed =
      ∑ parameter : PositiveObservedFreeConnectedParameter N m observed,
        (quadraticInputInteractionSign parameter.q
            parameter.selected).coefficient *
          (finiteTimeCollisionKernel m kappa
              (quadraticCollisionSign parameter.q) time
              (quadraticCollisionModes observed parameter.q) *
            modeAction energy (modeFrequency m) observed *
            modeAction energy (modeFrequency m) observed) := by
  rw [freeFeedback_eq_connected,
    sum_observedFreeConnected_eq_parameters m observed hObserved]
  apply Finset.sum_congr rfl
  intro parameter _hParameter
  exact observedFreeMap_feedback_eq_collapsedKernel
    m kappa time energy observed parameter hEnergy

/-- The carrier-observed local fiber retains all four nominal placements. -/
theorem carrierParameter_localImage_card_eq_four
    {N : Nat} [NeZero N] (m : Lattice.PositiveMassConfig N)
    (observed : Lattice.Site N)
    (parameter : PositiveObservedCarrierParameter N m observed) :
    (fixedDistinguishedReturnImage
      observed parameter.q parameter.selected).card = 4 :=
  card_fixedDistinguishedReturnImage_eq_four_of_observed_ne_other
    observed parameter.q parameter.selected
      parameter.observed_selected.2

/-- The free-observed connected local fiber has exactly two raw trees after
the redundant inner placement is removed. -/
theorem freeParameter_localImage_card_eq_two
    {N : Nat} [NeZero N] (m : Lattice.PositiveMassConfig N)
    (observed : Lattice.Site N)
    (parameter : PositiveObservedFreeConnectedParameter N m observed) :
    (fixedDistinguishedReturnImage
      observed parameter.q parameter.selected).card = 2 :=
  card_fixedDistinguishedReturnImage_eq_two_of_allEqual_freeSignOne
    observed parameter.q parameter.selected
      parameter.observed_free.1 parameter.free_sign

/-! ## Public resolved observed-child formula -/

/-- Four-placement carrier loss, now entirely at canonical quadratic
parameter level. -/
def observedCarrierSignedKernelSum
    {N : Nat} [NeZero N]
    (m : Lattice.PositiveMassConfig N) (kappa time : Real)
    (energy : Lattice.Site N → Real) (observed : Lattice.Site N) : Real :=
  ∑ parameter : PositiveObservedCarrierParameter N m observed,
    (quadraticInputInteractionSign parameter.q
        parameter.selected).coefficient *
      (finiteTimeCollisionKernel m kappa
          (quadraticCollisionSign parameter.q) time
          (quadraticCollisionModes observed parameter.q) *
        modeAction energy (modeFrequency m) observed *
        modeAction energy (modeFrequency m)
          (parameter.q.1 (otherQuadraticSlot parameter.selected)))

/-- Surviving two-placement correction after free-observed tadpole
cancellation and inner-placement collapse. -/
def observedFreeCollapsedKernelSum
    {N : Nat} [NeZero N]
    (m : Lattice.PositiveMassConfig N) (kappa time : Real)
    (energy : Lattice.Site N → Real) (observed : Lattice.Site N) : Real :=
  ∑ parameter : PositiveObservedFreeConnectedParameter N m observed,
    (quadraticInputInteractionSign parameter.q
        parameter.selected).coefficient *
      (finiteTimeCollisionKernel m kappa
          (quadraticCollisionSign parameter.q) time
          (quadraticCollisionModes observed parameter.q) *
        modeAction energy (modeFrequency m) observed *
        modeAction energy (modeFrequency m) observed)

theorem carrierFeedback_eq_signedKernelSum
    {N : Nat} [NeZero N]
    (m : Lattice.PositiveMassConfig N) (kappa time : Real)
    (energy : Lattice.Site N → Real) (observed : Lattice.Site N)
    (hObserved : 0 < modeFrequency m observed)
    (hEnergy : ∀ mode, 0 ≤ energy mode) :
    positiveInnerObservedOnlyAtCarrierFeedbackRemainder m kappa time
        (phaseEnergyRadius energy (modeFrequency m)) observed =
      observedCarrierSignedKernelSum
        m kappa time energy observed := by
  exact carrierFeedback_eq_parameterSignedKernel
    m kappa time energy observed hObserved hEnergy

theorem freeFeedback_eq_collapsedKernelSum
    {N : Nat} [NeZero N]
    (m : Lattice.PositiveMassConfig N) (kappa time : Real)
    (energy : Lattice.Site N → Real) (observed : Lattice.Site N)
    (hObserved : 0 < modeFrequency m observed)
    (hEnergy : ∀ mode, 0 ≤ energy mode) :
    positiveInnerObservedOnlyAtFreeFeedbackRemainder m kappa time
        (phaseEnergyRadius energy (modeFrequency m)) observed =
      observedFreeCollapsedKernelSum
        m kappa time energy observed := by
  exact freeFeedback_eq_collapsedParameterKernel
    m kappa time energy observed hObserved hEnergy

/-- Exact closure of the two q-level observed-child A1 gains with their two
original tree-level feedback strata.  The carrier term is a four-placement
signed loss.  The free term is the transparent two-placement correction; no
tree-level remainder remains in these two strata. -/
theorem observedChildA1_add_feedback_eq_resolved
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
        observedFreeCollapsedKernelSum m kappa time energy observed := by
  rw [carrierFeedback_eq_signedKernelSum
      m kappa time energy observed hObserved hEnergy,
    freeFeedback_eq_collapsedKernelSum
      m kappa time energy observed hObserved hEnergy]

end

end ArchonPhysics.FreeFPUTObservedChildGlobalFeedbackClosure
