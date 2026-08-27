import ArchonPhysics.FreeFPUTAllDistinctConnectedReturnFiber
import ArchonPhysics.FreeFPUTNonzeroChargeFiberClassification
import ArchonPhysics.MatchedIteratedQuadraticCanonicalReturnChannel
import ArchonPhysics.SignedThreeWaveCollisionFlux

/-!
# Equal-child, equal-sign correction to the local FPUT gain--loss bracket

This module isolates one repeated-mode boundary stratum of the local
quadratic FPUT collision algebra.  The two quadratic children have the same
mode and the same binary phase sign, while the observed mode remains
different.  Consequently the input-swap orbit is a fixed point and the two
choices of distinguished child construct the same return tree.  The literal
eight-index connected-return image therefore contains four, not eight,
distinct trees.

The exact local gain plus feedback is the usual signed collision bracket
plus an explicit repeated-child multiplicity correction.  The correction is
retained; no random-phase, zero-charge, counterrotating, or global-fiber
argument is used to discard it.
-/

namespace ArchonPhysics.FreeFPUTRepeatedChildSameSignCorrection

open ArchonPhysics
open ArchonPhysics.FiniteTimeResonanceWeight
open ArchonPhysics.FinitePhaseMonomials
open ArchonPhysics.FreeFPUTA0IteratedQuadraticFeedbackIdentity
open ArchonPhysics.FreeFPUTAllDistinctConnectedReturnFiber
open ArchonPhysics.FreeFPUTCanonicalConnectedReturnTree
open ArchonPhysics.FreeFPUTCollisionMismatchBridge
open ArchonPhysics.FreeFPUTEnergyCollisionWeightBridge
open ArchonPhysics.FreeFPUTNonzeroChargeFiberClassification
open ArchonPhysics.FreeFPUTQuadraticTermSwapSymmetry
open ArchonPhysics.FreeFPUTTensorPhaseExpansion
open ArchonPhysics.MicroscopicFiniteTimeCollisionPolynomial
open ArchonPhysics.MatchedIteratedQuadraticCanonicalReturnChannel
open ArchonPhysics.MatchedIteratedQuadraticReturnChannelClassification
open ArchonPhysics.ModalPhaseMismatch
open ArchonPhysics.NormalizedModeCoupling
open ArchonPhysics.PhyslibFPUTIteratedQuadraticSecondPicardCharacterFamily
open ArchonPhysics.PhyslibFPUTSecondOrderExplicitReturnFeedback
open ArchonPhysics.ResonanceWeightSinc
open ArchonPhysics.SignedThreeWaveCollisionFlux

noncomputable section

/-- The two ordered quadratic children have the same mode and binary phase
sign. -/
def RepeatedChildSameSign
    {N : Nat} [NeZero N] (q : QuadraticPhaseTerm N) : Prop :=
  q.1 0 = q.1 1 ∧ q.2.1 = q.2.2

/-- The equal child remains separated from the observed mode.  This is the
precise boundary stratum considered below. -/
def ObservedSeparatedRepeatedChildSameSign
    {N : Nat} [NeZero N] (observed : Lattice.Site N)
    (q : QuadraticPhaseTerm N) : Prop :=
  RepeatedChildSameSign q ∧ observed ≠ q.1 0

/-- Equal mode and equal sign are exactly enough to make the ordered
quadratic term a fixed point of input swap. -/
theorem swapQuadraticPhaseTerm_eq_self_of_repeatedChildSameSign
    {N : Nat} [NeZero N] (q : QuadraticPhaseTerm N)
    (hRepeated : RepeatedChildSameSign q) :
    swapQuadraticPhaseTerm q = q := by
  exact (swapQuadraticPhaseTerm_eq_self_iff q).2 hRepeated

/-- Hence the deduplicated input-swap orbit has cardinality one. -/
theorem card_quadraticSwapOrbit_eq_one_of_repeatedChildSameSign
    {N : Nat} [NeZero N] (q : QuadraticPhaseTerm N)
    (hRepeated : RepeatedChildSameSign q) :
    (quadraticSwapOrbit q).card = 1 := by
  exact card_quadraticSwapOrbit_eq_one_of_fixed q
    (swapQuadraticPhaseTerm_eq_self_of_repeatedChildSameSign q hRepeated)

/-- Same-mode children with the same sign carry twice one unit charge, so
this stratum is not the exceptional zero-charge fiber. -/
theorem quadraticPhaseCharge_ne_zero_of_repeatedChildSameSign
    {N : Nat} [NeZero N] (q : QuadraticPhaseTerm N)
    (hRepeated : RepeatedChildSameSign q) :
    quadraticPhaseCharge q ≠ 0 := by
  intro hZero
  have hSignedZero :
      SignedMode.charge
            ⟨q.1 0, binaryPhaseSign q.2.1⟩ +
          SignedMode.charge
            ⟨q.1 0, binaryPhaseSign q.2.2⟩ = 0 := by
    simpa only [quadraticPhaseCharge, binarySignedMode,
      hRepeated.1] using hZero
  have hOpposite :=
    (add_signedMode_charge_eq_zero_of_same_mode_iff
      (q.1 0) (binaryPhaseSign q.2.1)
        (binaryPhaseSign q.2.2)).1 hSignedZero
  exact hOpposite (congrArg binaryPhaseSign hRepeated.2)

/-- Consequently every quadratic term with the same phase charge is already
in this term's singleton swap orbit.  There is no cross-orbit coherent
partner on the present stratum. -/
theorem mem_quadraticSwapOrbit_of_charge_eq_repeatedChildSameSign
    {N : Nat} [NeZero N] (q right : QuadraticPhaseTerm N)
    (hRepeated : RepeatedChildSameSign q)
    (hCharge : quadraticPhaseCharge q = quadraticPhaseCharge right) :
    right ∈ quadraticSwapOrbit q := by
  exact mem_quadraticSwapOrbit_of_charge_eq_of_nonzero q right hCharge
    (quadraticPhaseCharge_ne_zero_of_repeatedChildSameSign q hRepeated)

/-- On the fixed-point stratum, choosing child one as distinguished is the
same as first swapping the ordered quadratic term and choosing child zero. -/
theorem connectedReturnTree_one_eq_swap_zero
    {N : Nat} [NeZero N] (observed : Lattice.Site N)
    (q : QuadraticPhaseTerm N) (outerSlot innerSlot : Fin 2) :
    connectedReturnTree observed q 1 outerSlot innerSlot =
      connectedReturnTree observed (swapQuadraticPhaseTerm q) 0
        outerSlot innerSlot := by
  rfl

/-- The distinguished-child index is redundant on the equal-child,
equal-sign stratum. -/
theorem connectedReturnTree_r_eq_zero
    {N : Nat} [NeZero N] (observed : Lattice.Site N)
    (q : QuadraticPhaseTerm N) (r outerSlot innerSlot : Fin 2)
    (hRepeated : RepeatedChildSameSign q) :
    connectedReturnTree observed q r outerSlot innerSlot =
      connectedReturnTree observed q 0 outerSlot innerSlot := by
  fin_cases r
  · rfl
  · change connectedReturnTree observed q 1 outerSlot innerSlot = _
    rw [connectedReturnTree_one_eq_swap_zero,
      swapQuadraticPhaseTerm_eq_self_of_repeatedChildSameSign q hRepeated]

/-- Only the two placement choices remain after quotienting the redundant
distinguished-child index. -/
abbrev RepeatedChildConnectedReturnIndex := Fin 2 × Fin 2

/-- Four-placement constructor for the repeated-child connected trees. -/
def repeatedChildConnectedReturnMap
    {N : Nat} [NeZero N] (observed : Lattice.Site N)
    (q : QuadraticPhaseTerm N) (index : RepeatedChildConnectedReturnIndex) :
    FreeInitialMatchedIteratedQuadraticTerm N observed :=
  matchedConnectedReturnTree observed q 0 index.1 index.2

@[simp] theorem repeatedChildConnectedReturnMap_val
    {N : Nat} [NeZero N] (observed : Lattice.Site N)
    (q : QuadraticPhaseTerm N) (index : RepeatedChildConnectedReturnIndex) :
    (repeatedChildConnectedReturnMap observed q index).1 =
      connectedReturnTree observed q 0 index.1 index.2 := rfl

/-- Literal finite image of the four nonredundant placements. -/
def repeatedChildConnectedReturnImage
    {N : Nat} [NeZero N] (observed : Lattice.Site N)
    (q : QuadraticPhaseTerm N) :
    Finset (FreeInitialMatchedIteratedQuadraticTerm N observed) := by
  classical
  exact Finset.univ.image (repeatedChildConnectedReturnMap observed q)

/-- Separation from the observed mode makes the four placement trees
distinct. -/
theorem repeatedChildConnectedReturnMap_injective
    {N : Nat} [NeZero N] (observed : Lattice.Site N)
    (q : QuadraticPhaseTerm N)
    (hSeparated : ObservedSeparatedRepeatedChildSameSign observed q) :
    Function.Injective (repeatedChildConnectedReturnMap observed q) := by
  intro left right htree
  apply connectedReturnTree_placement_injective observed q 0
  · intro hObservedOne
    exact hSeparated.2 (hObservedOne.trans hSeparated.1.1.symm)
  · exact congrArg Subtype.val htree

/-- Separation of the observed and repeated-child modes rules out both raw
tadpole predicates for every mapped tree. -/
theorem repeatedChildConnectedReturnMap_not_tadpole
    {N : Nat} [NeZero N] (observed : Lattice.Site N)
    (q : QuadraticPhaseTerm N) (index : RepeatedChildConnectedReturnIndex)
    (hSeparated : ObservedSeparatedRepeatedChildSameSign observed q) :
    ¬ MatchedIteratedQuadraticTadpoleChannel observed
        (repeatedChildConnectedReturnMap observed q index).1 := by
  intro hTadpole
  rcases hTadpole with hTadpole | hTadpole
  · unfold FreeObservedInnerZeroCancelsInnerOne at hTadpole
    dsimp only at hTadpole
    rcases hTadpole with ⟨_, _, _, hFreeObserved, _⟩
    have hChildObserved : q.1 1 = observed := by
      simpa [binarySignedMode] using hFreeObserved
    exact hSeparated.2 (hSeparated.1.1.trans hChildObserved).symm
  · unfold FreeObservedInnerOneCancelsInnerZero at hTadpole
    dsimp only at hTadpole
    rcases hTadpole with ⟨_, _, _, hFreeObserved, _⟩
    have hChildObserved : q.1 1 = observed := by
      simpa [binarySignedMode] using hFreeObserved
    exact hSeparated.2 (hSeparated.1.1.trans hChildObserved).symm

/-- The first-match selector cannot assign a repeated-child mapped tree to
either free-observed (tadpole) label.  Thus the canonical selector retains
it in one of the four connected labels without double counting. -/
theorem repeatedChildConnectedReturnMap_canonical_not_tadpole
    {N : Nat} [NeZero N] (observed : Lattice.Site N)
    (q : QuadraticPhaseTerm N) (index : RepeatedChildConnectedReturnIndex)
    (hSeparated : ObservedSeparatedRepeatedChildSameSign observed q) :
    canonicalReturnChannel observed
          (repeatedChildConnectedReturnMap observed q index) ≠
        .freeObservedInnerZeroCancelsInnerOne ∧
      canonicalReturnChannel observed
          (repeatedChildConnectedReturnMap observed q index) ≠
        .freeObservedInnerOneCancelsInnerZero := by
  have hNotTadpole := repeatedChildConnectedReturnMap_not_tadpole
    observed q index hSeparated
  constructor
  · intro hChannel
    have hRaw := canonicalReturnChannel_rawHolds observed
      (repeatedChildConnectedReturnMap observed q index)
    rw [hChannel] at hRaw
    exact hNotTadpole (Or.inl hRaw)
  · intro hChannel
    have hRaw := canonicalReturnChannel_rawHolds observed
      (repeatedChildConnectedReturnMap observed q index)
    rw [hChannel] at hRaw
    exact hNotTadpole (Or.inr hRaw)

/-- The repeated-child local connected image has exactly four elements. -/
theorem card_repeatedChildConnectedReturnImage
    {N : Nat} [NeZero N] (observed : Lattice.Site N)
    (q : QuadraticPhaseTerm N)
    (hSeparated : ObservedSeparatedRepeatedChildSameSign observed q) :
    (repeatedChildConnectedReturnImage observed q).card = 4 := by
  classical
  unfold repeatedChildConnectedReturnImage
  rw [Finset.card_image_of_injective _
    (repeatedChildConnectedReturnMap_injective observed q hSeparated)]
  decide

/-- The nominal eight-index image collapses exactly to the four-placement
image.  Thus the canonical finite-set representation counts each literal
tree once even though both distinguished-child indices construct it. -/
theorem allDistinctConnectedReturnImage_eq_repeatedChildImage
    {N : Nat} [NeZero N] (observed : Lattice.Site N)
    (q : QuadraticPhaseTerm N)
    (hRepeated : RepeatedChildSameSign q) :
    allDistinctConnectedReturnImage observed q =
      repeatedChildConnectedReturnImage observed q := by
  classical
  ext term
  simp only [allDistinctConnectedReturnImage,
    repeatedChildConnectedReturnImage, Finset.mem_image,
    Finset.mem_univ, true_and]
  constructor
  · rintro ⟨⟨r, outerSlot, innerSlot⟩, rfl⟩
    refine ⟨(outerSlot, innerSlot), ?_⟩
    apply Subtype.ext
    exact (connectedReturnTree_r_eq_zero observed q r outerSlot innerSlot
      hRepeated).symm
  · rintro ⟨⟨outerSlot, innerSlot⟩, rfl⟩
    exact ⟨(0, outerSlot, innerSlot), rfl⟩

/-- Exact reindex of an additive weight over the four repeated-child trees. -/
theorem sum_repeatedChildConnectedReturnImage
    {N : Nat} [NeZero N] {M : Type*} [AddCommMonoid M]
    (observed : Lattice.Site N) (q : QuadraticPhaseTerm N)
    (hSeparated : ObservedSeparatedRepeatedChildSameSign observed q)
    (weight : FreeInitialMatchedIteratedQuadraticTerm N observed → M) :
    (∑ term ∈ repeatedChildConnectedReturnImage observed q, weight term) =
      ∑ index : RepeatedChildConnectedReturnIndex,
        weight (repeatedChildConnectedReturnMap observed q index) := by
  classical
  unfold repeatedChildConnectedReturnImage
  rw [Finset.sum_image]
  intro left _hleft right _hright htree
  exact repeatedChildConnectedReturnMap_injective observed q hSeparated htree

/-- One of the four mapped feedback terms is the child-zero signed kernel
contribution. -/
theorem repeatedChildConnectedReturnMap_feedback_eq
    {N : Nat} [NeZero N]
    (m : Lattice.PositiveMassConfig N) (kappa time : Real)
    (energy : Lattice.Site N → Real) (observed : Lattice.Site N)
    (q : QuadraticPhaseTerm N) (index : RepeatedChildConnectedReturnIndex)
    (hEnergy : ∀ mode, 0 ≤ energy mode)
    (hPositive : PositiveModeTuple m (quadraticCollisionModes observed q)) :
    compactIteratedQuadraticStaticFeedbackWeight m kappa
          (phaseEnergyRadius energy (modeFrequency m)) observed
          (repeatedChildConnectedReturnMap observed q index).1 *
        finiteTimeResonanceWeight
          (iteratedQuadraticInnerMismatch m
            (repeatedChildConnectedReturnMap observed q index).1) time =
      (quadraticInputInteractionSign q 0).coefficient *
        (finiteTimeCollisionKernel m kappa
            (quadraticCollisionSign q) time
            (quadraticCollisionModes observed q) *
          modeAction energy (modeFrequency m) observed *
          modeAction energy (modeFrequency m) (q.1 1)) := by
  rw [repeatedChildConnectedReturnMap_val,
    connectedReturnTree_innerMismatch,
    finiteTimeResonanceWeight_neg]
  simpa only [quadraticCollisionSign_succ, otherQuadraticSlot_zero] using
    (connectedReturnTree_feedback_eq_signedKernel_mul_actions
      m kappa time energy observed q 0 index.1 index.2 hEnergy hPositive)

/-- Physical feedback over the four distinct repeated-child trees. -/
def repeatedChildConnectedReturnFeedbackSum
    {N : Nat} [NeZero N]
    (m : Lattice.PositiveMassConfig N) (kappa time : Real)
    (energy : Lattice.Site N → Real) (observed : Lattice.Site N)
    (q : QuadraticPhaseTerm N) : Real :=
  ∑ term ∈ repeatedChildConnectedReturnImage observed q,
    compactIteratedQuadraticStaticFeedbackWeight m kappa
        (phaseEnergyRadius energy (modeFrequency m)) observed term.1 *
      finiteTimeResonanceWeight
        (iteratedQuadraticInnerMismatch m term.1) time

/-- The four distinct return trees supply exactly four copies of the single
child-sign feedback factor. -/
theorem repeatedChildConnectedReturnFeedbackSum_eq
    {N : Nat} [NeZero N]
    (m : Lattice.PositiveMassConfig N) (kappa time : Real)
    (energy : Lattice.Site N → Real) (observed : Lattice.Site N)
    (q : QuadraticPhaseTerm N)
    (hSeparated : ObservedSeparatedRepeatedChildSameSign observed q)
    (hEnergy : ∀ mode, 0 ≤ energy mode)
    (hPositive : PositiveModeTuple m (quadraticCollisionModes observed q)) :
    repeatedChildConnectedReturnFeedbackSum
        m kappa time energy observed q =
      4 * (quadraticInputInteractionSign q 0).coefficient *
        finiteTimeCollisionKernel m kappa
          (quadraticCollisionSign q) time
          (quadraticCollisionModes observed q) *
        modeAction energy (modeFrequency m) observed *
        modeAction energy (modeFrequency m) (q.1 0) := by
  unfold repeatedChildConnectedReturnFeedbackSum
  rw [sum_repeatedChildConnectedReturnImage observed q hSeparated]
  simp_rw [repeatedChildConnectedReturnMap_feedback_eq
    m kappa time energy observed q _ hEnergy hPositive]
  rw [← hSeparated.1.1]
  simp only [Fintype.sum_prod_type, Fin.sum_univ_two]
  ring

/-- Fixed-point coherent A1 gain on the repeated-child swap orbit. -/
def repeatedChildLocalA1Gain
    {N : Nat} [NeZero N]
    (m : Lattice.PositiveMassConfig N) (kappa time : Real)
    (energy : Lattice.Site N → Real) (observed : Lattice.Site N)
    (q : QuadraticPhaseTerm N) : Real :=
  ((quadraticSwapOrbit q).card : Real) ^ 2 *
    finiteTimeCollisionKernel m kappa
      (quadraticCollisionSign q) time
      (quadraticCollisionModes observed q) *
    ∏ r : Fin 2, modeAction energy (modeFrequency m) (q.1 r)

/-- Local A1 gain plus the four-tree connected feedback on this repeated
stratum. -/
def repeatedChildSameSignLocalGainFeedback
    {N : Nat} [NeZero N]
    (m : Lattice.PositiveMassConfig N) (kappa time : Real)
    (energy : Lattice.Site N → Real) (observed : Lattice.Site N)
    (q : QuadraticPhaseTerm N) : Real :=
  repeatedChildLocalA1Gain m kappa time energy observed q +
    repeatedChildConnectedReturnFeedbackSum
      m kappa time energy observed q

/-- Exact raw multiplicity formula: one fixed-point A1 gain and four
distinct connected feedback trees. -/
theorem repeatedChildSameSignLocalGainFeedback_eq_raw
    {N : Nat} [NeZero N]
    (m : Lattice.PositiveMassConfig N) (kappa time : Real)
    (energy : Lattice.Site N → Real) (observed : Lattice.Site N)
    (q : QuadraticPhaseTerm N)
    (hSeparated : ObservedSeparatedRepeatedChildSameSign observed q)
    (hEnergy : ∀ mode, 0 ≤ energy mode)
    (hPositive : PositiveModeTuple m (quadraticCollisionModes observed q)) :
    repeatedChildSameSignLocalGainFeedback
        m kappa time energy observed q =
      finiteTimeCollisionKernel m kappa
          (quadraticCollisionSign q) time
          (quadraticCollisionModes observed q) *
        (modeAction energy (modeFrequency m) (q.1 0) ^ 2 +
          4 * (quadraticInputInteractionSign q 0).coefficient *
            modeAction energy (modeFrequency m) observed *
            modeAction energy (modeFrequency m) (q.1 0)) := by
  unfold repeatedChildSameSignLocalGainFeedback repeatedChildLocalA1Gain
  rw [card_quadraticSwapOrbit_eq_one_of_repeatedChildSameSign
      q hSeparated.1,
    repeatedChildConnectedReturnFeedbackSum_eq
      m kappa time energy observed q hSeparated hEnergy hPositive]
  simp only [Nat.cast_one, one_pow, one_mul, Fin.prod_univ_two]
  rw [← hSeparated.1.1]
  ring

/-- Exact correction identity.  Relative to one copy of the signed
three-wave bracket, repeated-child deduplication leaves two additional
copies of the signed observed--child feedback term. -/
theorem repeatedChildSameSignLocalGainFeedback_eq_signedFlux_add_correction
    {N : Nat} [NeZero N]
    (m : Lattice.PositiveMassConfig N) (kappa time : Real)
    (energy : Lattice.Site N → Real) (observed : Lattice.Site N)
    (q : QuadraticPhaseTerm N)
    (hSeparated : ObservedSeparatedRepeatedChildSameSign observed q)
    (hEnergy : ∀ mode, 0 ≤ energy mode)
    (hPositive : PositiveModeTuple m (quadraticCollisionModes observed q)) :
    repeatedChildSameSignLocalGainFeedback
        m kappa time energy observed q =
      finiteTimeCollisionKernel m kappa
          (quadraticCollisionSign q) time
          (quadraticCollisionModes observed q) *
        quadraticSignedCollisionFlux q
          (modeAction energy (modeFrequency m)) observed +
      2 * finiteTimeCollisionKernel m kappa
          (quadraticCollisionSign q) time
          (quadraticCollisionModes observed q) *
        (quadraticInputInteractionSign q 0).coefficient *
        modeAction energy (modeFrequency m) observed *
        modeAction energy (modeFrequency m) (q.1 0) := by
  rw [repeatedChildSameSignLocalGainFeedback_eq_raw
    m kappa time energy observed q hSeparated hEnergy hPositive]
  have hAction :
      modeAction energy (modeFrequency m) (q.1 1) =
        modeAction energy (modeFrequency m) (q.1 0) :=
    congrArg (modeAction energy (modeFrequency m)) hSeparated.1.1.symm
  have hInputSign :
      quadraticInputInteractionSign q 1 =
        quadraticInputInteractionSign q 0 := by
    simp [quadraticInputInteractionSign, hSeparated.1.2]
  unfold quadraticSignedCollisionFlux signedThreeWaveCollisionFlux
  rw [hAction, hInputSign]
  ring

end

end ArchonPhysics.FreeFPUTRepeatedChildSameSignCorrection
