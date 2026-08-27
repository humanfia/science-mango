import ArchonPhysics.FreeFPUTAllDistinctConnectedReturnFiber
import ArchonPhysics.FreeFPUTNonzeroChargeFiberClassification
import ArchonPhysics.FreeFPUTSwapOrbitCollisionCorrection
import ArchonPhysics.SignedThreeWaveCollisionFlux

/-!
# Equal-child, opposite-sign local FPUT gain--loss stratum

This module treats the repeated-mode boundary complementary to
`FreeFPUTRepeatedChildSameSignCorrection`: the two quadratic children have
the same mode but opposite binary phase signs, while the observed mode is
different.  Input swap is not fixed on this stratum, and the distinguished
child is still recorded by the free sign.  Consequently all eight local
connected-return trees remain distinct.

The quadratic phase charge is nevertheless zero.  The two four-tree
feedback families have opposite interaction signs and cancel exactly, while
the coherent input-swap gain has multiplicity four.  Thus the local gain plus
feedback is exactly four copies of the signed collision flux and its local
repeated-child correction is zero.

This is only a literal local-image identity.  Zero charge admits partners in
other swap orbits; an explicit such partner is constructed below.  Hence no
cross-orbit coherent term is discarded, and no global connected-fiber,
random-phase, counterrotating, or kinetic-limit conclusion is asserted.
-/

namespace ArchonPhysics.FreeFPUTRepeatedChildOppositeSignCorrection

open ArchonPhysics
open ArchonPhysics.FiniteTimeResonanceWeight
open ArchonPhysics.FreeFPUTA0IteratedQuadraticFeedbackIdentity
open ArchonPhysics.FreeFPUTAllDistinctConnectedReturnFiber
open ArchonPhysics.FreeFPUTCanonicalConnectedReturnTree
open ArchonPhysics.FreeFPUTCollisionMismatchBridge
open ArchonPhysics.FreeFPUTEnergyCollisionWeightBridge
open ArchonPhysics.FreeFPUTMismatchPhaseExpansion
open ArchonPhysics.FreeFPUTNonzeroChargeFiberClassification
open ArchonPhysics.FreeFPUTQuadraticTermSwapSymmetry
open ArchonPhysics.FreeFPUTSwapOrbitCollisionCorrection
open ArchonPhysics.FreeFPUTTensorPhaseExpansion
open ArchonPhysics.MicroscopicFiniteTimeCollisionPolynomial
open ArchonPhysics.ModalPhaseMismatch
open ArchonPhysics.NormalizedModeCoupling
open ArchonPhysics.PhyslibFPUTIteratedQuadraticSecondPicardCharacterFamily
open ArchonPhysics.PhyslibFPUTSecondOrderExplicitReturnFeedback
open ArchonPhysics.SignedThreeWaveCollisionFlux
open ArchonPhysics.ThreeSignedChargeCancellationClassification

noncomputable section

/-- The two ordered quadratic children have the same mode and opposite
binary phase signs. -/
def RepeatedChildOppositeSign
    {N : Nat} [NeZero N] (q : QuadraticPhaseTerm N) : Prop :=
  q.1 0 = q.1 1 ∧ q.2.1 ≠ q.2.2

/-- The repeated child remains separated from the observed mode. -/
def ObservedSeparatedRepeatedChildOppositeSign
    {N : Nat} [NeZero N] (observed : Lattice.Site N)
    (q : QuadraticPhaseTerm N) : Prop :=
  RepeatedChildOppositeSign q ∧ observed ≠ q.1 0

/-- Opposite signs prevent the simultaneous input swap from being fixed,
even though the two input modes agree. -/
theorem swapQuadraticPhaseTerm_ne_self_of_repeatedChildOppositeSign
    {N : Nat} [NeZero N] (q : QuadraticPhaseTerm N)
    (hRepeated : RepeatedChildOppositeSign q) :
    swapQuadraticPhaseTerm q ≠ q := by
  intro hfixed
  exact hRepeated.2 ((swapQuadraticPhaseTerm_eq_self_iff q).1 hfixed).2

/-- The input-swap orbit therefore retains its two ordered elements. -/
theorem card_quadraticSwapOrbit_eq_two_of_repeatedChildOppositeSign
    {N : Nat} [NeZero N] (q : QuadraticPhaseTerm N)
    (hRepeated : RepeatedChildOppositeSign q) :
    (quadraticSwapOrbit q).card = 2 := by
  exact card_quadraticSwapOrbit_eq_two_of_ne q
    (swapQuadraticPhaseTerm_ne_self_of_repeatedChildOppositeSign q hRepeated)

/-- Equal-mode children with opposite signs have exactly zero quadratic
phase charge. -/
theorem quadraticPhaseCharge_eq_zero_of_repeatedChildOppositeSign
    {N : Nat} [NeZero N] (q : QuadraticPhaseTerm N)
    (hRepeated : RepeatedChildOppositeSign q) :
    quadraticPhaseCharge q = 0 := by
  exact quadraticPhaseCharge_eq_zero_of_sameMode_oppositeSigns q
    hRepeated.1 hRepeated.2

/-- The two input interaction coefficients are additive opposites. -/
theorem inputInteractionCoefficient_add_eq_zero_of_oppositeSigns
    {N : Nat} [NeZero N] (q : QuadraticPhaseTerm N)
    (hRepeated : RepeatedChildOppositeSign q) :
    (quadraticInputInteractionSign q 0).coefficient +
        (quadraticInputInteractionSign q 1).coefficient = 0 := by
  rcases q with ⟨modes, signZero, signOne⟩
  change modes 0 = modes 1 ∧ signZero ≠ signOne at hRepeated
  fin_cases signZero <;> fin_cases signOne <;>
    simp_all [quadraticInputInteractionSign,
      phaseSignToInputInteractionSign, binaryPhaseSign,
      InteractionSign.coefficient]

/-- A canonical zero-charge quadratic term based at one supplied mode. -/
def canonicalOppositeSignTermAt
    {N : Nat} [NeZero N] (mode : Lattice.Site N) : QuadraticPhaseTerm N :=
  (fun _ ↦ mode, (0, 1))

@[simp] theorem canonicalOppositeSignTermAt_mode
    {N : Nat} [NeZero N] (mode : Lattice.Site N) (r : Fin 2) :
    (canonicalOppositeSignTermAt mode).1 r = mode := rfl

@[simp] theorem canonicalOppositeSignTermAt_charge
    {N : Nat} [NeZero N] (mode : Lattice.Site N) :
    quadraticPhaseCharge (canonicalOppositeSignTermAt mode) = 0 := by
  refine quadraticPhaseCharge_eq_zero_of_sameMode_oppositeSigns
    (canonicalOppositeSignTermAt mode) (by rfl) ?_
  change (0 : Fin 2) ≠ 1
  decide

/-- Separation gives an explicit same-charge term outside the supplied
swap orbit: put an opposite-sign pair at the observed mode.  This witnesses
why zero-charge cross-orbit coherence cannot be removed by the nonzero-charge
fiber classification. -/
theorem canonicalOppositeSignTermAt_observed_not_mem_swapOrbit
    {N : Nat} [NeZero N] (observed : Lattice.Site N)
    (q : QuadraticPhaseTerm N)
    (hSeparated : ObservedSeparatedRepeatedChildOppositeSign observed q) :
    canonicalOppositeSignTermAt observed ∉ quadraticSwapOrbit q := by
  intro hmem
  rcases (mem_quadraticSwapOrbit_iff
    (canonicalOppositeSignTermAt observed) q).1 hmem with hterm | hswap
  · have hmodes := congrArg
      (fun term : QuadraticPhaseTerm N ↦ term.1 0) hterm
    exact hSeparated.2 (by simpa using hmodes)
  · have hmodes := congrArg
      (fun term : QuadraticPhaseTerm N ↦ term.1 0) hswap
    have hobservedOne : observed = q.1 1 := by simpa using hmodes
    exact hSeparated.2 (hobservedOne.trans hSeparated.1.1.symm)

/-- The explicit outside-orbit partner nevertheless has exactly the same
quadratic phase charge. -/
theorem canonicalOppositeSignTermAt_observed_charge_eq
    {N : Nat} [NeZero N] (observed : Lattice.Site N)
    (q : QuadraticPhaseTerm N)
    (hRepeated : RepeatedChildOppositeSign q) :
    quadraticPhaseCharge (canonicalOppositeSignTermAt observed) =
      quadraticPhaseCharge q := by
  rw [canonicalOppositeSignTermAt_charge,
    quadraticPhaseCharge_eq_zero_of_repeatedChildOppositeSign q hRepeated]

/-- On this stratum the free sign distinguishes the two choices of
distinguished child, and observed/child separation distinguishes both
placements.  Hence the full local three-bit constructor is injective. -/
theorem allDistinctConnectedReturnMap_injective_of_repeatedChildOppositeSign
    {N : Nat} [NeZero N] (observed : Lattice.Site N)
    (q : QuadraticPhaseTerm N)
    (hSeparated : ObservedSeparatedRepeatedChildOppositeSign observed q) :
    Function.Injective (allDistinctConnectedReturnMap observed q) := by
  rintro ⟨rLeft, outerLeft, innerLeft⟩
    ⟨rRight, outerRight, innerRight⟩ htree
  have htreeVal := congrArg Subtype.val htree
  have hfree :
      quadraticPhaseTermBinarySign q (otherQuadraticSlot rLeft) =
        quadraticPhaseTermBinarySign q (otherQuadraticSlot rRight) := by
    simpa using congrArg iteratedQuadraticFreeSign htreeVal
  have hr : rLeft = rRight := by
    fin_cases rLeft <;> fin_cases rRight
    · rfl
    · exfalso
      exact hSeparated.1.2 (by simpa using hfree.symm)
    · exfalso
      exact hSeparated.1.2 (by simpa using hfree)
    · rfl
  subst rRight
  have hObservedOther :
      observed ≠ q.1 (otherQuadraticSlot rLeft) := by
    fin_cases rLeft
    · simpa [hSeparated.1.1] using hSeparated.2
    · simpa using hSeparated.2
  have hplacement : (outerLeft, innerLeft) =
      (outerRight, innerRight) :=
    connectedReturnTree_placement_injective observed q rLeft
      hObservedOther htreeVal
  cases hplacement
  rfl

/-- The deduplicated literal local connected-return image still contains
all eight trees. -/
theorem card_allDistinctConnectedReturnImage_of_repeatedChildOppositeSign
    {N : Nat} [NeZero N] (observed : Lattice.Site N)
    (q : QuadraticPhaseTerm N)
    (hSeparated : ObservedSeparatedRepeatedChildOppositeSign observed q) :
    (allDistinctConnectedReturnImage observed q).card = 8 := by
  classical
  unfold allDistinctConnectedReturnImage
  rw [Finset.card_image_of_injective _
    (allDistinctConnectedReturnMap_injective_of_repeatedChildOppositeSign
      observed q hSeparated)]
  decide

/-- Exact additive reindex over the eight-tree local image on this repeated
stratum. -/
theorem sum_allDistinctConnectedReturnImage_of_repeatedChildOppositeSign
    {N : Nat} [NeZero N] {M : Type*} [AddCommMonoid M]
    (observed : Lattice.Site N) (q : QuadraticPhaseTerm N)
    (hSeparated : ObservedSeparatedRepeatedChildOppositeSign observed q)
    (weight : FreeInitialMatchedIteratedQuadraticTerm N observed → M) :
    (∑ term ∈ allDistinctConnectedReturnImage observed q, weight term) =
      ∑ index : AllDistinctConnectedReturnIndex,
        weight (allDistinctConnectedReturnMap observed q index) := by
  classical
  unfold allDistinctConnectedReturnImage
  rw [Finset.sum_image]
  intro left _hleft right _hright htree
  exact allDistinctConnectedReturnMap_injective_of_repeatedChildOppositeSign
    observed q hSeparated htree

/-- Physical feedback over the eight distinct local return trees. -/
def repeatedChildOppositeSignConnectedReturnFeedbackSum
    {N : Nat} [NeZero N]
    (m : Lattice.PositiveMassConfig N) (kappa time : Real)
    (energy : Lattice.Site N → Real) (observed : Lattice.Site N)
    (q : QuadraticPhaseTerm N) : Real :=
  ∑ term ∈ allDistinctConnectedReturnImage observed q,
    compactIteratedQuadraticStaticFeedbackWeight m kappa
        (phaseEnergyRadius energy (modeFrequency m)) observed term.1 *
      finiteTimeResonanceWeight
        (iteratedQuadraticInnerMismatch m term.1) time

/-- Before using opposite signs, the eight-tree sum is four copies of each
distinguished-child feedback term. -/
theorem repeatedChildOppositeSignConnectedReturnFeedbackSum_eq_pair
    {N : Nat} [NeZero N]
    (m : Lattice.PositiveMassConfig N) (kappa time : Real)
    (energy : Lattice.Site N → Real) (observed : Lattice.Site N)
    (q : QuadraticPhaseTerm N)
    (hSeparated : ObservedSeparatedRepeatedChildOppositeSign observed q)
    (hEnergy : ∀ mode, 0 ≤ energy mode)
    (hPositive : PositiveModeTuple m (quadraticCollisionModes observed q)) :
    repeatedChildOppositeSignConnectedReturnFeedbackSum
        m kappa time energy observed q =
      4 * finiteTimeCollisionKernel m kappa
            (quadraticCollisionSign q) time
            (quadraticCollisionModes observed q) *
        ((quadraticInputInteractionSign q 0).coefficient *
            modeAction energy (modeFrequency m) observed *
            modeAction energy (modeFrequency m) (q.1 0) +
          (quadraticInputInteractionSign q 1).coefficient *
            modeAction energy (modeFrequency m) observed *
            modeAction energy (modeFrequency m) (q.1 0)) := by
  unfold repeatedChildOppositeSignConnectedReturnFeedbackSum
  rw [sum_allDistinctConnectedReturnImage_of_repeatedChildOppositeSign
    observed q hSeparated]
  simp_rw [allDistinctConnectedReturnMap_feedback_eq_signedKernel_mul_actions
    m kappa time energy observed q _ hEnergy hPositive]
  simp only [Fintype.sum_prod_type, Fin.sum_univ_two,
    otherQuadraticSlot_zero, otherQuadraticSlot_one,
    quadraticCollisionSign_succ]
  rw [← hSeparated.1.1]
  ring

/-- The two four-tree feedback families cancel exactly. -/
theorem repeatedChildOppositeSignConnectedReturnFeedbackSum_eq_zero
    {N : Nat} [NeZero N]
    (m : Lattice.PositiveMassConfig N) (kappa time : Real)
    (energy : Lattice.Site N → Real) (observed : Lattice.Site N)
    (q : QuadraticPhaseTerm N)
    (hSeparated : ObservedSeparatedRepeatedChildOppositeSign observed q)
    (hEnergy : ∀ mode, 0 ≤ energy mode)
    (hPositive : PositiveModeTuple m (quadraticCollisionModes observed q)) :
    repeatedChildOppositeSignConnectedReturnFeedbackSum
        m kappa time energy observed q = 0 := by
  rw [repeatedChildOppositeSignConnectedReturnFeedbackSum_eq_pair
    m kappa time energy observed q hSeparated hEnergy hPositive]
  have hCoefficient :=
    inputInteractionCoefficient_add_eq_zero_of_oppositeSigns q hSeparated.1
  linear_combination
    (4 * finiteTimeCollisionKernel m kappa
      (quadraticCollisionSign q) time
      (quadraticCollisionModes observed q) *
      modeAction energy (modeFrequency m) observed *
      modeAction energy (modeFrequency m) (q.1 0)) * hCoefficient

/-- Coherent A1 gain attached to the two-element input-swap orbit. -/
def repeatedChildOppositeSignLocalA1Gain
    {N : Nat} [NeZero N]
    (m : Lattice.PositiveMassConfig N) (kappa time : Real)
    (energy : Lattice.Site N → Real) (observed : Lattice.Site N)
    (q : QuadraticPhaseTerm N) : Real :=
  ((quadraticSwapOrbit q).card : Real) ^ 2 *
    finiteTimeCollisionKernel m kappa
      (quadraticCollisionSign q) time
      (quadraticCollisionModes observed q) *
    ∏ r : Fin 2, modeAction energy (modeFrequency m) (q.1 r)

/-- The two-element orbit gives four copies of the repeated-child action
square. -/
theorem repeatedChildOppositeSignLocalA1Gain_eq
    {N : Nat} [NeZero N]
    (m : Lattice.PositiveMassConfig N) (kappa time : Real)
    (energy : Lattice.Site N → Real) (observed : Lattice.Site N)
    (q : QuadraticPhaseTerm N)
    (hRepeated : RepeatedChildOppositeSign q) :
    repeatedChildOppositeSignLocalA1Gain
        m kappa time energy observed q =
      4 * finiteTimeCollisionKernel m kappa
          (quadraticCollisionSign q) time
          (quadraticCollisionModes observed q) *
        modeAction energy (modeFrequency m) (q.1 0) ^ 2 := by
  unfold repeatedChildOppositeSignLocalA1Gain
  rw [card_quadraticSwapOrbit_eq_two_of_repeatedChildOppositeSign q hRepeated]
  simp only [Nat.cast_ofNat, Fin.prod_univ_two]
  rw [← hRepeated.1]
  ring

/-- For equal child actions and opposite input coefficients, the signed
collision flux reduces exactly to the child action square. -/
theorem quadraticSignedCollisionFlux_eq_child_sq_of_repeatedChildOppositeSign
    {N : Nat} [NeZero N] (observed : Lattice.Site N)
    (q : QuadraticPhaseTerm N) (action : Lattice.Site N → Real)
    (hRepeated : RepeatedChildOppositeSign q) :
    quadraticSignedCollisionFlux q action observed =
      action (q.1 0) ^ 2 := by
  unfold quadraticSignedCollisionFlux signedThreeWaveCollisionFlux
  have hCoefficient :=
    inputInteractionCoefficient_add_eq_zero_of_oppositeSigns q hRepeated
  rw [← hRepeated.1]
  linear_combination
    action observed * action (q.1 0) * hCoefficient

/-- Local coherent gain plus the literal eight-tree feedback. -/
def repeatedChildOppositeSignLocalGainFeedback
    {N : Nat} [NeZero N]
    (m : Lattice.PositiveMassConfig N) (kappa time : Real)
    (energy : Lattice.Site N → Real) (observed : Lattice.Site N)
    (q : QuadraticPhaseTerm N) : Real :=
  repeatedChildOppositeSignLocalA1Gain
      m kappa time energy observed q +
    repeatedChildOppositeSignConnectedReturnFeedbackSum
      m kappa time energy observed q

/-- Exact local gain--loss identity: the repeated/opposite-sign stratum has
no additional local multiplicity correction relative to four copies of the
signed flux. -/
theorem repeatedChildOppositeSignLocalGainFeedback_eq_four_signedFlux
    {N : Nat} [NeZero N]
    (m : Lattice.PositiveMassConfig N) (kappa time : Real)
    (energy : Lattice.Site N → Real) (observed : Lattice.Site N)
    (q : QuadraticPhaseTerm N)
    (hSeparated : ObservedSeparatedRepeatedChildOppositeSign observed q)
    (hEnergy : ∀ mode, 0 ≤ energy mode)
    (hPositive : PositiveModeTuple m (quadraticCollisionModes observed q)) :
    repeatedChildOppositeSignLocalGainFeedback
        m kappa time energy observed q =
      4 * finiteTimeCollisionKernel m kappa
          (quadraticCollisionSign q) time
          (quadraticCollisionModes observed q) *
        quadraticSignedCollisionFlux q
          (modeAction energy (modeFrequency m)) observed := by
  unfold repeatedChildOppositeSignLocalGainFeedback
  rw [repeatedChildOppositeSignLocalA1Gain_eq
      m kappa time energy observed q hSeparated.1,
    repeatedChildOppositeSignConnectedReturnFeedbackSum_eq_zero
      m kappa time energy observed q hSeparated hEnergy hPositive,
    add_zero,
    quadraticSignedCollisionFlux_eq_child_sq_of_repeatedChildOppositeSign
      observed q (modeAction energy (modeFrequency m)) hSeparated.1]

/-- The corresponding correction, defined by subtraction from the expected
four-fold signed flux, is exactly zero. -/
theorem repeatedChildOppositeSignLocalCorrection_eq_zero
    {N : Nat} [NeZero N]
    (m : Lattice.PositiveMassConfig N) (kappa time : Real)
    (energy : Lattice.Site N → Real) (observed : Lattice.Site N)
    (q : QuadraticPhaseTerm N)
    (hSeparated : ObservedSeparatedRepeatedChildOppositeSign observed q)
    (hEnergy : ∀ mode, 0 ≤ energy mode)
    (hPositive : PositiveModeTuple m (quadraticCollisionModes observed q)) :
    repeatedChildOppositeSignLocalGainFeedback
          m kappa time energy observed q -
        4 * finiteTimeCollisionKernel m kappa
          (quadraticCollisionSign q) time
          (quadraticCollisionModes observed q) *
        quadraticSignedCollisionFlux q
          (modeAction energy (modeFrequency m)) observed = 0 := by
  rw [repeatedChildOppositeSignLocalGainFeedback_eq_four_signedFlux
    m kappa time energy observed q hSeparated hEnergy hPositive]
  ring

end

end ArchonPhysics.FreeFPUTRepeatedChildOppositeSignCorrection
