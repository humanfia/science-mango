import ArchonPhysics.CanonicalIIDCoerciveActualSourceSlotSplit

/-!
# Continuous canonical cluster source resolved into actual source slots

This module completes the continuous-law bridge to
`PhyslibFPUTActualClusterSourceSlotClosure`.  On the genuine canonical iid
coercive alpha--beta flow, the exact derivative source of a two-block
factorization defect is the sum of the full nonlinear expectation defects
obtained by replacing one displayed slot, on either side.  Every full slot
then splits into the quadratic-force and quartic-force channels.

Consequently the whole finite cluster source has a deterministic global
good/bad-event cost obtained by summing the explicit channel costs over all
displayed slots.  This cost is sample-independent, but is not asserted to be
small.  No RPA, Markov approximation, decay, nonresonance, or recollision
suppression enters the identity or the bound.
-/

namespace ArchonPhysics.CanonicalIIDCoerciveActualClusterSourceSlotClosure

open scoped BigOperators Matrix Topology

open ArchonPhysics
open ArchonPhysics.CanonicalIIDCoerciveActualExpectationAdapter
open ArchonPhysics.CanonicalIIDCoerciveActualExpectationCompleted
open ArchonPhysics.CanonicalIIDCoerciveActualSourceSlotExpectation
open ArchonPhysics.CanonicalIIDCoerciveActualSourceSlotSplit
open ArchonPhysics.CanonicalIIDCoerciveClusterExpectationClosure
open ArchonPhysics.CanonicalIIDCoerciveContinuousMomentFrontier
open ArchonPhysics.CanonicalIIDCoercivePotentialChannelExpectation
open ArchonPhysics.CanonicalIIDCoerciveSignedModalBlockHierarchy
open ArchonPhysics.CanonicalIIDCoerciveSignedModalHierarchy
open ArchonPhysics.CanonicalIIDCoerciveSignedModalObservableBridge
open ArchonPhysics.CanonicalIIDCoerciveSourceSlotExpectationClosure
open ArchonPhysics.FinitePhaseMonomials
open ArchonPhysics.OrderedTranslationLastMode
open ArchonPhysics.PhyslibFPUTHigherOrderClusterFactorizationPropagation
open ArchonPhysics.RandomMassPositiveCollisionData
open MeasureTheory

noncomputable section

variable {N : Nat} [NeZero N]
variable {I : Type*} [Fintype I] [DecidableEq I]

/-- Mixed full-source insertion on the left block. -/
def canonicalLeftFullInsertionFactorizationDefect
    (kappa beta g : Real) (hbeta : 2 * kappa ^ 2 / 9 < beta)
    (a : Real) (entry : I → PhaseSign × OrderedModeIndex N)
    (left right : Finset I) (time : Real) : Complex :=
  (∫ omega,
      canonicalSignedBlockInsertion (N := N)
          kappa beta g hbeta a entry left (omega, time) *
        canonicalSignedBlockObservable (N := N)
          kappa beta g hbeta a entry right (omega, time)
    ∂canonicalIIDMassPhaseEnsemble.probability) -
    canonicalSignedBlockInsertionBochnerIntegral (N := N)
        kappa beta g hbeta a entry left time *
      canonicalSignedBlockBochnerIntegral (N := N)
        kappa beta g hbeta a entry right time

/-- Mixed full-source insertion on the right block. -/
def canonicalRightFullInsertionFactorizationDefect
    (kappa beta g : Real) (hbeta : 2 * kappa ^ 2 / 9 < beta)
    (a : Real) (entry : I → PhaseSign × OrderedModeIndex N)
    (left right : Finset I) (time : Real) : Complex :=
  (∫ omega,
      canonicalSignedBlockObservable (N := N)
          kappa beta g hbeta a entry left (omega, time) *
        canonicalSignedBlockInsertion (N := N)
          kappa beta g hbeta a entry right (omega, time)
    ∂canonicalIIDMassPhaseEnsemble.probability) -
    canonicalSignedBlockBochnerIntegral (N := N)
        kappa beta g hbeta a entry left time *
      canonicalSignedBlockInsertionBochnerIntegral (N := N)
        kappa beta g hbeta a entry right time

/-- Sample-independent cost for the complete two-block source after resolving
both potential channels and every displayed slot. -/
def canonicalClusterSourceSlotChannelCost
    (A quadraticS quarticS : Real)
    (left right : Finset I) : Real :=
  (∑ slot ∈ left,
      (canonicalLeftSourceSlotDefectCost A quadraticS left right slot +
        canonicalLeftSourceSlotDefectCost A quarticS left right slot)) +
    ∑ slot ∈ right,
      (canonicalRightSourceSlotDefectCost A quadraticS left right slot +
        canonicalRightSourceSlotDefectCost A quarticS left right slot)

theorem integrable_canonicalLeftBlockInsertionProduct_fixedTime
    (hN : 3 ≤ N) {a : Real} (ha0 : 0 ≤ a) (ha1 : a ≤ 1 / 4)
    (kappa beta g : Real) (hbeta : 2 * kappa ^ 2 / 9 < beta)
    (entry : I → PhaseSign × OrderedModeIndex N)
    (hpositive : ∀ i, (entry i).2 ≠
      lastOrderedIndex (ι := Lattice.Site N))
    (left right : Finset I) (time : Real) :
    Integrable (fun omega : CanonicalSample =>
      canonicalSignedBlockInsertion (N := N)
          kappa beta g hbeta a entry left (omega, time) *
        canonicalSignedBlockObservable (N := N)
          kappa beta g hbeta a entry right (omega, time))
      canonicalIIDMassPhaseEnsemble.probability := by
  let _ : IsFiniteMeasure canonicalIIDMassPhaseEnsemble.probability :=
    ⟨by rw [canonicalIIDMassPhaseEnsemble.probability_univ]; norm_num⟩
  apply Integrable.of_bound
    (((measurable_canonicalSignedBlockInsertion (N := N)
      kappa beta g hbeta a entry left).comp
        (measurable_id.prodMk measurable_const)).mul
      (measurable_canonicalSignedBlockObservable_fixedTime (N := N)
        kappa beta g hbeta a entry right time)).aestronglyMeasurable
    (canonicalSignedBlockInsertionEnvelope
        (canonicalSignedAmplitudeEnvelope N kappa beta g hbeta)
        (canonicalSignedSourceEnvelope N kappa beta g hbeta) left *
      canonicalSignedBlockEnvelope
        (canonicalSignedAmplitudeEnvelope N kappa beta g hbeta) right)
  filter_upwards [canonicalSignedBlockBounds_ae_allTime
    hN ha0 ha1 kappa beta g hbeta entry hpositive] with omega hbound
  simp only [Pi.mul_apply, norm_mul]
  exact mul_le_mul (hbound time left).2 (hbound time right).1
    (norm_nonneg _) (by
      unfold canonicalSignedBlockInsertionEnvelope
        canonicalSignedBlockEnvelope
      exact mul_nonneg
        (mul_nonneg (Nat.cast_nonneg _)
          (pow_nonneg (by
            linarith [canonicalSignedAmplitudeEnvelope_nonneg
              (N := N) kappa beta g hbeta]) _))
        (canonicalSignedSourceEnvelope_nonneg
          (N := N) kappa beta g hbeta))

theorem integrable_canonicalRightBlockInsertionProduct_fixedTime
    (hN : 3 ≤ N) {a : Real} (ha0 : 0 ≤ a) (ha1 : a ≤ 1 / 4)
    (kappa beta g : Real) (hbeta : 2 * kappa ^ 2 / 9 < beta)
    (entry : I → PhaseSign × OrderedModeIndex N)
    (hpositive : ∀ i, (entry i).2 ≠
      lastOrderedIndex (ι := Lattice.Site N))
    (left right : Finset I) (time : Real) :
    Integrable (fun omega : CanonicalSample =>
      canonicalSignedBlockObservable (N := N)
          kappa beta g hbeta a entry left (omega, time) *
        canonicalSignedBlockInsertion (N := N)
          kappa beta g hbeta a entry right (omega, time))
      canonicalIIDMassPhaseEnsemble.probability := by
  let _ : IsFiniteMeasure canonicalIIDMassPhaseEnsemble.probability :=
    ⟨by rw [canonicalIIDMassPhaseEnsemble.probability_univ]; norm_num⟩
  apply Integrable.of_bound
    ((measurable_canonicalSignedBlockObservable_fixedTime (N := N)
      kappa beta g hbeta a entry left time).mul
      ((measurable_canonicalSignedBlockInsertion (N := N)
        kappa beta g hbeta a entry right).comp
          (measurable_id.prodMk measurable_const))).aestronglyMeasurable
    (canonicalSignedBlockEnvelope
        (canonicalSignedAmplitudeEnvelope N kappa beta g hbeta) left *
      canonicalSignedBlockInsertionEnvelope
        (canonicalSignedAmplitudeEnvelope N kappa beta g hbeta)
        (canonicalSignedSourceEnvelope N kappa beta g hbeta) right)
  filter_upwards [canonicalSignedBlockBounds_ae_allTime
    hN ha0 ha1 kappa beta g hbeta entry hpositive] with omega hbound
  simp only [Pi.mul_apply, norm_mul]
  exact mul_le_mul (hbound time left).1 (hbound time right).2
    (norm_nonneg _) (by
      unfold canonicalSignedBlockEnvelope
      exact pow_nonneg (by
        linarith [canonicalSignedAmplitudeEnvelope_nonneg
          (N := N) kappa beta g hbeta]) _)

/-- The exact Bochner insertion on a disjoint union obeys the product rule. -/
theorem canonicalSignedBlockInsertionBochnerIntegral_union
    (hN : 3 ≤ N) {a : Real} (ha0 : 0 ≤ a) (ha1 : a ≤ 1 / 4)
    (kappa beta g : Real) (hbeta : 2 * kappa ^ 2 / 9 < beta)
    (entry : I → PhaseSign × OrderedModeIndex N)
    (hpositive : ∀ i, (entry i).2 ≠
      lastOrderedIndex (ι := Lattice.Site N))
    {left right : Finset I} (hindex : Disjoint left right)
    (time : Real) :
    canonicalSignedBlockInsertionBochnerIntegral (N := N)
        kappa beta g hbeta a entry (left ∪ right) time =
      (∫ omega,
          canonicalSignedBlockInsertion (N := N)
              kappa beta g hbeta a entry left (omega, time) *
            canonicalSignedBlockObservable (N := N)
              kappa beta g hbeta a entry right (omega, time)
        ∂canonicalIIDMassPhaseEnsemble.probability) +
        ∫ omega,
          canonicalSignedBlockObservable (N := N)
              kappa beta g hbeta a entry left (omega, time) *
            canonicalSignedBlockInsertion (N := N)
              kappa beta g hbeta a entry right (omega, time)
        ∂canonicalIIDMassPhaseEnsemble.probability := by
  have hleft := integrable_canonicalLeftBlockInsertionProduct_fixedTime
    hN ha0 ha1 kappa beta g hbeta entry hpositive left right time
  have hright := integrable_canonicalRightBlockInsertionProduct_fixedTime
    hN ha0 ha1 kappa beta g hbeta entry hpositive left right time
  rw [← integral_add hleft hright]
  unfold canonicalSignedBlockInsertionBochnerIntegral
  apply integral_congr_ae
  filter_upwards [canonicalSignedBlockHierarchy_ae_allTime
    hN ha0 ha1 kappa beta g hbeta entry hpositive] with omega hhierarchy
  have hunion := hhierarchy (left ∪ right) time
  have hleftDeriv := hhierarchy left time
  have hrightDeriv := hhierarchy right time
  have hunion' : HasDerivAt
      (fun s =>
        canonicalSignedBlockObservable (N := N)
            kappa beta g hbeta a entry left (omega, s) *
          canonicalSignedBlockObservable (N := N)
            kappa beta g hbeta a entry right (omega, s))
      (canonicalSignedBlockInsertion (N := N)
        kappa beta g hbeta a entry (left ∪ right) (omega, time)) time := by
    convert hunion using 1
    funext s
    unfold canonicalSignedBlockObservable
    rw [Finset.prod_union hindex]
  exact hunion'.unique (hleftDeriv.mul hrightDeriv)

theorem integrable_canonicalFullSourceSlotObservable_fixedTime
    (hN : 3 ≤ N) {a : Real} (ha0 : 0 ≤ a) (ha1 : a ≤ 1 / 4)
    (kappa beta g : Real) (hbeta : 2 * kappa ^ 2 / 9 < beta)
    (entry : I → PhaseSign × OrderedModeIndex N)
    (hpositive : ∀ i, (entry i).2 ≠
      lastOrderedIndex (ι := Lattice.Site N))
    (block : Finset I) (slot : I) (time : Real) :
    Integrable (fun omega : CanonicalSample =>
      canonicalFullSourceSlotObservable (N := N)
        kappa beta g hbeta a entry block slot (omega, time))
      canonicalIIDMassPhaseEnsemble.probability := by
  have h :=
    (integrable_canonicalQuadraticSourceSlotObservable_fixedTime
      hN ha0 ha1 kappa beta g hbeta entry hpositive block slot time).add
    (integrable_canonicalQuarticSourceSlotObservable_fixedTime
      hN ha0 ha1 kappa beta g hbeta entry hpositive block slot time)
  exact h.congr (Filter.Eventually.of_forall fun omega =>
    (canonicalFullSourceSlotObservable_eq_quadratic_add_quartic
      kappa beta g hbeta a entry block slot (omega, time)).symm)

theorem integrable_canonicalLeftFullSourceSlotProduct_fixedTime
    (hN : 3 ≤ N) {a : Real} (ha0 : 0 ≤ a) (ha1 : a ≤ 1 / 4)
    (kappa beta g : Real) (hbeta : 2 * kappa ^ 2 / 9 < beta)
    (entry : I → PhaseSign × OrderedModeIndex N)
    (hpositive : ∀ i, (entry i).2 ≠
      lastOrderedIndex (ι := Lattice.Site N))
    (left right : Finset I) (slot : I) (time : Real) :
    Integrable (fun omega : CanonicalSample =>
      canonicalFullSourceSlotObservable (N := N)
          kappa beta g hbeta a entry left slot (omega, time) *
        canonicalSignedBlockObservable (N := N)
          kappa beta g hbeta a entry right (omega, time))
      canonicalIIDMassPhaseEnsemble.probability := by
  have h :=
    (integrable_canonicalLeftQuadraticSlotProduct_fixedTime
      hN ha0 ha1 kappa beta g hbeta entry hpositive left right slot time).add
    (integrable_canonicalLeftQuarticSlotProduct_fixedTime
      hN ha0 ha1 kappa beta g hbeta entry hpositive left right slot time)
  exact h.congr (Filter.Eventually.of_forall fun omega => by
    simp only [Pi.add_apply]
    rw [canonicalFullSourceSlotObservable_eq_quadratic_add_quartic]
    ring)

theorem integrable_canonicalRightFullSourceSlotProduct_fixedTime
    (hN : 3 ≤ N) {a : Real} (ha0 : 0 ≤ a) (ha1 : a ≤ 1 / 4)
    (kappa beta g : Real) (hbeta : 2 * kappa ^ 2 / 9 < beta)
    (entry : I → PhaseSign × OrderedModeIndex N)
    (hpositive : ∀ i, (entry i).2 ≠
      lastOrderedIndex (ι := Lattice.Site N))
    (left right : Finset I) (slot : I) (time : Real) :
    Integrable (fun omega : CanonicalSample =>
      canonicalSignedBlockObservable (N := N)
          kappa beta g hbeta a entry left (omega, time) *
        canonicalFullSourceSlotObservable (N := N)
          kappa beta g hbeta a entry right slot (omega, time))
      canonicalIIDMassPhaseEnsemble.probability := by
  have h :=
    (integrable_canonicalRightQuadraticSlotProduct_fixedTime
      hN ha0 ha1 kappa beta g hbeta entry hpositive left right slot time).add
    (integrable_canonicalRightQuarticSlotProduct_fixedTime
      hN ha0 ha1 kappa beta g hbeta entry hpositive left right slot time)
  exact h.congr (Filter.Eventually.of_forall fun omega => by
    simp only [Pi.add_apply]
    rw [canonicalFullSourceSlotObservable_eq_quadratic_add_quartic]
    ring)

theorem canonicalSignedBlockInsertionBochnerIntegral_eq_sum_fullSlots
    (hN : 3 ≤ N) {a : Real} (ha0 : 0 ≤ a) (ha1 : a ≤ 1 / 4)
    (kappa beta g : Real) (hbeta : 2 * kappa ^ 2 / 9 < beta)
    (entry : I → PhaseSign × OrderedModeIndex N)
    (hpositive : ∀ i, (entry i).2 ≠
      lastOrderedIndex (ι := Lattice.Site N))
    (block : Finset I) (time : Real) :
    canonicalSignedBlockInsertionBochnerIntegral (N := N)
        kappa beta g hbeta a entry block time =
      ∑ slot ∈ block,
        ∫ omega, canonicalFullSourceSlotObservable (N := N)
          kappa beta g hbeta a entry block slot (omega, time)
        ∂canonicalIIDMassPhaseEnsemble.probability := by
  rw [← integral_finsetSum block (fun slot _hslot =>
    integrable_canonicalFullSourceSlotObservable_fixedTime
      hN ha0 ha1 kappa beta g hbeta entry hpositive block slot time)]
  unfold canonicalSignedBlockInsertionBochnerIntegral
  apply integral_congr_ae
  filter_upwards with omega
  rfl

theorem canonicalLeftFullInsertionMixedMoment_eq_sum_fullSlots
    (hN : 3 ≤ N) {a : Real} (ha0 : 0 ≤ a) (ha1 : a ≤ 1 / 4)
    (kappa beta g : Real) (hbeta : 2 * kappa ^ 2 / 9 < beta)
    (entry : I → PhaseSign × OrderedModeIndex N)
    (hpositive : ∀ i, (entry i).2 ≠
      lastOrderedIndex (ι := Lattice.Site N))
    (left right : Finset I) (time : Real) :
    (∫ omega,
        canonicalSignedBlockInsertion (N := N)
            kappa beta g hbeta a entry left (omega, time) *
          canonicalSignedBlockObservable (N := N)
            kappa beta g hbeta a entry right (omega, time)
      ∂canonicalIIDMassPhaseEnsemble.probability) =
      ∑ slot ∈ left,
        ∫ omega,
          canonicalFullSourceSlotObservable (N := N)
              kappa beta g hbeta a entry left slot (omega, time) *
            canonicalSignedBlockObservable (N := N)
              kappa beta g hbeta a entry right (omega, time)
        ∂canonicalIIDMassPhaseEnsemble.probability := by
  rw [← integral_finsetSum left (fun slot _hslot =>
    integrable_canonicalLeftFullSourceSlotProduct_fixedTime
      hN ha0 ha1 kappa beta g hbeta entry hpositive
        left right slot time)]
  apply integral_congr_ae
  filter_upwards with omega
  unfold canonicalSignedBlockInsertion canonicalFullSourceSlotObservable
  rw [Finset.sum_mul]

theorem canonicalRightFullInsertionMixedMoment_eq_sum_fullSlots
    (hN : 3 ≤ N) {a : Real} (ha0 : 0 ≤ a) (ha1 : a ≤ 1 / 4)
    (kappa beta g : Real) (hbeta : 2 * kappa ^ 2 / 9 < beta)
    (entry : I → PhaseSign × OrderedModeIndex N)
    (hpositive : ∀ i, (entry i).2 ≠
      lastOrderedIndex (ι := Lattice.Site N))
    (left right : Finset I) (time : Real) :
    (∫ omega,
        canonicalSignedBlockObservable (N := N)
            kappa beta g hbeta a entry left (omega, time) *
          canonicalSignedBlockInsertion (N := N)
            kappa beta g hbeta a entry right (omega, time)
      ∂canonicalIIDMassPhaseEnsemble.probability) =
      ∑ slot ∈ right,
        ∫ omega,
          canonicalSignedBlockObservable (N := N)
              kappa beta g hbeta a entry left (omega, time) *
            canonicalFullSourceSlotObservable (N := N)
              kappa beta g hbeta a entry right slot (omega, time)
        ∂canonicalIIDMassPhaseEnsemble.probability := by
  rw [← integral_finsetSum right (fun slot _hslot =>
    integrable_canonicalRightFullSourceSlotProduct_fixedTime
      hN ha0 ha1 kappa beta g hbeta entry hpositive
        left right slot time)]
  apply integral_congr_ae
  filter_upwards with omega
  unfold canonicalSignedBlockInsertion canonicalFullSourceSlotObservable
  rw [Finset.mul_sum]

theorem canonicalLeftFullInsertionFactorizationDefect_eq_sum_fullSlots
    (hN : 3 ≤ N) {a : Real} (ha0 : 0 ≤ a) (ha1 : a ≤ 1 / 4)
    (kappa beta g : Real) (hbeta : 2 * kappa ^ 2 / 9 < beta)
    (entry : I → PhaseSign × OrderedModeIndex N)
    (hpositive : ∀ i, (entry i).2 ≠
      lastOrderedIndex (ι := Lattice.Site N))
    (left right : Finset I) (time : Real) :
    canonicalLeftFullInsertionFactorizationDefect (N := N)
        kappa beta g hbeta a entry left right time =
      ∑ slot ∈ left,
        canonicalLeftFullSourceSlotFactorizationDefect (N := N)
          kappa beta g hbeta a entry left right slot time := by
  unfold canonicalLeftFullInsertionFactorizationDefect
  rw [canonicalLeftFullInsertionMixedMoment_eq_sum_fullSlots
      hN ha0 ha1 kappa beta g hbeta entry hpositive left right time,
    canonicalSignedBlockInsertionBochnerIntegral_eq_sum_fullSlots
      hN ha0 ha1 kappa beta g hbeta entry hpositive left time]
  unfold canonicalLeftFullSourceSlotFactorizationDefect
    canonicalLeftPotentialSourceSlotFactorizationDefect
    canonicalPotentialSourceSlotBochnerIntegral
  rw [Finset.sum_mul, ← Finset.sum_sub_distrib]
  rfl

theorem canonicalRightFullInsertionFactorizationDefect_eq_sum_fullSlots
    (hN : 3 ≤ N) {a : Real} (ha0 : 0 ≤ a) (ha1 : a ≤ 1 / 4)
    (kappa beta g : Real) (hbeta : 2 * kappa ^ 2 / 9 < beta)
    (entry : I → PhaseSign × OrderedModeIndex N)
    (hpositive : ∀ i, (entry i).2 ≠
      lastOrderedIndex (ι := Lattice.Site N))
    (left right : Finset I) (time : Real) :
    canonicalRightFullInsertionFactorizationDefect (N := N)
        kappa beta g hbeta a entry left right time =
      ∑ slot ∈ right,
        canonicalRightFullSourceSlotFactorizationDefect (N := N)
          kappa beta g hbeta a entry left right slot time := by
  unfold canonicalRightFullInsertionFactorizationDefect
  rw [canonicalRightFullInsertionMixedMoment_eq_sum_fullSlots
      hN ha0 ha1 kappa beta g hbeta entry hpositive left right time,
    canonicalSignedBlockInsertionBochnerIntegral_eq_sum_fullSlots
      hN ha0 ha1 kappa beta g hbeta entry hpositive right time]
  unfold canonicalRightFullSourceSlotFactorizationDefect
    canonicalRightPotentialSourceSlotFactorizationDefect
    canonicalPotentialSourceSlotBochnerIntegral
  rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
  rfl

/-- Exact actual continuous-law counterpart of
`actualFiniteCoerciveClusterFactorizationDefectSource_eq_slotSums`. -/
theorem canonicalCoerciveClusterFactorizationDefectSource_eq_fullSlotSums
    (hN : 3 ≤ N) {a : Real} (ha0 : 0 ≤ a) (ha1 : a ≤ 1 / 4)
    (kappa beta g : Real) (hbeta : 2 * kappa ^ 2 / 9 < beta)
    (entry : I → PhaseSign × OrderedModeIndex N)
    (hpositive : ∀ i, (entry i).2 ≠
      lastOrderedIndex (ι := Lattice.Site N))
    {left right : Finset I} (hindex : Disjoint left right)
    (time : Real) :
    canonicalCoerciveClusterFactorizationDefectSource (N := N)
        kappa beta g hbeta a entry left right time =
      (∑ slot ∈ left,
        canonicalLeftFullSourceSlotFactorizationDefect (N := N)
          kappa beta g hbeta a entry left right slot time) +
      ∑ slot ∈ right,
        canonicalRightFullSourceSlotFactorizationDefect (N := N)
          kappa beta g hbeta a entry left right slot time := by
  have hunion := canonicalSignedBlockInsertionBochnerIntegral_union
    hN ha0 ha1 kappa beta g hbeta entry hpositive hindex time
  have hleft := canonicalLeftFullInsertionFactorizationDefect_eq_sum_fullSlots
    hN ha0 ha1 kappa beta g hbeta entry hpositive left right time
  have hright := canonicalRightFullInsertionFactorizationDefect_eq_sum_fullSlots
    hN ha0 ha1 kappa beta g hbeta entry hpositive left right time
  unfold canonicalCoerciveClusterFactorizationDefectSource
    blockFactorizationDefectSource
  rw [hunion]
  calc
    _ = canonicalLeftFullInsertionFactorizationDefect (N := N)
          kappa beta g hbeta a entry left right time +
        canonicalRightFullInsertionFactorizationDefect (N := N)
          kappa beta g hbeta a entry left right time := by
      unfold canonicalLeftFullInsertionFactorizationDefect
        canonicalRightFullInsertionFactorizationDefect
      ring
    _ = _ := by rw [hleft, hright]

/-- Deterministic global bad-set budget for the entire resolved cluster
source.  It depends on finite volume, the two block cards, and the coercive
shell/potential parameters, but not on the canonical sample. -/
theorem norm_canonicalCoerciveClusterFactorizationDefectSource_le_slotChannelCost
    (hN : 3 ≤ N) {a : Real} (ha0 : 0 ≤ a) (ha1 : a ≤ 1 / 4)
    (kappa beta g : Real) (hbeta : 2 * kappa ^ 2 / 9 < beta)
    (entry : I → PhaseSign × OrderedModeIndex N)
    (hpositive : ∀ i, (entry i).2 ≠
      lastOrderedIndex (ι := Lattice.Site N))
    {left right : Finset I} (hindex : Disjoint left right)
    (time : Real) :
    ‖canonicalCoerciveClusterFactorizationDefectSource (N := N)
        kappa beta g hbeta a entry left right time‖ ≤
      canonicalClusterSourceSlotChannelCost
        (canonicalSignedAmplitudeEnvelope N kappa beta g hbeta)
        (canonicalSignedPotentialChannelSourceEnvelope N kappa 0 g
          (canonicalWeightedCoordinateEnvelope N kappa beta g hbeta))
        (canonicalSignedPotentialChannelSourceEnvelope N 0 beta g
          (canonicalWeightedCoordinateEnvelope N kappa beta g hbeta))
        left right := by
  rw [canonicalCoerciveClusterFactorizationDefectSource_eq_fullSlotSums
    hN ha0 ha1 kappa beta g hbeta entry hpositive hindex time]
  apply (norm_add_le _ _).trans
  unfold canonicalClusterSourceSlotChannelCost
  apply add_le_add
  · apply (norm_sum_le _ _).trans
    apply Finset.sum_le_sum
    intro slot _hslot
    exact norm_canonicalLeftFullSourceSlotFactorizationDefect_le_channelCosts
      hN ha0 ha1 kappa beta g hbeta entry hpositive
        left right slot time
  · apply (norm_sum_le _ _).trans
    apply Finset.sum_le_sum
    intro slot _hslot
    exact norm_canonicalRightFullSourceSlotFactorizationDefect_le_channelCosts
      hN ha0 ha1 kappa beta g hbeta entry hpositive
        left right slot time

end

end ArchonPhysics.CanonicalIIDCoerciveActualClusterSourceSlotClosure
