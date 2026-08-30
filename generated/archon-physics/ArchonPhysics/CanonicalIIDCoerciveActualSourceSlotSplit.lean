import ArchonPhysics.CanonicalIIDCoerciveActualSourceSlotExpectation

/-!
# Exact continuous-law split of actual alpha--beta source-slot defects

The full canonical iid source-slot expectation defect is exactly the sum of
its quadratic-force and quartic-force defects.  The proof uses the actual
alpha--beta source identity and the explicit Bochner integrability established
in `CanonicalIIDCoerciveActualSourceSlotExpectation`.

This is the continuous canonical-law counterpart of
`PhyslibFPUTActualSourceSlotPotentialSplit`.  It is an exact finite-volume
identity, not a claim that either channel is small or decorrelates.
-/

namespace ArchonPhysics.CanonicalIIDCoerciveActualSourceSlotSplit

open scoped BigOperators Matrix Topology

open ArchonPhysics
open ArchonPhysics.CanonicalIIDCoerciveActualExpectationAdapter
open ArchonPhysics.CanonicalIIDCoerciveActualSourceSlotExpectation
open ArchonPhysics.CanonicalIIDCoercivePotentialChannelExpectation
open ArchonPhysics.CanonicalIIDCoerciveSignedModalHierarchy
open ArchonPhysics.CanonicalIIDCoerciveSignedModalObservableBridge
open ArchonPhysics.CanonicalIIDCoerciveSourceSlotExpectationClosure
open ArchonPhysics.FinitePhaseMonomials
open ArchonPhysics.OrderedTranslationLastMode
open ArchonPhysics.RandomMassPositiveCollisionData
open MeasureTheory

noncomputable section

variable {N : Nat} [NeZero N]
variable {I : Type*} [Fintype I] [DecidableEq I]

/-- Full left source-slot factorization defect on the actual alpha--beta
canonical flow. -/
def canonicalLeftFullSourceSlotFactorizationDefect
    (kappa beta g : Real) (hbeta : 2 * kappa ^ 2 / 9 < beta)
    (a : Real) (entry : I → PhaseSign × OrderedModeIndex N)
    (left right : Finset I) (slot : I) (time : Real) : Complex :=
  canonicalLeftPotentialSourceSlotFactorizationDefect (N := N)
    kappa beta g hbeta a kappa beta g entry left right slot time

/-- Full right source-slot factorization defect on the actual alpha--beta
canonical flow. -/
def canonicalRightFullSourceSlotFactorizationDefect
    (kappa beta g : Real) (hbeta : 2 * kappa ^ 2 / 9 < beta)
    (a : Real) (entry : I → PhaseSign × OrderedModeIndex N)
    (left right : Finset I) (slot : I) (time : Real) : Complex :=
  canonicalRightPotentialSourceSlotFactorizationDefect (N := N)
    kappa beta g hbeta a kappa beta g entry left right slot time

theorem canonicalPotentialFullSourceSlotObservable_eq_quadratic_add_quartic
    (kappa beta g : Real) (hbeta : 2 * kappa ^ 2 / 9 < beta)
    (a : Real) (entry : I → PhaseSign × OrderedModeIndex N)
    (block : Finset I) (slot : I) (st : CanonicalSample × Real) :
    canonicalPotentialSourceSlotObservable (N := N)
        kappa beta g hbeta a kappa beta g entry block slot st =
      canonicalQuadraticSourceSlotObservable (N := N)
          kappa beta g hbeta a entry block slot st +
        canonicalQuarticSourceSlotObservable (N := N)
          kappa beta g hbeta a entry block slot st := by
  change canonicalFullSourceSlotObservable (N := N)
      kappa beta g hbeta a entry block slot st = _
  exact canonicalFullSourceSlotObservable_eq_quadratic_add_quartic
    kappa beta g hbeta a entry block slot st

theorem canonicalLeftFullSourceSlotFactorizationDefect_eq_channels
    (hN : 3 ≤ N) {a : Real} (ha0 : 0 ≤ a) (ha1 : a ≤ 1 / 4)
    (kappa beta g : Real) (hbeta : 2 * kappa ^ 2 / 9 < beta)
    (entry : I → PhaseSign × OrderedModeIndex N)
    (hpositive : ∀ i, (entry i).2 ≠
      lastOrderedIndex (ι := Lattice.Site N))
    (left right : Finset I) (slot : I) (time : Real) :
    canonicalLeftFullSourceSlotFactorizationDefect (N := N)
        kappa beta g hbeta a entry left right slot time =
      canonicalLeftQuadraticSourceSlotFactorizationDefect (N := N)
          kappa beta g hbeta a entry left right slot time +
        canonicalLeftQuarticSourceSlotFactorizationDefect (N := N)
          kappa beta g hbeta a entry left right slot time := by
  have hqSlot := integrable_canonicalQuadraticSourceSlotObservable_fixedTime
    hN ha0 ha1 kappa beta g hbeta entry hpositive left slot time
  have hrSlot := integrable_canonicalQuarticSourceSlotObservable_fixedTime
    hN ha0 ha1 kappa beta g hbeta entry hpositive left slot time
  have hqMixed := integrable_canonicalLeftQuadraticSlotProduct_fixedTime
    hN ha0 ha1 kappa beta g hbeta entry hpositive left right slot time
  have hrMixed := integrable_canonicalLeftQuarticSlotProduct_fixedTime
    hN ha0 ha1 kappa beta g hbeta entry hpositive left right slot time
  have hslot :
      (∫ omega, canonicalPotentialSourceSlotObservable (N := N)
          kappa beta g hbeta a kappa beta g entry left slot (omega, time)
        ∂canonicalIIDMassPhaseEnsemble.probability) =
        (∫ omega, canonicalQuadraticSourceSlotObservable (N := N)
          kappa beta g hbeta a entry left slot (omega, time)
        ∂canonicalIIDMassPhaseEnsemble.probability) +
        ∫ omega, canonicalQuarticSourceSlotObservable (N := N)
          kappa beta g hbeta a entry left slot (omega, time)
        ∂canonicalIIDMassPhaseEnsemble.probability := by
    rw [← integral_add hqSlot hrSlot]
    apply integral_congr_ae
    filter_upwards with omega
    exact canonicalPotentialFullSourceSlotObservable_eq_quadratic_add_quartic
      kappa beta g hbeta a entry left slot (omega, time)
  have hmixed :
      (∫ omega,
          canonicalPotentialSourceSlotObservable (N := N)
              kappa beta g hbeta a kappa beta g entry left slot (omega, time) *
            canonicalSignedBlockObservable (N := N)
              kappa beta g hbeta a entry right (omega, time)
        ∂canonicalIIDMassPhaseEnsemble.probability) =
        (∫ omega,
          canonicalQuadraticSourceSlotObservable (N := N)
              kappa beta g hbeta a entry left slot (omega, time) *
            canonicalSignedBlockObservable (N := N)
              kappa beta g hbeta a entry right (omega, time)
        ∂canonicalIIDMassPhaseEnsemble.probability) +
        ∫ omega,
          canonicalQuarticSourceSlotObservable (N := N)
              kappa beta g hbeta a entry left slot (omega, time) *
            canonicalSignedBlockObservable (N := N)
              kappa beta g hbeta a entry right (omega, time)
        ∂canonicalIIDMassPhaseEnsemble.probability := by
    rw [← integral_add hqMixed hrMixed]
    apply integral_congr_ae
    filter_upwards with omega
    rw [canonicalPotentialFullSourceSlotObservable_eq_quadratic_add_quartic]
    ring
  unfold canonicalLeftFullSourceSlotFactorizationDefect
    canonicalLeftQuadraticSourceSlotFactorizationDefect
    canonicalLeftQuarticSourceSlotFactorizationDefect
    canonicalLeftPotentialSourceSlotFactorizationDefect
    canonicalPotentialSourceSlotBochnerIntegral
  simp only [canonicalQuadraticSourceSlotObservable,
    canonicalQuarticSourceSlotObservable] at hmixed hslot
  rw [hmixed, hslot]
  ring

theorem canonicalRightFullSourceSlotFactorizationDefect_eq_channels
    (hN : 3 ≤ N) {a : Real} (ha0 : 0 ≤ a) (ha1 : a ≤ 1 / 4)
    (kappa beta g : Real) (hbeta : 2 * kappa ^ 2 / 9 < beta)
    (entry : I → PhaseSign × OrderedModeIndex N)
    (hpositive : ∀ i, (entry i).2 ≠
      lastOrderedIndex (ι := Lattice.Site N))
    (left right : Finset I) (slot : I) (time : Real) :
    canonicalRightFullSourceSlotFactorizationDefect (N := N)
        kappa beta g hbeta a entry left right slot time =
      canonicalRightQuadraticSourceSlotFactorizationDefect (N := N)
          kappa beta g hbeta a entry left right slot time +
        canonicalRightQuarticSourceSlotFactorizationDefect (N := N)
          kappa beta g hbeta a entry left right slot time := by
  have hqSlot := integrable_canonicalQuadraticSourceSlotObservable_fixedTime
    hN ha0 ha1 kappa beta g hbeta entry hpositive right slot time
  have hrSlot := integrable_canonicalQuarticSourceSlotObservable_fixedTime
    hN ha0 ha1 kappa beta g hbeta entry hpositive right slot time
  have hqMixed := integrable_canonicalRightQuadraticSlotProduct_fixedTime
    hN ha0 ha1 kappa beta g hbeta entry hpositive left right slot time
  have hrMixed := integrable_canonicalRightQuarticSlotProduct_fixedTime
    hN ha0 ha1 kappa beta g hbeta entry hpositive left right slot time
  have hslot :
      (∫ omega, canonicalPotentialSourceSlotObservable (N := N)
          kappa beta g hbeta a kappa beta g entry right slot (omega, time)
        ∂canonicalIIDMassPhaseEnsemble.probability) =
        (∫ omega, canonicalQuadraticSourceSlotObservable (N := N)
          kappa beta g hbeta a entry right slot (omega, time)
        ∂canonicalIIDMassPhaseEnsemble.probability) +
        ∫ omega, canonicalQuarticSourceSlotObservable (N := N)
          kappa beta g hbeta a entry right slot (omega, time)
        ∂canonicalIIDMassPhaseEnsemble.probability := by
    rw [← integral_add hqSlot hrSlot]
    apply integral_congr_ae
    filter_upwards with omega
    exact canonicalPotentialFullSourceSlotObservable_eq_quadratic_add_quartic
      kappa beta g hbeta a entry right slot (omega, time)
  have hmixed :
      (∫ omega,
          canonicalSignedBlockObservable (N := N)
              kappa beta g hbeta a entry left (omega, time) *
            canonicalPotentialSourceSlotObservable (N := N)
              kappa beta g hbeta a kappa beta g entry right slot (omega, time)
        ∂canonicalIIDMassPhaseEnsemble.probability) =
        (∫ omega,
          canonicalSignedBlockObservable (N := N)
              kappa beta g hbeta a entry left (omega, time) *
            canonicalQuadraticSourceSlotObservable (N := N)
              kappa beta g hbeta a entry right slot (omega, time)
        ∂canonicalIIDMassPhaseEnsemble.probability) +
        ∫ omega,
          canonicalSignedBlockObservable (N := N)
              kappa beta g hbeta a entry left (omega, time) *
            canonicalQuarticSourceSlotObservable (N := N)
              kappa beta g hbeta a entry right slot (omega, time)
        ∂canonicalIIDMassPhaseEnsemble.probability := by
    rw [← integral_add hqMixed hrMixed]
    apply integral_congr_ae
    filter_upwards with omega
    rw [canonicalPotentialFullSourceSlotObservable_eq_quadratic_add_quartic]
    ring
  unfold canonicalRightFullSourceSlotFactorizationDefect
    canonicalRightQuadraticSourceSlotFactorizationDefect
    canonicalRightQuarticSourceSlotFactorizationDefect
    canonicalRightPotentialSourceSlotFactorizationDefect
    canonicalPotentialSourceSlotBochnerIntegral
  simp only [canonicalQuadraticSourceSlotObservable,
    canonicalQuarticSourceSlotObservable] at hmixed hslot
  rw [hmixed, hslot]
  ring

/-- Full actual source-slot cost is controlled by the sum of the explicit
quadratic and quartic global costs. -/
theorem norm_canonicalLeftFullSourceSlotFactorizationDefect_le_channelCosts
    (hN : 3 ≤ N) {a : Real} (ha0 : 0 ≤ a) (ha1 : a ≤ 1 / 4)
    (kappa beta g : Real) (hbeta : 2 * kappa ^ 2 / 9 < beta)
    (entry : I → PhaseSign × OrderedModeIndex N)
    (hpositive : ∀ i, (entry i).2 ≠
      lastOrderedIndex (ι := Lattice.Site N))
    (left right : Finset I) (slot : I) (time : Real) :
    ‖canonicalLeftFullSourceSlotFactorizationDefect (N := N)
        kappa beta g hbeta a entry left right slot time‖ ≤
      canonicalLeftSourceSlotDefectCost
          (canonicalSignedAmplitudeEnvelope N kappa beta g hbeta)
          (canonicalSignedPotentialChannelSourceEnvelope N kappa 0 g
            (canonicalWeightedCoordinateEnvelope N kappa beta g hbeta))
          left right slot +
        canonicalLeftSourceSlotDefectCost
          (canonicalSignedAmplitudeEnvelope N kappa beta g hbeta)
          (canonicalSignedPotentialChannelSourceEnvelope N 0 beta g
            (canonicalWeightedCoordinateEnvelope N kappa beta g hbeta))
          left right slot := by
  rw [canonicalLeftFullSourceSlotFactorizationDefect_eq_channels
    hN ha0 ha1 kappa beta g hbeta entry hpositive left right slot time]
  exact (norm_add_le _ _).trans (add_le_add
    (norm_canonicalLeftQuadraticSourceSlotFactorizationDefect_le_cost
      hN ha0 ha1 kappa beta g hbeta entry hpositive left right slot time)
    (norm_canonicalLeftQuarticSourceSlotFactorizationDefect_le_cost
      hN ha0 ha1 kappa beta g hbeta entry hpositive left right slot time))

/-- Symmetric full actual right-source-slot global cost. -/
theorem norm_canonicalRightFullSourceSlotFactorizationDefect_le_channelCosts
    (hN : 3 ≤ N) {a : Real} (ha0 : 0 ≤ a) (ha1 : a ≤ 1 / 4)
    (kappa beta g : Real) (hbeta : 2 * kappa ^ 2 / 9 < beta)
    (entry : I → PhaseSign × OrderedModeIndex N)
    (hpositive : ∀ i, (entry i).2 ≠
      lastOrderedIndex (ι := Lattice.Site N))
    (left right : Finset I) (slot : I) (time : Real) :
    ‖canonicalRightFullSourceSlotFactorizationDefect (N := N)
        kappa beta g hbeta a entry left right slot time‖ ≤
      canonicalRightSourceSlotDefectCost
          (canonicalSignedAmplitudeEnvelope N kappa beta g hbeta)
          (canonicalSignedPotentialChannelSourceEnvelope N kappa 0 g
            (canonicalWeightedCoordinateEnvelope N kappa beta g hbeta))
          left right slot +
        canonicalRightSourceSlotDefectCost
          (canonicalSignedAmplitudeEnvelope N kappa beta g hbeta)
          (canonicalSignedPotentialChannelSourceEnvelope N 0 beta g
            (canonicalWeightedCoordinateEnvelope N kappa beta g hbeta))
          left right slot := by
  rw [canonicalRightFullSourceSlotFactorizationDefect_eq_channels
    hN ha0 ha1 kappa beta g hbeta entry hpositive left right slot time]
  exact (norm_add_le _ _).trans (add_le_add
    (norm_canonicalRightQuadraticSourceSlotFactorizationDefect_le_cost
      hN ha0 ha1 kappa beta g hbeta entry hpositive left right slot time)
    (norm_canonicalRightQuarticSourceSlotFactorizationDefect_le_cost
      hN ha0 ha1 kappa beta g hbeta entry hpositive left right slot time))

end

end ArchonPhysics.CanonicalIIDCoerciveActualSourceSlotSplit
