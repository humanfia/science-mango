import ArchonPhysics.CanonicalIIDCoercivePotentialChannelExpectation

/-!
# Canonical iid source-slot expectation closure

This module connects the continuous canonical iid Bochner hierarchy to the
source-slot resolution of `PhyslibFPUTActualClusterSourceSlotClosure` and the
quadratic/quartic split of `PhyslibFPUTActualSourceSlotPotentialSplit`.

For every fixed finite ordered block, replacing one displayed amplitude by
either the quadratic-force or quartic-force source gives a measurable,
Bochner-integrable random variable.  Its two-block factorization defect has
an explicit deterministic global envelope `D`, independent of the sample.
The full alpha--beta slot defect is exactly the sum of the two channel
defects.

These are domination and algebraic closure statements.  The constants are
not asserted to be small, and no random-phase, Markov, decay, nonresonance,
or kinetic-limit hypothesis is introduced.  Resonant, charge-balanced, and
recollision sectors remain inside the exact expectation defects.
-/

namespace ArchonPhysics.CanonicalIIDCoerciveSourceSlotExpectationClosure

open scoped BigOperators Matrix Topology

open ArchonPhysics
open ArchonPhysics.CanonicalIIDCoerciveActualExpectationAdapter
open ArchonPhysics.CanonicalIIDCoerciveActualExpectationCompleted
open ArchonPhysics.CanonicalIIDCoerciveClusterExpectationClosure
open ArchonPhysics.CanonicalIIDCoerciveContinuousMomentFrontier
open ArchonPhysics.CanonicalIIDCoerciveExpectationHierarchy
open ArchonPhysics.CanonicalIIDCoercivePotentialChannelExpectation
open ArchonPhysics.CanonicalIIDCoerciveSignedModalBlockHierarchy
open ArchonPhysics.CanonicalIIDCoerciveSignedModalHierarchy
open ArchonPhysics.CanonicalIIDCoerciveSignedModalObservableBridge
open ArchonPhysics.FinitePhaseMonomials
open ArchonPhysics.OrderedTranslationLastMode
open ArchonPhysics.PhyslibFPUTActualClusterSourceSlotClosure
open ArchonPhysics.PhyslibFPUTActualSourceSlotPotentialSplit
open ArchonPhysics.PhyslibFPUTHigherOrderClusterFactorizationPropagation
open ArchonPhysics.PhyslibFPUTSourceInsertionClusterExpansion
open ArchonPhysics.RandomMassPositiveCollisionData
open MeasureTheory

noncomputable section

variable {N : Nat} [NeZero N]
variable {I : Type*} [Fintype I] [DecidableEq I]

/-- One canonical ordered block with one displayed slot replaced by a
separated potential channel source. -/
def canonicalPotentialSourceSlotObservable
    (flowKappa flowBeta flowG : Real)
    (hflowBeta : 2 * flowKappa ^ 2 / 9 < flowBeta)
    (a sourceKappa sourceBeta sourceG : Real)
    (entry : I → PhaseSign × OrderedModeIndex N)
    (block : Finset I) (slot : I)
    (st : CanonicalSample × Real) : Complex :=
  (∏ j ∈ block.erase slot,
    canonicalSignedInteractionAmplitude (N := N)
      flowKappa flowBeta flowG hflowBeta a (entry j) st) *
    canonicalSignedPotentialChannelRotatedSource (N := N)
      flowKappa flowBeta flowG hflowBeta a
      sourceKappa sourceBeta sourceG (entry slot) st

/-- Quadratic-force source-slot observable on the actual alpha--beta flow. -/
def canonicalQuadraticSourceSlotObservable
    (kappa beta g : Real) (hbeta : 2 * kappa ^ 2 / 9 < beta)
    (a : Real) (entry : I → PhaseSign × OrderedModeIndex N)
    (block : Finset I) (slot : I) :=
  canonicalPotentialSourceSlotObservable (N := N)
    kappa beta g hbeta a kappa 0 g entry block slot

/-- Quartic-force source-slot observable on the actual alpha--beta flow. -/
def canonicalQuarticSourceSlotObservable
    (kappa beta g : Real) (hbeta : 2 * kappa ^ 2 / 9 < beta)
    (a : Real) (entry : I → PhaseSign × OrderedModeIndex N)
    (block : Finset I) (slot : I) :=
  canonicalPotentialSourceSlotObservable (N := N)
    kappa beta g hbeta a 0 beta g entry block slot

/-- The corresponding full alpha--beta source-slot observable. -/
def canonicalFullSourceSlotObservable
    (kappa beta g : Real) (hbeta : 2 * kappa ^ 2 / 9 < beta)
    (a : Real) (entry : I → PhaseSign × OrderedModeIndex N)
    (block : Finset I) (slot : I)
    (st : CanonicalSample × Real) : Complex :=
  (∏ j ∈ block.erase slot,
    canonicalSignedInteractionAmplitude (N := N)
      kappa beta g hbeta a (entry j) st) *
    canonicalSignedRotatedSource (N := N)
      kappa beta g hbeta a (entry slot) st

/-- Uniform bound for one source-replaced block. -/
def canonicalPotentialSourceSlotEnvelope
    (A S : Real) (block : Finset I) (slot : I) : Real :=
  canonicalSignedBlockEnvelope A (block.erase slot) * S

/-- Global good/bad cost for a left source slot against a right block. -/
def canonicalLeftSourceSlotDefectCost
    (A S : Real) (left right : Finset I) (slot : I) : Real :=
  2 * canonicalPotentialSourceSlotEnvelope A S left slot *
    canonicalSignedBlockEnvelope A right

/-- Global good/bad cost for a left block against a right source slot. -/
def canonicalRightSourceSlotDefectCost
    (A S : Real) (left right : Finset I) (slot : I) : Real :=
  2 * canonicalSignedBlockEnvelope A left *
    canonicalPotentialSourceSlotEnvelope A S right slot

/-- Bochner expectation of one separated source-replaced block. -/
def canonicalPotentialSourceSlotBochnerIntegral
    (flowKappa flowBeta flowG : Real)
    (hflowBeta : 2 * flowKappa ^ 2 / 9 < flowBeta)
    (a sourceKappa sourceBeta sourceG : Real)
    (entry : I → PhaseSign × OrderedModeIndex N)
    (block : Finset I) (slot : I) (time : Real) : Complex :=
  ∫ omega, canonicalPotentialSourceSlotObservable (N := N)
      flowKappa flowBeta flowG hflowBeta a
      sourceKappa sourceBeta sourceG entry block slot (omega, time)
    ∂canonicalIIDMassPhaseEnsemble.probability

/-- Continuous-law left source-slot factorization defect. -/
def canonicalLeftPotentialSourceSlotFactorizationDefect
    (flowKappa flowBeta flowG : Real)
    (hflowBeta : 2 * flowKappa ^ 2 / 9 < flowBeta)
    (a sourceKappa sourceBeta sourceG : Real)
    (entry : I → PhaseSign × OrderedModeIndex N)
    (left right : Finset I) (slot : I) (time : Real) : Complex :=
  ∫ omega,
      canonicalPotentialSourceSlotObservable (N := N)
          flowKappa flowBeta flowG hflowBeta a
          sourceKappa sourceBeta sourceG entry left slot (omega, time) *
        canonicalSignedBlockObservable (N := N)
          flowKappa flowBeta flowG hflowBeta a entry right (omega, time)
    ∂canonicalIIDMassPhaseEnsemble.probability -
    canonicalPotentialSourceSlotBochnerIntegral (N := N)
        flowKappa flowBeta flowG hflowBeta a
        sourceKappa sourceBeta sourceG entry left slot time *
      canonicalSignedBlockBochnerIntegral (N := N)
        flowKappa flowBeta flowG hflowBeta a entry right time

/-- Continuous-law right source-slot factorization defect. -/
def canonicalRightPotentialSourceSlotFactorizationDefect
    (flowKappa flowBeta flowG : Real)
    (hflowBeta : 2 * flowKappa ^ 2 / 9 < flowBeta)
    (a sourceKappa sourceBeta sourceG : Real)
    (entry : I → PhaseSign × OrderedModeIndex N)
    (left right : Finset I) (slot : I) (time : Real) : Complex :=
  ∫ omega,
      canonicalSignedBlockObservable (N := N)
          flowKappa flowBeta flowG hflowBeta a entry left (omega, time) *
        canonicalPotentialSourceSlotObservable (N := N)
          flowKappa flowBeta flowG hflowBeta a
          sourceKappa sourceBeta sourceG entry right slot (omega, time)
    ∂canonicalIIDMassPhaseEnsemble.probability -
    canonicalSignedBlockBochnerIntegral (N := N)
        flowKappa flowBeta flowG hflowBeta a entry left time *
      canonicalPotentialSourceSlotBochnerIntegral (N := N)
        flowKappa flowBeta flowG hflowBeta a
        sourceKappa sourceBeta sourceG entry right slot time

theorem canonicalFullSourceSlotObservable_eq_quadratic_add_quartic
    (kappa beta g : Real) (hbeta : 2 * kappa ^ 2 / 9 < beta)
    (a : Real) (entry : I → PhaseSign × OrderedModeIndex N)
    (block : Finset I) (slot : I) (st : CanonicalSample × Real) :
    canonicalFullSourceSlotObservable (N := N)
        kappa beta g hbeta a entry block slot st =
      canonicalQuadraticSourceSlotObservable (N := N)
          kappa beta g hbeta a entry block slot st +
        canonicalQuarticSourceSlotObservable (N := N)
          kappa beta g hbeta a entry block slot st := by
  unfold canonicalFullSourceSlotObservable
    canonicalQuadraticSourceSlotObservable
    canonicalQuarticSourceSlotObservable
    canonicalPotentialSourceSlotObservable
  rw [canonicalSignedRotatedSource_eq_quadratic_add_quartic]
  simp only [canonicalSignedQuadraticRotatedSource,
    canonicalSignedQuarticRotatedSource]
  ring

theorem measurable_canonicalPotentialSourceSlotObservable
    (flowKappa flowBeta flowG : Real)
    (hflowBeta : 2 * flowKappa ^ 2 / 9 < flowBeta)
    (a sourceKappa sourceBeta sourceG : Real)
    (entry : I → PhaseSign × OrderedModeIndex N)
    (block : Finset I) (slot : I) :
    Measurable (canonicalPotentialSourceSlotObservable (N := N)
      flowKappa flowBeta flowG hflowBeta a
      sourceKappa sourceBeta sourceG entry block slot) := by
  unfold canonicalPotentialSourceSlotObservable
  apply Measurable.mul
  · apply Finset.measurable_prod
    intro j _hj
    exact measurable_canonicalSignedInteractionAmplitude (N := N)
      flowKappa flowBeta flowG hflowBeta a (entry j)
  · exact measurable_canonicalSignedPotentialChannelRotatedSource (N := N)
      flowKappa flowBeta flowG hflowBeta a
      sourceKappa sourceBeta sourceG (entry slot)

theorem measurable_canonicalPotentialSourceSlotObservable_fixedTime
    (flowKappa flowBeta flowG : Real)
    (hflowBeta : 2 * flowKappa ^ 2 / 9 < flowBeta)
    (a sourceKappa sourceBeta sourceG : Real)
    (entry : I → PhaseSign × OrderedModeIndex N)
    (block : Finset I) (slot : I) (time : Real) :
    Measurable fun omega : CanonicalSample =>
      canonicalPotentialSourceSlotObservable (N := N)
        flowKappa flowBeta flowG hflowBeta a
        sourceKappa sourceBeta sourceG entry block slot (omega, time) := by
  exact (measurable_canonicalPotentialSourceSlotObservable (N := N)
    flowKappa flowBeta flowG hflowBeta a
    sourceKappa sourceBeta sourceG entry block slot).comp
      (measurable_id.prodMk measurable_const)

theorem canonicalPotentialSourceSlotBounds_ae_allTime
    (hN : 3 ≤ N) {a : Real} (ha0 : 0 ≤ a) (ha1 : a ≤ 1 / 4)
    (flowKappa flowBeta flowG : Real)
    (hflowBeta : 2 * flowKappa ^ 2 / 9 < flowBeta)
    (sourceKappa sourceBeta sourceG : Real)
    (entry : I → PhaseSign × OrderedModeIndex N)
    (hpositive : ∀ i, (entry i).2 ≠
      lastOrderedIndex (ι := Lattice.Site N))
    (block : Finset I) (slot : I) :
    ∀ᵐ omega ∂canonicalIIDMassPhaseEnsemble.probability,
      ∀ time : Real,
        ‖canonicalPotentialSourceSlotObservable (N := N)
            flowKappa flowBeta flowG hflowBeta a
            sourceKappa sourceBeta sourceG entry block slot (omega, time)‖ ≤
          canonicalPotentialSourceSlotEnvelope
            (canonicalSignedAmplitudeEnvelope N
              flowKappa flowBeta flowG hflowBeta)
            (canonicalSignedPotentialChannelSourceEnvelope N
              sourceKappa sourceBeta sourceG
              (canonicalWeightedCoordinateEnvelope N
                flowKappa flowBeta flowG hflowBeta)) block slot := by
  filter_upwards [canonicalSignedBlockBounds_ae_allTime
      hN ha0 ha1 flowKappa flowBeta flowG hflowBeta entry hpositive,
    canonicalSignedPotentialChannelSourceBounds_ae_allTime
      hN ha0 ha1 flowKappa flowBeta flowG hflowBeta
      sourceKappa sourceBeta sourceG (entry slot) (hpositive slot)]
      with omega hblock hsource
  intro time
  unfold canonicalPotentialSourceSlotObservable
    canonicalPotentialSourceSlotEnvelope
  simp only [Pi.mul_apply, norm_mul]
  exact mul_le_mul (hblock time (block.erase slot)).1 (hsource time)
    (norm_nonneg _) (by
      unfold canonicalSignedBlockEnvelope
      exact pow_nonneg (by
        linarith [canonicalSignedAmplitudeEnvelope_nonneg
          (N := N) flowKappa flowBeta flowG hflowBeta]) _)

theorem integrable_canonicalPotentialSourceSlotObservable_fixedTime
    (hN : 3 ≤ N) {a : Real} (ha0 : 0 ≤ a) (ha1 : a ≤ 1 / 4)
    (flowKappa flowBeta flowG : Real)
    (hflowBeta : 2 * flowKappa ^ 2 / 9 < flowBeta)
    (sourceKappa sourceBeta sourceG : Real)
    (entry : I → PhaseSign × OrderedModeIndex N)
    (hpositive : ∀ i, (entry i).2 ≠
      lastOrderedIndex (ι := Lattice.Site N))
    (block : Finset I) (slot : I) (time : Real) :
    Integrable (fun omega : CanonicalSample =>
      canonicalPotentialSourceSlotObservable (N := N)
        flowKappa flowBeta flowG hflowBeta a
        sourceKappa sourceBeta sourceG entry block slot (omega, time))
      canonicalIIDMassPhaseEnsemble.probability := by
  let _ : IsFiniteMeasure canonicalIIDMassPhaseEnsemble.probability :=
    ⟨by rw [canonicalIIDMassPhaseEnsemble.probability_univ]; norm_num⟩
  apply Integrable.of_bound
    (measurable_canonicalPotentialSourceSlotObservable_fixedTime (N := N)
      flowKappa flowBeta flowG hflowBeta a
      sourceKappa sourceBeta sourceG entry block slot time).aestronglyMeasurable
    (canonicalPotentialSourceSlotEnvelope
      (canonicalSignedAmplitudeEnvelope N flowKappa flowBeta flowG hflowBeta)
      (canonicalSignedPotentialChannelSourceEnvelope N
        sourceKappa sourceBeta sourceG
        (canonicalWeightedCoordinateEnvelope N
          flowKappa flowBeta flowG hflowBeta)) block slot)
  filter_upwards [canonicalPotentialSourceSlotBounds_ae_allTime
    hN ha0 ha1 flowKappa flowBeta flowG hflowBeta
    sourceKappa sourceBeta sourceG entry hpositive block slot]
      with omega hbound
  exact hbound time

theorem integrable_canonicalPotentialLeftSlotProduct_fixedTime
    (hN : 3 ≤ N) {a : Real} (ha0 : 0 ≤ a) (ha1 : a ≤ 1 / 4)
    (flowKappa flowBeta flowG : Real)
    (hflowBeta : 2 * flowKappa ^ 2 / 9 < flowBeta)
    (sourceKappa sourceBeta sourceG : Real)
    (entry : I → PhaseSign × OrderedModeIndex N)
    (hpositive : ∀ i, (entry i).2 ≠
      lastOrderedIndex (ι := Lattice.Site N))
    (left right : Finset I) (slot : I) (time : Real) :
    Integrable (fun omega : CanonicalSample =>
      canonicalPotentialSourceSlotObservable (N := N)
          flowKappa flowBeta flowG hflowBeta a
          sourceKappa sourceBeta sourceG entry left slot (omega, time) *
        canonicalSignedBlockObservable (N := N)
          flowKappa flowBeta flowG hflowBeta a entry right (omega, time))
      canonicalIIDMassPhaseEnsemble.probability := by
  let _ : IsFiniteMeasure canonicalIIDMassPhaseEnsemble.probability :=
    ⟨by rw [canonicalIIDMassPhaseEnsemble.probability_univ]; norm_num⟩
  apply Integrable.of_bound
    ((measurable_canonicalPotentialSourceSlotObservable_fixedTime (N := N)
      flowKappa flowBeta flowG hflowBeta a
      sourceKappa sourceBeta sourceG entry left slot time).mul
      (measurable_canonicalSignedBlockObservable_fixedTime (N := N)
        flowKappa flowBeta flowG hflowBeta a entry right time)).aestronglyMeasurable
    (canonicalPotentialSourceSlotEnvelope
      (canonicalSignedAmplitudeEnvelope N flowKappa flowBeta flowG hflowBeta)
      (canonicalSignedPotentialChannelSourceEnvelope N
        sourceKappa sourceBeta sourceG
        (canonicalWeightedCoordinateEnvelope N
          flowKappa flowBeta flowG hflowBeta)) left slot *
      canonicalSignedBlockEnvelope
        (canonicalSignedAmplitudeEnvelope N flowKappa flowBeta flowG hflowBeta)
        right)
  filter_upwards [canonicalPotentialSourceSlotBounds_ae_allTime
      hN ha0 ha1 flowKappa flowBeta flowG hflowBeta
        sourceKappa sourceBeta sourceG entry hpositive left slot,
    canonicalSignedBlockBounds_ae_allTime
      hN ha0 ha1 flowKappa flowBeta flowG hflowBeta entry hpositive]
      with omega hslot hblock
  simp only [Pi.mul_apply, norm_mul]
  exact mul_le_mul (hslot time) (hblock time right).1
    (norm_nonneg _) (by
      unfold canonicalPotentialSourceSlotEnvelope
      exact mul_nonneg
        (by
          unfold canonicalSignedBlockEnvelope
          exact pow_nonneg (by
            linarith [canonicalSignedAmplitudeEnvelope_nonneg
              (N := N) flowKappa flowBeta flowG hflowBeta]) _)
        (canonicalSignedPotentialChannelSourceEnvelope_nonneg
          sourceKappa sourceBeta sourceG
          (canonicalWeightedCoordinateEnvelope N
            flowKappa flowBeta flowG hflowBeta)
          (canonicalWeightedCoordinateEnvelope_nonneg
            flowKappa flowBeta flowG hflowBeta)))

theorem integrable_canonicalPotentialRightSlotProduct_fixedTime
    (hN : 3 ≤ N) {a : Real} (ha0 : 0 ≤ a) (ha1 : a ≤ 1 / 4)
    (flowKappa flowBeta flowG : Real)
    (hflowBeta : 2 * flowKappa ^ 2 / 9 < flowBeta)
    (sourceKappa sourceBeta sourceG : Real)
    (entry : I → PhaseSign × OrderedModeIndex N)
    (hpositive : ∀ i, (entry i).2 ≠
      lastOrderedIndex (ι := Lattice.Site N))
    (left right : Finset I) (slot : I) (time : Real) :
    Integrable (fun omega : CanonicalSample =>
      canonicalSignedBlockObservable (N := N)
          flowKappa flowBeta flowG hflowBeta a entry left (omega, time) *
        canonicalPotentialSourceSlotObservable (N := N)
          flowKappa flowBeta flowG hflowBeta a
          sourceKappa sourceBeta sourceG entry right slot (omega, time))
      canonicalIIDMassPhaseEnsemble.probability := by
  let _ : IsFiniteMeasure canonicalIIDMassPhaseEnsemble.probability :=
    ⟨by rw [canonicalIIDMassPhaseEnsemble.probability_univ]; norm_num⟩
  apply Integrable.of_bound
    ((measurable_canonicalSignedBlockObservable_fixedTime (N := N)
      flowKappa flowBeta flowG hflowBeta a entry left time).mul
      (measurable_canonicalPotentialSourceSlotObservable_fixedTime (N := N)
        flowKappa flowBeta flowG hflowBeta a
        sourceKappa sourceBeta sourceG entry right slot time)).aestronglyMeasurable
    (canonicalSignedBlockEnvelope
        (canonicalSignedAmplitudeEnvelope N flowKappa flowBeta flowG hflowBeta)
        left *
      canonicalPotentialSourceSlotEnvelope
        (canonicalSignedAmplitudeEnvelope N flowKappa flowBeta flowG hflowBeta)
        (canonicalSignedPotentialChannelSourceEnvelope N
          sourceKappa sourceBeta sourceG
          (canonicalWeightedCoordinateEnvelope N
            flowKappa flowBeta flowG hflowBeta)) right slot)
  filter_upwards [canonicalSignedBlockBounds_ae_allTime
      hN ha0 ha1 flowKappa flowBeta flowG hflowBeta entry hpositive,
    canonicalPotentialSourceSlotBounds_ae_allTime
      hN ha0 ha1 flowKappa flowBeta flowG hflowBeta
        sourceKappa sourceBeta sourceG entry hpositive right slot]
      with omega hblock hslot
  simp only [Pi.mul_apply, norm_mul]
  exact mul_le_mul (hblock time left).1 (hslot time)
    (norm_nonneg _) (by
      unfold canonicalSignedBlockEnvelope
      exact pow_nonneg (by
        linarith [canonicalSignedAmplitudeEnvelope_nonneg
          (N := N) flowKappa flowBeta flowG hflowBeta]) _)

end

end ArchonPhysics.CanonicalIIDCoerciveSourceSlotExpectationClosure
