import Family8Grounding.Family8EndpointIdentityExactSameCoreHighPayloadFiberLogReselectionV1
import Family8Grounding.Family8EndpointIdentityTauActiveParentAdmissibilityV1
import Family8Grounding.Family8SelectedOccurrenceWinnerSideLocalBlockPositiveCarrierPaymentV1
import Mathlib.Tactic

/-!
# Endpoint fibre-log-first winner-side same-q payment

This is the object-preserving replacement for the old occurrence-first high
selection.  It retains the literal endpoint tau datum, greedy partition,
selected first-hit prefix, and cover; selects a whole fibre-log bucket first;
then selects a mass-weighted common outer-side bucket; and only afterwards
lets the exact-outer assembly select one quality occurrence `q` and one inner
side label on that same `q`.

The output keeps the source-average payment from the fibre-log bucket next to
the existing winner-side payment.  Unfolding the latter exposes the literal
`Rside.card * fiber(q).card` count, exact-outer/final-fibre product, same-q
Córdoba estimate, and carrier-floor cross payment.  No DSO-valued callback is
used.
-/

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 9000000

open Set MeasureTheory
open scoped BigOperators ENNReal NNReal

namespace Family8EndpointIdentityExactSameCoreHighPayloadWinnerSideSameQPaymentV1

open LeanEval.Analysis.WangZahlKakeya
open Submission.Kakeya.ConvexGeometry
open Submission.Kakeya.ConvexFactoring
open Submission.Kakeya.ConvexFactoring.FiberwiseMultiplicityAssembly
open Submission.Kakeya.ConvexFactoring.FullConvexMaximalDensity
open Submission.Kakeya.ConvexFactoring.GreedyOccurrenceFactorization
open Submission.Kakeya.ConvexFactoring.GreedyDensityBucketing
open Submission.Kakeya.Uniformity
open Family8CoreHighPrefixFiberLogBucketFineShadingV1
open Family8EndpointIdentityExactSameCoreHighPayloadFiberLogReselectionV1
open Family8EndpointIdentityTauActiveParentAdmissibilityV1
open Family8EndpointIdentityTauActiveSameCoreOccurrenceWeightedCordobaMassStrengthenedV1
open Family8EndpointLongCoreIdentityFirstFieldsV3
open Family8EndpointLongCoreTauActiveSourceMassIdentityV1
open Family8FullRefinementActualDatumV1
open Family8GeneralizedKatzTaoMultiplicityV1
open Family8GreedyHighOccurrenceSelectedParentJohnPlankConnectorV1
open Family8KatzTaoFrostmanPropertiesV1
open Family8NormalizedLongCoreCanonicalTauCoarseDatumV2
open Family8NormalizedLongIntervalCoreConsumerV1
open Family8ParameterLadderV1
open Family8SelectedOccurrenceDensityFrostmanV1
open Family8SelectedOccurrenceWinnerSideLocalBlockPositiveCarrierPaymentV1
open Family8StickySelectedParentGreedyBlockFrostmanV3
open Family8TauActiveParentGreedyLowCallbackOrSameOccurrenceWeightedCordobaCoreV1
open Family8TauActiveParentGreedyRetainedHighPrefixSplitV1
open FamilyStickyAtEveryScaleCoreV1
open FamilyStickyDividingScalesFiniteStoppingV1
open FamilyStickyHierarchyEndpointPrefixShadingTransportV1.StickyScaleCover
open FamilyStickyScaleChainCappedSeedSequenceV2
open FamilyStickyScaleChainCoherentIntervalProducerV1
open FamilyStickyScaleChainSelectedCanonicalCoverCoordinatesProducerV1

noncomputable section

local instance (p : Prop) : Decidable p := Classical.propDecidable p

variable {delta : NNReal} {index : Type}
  [Fintype index] [DecidableEq index]
  {epsilon0 beta gamma : Real}

/-- Endpoint-shaped bundle after the corrected selector order.  The first
eight fields are the whole fibre-log bucket invariants; the final named
payment transparently contains the retained outer-side set, its source
mass/average payment, the later same-q count, and the Córdoba/cross fields. -/
def EndpointIdentityFiberLogFirstWinnerSideSameQPaymentAt
    (D : ActualTubeDatum delta index) (hD : D.IsAdmissible)
    (L : ParameterLadder epsilon0 beta gamma)
    (W : NormalizedLongIntervalCoreWitness
      (fullRefinementDatum D).family
      (identityRadiusCoherentCover (fullRefinementDatum D).family)
      L.N L.epsilon L.eta
      (endpointScaleSequence delta
        (hD.delta_le_half.trans (by norm_num))))
    (A : ENNReal) (rFrozen : Real) (r : NNReal) (hr : 0 < r) : Prop :=
  let E := fullRefinementDatum D
  let C := identityRadiusCoherentCover E.family
  let S := endpointScaleSequence delta
    (hD.delta_le_half.trans (by norm_num))
  let T := tauScaleCover E C S W
  let Dtau := activeParentActualTubeDatum T E.shading
  let hrho : 0 < S.tau W.m :=
    hD.delta_pos.trans_le (S.delta_le_tau W.m)
  exists P : GreedyDensityPartition Dtau.family.bodyFamily
      (hullCandidates (Finset.univ : Finset (ActiveParentIndex T)))
      (hullContainer Dtau.family.bodyFamily) Finset.univ,
    exists selected : Finset (ActiveParentIndex T),
      exists hcover : (forall i, i ∈ selected ->
        exists q : Fin (blocks Dtau.family.bodyFamily P).length,
          i ∈ (blockAt Dtau.family.bodyFamily P q).fiber /\
            CoreHighConcentrationOccurrence Dtau P A q),
        exists b : Fin (Nat.log 2 (Fintype.card (ActiveParentIndex T)) + 1),
          let R := coreHighFiberLogOccurrenceBucket
            Dtau P A selected hcover b
          let fineBucket := coreHighFiberLogFineBucket
            Dtau P A selected hcover b
          let Ybucket := coreHighFiberLogFineShading
            Dtau P A selected hcover b
          R.Nonempty /\
          R ⊆ occupiedCoreHighOccurrences Dtau P A selected hcover /\
          fineBucket ⊆ selectedOccurrenceFineIndices P R /\
          (forall q, q ∈ R -> CoreHighConcentrationOccurrence Dtau P A q) /\
          (forall q, q ∈ R -> forall k, k ∈ R ->
            (((blockAt Dtau.family.bodyFamily P q).fiber.card : Nat) :
                ENNReal) <=
              2 * (((blockAt Dtau.family.bodyFamily P k).fiber.card : Nat) :
                ENNReal)) /\
          (forall q, q ∈ R ->
            R.card * (blockAt Dtau.family.bodyFamily P q).fiber.card <=
              2 * Fintype.card (ActiveParentIndex T)) /\
          Dtau.shading.shadingMass <=
            (((2 * (Nat.log 2 (Fintype.card (ActiveParentIndex T)) + 1) :
                Nat) : ENNReal) * Ybucket.shadingMass) /\
          Dtau.shading.averageMultiplicity <=
            (((2 * (Nat.log 2 (Fintype.card (ActiveParentIndex T)) + 1) :
                Nat) : ENNReal) * Ybucket.averageMultiplicity) /\
          WinnerSideLocalBlockPositiveCarrierPaymentConclusion
            E T P R Dtau.shading fineBucket rFrozen hrho r hr

/-- Build the endpoint-shaped corrected-selector bundle from the historical
exact-high payload.  Its old occurrence and side label are not reused. -/
theorem endpointIdentity_fiberLogFirst_winnerSide_sameQ_payment_of_exactSameCoreHighPayload
    (D : ActualTubeDatum delta index) (hD : D.IsAdmissible)
    (L : ParameterLadder epsilon0 beta gamma)
    (W : NormalizedLongIntervalCoreWitness
      (fullRefinementDatum D).family
      (identityRadiusCoherentCover (fullRefinementDatum D).family)
      L.N L.epsilon L.eta
      (endpointScaleSequence delta
        (hD.delta_le_half.trans (by norm_num))))
    (A : ENNReal) (rFrozen : Real) (hrFrozen : 0 < rFrozen)
    (r : NNReal) (hr : 0 < r) (KT : ENNReal)
    (hsource0 : D.shading.shadingMass ≠ 0)
    (hHigh :
      EndpointIdentitySameCoreOccurrenceWeightedCordobaMassStrengthenedConclusion
        D hD L W A False r hr KT) :
    EndpointIdentityFiberLogFirstWinnerSideSameQPaymentAt
      D hD L W A rFrozen r hr := by
  classical
  let E := fullRefinementDatum D
  let C := identityRadiusCoherentCover E.family
  let S := endpointScaleSequence delta
    (hD.delta_le_half.trans (by norm_num))
  let T := tauScaleCover E C S W
  let Dtau := activeParentActualTubeDatum T E.shading
  let hrho : 0 < S.tau W.m :=
    hD.delta_pos.trans_le (S.delta_le_tau W.m)
  have hmassEq : Dtau.shading.shadingMass = D.shading.shadingMass := by
    change (tauActiveCoarseDatum E C S W).shading.shadingMass =
      D.shading.shadingMass
    simpa only [E, C, S] using
      (endpointLongCore_tauActive_shadingMass_eq_source D hD L W)
  have hDtau0 : Dtau.shading.shadingMass ≠ 0 := by
    rw [hmassEq]
    exact hsource0
  have hbucket : CoreHighPrefixFiberLogBucketFineShadingPayload Dtau A := by
    simpa only [E, C, S, T, Dtau] using
      (fiberLogBucketFineShadingPayload_of_endpointIdentity_exactSameCoreHighPayload
        D hD L W A r hr KT hsource0 hHigh)
  obtain ⟨P, selected, hcover, b, hRnonempty, hRsubset,
      hfineBucket, hcore, huniform, hcount, hmass, havg⟩ := hbucket
  let R := coreHighFiberLogOccurrenceBucket Dtau P A selected hcover b
  let fineBucket := coreHighFiberLogFineBucket Dtau P A selected hcover b
  let Ybucket := coreHighFiberLogFineShading Dtau P A selected hcover b
  have hYbucket0 : Ybucket.shadingMass ≠ 0 := by
    intro hzero
    rw [hzero, mul_zero] at hmass
    exact hDtau0 (bot_unique hmass)
  have hParent : Dtau.IsAdmissible := by
    simpa only [E, C, S, T, Dtau] using
      (endpointIdentity_tauActiveParent_isAdmissible D hD L W)
  have htau : S.tau W.m = delta :=
    endpointLongCore_tau_eq_delta
      (hD.delta_le_half.trans (by norm_num)) C W
  have hrhoOne : S.tau W.m <= 1 := by
    rw [htau]
    exact hD.delta_le_half.trans (by norm_num)
  have hrhoHalf : S.tau W.m <= (2 : NNReal)⁻¹ := by
    rw [htau]
    exact hD.delta_le_half
  have hwinner : WinnerSideLocalBlockPositiveCarrierPaymentConclusion
      E T P R Dtau.shading fineBucket rFrozen hrho r hr := by
    apply exists_winnerSide_sameQ_localBlockPositiveCarrierPayment
      E (fullRefinementDatum_isAdmissible hD) T hParent
      hrho hrhoOne hrhoHalf P R Dtau.shading fineBucket
        (by
          change fineBucket ⊆ selectedOccurrenceFineIndices P R
          exact hfineBucket)
        (by
          change Ybucket.shadingMass ≠ 0
          exact hYbucket0)
        (by
          intro q hq k hk
          change (((blockAt Dtau.family.bodyFamily P q).fiber.card : Nat) :
              ENNReal) <=
            2 * (((blockAt Dtau.family.bodyFamily P k).fiber.card : Nat) :
              ENNReal)
          exact huniform q hq k hk)
        rFrozen hrFrozen r hr
  unfold EndpointIdentityFiberLogFirstWinnerSideSameQPaymentAt
  dsimp only
  refine ⟨P, selected, hcover, b, ?_⟩
  exact ⟨hRnonempty, hRsubset, hfineBucket, hcore, huniform, hcount,
    hmass, havg, hwinner⟩

#print axioms EndpointIdentityFiberLogFirstWinnerSideSameQPaymentAt
#print axioms
  endpointIdentity_fiberLogFirst_winnerSide_sameQ_payment_of_exactSameCoreHighPayload

end
end Family8EndpointIdentityExactSameCoreHighPayloadWinnerSideSameQPaymentV1
