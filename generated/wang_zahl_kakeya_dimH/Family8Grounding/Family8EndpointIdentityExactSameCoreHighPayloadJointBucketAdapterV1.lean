import Family8Grounding.Family8EndpointIdentityCorrelatedSameCoreHighCloserDatumAdapterV1
import Family8Grounding.Family8CoreHighOccupiedDensityBandCoverageV1
import Family8Grounding.Family8EndpointLongCoreTauActiveSourceMassIdentityV1
import Family8Grounding.Family8EndpointIdentityTauActiveParentAdmissibilityV1
import Family8Grounding.Family8SelectedOccurrenceWinnerSideLocalBlockPositiveCarrierPaymentV1
import Mathlib.Tactic

/-!
# Re-bucket the exact endpoint high payload without changing its core

The endpoint high payload remembers a particular occupied occurrence and a
later side-shape label.  Neither witness occurs in the type of the endpoint
payment.  This file records the safe re-bucketing step: discard only those
two downstream choices, retain the literal greedy partition, selected prefix,
first-hit mass estimate, and pointwise high-occurrence cover, and choose a
joint fibre-cardinality/density bucket from that same prefix.

Thus the new occurrence bucket is not a replacement of the endpoint core.
It is a refinement of the already fixed `P`/`selected`/`hcover` data.
-/

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 5000000

open Set MeasureTheory
open scoped BigOperators ENNReal NNReal

namespace Family8EndpointIdentityExactSameCoreHighPayloadJointBucketAdapterV1

open LeanEval.Analysis.WangZahlKakeya
open Submission.Kakeya.ConvexFactoring
open Submission.Kakeya.ConvexFactoring.FullConvexMaximalDensity
open Submission.Kakeya.ConvexFactoring.GreedyOccurrenceFactorization
open Submission.Kakeya.ConvexFactoring.GreedyDensityBucketing
open Submission.Kakeya.Uniformity
open Family8CoreHighOccupiedDensityBandCoverageV1
open Family8CoreHighPrefixFiberDensityBucketFineShadingV1
open Family8EndpointIdentityCorrelatedSameCoreHighCloserDatumAdapterV1
open Family8EndpointIdentityTauActiveSameCoreOccurrenceWeightedCordobaMassStrengthenedV1
open Family8EndpointIdentityTauActiveParentAdmissibilityV1
open Family8EndpointLongCoreIdentityFirstFieldsV3
open Family8EndpointLongCoreTauActiveSourceMassIdentityV1
open Family8FullRefinementActualDatumV1
open Family8GeneralizedKatzTaoMultiplicityV1
open Family8GreedyHighOccurrenceSelectedParentJohnPlankConnectorV1
open Family8KatzTaoFrostmanPropertiesV1
open Family8NormalizedLongCoreCanonicalTauCoarseDatumV2
open Family8NormalizedLongIntervalCoreConsumerV1
open Family8ParameterLadderV1
open Family8Prop51JointOccurrenceWeightedSelectionV1
open Family8SelectedOccurrenceDensityFrostmanV1
open Family8SelectedOccurrenceWinnerSideLocalBlockPositiveCarrierPaymentV1
open Family8TauActiveParentGreedyRetainedHighPrefixSplitV1
open Family8TauActiveParentGreedyLowCallbackOrSameOccurrenceWeightedCordobaCoreV1
open Family8StickySelectedParentGreedyBlockFrostmanV3
open FamilyStickyAtEveryScaleCoreV1
open FamilyStickyDividingScalesFiniteStoppingV1
open FamilyStickyHierarchyEndpointPrefixShadingTransportV1.StickyScaleCover
open FamilyStickyScaleChainCappedSeedSequenceV2
open FamilyStickyScaleChainCoherentIntervalProducerV1
open FamilyStickyScaleChainSelectedCanonicalCoverCoordinatesProducerV1

noncomputable section

variable {delta : NNReal} {index : Type}
  [Fintype index] [DecidableEq index]
  {epsilon0 beta gamma : Real}

/-- Forget the old occurrence and side label in the exact endpoint high
payload, then jointly bucket fibre cardinality and block density inside the
same greedy partition, selected prefix, and high-occurrence cover.

The two scalar premises are automatic at the intended endpoint application:
`A` is the negative power of a scale at most one, and nonzero source mass is
available from the Frostman input.  They are kept explicit here so this
adapter performs no hidden analytic strengthening. -/
theorem jointBucketFineShadingPayload_of_endpointIdentity_exactSameCoreHighPayload
    (D : ActualTubeDatum delta index) (hD : D.IsAdmissible)
    (L : ParameterLadder epsilon0 beta gamma)
    (W : NormalizedLongIntervalCoreWitness
      (fullRefinementDatum D).family
      (identityRadiusCoherentCover (fullRefinementDatum D).family)
      L.N L.epsilon L.eta
      (endpointScaleSequence delta
        (hD.delta_le_half.trans (by norm_num))))
    (A : ENNReal) (r : NNReal) (hr : 0 < r) (KT : ENNReal)
    (hA : 1 <= A)
    (hsource0 : D.shading.shadingMass ≠ 0)
    (hHigh : EndpointIdentityExactSameCoreHighPayloadAt
      D hD L W A r hr KT) :
    let E := fullRefinementDatum D
    let C := identityRadiusCoherentCover E.family
    let S := endpointScaleSequence delta
      (hD.delta_le_half.trans (by norm_num))
    let T := tauScaleCover E C S W
    let Dtau := activeParentActualTubeDatum T E.shading
    CoreHighPrefixFiberDensityBucketFineShadingPayload
      Dtau A A (Nat.log 2 (Fintype.card (ActiveParentIndex T))) := by
  let E := fullRefinementDatum D
  let C := identityRadiusCoherentCover E.family
  let S := endpointScaleSequence delta
    (hD.delta_le_half.trans (by norm_num))
  let T := tauScaleCover E C S W
  let Dtau := activeParentActualTubeDatum T E.shading
  have hrho : 0 < S.tau W.m :=
    hD.delta_pos.trans_le (S.delta_le_tau W.m)
  dsimp only
    [EndpointIdentityExactSameCoreHighPayloadAt,
      EndpointIdentitySameCoreOccurrenceWeightedCordobaMassStrengthenedConclusion]
      at hHigh
  rcases hHigh with hfalse | hpayload
  · exact False.elim hfalse
  · obtain ⟨P, selected, hfirst, hcover, _q, _hqOccupied,
        _hqHigh, _payloadAtQ⟩ := hpayload
    have hmassEq : Dtau.shading.shadingMass = D.shading.shadingMass := by
      change (tauActiveCoarseDatum E C S W).shading.shadingMass =
        D.shading.shadingMass
      simpa only [E, C, S] using
        (endpointLongCore_tauActive_shadingMass_eq_source D hD L W)
    have hDtau0 : Dtau.shading.shadingMass ≠ 0 := by
      rw [hmassEq]
      exact hsource0
    have hfirstDtau : Dtau.shading.shadingMass <=
        2 * (restrictActualTubeDatum Dtau selected).shading.shadingMass := by
      rw [hmassEq]
      exact hfirst
    have hprefix : CoreHighPrefixWithFirstHitMass Dtau A := by
      exact ⟨P, selected, hfirstDtau, hcover⟩
    have hcovered : CoreHighPrefixWithFirstHitMassDensityCovered
        Dtau A A (Nat.log 2 (Fintype.card (ActiveParentIndex T))) := by
      simpa only [Dtau] using
        (activeParent_coreHighPrefixWithFirstHitMass_to_densityCovered
          T E.shading hrho A hA hprefix)
    exact
      coreHighPrefixWithFirstHitMassDensityCovered_to_fiberDensityBucketFineShadingPayload
        Dtau A A (Nat.log 2 (Fintype.card (ActiveParentIndex T)))
          hDtau0 hcovered

/-- Endpoint-shaped output of the corrected joint-label-first order.

Besides the full joint fibre/density bucket invariants, this contains the
automatically selected outer winner-side label and the local frozen same-`q`
positive-carrier payment.  The latter selects its inner label only after its
literal occurrence `q`; hence all count and density facts still refer to the
same original bucket. -/
def EndpointIdentityJointDensityFirstWinnerSideSameQPaymentAt
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
  let M := Nat.log 2 (Fintype.card (ActiveParentIndex T))
  exists P : GreedyDensityPartition Dtau.family.bodyFamily
      (hullCandidates (Finset.univ : Finset (ActiveParentIndex T)))
      (hullContainer Dtau.family.bodyFamily) Finset.univ,
    exists selected : Finset (ActiveParentIndex T),
      exists hcover : (forall i, i ∈ selected ->
        exists q : Fin (blocks Dtau.family.bodyFamily P).length,
          i ∈ (blockAt Dtau.family.bodyFamily P q).fiber /\
            CoreHighConcentrationOccurrence Dtau P A q),
        exists b : Fin (Nat.log 2 (Fintype.card (ActiveParentIndex T)) + 1) ×
            Fin (M + 1),
          let R := coreHighFiberDensityOccurrenceBucket
            Dtau P A A M selected hcover b
          let fineBucket := coreHighFiberDensityFineBucket
            Dtau P A A M selected hcover b
          let Ybucket := coreHighFiberDensityFineShading
            Dtau P A A M selected hcover b
          R.Nonempty /\
          R ⊆ occupiedCoreHighOccurrences Dtau P A selected hcover /\
          fineBucket ⊆ selectedOccurrenceFineIndices P R /\
          (forall q, q ∈ R -> CoreHighConcentrationOccurrence Dtau P A q) /\
          (forall q, q ∈ R ->
            InENNRealDyadicBand A b.2.1
              (blockDensity Dtau.family.bodyFamily
                (blockAt Dtau.family.bodyFamily P q))) /\
          (forall q, q ∈ R -> forall k, k ∈ R ->
            ((((blockAt Dtau.family.bodyFamily P q).fiber.card : Nat) :
                ENNReal) <=
                2 * (((blockAt Dtau.family.bodyFamily P k).fiber.card : Nat) :
                  ENNReal) /\
              blockDensity Dtau.family.bodyFamily
                  (blockAt Dtau.family.bodyFamily P q) <=
                2 * blockDensity Dtau.family.bodyFamily
                  (blockAt Dtau.family.bodyFamily P k))) /\
          Dtau.shading.shadingMass <=
            (((2 * prop51JointOccurrenceLoss (ActiveParentIndex T) M : Nat) :
                ENNReal) * Ybucket.shadingMass) /\
          Dtau.shading.averageMultiplicity <=
            (((2 * prop51JointOccurrenceLoss (ActiveParentIndex T) M : Nat) :
                ENNReal) * Ybucket.averageMultiplicity) /\
          WinnerSideLocalBlockPositiveCarrierPaymentConclusion
            E T P R Dtau.shading fineBucket rFrozen hrho r hr

/-- From the exact endpoint high payload, run the corrected joint-density
bucket first and then the already-grounded winner-side/same-`q` producer.
All geometric choices through the inner positive-carrier payload are thereby
automatic; only the later outer Proposition-6.6/Eq.-(32) estimate and scalar
loss payment remain outside this theorem. -/
theorem endpointIdentity_jointDensityFirst_winnerSide_sameQ_payment_of_exactSameCoreHighPayload
    (D : ActualTubeDatum delta index) (hD : D.IsAdmissible)
    (L : ParameterLadder epsilon0 beta gamma)
    (W : NormalizedLongIntervalCoreWitness
      (fullRefinementDatum D).family
      (identityRadiusCoherentCover (fullRefinementDatum D).family)
      L.N L.epsilon L.eta
      (endpointScaleSequence delta
        (hD.delta_le_half.trans (by norm_num))))
    (A : ENNReal) (hA : 1 <= A)
    (rFrozen : Real) (hrFrozen : 0 < rFrozen)
    (r : NNReal) (hr : 0 < r) (KT : ENNReal)
    (hsource0 : D.shading.shadingMass ≠ 0)
    (hHigh : EndpointIdentityExactSameCoreHighPayloadAt
      D hD L W A r hr KT) :
    EndpointIdentityJointDensityFirstWinnerSideSameQPaymentAt
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
  let M := Nat.log 2 (Fintype.card (ActiveParentIndex T))
  have hmassEq : Dtau.shading.shadingMass = D.shading.shadingMass := by
    change (tauActiveCoarseDatum E C S W).shading.shadingMass =
      D.shading.shadingMass
    simpa only [E, C, S] using
      (endpointLongCore_tauActive_shadingMass_eq_source D hD L W)
  have hDtau0 : Dtau.shading.shadingMass ≠ 0 := by
    rw [hmassEq]
    exact hsource0
  have hbucket : CoreHighPrefixFiberDensityBucketFineShadingPayload
      Dtau A A M := by
    simpa only [E, C, S, T, Dtau, M] using
      (jointBucketFineShadingPayload_of_endpointIdentity_exactSameCoreHighPayload
        D hD L W A r hr KT hA hsource0 hHigh)
  obtain ⟨P, selected, hcover, b, hRnonempty, hRsubset,
      hfineBucket, hcore, hband, hcomparable, hmass, havg⟩ := hbucket
  let R := coreHighFiberDensityOccurrenceBucket
    Dtau P A A M selected hcover b
  let fineBucket := coreHighFiberDensityFineBucket
    Dtau P A A M selected hcover b
  let Ybucket := coreHighFiberDensityFineShading
    Dtau P A A M selected hcover b
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
  have hfineBucket' : fineBucket ⊆ selectedOccurrenceFineIndices P R := by
    exact hfineBucket
  have hYbucketRestrict0 :
      (IndexedShadingRefinement.restrictTo Dtau.shading
        fineBucket).shading.shadingMass ≠ 0 := by
    change Ybucket.shadingMass ≠ 0
    exact hYbucket0
  have hwinner : WinnerSideLocalBlockPositiveCarrierPaymentConclusion
      E T P R Dtau.shading fineBucket rFrozen hrho r hr := by
    apply exists_winnerSide_sameQ_localBlockPositiveCarrierPayment
      E (fullRefinementDatum_isAdmissible hD) T hParent
      hrho hrhoOne hrhoHalf P R Dtau.shading fineBucket
        hfineBucket' hYbucketRestrict0
        (fun q hq k hk => (hcomparable q hq k hk).1)
        rFrozen hrFrozen r hr
  unfold EndpointIdentityJointDensityFirstWinnerSideSameQPaymentAt
  dsimp only
  refine ⟨P, selected, hcover, b, ?_⟩
  exact ⟨hRnonempty, hRsubset, hfineBucket, hcore, hband,
    hcomparable, hmass, havg, hwinner⟩

#print axioms
  jointBucketFineShadingPayload_of_endpointIdentity_exactSameCoreHighPayload
#print axioms EndpointIdentityJointDensityFirstWinnerSideSameQPaymentAt
#print axioms
  endpointIdentity_jointDensityFirst_winnerSide_sameQ_payment_of_exactSameCoreHighPayload

end
end Family8EndpointIdentityExactSameCoreHighPayloadJointBucketAdapterV1
