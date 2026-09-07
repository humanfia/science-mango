import Family8Grounding.Family8EndpointLongCoreIdentityFirstFieldsV3
import Family8Grounding.Family8EndpointLongCoreSourceTauIdentityTransportV5
import Family8Grounding.Family8EndpointLongCoreTauActiveSourceScalarBoundTransportV1
import Family8Grounding.Family8EndpointLongCoreTauActiveSourceMassIdentityV1
import Family8Grounding.Family8EndpointIdentityTauActiveSameCoreOccurrenceWeightedCordobaMassStrengthenedPayloadV1
import Family8Grounding.Family8TauActiveParentGreedyLowCallbackOrSameOccurrenceWeightedCordobaCoreV1
import Mathlib.Tactic

/-!
# Endpoint same-core weighted Cordoba split with source mass and average

The endpoint identity cover preserves both shading mass and average
multiplicity.  This thin adapter rewrites the admissibility-free same-core
split at those two scalars only.  In particular, the high branch keeps the
literal greedy partition, selected prefix, raw occurrence `q`, block, and
zero-extended shading produced by the core theorem.

The low branch is deliberately a local callback.  Its only geometric input
is the actual factor-two restriction and its Katz--Tao certificate.  No
source Katz--Tao hypothesis, first cap, or tau-parent admissibility occurs in
the interface.
-/

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 9000000

open Set MeasureTheory
open scoped BigOperators ENNReal NNReal

namespace Family8EndpointIdentityTauActiveSameCoreOccurrenceWeightedCordobaMassStrengthenedV1

open LeanEval.Analysis.WangZahlKakeya
open Submission.Kakeya.ConvexGeometry
open Submission.Kakeya.ConvexFactoring
open Submission.Kakeya.ConvexFactoring.FullConvexMaximalDensity
open Submission.Kakeya.ConvexFactoring.GreedyOccurrenceFactorization
open Submission.Kakeya.ConvexFactoring.GreedyDensityBucketing
open Submission.Kakeya.Uniformity
open Family6AffineConvexVolumeCoreV1
open Family8CertifiedPlankDyadicCordobaV2
open Family8EndpointLongCoreSourceTauIdentityTransportV5
open Family8EndpointLongCoreTauActiveSourceScalarBoundTransportV1
open Family8EndpointLongCoreTauActiveSourceMassIdentityV1
open Family8FullRefinementActualDatumV1
open Family8GeneralizedKatzTaoMultiplicityV1
open Family8GreedyHighOccurrenceSelectedParentJohnPlankConnectorV1
open Family8KatzTaoFrostmanPropertiesV1
open Family8NormalizedLongCoreCanonicalTauCoarseDatumV2
open Family8NormalizedLongIntervalCoreConsumerV1
open Family8ParameterLadderV1
open Family8PositiveCarrierShadingRestrictionV4
open Family8QuantitativeCarrierPopularityRestrictionV3
open Family8SelectedParentAffineShadingTransportV4
open Family8SelectedParentArbitraryBlockPlankBucketV4
open Family8SelectedParentCertifiedPlankCordobaConnectorV3
open Family8SelectedParentCertifiedPlankCordobaThresholdedAngleV6
open Family8SelectedParentJohnFrameNormalizationV9
open Family8SelectedParentJohnPlankQuantitativeLossV9
open Family8SelectedParentJohnPlankSideWidthBridgeV4
open Family8SelectedParentJohnPlankSideWidthBridgeV5
open Family8SelectedParentJohnPlankSideWidthBridgeV7
open Family8SelectedParentJohnPlankSideWidthBridgeV8
open Family8StickySelectedParentGreedyBlockFrostmanV3
open Family8TauActiveParentGreedyLowCallbackOrSameOccurrenceWeightedCordobaCoreV1
open Family8TauActiveParentSameOccurrenceWeightedCordobaScalarEnvelopeV1
open FamilyStickyAtEveryScaleCoreV1
open FamilyStickyCinematicL32FiniteWeightedBucketV1
open FamilyStickyDividingScalesFiniteStoppingV1
open FamilyStickyHierarchyEndpointPrefixShadingTransportV1.StickyScaleCover
open FamilyStickyScaleChainCappedSeedSequenceV2
open FamilyStickyScaleChainCoherentIntervalProducerV1
open FamilyStickyScaleChainSelectedCanonicalCoverCoordinatesProducerV1

noncomputable section

variable {delta : NNReal} {index : Type}
  [Fintype index] [DecidableEq index]
  {epsilon0 beta gamma : Real}

/-- Endpoint identity adapter for the raw mass-strengthened split.  The
source-mass premise is transported to the tau parent by exact identity, and
the same identities rewrite the two public high-branch bounds. -/
theorem exists_endpointIdentity_source_lowCallback_or_sameCoreOccurrenceWeightedCordoba_massStrengthened
    (D : ActualTubeDatum delta index) (hD : D.IsAdmissible)
    (L : ParameterLadder epsilon0 beta gamma)
    (W : NormalizedLongIntervalCoreWitness
      (fullRefinementDatum D).family
      (identityRadiusCoherentCover (fullRefinementDatum D).family)
      L.N L.epsilon L.eta
      (endpointScaleSequence delta
        (hD.delta_le_half.trans (by norm_num))))
    (A : ENNReal)
    (lowResult : Prop)
    (closeLow : forall selected : Finset
        (ActiveParentIndex (tauScaleCover
          (fullRefinementDatum D)
          (identityRadiusCoherentCover (fullRefinementDatum D).family)
          (endpointScaleSequence delta
            (hD.delta_le_half.trans (by norm_num))) W)),
      D.shading.shadingMass <=
        2 * (restrictActualTubeDatum
          (activeParentActualTubeDatum
            (tauScaleCover
              (fullRefinementDatum D)
              (identityRadiusCoherentCover (fullRefinementDatum D).family)
              (endpointScaleSequence delta
                (hD.delta_le_half.trans (by norm_num))) W)
            (fullRefinementDatum D).shading)
          selected).shading.shadingMass ->
      IsKatzTao A
        (restrictActualTubeDatum
          (activeParentActualTubeDatum
            (tauScaleCover
              (fullRefinementDatum D)
              (identityRadiusCoherentCover (fullRefinementDatum D).family)
              (endpointScaleSequence delta
                (hD.delta_le_half.trans (by norm_num))) W)
            (fullRefinementDatum D).shading)
          selected).family.bodyFamily ->
      lowResult)
    (hsourceMass : D.shading.shadingMass ≠ 0)
    (r : NNReal) (hr : 0 < r)
    (KT : ENNReal)
    (hKT : IsKatzTao KT
      (tauScaleCover
        (fullRefinementDatum D)
        (identityRadiusCoherentCover (fullRefinementDatum D).family)
        (endpointScaleSequence delta
          (hD.delta_le_half.trans (by norm_num))) W).activeCoarseFamily) :
    EndpointIdentitySameCoreOccurrenceWeightedCordobaMassStrengthenedConclusion
      D hD L W A lowResult r hr KT := by
  let E := fullRefinementDatum D
  let hE : E.IsAdmissible := fullRefinementDatum_isAdmissible hD
  let C := identityRadiusCoherentCover E.family
  let S := endpointScaleSequence delta
    (hD.delta_le_half.trans (by norm_num))
  let T := tauScaleCover E C S W
  let Dtau := activeParentActualTubeDatum T E.shading
  have htau : S.tau W.m = delta :=
    Family8EndpointLongCoreIdentityFirstFieldsV3.endpointLongCore_tau_eq_delta
      (hD.delta_le_half.trans (by norm_num)) C W
  have htauHalf : S.tau W.m <= (2 : NNReal)⁻¹ := by
    rw [htau]
    exact hD.delta_le_half
  have hMassEq : Dtau.shading.shadingMass = D.shading.shadingMass := by
    change (tauActiveCoarseDatum E C S W).shading.shadingMass =
      D.shading.shadingMass
    simpa only [E, C, S] using
      (endpointLongCore_tauActive_shadingMass_eq_source D hD L W)
  have hparentMass : Dtau.shading.shadingMass ≠ 0 := by
    intro hz
    exact hsourceMass (hMassEq.symm.trans hz)
  have closeLowTau : forall selected : Finset {k // k ∈ T.activeCoarse},
      Dtau.shading.shadingMass <=
        2 * (restrictActualTubeDatum Dtau selected).shading.shadingMass ->
      IsKatzTao A
        (restrictActualTubeDatum Dtau selected).family.bodyFamily ->
      lowResult := by
    intro selected hmass hlocalKT
    apply closeLow selected
    · exact hMassEq.symm.le.trans hmass
    · exact hlocalKT
  have hsplit :=
    exists_factorTwo_lowKatzTaoRestriction_or_coreHighOccurrencePrefix
      Dtau A
  rcases hsplit with hlow | hhigh
  · obtain ⟨selected, hfirst, hlocalKT⟩ := hlow
    exact Or.inl (closeLowTau selected hfirst hlocalKT)
  · obtain ⟨P, selected, hfirst, hcover⟩ := hhigh
    have hselection :=
      exists_sameCoreOccurrenceBlockShading_weighted_retention_of_source_ne_zero
        Dtau P A selected hcover 2 hfirst hparentMass
    obtain ⟨q, hq, hqcore, hselectedMass, hparentMassBound,
      hparentAverage⟩ := hselection
    let Z := sameCoreOccurrenceBlockShading Dtau P A selected hcover q
    let hrho : 0 < S.tau W.m :=
      hD.delta_pos.trans_le (S.delta_le_tau W.m)
    have hrhoOne : S.tau W.m <= 1 :=
      htauHalf.trans (by norm_num)
    have hcordoba :=
      exists_selectedParentArbitraryPlankBucket_massRetention_and_averageMultiplicity_le_of_fine_admissible
        E hE T hrho hrhoOne P q r hr Z KT hKT
    dsimp only at hcordoba
    obtain ⟨label, hoccupied, ha, hab, hb, hplank, hretained,
      hbound⟩ := hcordoba
    have hZMassNe : Z.shadingMass ≠ 0 := by
      intro hzero
      have hle := hparentMassBound
      rw [hzero, mul_zero] at hle
      exact hparentMass (bot_unique hle)
    have hbucket0 :=
      bucket_ne_zero_of_nonzero_source_and_retention
        (affineJacobian_pos
          (bucketNormalizedAffineEquiv
            (contractedJohnAffineEquiv
              (selectedParentGreedyBlockJohnFrame T hrho P q) r hr)
            label)).ne'
        hZMassNe hretained
    have hparentAverage' :=
      hparentAverage.trans (mul_le_mul' le_rfl hbound)
    have hsourceFirst : D.shading.shadingMass <=
        2 * (restrictActualTubeDatum Dtau selected).shading.shadingMass :=
      hMassEq.symm.le.trans hfirst
    have hsourceMassBound :=
      endpointLongCore_source_shadingMass_le_of_tauActive
        D hD L W (by
          change Dtau.shading.shadingMass <= _
          exact hparentMassBound)
    have hsourceAverage :=
      endpointLongCore_source_averageMultiplicity_le_of_tauActive
        D hD L W (by
          change Dtau.shading.averageMultiplicity <= _
          exact hparentAverage')
    dsimp only
      [EndpointIdentitySameCoreOccurrenceWeightedCordobaMassStrengthenedConclusion]
    refine Or.inr ⟨P, selected, hsourceFirst, hcover, q, hq, hqcore,
      hselectedMass, hsourceMassBound, label, hoccupied, ha, hab, hb,
      hplank, hretained, hbucket0, ?_⟩
    dsimp only [E, C, S, T, Dtau, Z, hrho] at hsourceAverage ⊢
    convert hsourceAverage using 1
    congr 1

#print axioms
  EndpointIdentitySameCoreOccurrenceWeightedCordobaMassStrengthenedConclusion
#print axioms
  exists_endpointIdentity_source_lowCallback_or_sameCoreOccurrenceWeightedCordoba_massStrengthened

end
end Family8EndpointIdentityTauActiveSameCoreOccurrenceWeightedCordobaMassStrengthenedV1
