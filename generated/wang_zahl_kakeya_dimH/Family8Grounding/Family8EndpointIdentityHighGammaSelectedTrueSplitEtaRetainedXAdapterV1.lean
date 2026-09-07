import Family8Grounding.Family8EndpointIdentityHighGammaSelectedTrueSplitEtaAutomaticAdapterV4
import Family8Grounding.Family8EndpointIdentityAutomaticRefinedCardRetainedWitnessProducerV1
import Family8Grounding.Family8LocalCardRetainedSelectedTrueSplitEtaXPowerAdapterV1
import Mathlib.Tactic

/-!
# Retained local card input for the automatic selected high-gamma endpoint

The automatic high-gamma endpoint fixes one normalized LongCore witness `W`.
An arbitrary `LocalCardRetainedNormalizedLongCoreWitness` cannot be used here:
its `core` field need not be that `W`, so its canonical restricted cover need
not be the cover consumed by the endpoint.

This module records the pointwise local-card certificate directly at the
automatic witness's literal index.  Its conversion to the generic retained
witness sets `core := W` definitionally.  Thus the local-card X producer and
the endpoint use the same `W`, `m`, and `U`, with no equality transport and no
second selection.
-/

set_option autoImplicit false
set_option warningAsError true
set_option linter.unusedSectionVars false
set_option maxHeartbeats 10000000

open scoped ENNReal NNReal

namespace Family8EndpointIdentityHighGammaSelectedTrueSplitEtaRetainedXAdapterV1

open Submission.Kakeya.Uniformity
open Family8EndpointIdentityAutomaticRefinedCardRetainedWitnessProducerV1
open Family8EndpointIdentityDividingScaleOutputOrchestrationV4
open Family8EndpointIdentityFirstCrossingImpossibleV1
open Family8EndpointIdentityHighGammaAutomaticHLongGeometryAdapterV1
open Family8EndpointIdentityHighGammaParentwiseLongCoreAutomaticV1
open Family8EndpointIdentityHighGammaSelectedTrueSplitEtaAutomaticAdapterV4
open Family8EndpointIdentityHighGammaSelectedTrueSplitEtaXPowerV4
open Family8FullRefinementActualDatumV1
open Family8HighGammaParameterLadderV1
open Family8KatzTaoFrostmanPropertiesV1
open Family8LocalCardRetainedNormalizedLongCoreWitnessV1
open Family8LocalCardRetainedNormalizedLongCoreWitnessV1.LocalCardRetainedNormalizedLongCoreWitness
open Family8LocalCardRetainedSelectedTrueSplitEtaXPowerAdapterV1
open Family8NormalizedLongCoreCanonicalTauCoarseDatumV2
open Family8NormalizedLongIntervalCoreConsumerV1
open Family8ParameterLadderV1
open Family8ParameterSelectedTrueSplitEtaStrongFrostmanLongCoreOnlyMainLemmaV3
open Family8ParentAggregatedShadingActiveCoarseXUpperV3.StickyScaleCover
open Family8RelativeScaleFixedNuEndpointOrchestrationV1
open Family8SectionEightOutputEtaV1
open Family8StickyScaleCoverActiveFineRestrictionV2.ScaleCover
open FamilyStickyDividingScalesFiniteStoppingV1
open FamilyStickyScaleChainCappedSeedSequenceV2
open FamilyStickyScaleChainCoherentIntervalProducerV1
open FamilyStickyScaleChainLocalCardAutomaticBoundsV2
open FamilyStickyScaleChainSelectedCanonicalCoverCoordinatesProducerV1

noncomputable section

variable {delta : NNReal} {index : Type}
  [Fintype index] [DecidableEq index]
  {epsilon0 beta gamma : Real}

/-- A pointwise local-card certificate retained at the literal index of the
one automatic normalized LongCore witness.  It stores no global budget and
does not expose an equality identifying two independently selected cores. -/
structure AutomaticNormalizedLongCoreLocalCardRetainedWitness
    (D : ActualTubeDatum delta index) (hD : D.IsAdmissible)
    (P : ParameterLadder epsilon0 beta gamma)
    (hbeta : 0 < beta) (hgamma : gamma <= 1)
    (hselectorSmall : delta <=
      endpointIdentityFirstCrossingImpossibleThreshold P)
    {outputEta : Real} (hFOutput : FrostmanHypotheses D outputEta) where
  n : Nat
  not_large :
    let W := automaticNormalizedLongCoreWitness
      D hD P hbeta hgamma hselectorSmall hFOutput
    let S := endpointScaleSequence delta
      (hD.delta_le_half.trans (by norm_num))
    Not (S.IsLarge P.epsilon W.m)
  local_card_le :
    let W := automaticNormalizedLongCoreWitness
      D hD P hbeta hgamma hselectorSmall hFOutput
    let E := fullRefinementDatum D
    let C := identityRadiusCoherentCover E.family
    let S := endpointScaleSequence delta
      (hD.delta_le_half.trans (by norm_num))
    adjacentIntervalActiveFineCard C S W.m <= n

namespace AutomaticNormalizedLongCoreLocalCardRetainedWitness

/-- Convert the automatic pointwise certificate to the generic retained
LongCore wrapper.  The `core` field reduces to the endpoint's automatic `W`;
there is no witness equality or index transport. -/
noncomputable def toLocalCardRetained
    {D : ActualTubeDatum delta index} {hD : D.IsAdmissible}
    {P : ParameterLadder epsilon0 beta gamma}
    {hbeta : 0 < beta} {hgamma : gamma <= 1}
    {hselectorSmall : delta <=
      endpointIdentityFirstCrossingImpossibleThreshold P}
    {outputEta : Real} {hFOutput : FrostmanHypotheses D outputEta}
    (R : AutomaticNormalizedLongCoreLocalCardRetainedWitness
      D hD P hbeta hgamma hselectorSmall hFOutput) :
    LocalCardRetainedNormalizedLongCoreWitness
      (fullRefinementDatum D).family
      (identityRadiusCoherentCover (fullRefinementDatum D).family)
      P.N P.epsilon P.eta
      (endpointScaleSequence delta
        (hD.delta_le_half.trans (by norm_num))) :=
  ofCore
    (automaticNormalizedLongCoreWitness
      D hD P hbeta hgamma hselectorSmall hFOutput)
    R.not_large R.n R.local_card_le

end AutomaticNormalizedLongCoreLocalCardRetainedWitness

/-- The selected automatic high-gamma endpoint with its naked same-cover
X-power premise replaced by one retained same-index local-card witness and
the power envelope for that witness's stored natural bound. -/
theorem dividingScaleOutput_of_endpointIdentity_highGamma_selectedTrueSplitEta_automatic_of_retainedLocalCard
    (H : HighGammaParameterLadder epsilon0 beta gamma)
    (hbeta : 0 < beta) (hgamma : gamma <= 1)
    (targetEpsilon etaKT thirdEta : Real) (delta0 : NNReal)
    (hTarget : 0 < targetEpsilon)
    (hThirdEta : 0 < thirdEta)
    (hThirdCap : thirdEta <= H.ladder.eta 0)
    (D : ActualTubeDatum delta index) (hD : D.IsAdmissible)
    (hdeltaRaw : delta <= highGammaSelectedTrueSplitEtaRawDelta0
      H targetEpsilon etaKT thirdEta delta0)
    (hFOutput : FrostmanHypotheses D
      (selectedTrueSplitOutputEta H.ladder thirdEta))
    (hFExact : FrostmanAtParameters gamma
      (sectionEightSourceLoss H.ladder targetEpsilon) thirdEta delta0)
    (R : AutomaticNormalizedLongCoreLocalCardRetainedWitness
      D hD H.ladder hbeta hgamma
        (hdeltaRaw.trans
          (highGammaSelectedTrueSplitEtaRawDelta0_le_selector
            H targetEpsilon etaKT thirdEta delta0))
        hFOutput)
    (hNPower : (R.n : ENNReal) <=
      (delta : ENNReal) ^
        (-selectedTrueSplitCardScaleEta H.ladder thirdEta)) :
    DividingScaleOutput D H.ladder
      (4 * sectionEightSourceLoss H.ladder targetEpsilon) := by
  have hXPower : selectedTrueSplitEtaXPowerAtRaw
      H hbeta hgamma targetEpsilon etaKT thirdEta delta0
        D hD hdeltaRaw hFOutput := by
    simp only [selectedTrueSplitEtaXPowerAtRaw]
    convert
      canonicalBufferedTauActiveRestricted_activeCoarseCardScaleMass_le_delta_negativePower_of_retained
        (fullRefinementDatum D) (fullRefinementDatum_isAdmissible hD)
        (identityRadiusCoherentCover (fullRefinementDatum D).family)
        (endpointScaleSequence delta
          (hD.delta_le_half.trans (by norm_num)))
        R.toLocalCardRetained H.ladder.epsilon_pos.le
          (highGammaLadder_epsilon_le_half H hbeta hgamma) hNPower using 1
    all_goals simp only [
        AutomaticNormalizedLongCoreLocalCardRetainedWitness.toLocalCardRetained,
        ofCore]
    all_goals congr 1
  exact
    dividingScaleOutput_of_endpointIdentity_highGamma_selectedTrueSplitEta_automatic_conditionalOnX
      H hbeta hgamma targetEpsilon etaKT thirdEta delta0
        hTarget hThirdEta hThirdCap D hD hdeltaRaw hFOutput hFExact hXPower

/-- Fully automatic retained-witness specialization.  The identity endpoint
producer supplies the retained witness at the same automatic `W` with stored
bound exactly `Fintype.card index`; consequently the sole remaining public
cardinality seam is the corresponding selected power envelope. -/
theorem dividingScaleOutput_of_endpointIdentity_highGamma_selectedTrueSplitEta_automatic_of_refinedCardPower
    (H : HighGammaParameterLadder epsilon0 beta gamma)
    (hbeta : 0 < beta) (hgamma : gamma <= 1)
    (targetEpsilon etaKT thirdEta : Real) (delta0 : NNReal)
    (hTarget : 0 < targetEpsilon)
    (hThirdEta : 0 < thirdEta)
    (hThirdCap : thirdEta <= H.ladder.eta 0)
    (D : ActualTubeDatum delta index) (hD : D.IsAdmissible)
    (hdeltaRaw : delta <= highGammaSelectedTrueSplitEtaRawDelta0
      H targetEpsilon etaKT thirdEta delta0)
    (hFOutput : FrostmanHypotheses D
      (selectedTrueSplitOutputEta H.ladder thirdEta))
    (hFExact : FrostmanAtParameters gamma
      (sectionEightSourceLoss H.ladder targetEpsilon) thirdEta delta0)
    (hCardPower : (Fintype.card index : ENNReal) <=
      (delta : ENNReal) ^
        (-selectedTrueSplitCardScaleEta H.ladder thirdEta)) :
    DividingScaleOutput D H.ladder
      (4 * sectionEightSourceLoss H.ladder targetEpsilon) := by
  let hselectorSmall : delta <=
      endpointIdentityFirstCrossingImpossibleThreshold H.ladder :=
    hdeltaRaw.trans
      (highGammaSelectedTrueSplitEtaRawDelta0_le_selector
        H targetEpsilon etaKT thirdEta delta0)
  let R0 := automaticRefinedCardRetainedNormalizedLongCoreWitness
    D hD H.ladder hbeta hgamma hselectorSmall hFOutput
  let R : AutomaticNormalizedLongCoreLocalCardRetainedWitness
      D hD H.ladder hbeta hgamma hselectorSmall hFOutput := {
    n := R0.n
    not_large := R0.not_large
    local_card_le := R0.local_card_le }
  have hRPower : (R.n : ENNReal) <=
      (delta : ENNReal) ^
        (-selectedTrueSplitCardScaleEta H.ladder thirdEta) := by
    change (R0.n : ENNReal) <=
      (delta : ENNReal) ^
        (-selectedTrueSplitCardScaleEta H.ladder thirdEta)
    simpa only [R0,
      automaticRefinedCardRetainedNormalizedLongCoreWitness_n_eq_card] using
        hCardPower
  exact
    dividingScaleOutput_of_endpointIdentity_highGamma_selectedTrueSplitEta_automatic_of_retainedLocalCard
      H hbeta hgamma targetEpsilon etaKT thirdEta delta0
        hTarget hThirdEta hThirdCap D hD hdeltaRaw hFOutput hFExact R hRPower

#print axioms AutomaticNormalizedLongCoreLocalCardRetainedWitness
#print axioms
  AutomaticNormalizedLongCoreLocalCardRetainedWitness.toLocalCardRetained
#print axioms
  dividingScaleOutput_of_endpointIdentity_highGamma_selectedTrueSplitEta_automatic_of_retainedLocalCard
#print axioms
  dividingScaleOutput_of_endpointIdentity_highGamma_selectedTrueSplitEta_automatic_of_refinedCardPower

end
end Family8EndpointIdentityHighGammaSelectedTrueSplitEtaRetainedXAdapterV1
