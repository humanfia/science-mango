import Family8Grounding.Family8AllFrostmanFixedNuBranchOrchestrationV2
import Family8Grounding.Family8DividingScaleOutputTargetMonotonicityV1
import Family8Grounding.Family8EndpointIdentityFirstCrossingImpossibleV1
import Family8Grounding.Family8EndpointIdentityFullRefinementDividingScaleOutputOrchestrationV1
import Family8Grounding.Family8NonzeroMassParameterEndpointOrchestrationV3
import Family8Grounding.Family8GeneralizedKatzTaoPropertyV1
import Family8Grounding.Family8MultiplicityLossMonotonicityV4
import Family8Grounding.Family8RelativeScaleParameterMonotonicityV2
import Family8Grounding.Family8SeparateExactAndRelativeScaleParametersV1
import Family8Grounding.Family8SectionEightOutputEtaV1

/-!
# Capped-output-eta arbitrary-parameter LongCore orchestration

The split source-parameter theorem retains the Frostman estimates at the
strong loss `sectionEightSourceLoss P targetEpsilon`.  We cap its Frostman
hypothesis exponent by `P.eta 0`, ask the LongCore producer for a DSO at the
effective target `4 * sectionEightSourceLoss P targetEpsilon`, and then use
target monotonicity to recover the user-requested target.

The Katz--Tao and Frostman hypothesis exponents remain separate.  In
particular, this wrapper neither identifies parameter ladders nor feeds the
uncapped third-factor exponent to the LongCore producer.
-/

set_option autoImplicit false
set_option warningAsError true

open MeasureTheory
open scoped ENNReal NNReal

namespace Family8ParameterCappedOutputEtaStrongFrostmanLongCoreOnlyMainLemmaV1

open Submission.Kakeya.ConvexGeometry
open Family8AllFrostmanFixedNuBranchOrchestrationV2
open Family8DividingScaleOutputTargetMonotonicityV1
open Family8EndpointIdentityDividingScaleOutputOrchestrationV4
open Family8EndpointIdentityFirstCrossingImpossibleV1
open Family8EndpointIdentityFullRefinementDividingScaleOutputOrchestrationV1
open Family8FullRefinementActualDatumV1
open Family8GeneralizedScaleTrivialBranchV1
open Family8KatzTaoFrostmanPropertiesV1
open Family8NormalizedFirstCrossingFullRefinementAssemblyV1
open Family8NormalizedLongIntervalCoreConsumerV1
open Family8ParameterLadderV1
open Family8RelativeScaleFixedNuEndpointOrchestrationV1
open Family8Section8FixedPositiveSelfImprovementBudgetV3
open Family8SectionEightOutputEtaV1
open FamilyStickyScaleChainCappedSeedSequenceV2
open FamilyStickyScaleChainSelectedCanonicalCoverCoordinatesProducerV1

noncomputable section

/-- Stable local replacement for the uncompiled V3--V5 cap drafts. -/
def cappedOutputEtaKatzTaoHypothesisLossCap
    {epsilon0 beta gamma : Real}
    (P : ParameterLadder epsilon0 beta gamma) : Real :=
  P.epsilon ^ 2 * P.eta 0 / 32

theorem cappedOutputEtaKatzTaoHypothesisLossCap_pos
    {epsilon0 beta gamma : Real}
    (P : ParameterLadder epsilon0 beta gamma) :
    0 < cappedOutputEtaKatzTaoHypothesisLossCap P := by
  unfold cappedOutputEtaKatzTaoHypothesisLossCap
  exact div_pos
    (mul_pos (sq_pos_of_pos P.epsilon_pos) (P.eta_pos 0))
    (by norm_num)

/-- Split exact/relative source parameters while retaining Frostman at the
strong source loss. -/
theorem exists_cappedOutputEta_split_source_parameters_with_strong_frostman
    {epsilon0 beta gamma targetEpsilon : Real}
    (P : ParameterLadder epsilon0 beta gamma)
    (hKT : KatzTaoProperty beta)
    (hF : FrostmanProperty gamma)
    (hBeta0 : 0 <= beta)
    (hGamma0 : 0 <= gamma)
    (hGamma1 : gamma <= 1)
    (hTarget : 0 < targetEpsilon) :
    exists etaKT etaThird : Real, exists delta0 : NNReal,
      0 < etaKT /\
      etaKT <= cappedOutputEtaKatzTaoHypothesisLossCap P /\
      0 < etaThird /\
      0 < delta0 /\ delta0 <= (2 : NNReal)⁻¹ /\
        KatzTaoAtParameters
          beta (sectionEightFixedNu P) etaKT delta0 /\
        KatzTaoAtRelativeScaleParameters
          beta (sectionEightFixedNu P) etaKT delta0 /\
        FrostmanAtParameters gamma
          (targetEpsilon / 4) etaThird delta0 /\
        FrostmanAtRelativeScaleParameters gamma
          (targetEpsilon / 4) etaThird delta0 /\
        FrostmanAtParameters gamma
          (sectionEightSourceLoss P targetEpsilon) etaThird delta0 /\
        FrostmanAtRelativeScaleParameters gamma
          (sectionEightSourceLoss P targetEpsilon) etaThird delta0 := by
  have hSource : 0 < sectionEightSourceLoss P targetEpsilon :=
    sectionEightSourceLoss_pos P hTarget
  obtain ⟨etaKTRaw, deltaKT, hetaKTRaw, hdeltaKT, hdeltaKTHalf,
      hKTExactRaw, hKTRelativeRaw⟩ :=
    Family8SeparateExactAndRelativeScaleParametersV1.exists_exactAndRelativeScale_katzTao_parameters
        hKT hBeta0 hSource
  obtain ⟨etaThird, deltaF, hetaThird, hdeltaF, _hdeltaFHalf,
      hFExactStrong, hFRelativeStrong⟩ :=
    Family8SeparateExactAndRelativeScaleParametersV1.exists_exactAndRelativeScale_frostman_parameters
        hF hGamma0 hGamma1 hSource
  let etaKT : Real :=
    min etaKTRaw (cappedOutputEtaKatzTaoHypothesisLossCap P)
  let delta0 : NNReal := min deltaKT deltaF
  have hetaKT : 0 < etaKT := by
    dsimp only [etaKT]
    exact lt_min hetaKTRaw
      (cappedOutputEtaKatzTaoHypothesisLossCap_pos P)
  have hetaKTRawLe : etaKT <= etaKTRaw := by
    dsimp only [etaKT]
    exact min_le_left _ _
  have hetaKTCap :
      etaKT <= cappedOutputEtaKatzTaoHypothesisLossCap P := by
    dsimp only [etaKT]
    exact min_le_right _ _
  have hdelta0 : 0 < delta0 := by
    dsimp only [delta0]
    exact lt_min hdeltaKT hdeltaF
  have hdelta0Half : delta0 <= (2 : NNReal)⁻¹ :=
    (min_le_left deltaKT deltaF).trans hdeltaKTHalf
  have hKTExactSmallEta : KatzTaoAtParameters
      beta (sectionEightSourceLoss P targetEpsilon) etaKT deltaKT :=
    Family8GeneralizedKatzTaoPropertyV1.katzTaoAtParameters_of_eta_le hKTExactRaw hetaKTRawLe
  have hKTRelativeSmallEta : KatzTaoAtRelativeScaleParameters
      beta (sectionEightSourceLoss P targetEpsilon) etaKT deltaKT :=
    Family8RelativeScaleParameterMonotonicityV2.katzTaoAtRelativeScaleParameters_of_eta_le
        hKTRelativeRaw hetaKTRawLe
  have hSourceNu :
      sectionEightSourceLoss P targetEpsilon <= sectionEightFixedNu P :=
    sectionEightSourceLoss_le_fixedNu P targetEpsilon
  have hSourceTarget :
      sectionEightSourceLoss P targetEpsilon <= targetEpsilon / 4 :=
    sectionEightSourceLoss_le_targetQuarter P targetEpsilon
  exact ⟨etaKT, etaThird, delta0,
    hetaKT, hetaKTCap, hetaThird, hdelta0, hdelta0Half,
    (Family8MultiplicityLossMonotonicityV4.katzTaoAtParameters_of_epsilon_le
        hKTExactSmallEta hSourceNu).mono_delta0
          (min_le_left deltaKT deltaF),
    Family8RelativeScaleParameterMonotonicityV2.katzTaoAtRelativeScaleParameters_mono_delta0
        (Family8MultiplicityLossMonotonicityV4.katzTaoAtRelativeScaleParameters_of_epsilon_le
            hKTRelativeSmallEta hSourceNu)
        (min_le_left deltaKT deltaF),
    (Family8MultiplicityLossMonotonicityV4.frostmanAtParameters_of_epsilon_le
        hFExactStrong hSourceTarget).mono_delta0
          (min_le_right deltaKT deltaF),
    Family8RelativeScaleParameterMonotonicityV2.frostmanAtRelativeScaleParameters_mono_delta0
        (Family8MultiplicityLossMonotonicityV4.frostmanAtRelativeScaleParameters_of_epsilon_le
            hFRelativeStrong hSourceTarget)
        (min_le_right deltaKT deltaF),
    hFExactStrong.mono_delta0 (min_le_right deltaKT deltaF),
    Family8RelativeScaleParameterMonotonicityV2.frostmanAtRelativeScaleParameters_mono_delta0
        hFRelativeStrong (min_le_right deltaKT deltaF)⟩

/-- Main Lemma 1 from a split-parameter LongCore producer.

The producer receives a capped Frostman exponent and the exact/relative
Frostman estimates at the retained strong source loss.  Its DSO target is
four times that loss, so the Frostman loss displayed inside the DSO is
exactly the retained source loss. -/
theorem mainLemmaOne_of_parameter_cappedOutputEta_strongFrostman_longCoreOnlyDSO
    (hLongGeometry : forall (beta gamma : Real)
      (hBeta : 0 < beta) (hGap : beta < gamma) (hGamma : gamma <= 1),
      exists epsilon0 : Real,
      exists P : ParameterLadder epsilon0 beta gamma,
      forall targetEpsilon : Real, 0 < targetEpsilon ->
      forall etaKT sourceEta : Real, forall delta0 : NNReal,
        0 < etaKT ->
        etaKT <= P.epsilon ^ 2 * P.eta 0 / 32 ->
        0 < sourceEta -> sourceEta <= P.eta 0 ->
        0 < delta0 -> delta0 <= (2 : NNReal)⁻¹ ->
        KatzTaoAtParameters
          beta (sectionEightFixedNu P) etaKT delta0 ->
        KatzTaoAtRelativeScaleParameters
          beta (sectionEightFixedNu P) etaKT delta0 ->
        FrostmanAtParameters gamma
          (sectionEightSourceLoss P targetEpsilon) sourceEta delta0 ->
        FrostmanAtRelativeScaleParameters gamma
          (sectionEightSourceLoss P targetEpsilon) sourceEta delta0 ->
          exists rawDelta0 : NNReal, 0 < rawDelta0 /\
            forall (delta : NNReal) (index : Type)
              [Fintype index] [DecidableEq index]
              (D : ActualTubeDatum delta index)
              (hD : D.IsAdmissible),
                delta <= rawDelta0 ->
                FrostmanHypotheses D sourceEta ->
                D.shading.shadingMass ≠ 0 ->
                  forall _W : NormalizedLongIntervalCoreWitness
                    (fullRefinementDatum D).family
                      (identityRadiusCoherentCover
                        (fullRefinementDatum D).family)
                      P.N P.epsilon P.eta
                        (endpointScaleSequence delta
                          (hD.delta_le_half.trans (by norm_num))),
                    DividingScaleOutput D P
                      (4 * sectionEightSourceLoss P targetEpsilon))
    (beta : Real) :
    KatzTaoProperty beta -> FrostmanProperty beta := by
  apply
    Family8NonzeroMassParameterEndpointOrchestrationV3.mainLemmaOne_of_parameterLadderNonzeroMassEndpoint
  intro target source hTargetPos hTargetSource hSourceOne hKT hF
  obtain ⟨epsilon0, P, hEndpoint⟩ :=
    hLongGeometry target source hTargetPos hTargetSource hSourceOne
  refine ⟨epsilon0, P, ?_⟩
  intro targetEpsilon hTargetEpsilon
  have hSourceZero : 0 <= source := by linarith
  obtain ⟨etaKT, etaThird, delta0,
      hetaKT, hetaKTCap, hetaThird, hdelta0, hdelta0Half,
      hKTExact, hKTRelative,
      _hFExactQuarter, _hFRelativeQuarter,
      hFExactSource, hFRelativeSource⟩ :=
    exists_cappedOutputEta_split_source_parameters_with_strong_frostman
      P hKT hF hTargetPos.le hSourceZero hSourceOne hTargetEpsilon
  let sourceEta : Real := sectionEightOutputEta P etaThird
  have hSourceEtaPos : 0 < sourceEta := by
    dsimp only [sourceEta]
    exact sectionEightOutputEta_pos P hetaThird
  have hSourceEtaLeThird : sourceEta <= etaThird := by
    dsimp only [sourceEta]
    exact sectionEightOutputEta_le_source P etaThird
  have hSourceEtaCap : sourceEta <= P.eta 0 := by
    dsimp only [sourceEta]
    exact sectionEightOutputEta_le_fixedNu P etaThird
  have hFExactSourceCapped : FrostmanAtParameters source
      (sectionEightSourceLoss P targetEpsilon) sourceEta delta0 :=
    Family8FrostmanHypothesesLossMonotonicityV1.frostmanAtParameters_of_eta_le
        hFExactSource hSourceEtaLeThird
  have hFRelativeSourceCapped : FrostmanAtRelativeScaleParameters source
      (sectionEightSourceLoss P targetEpsilon) sourceEta delta0 :=
    Family8RelativeScaleParameterMonotonicityV2.frostmanAtRelativeScaleParameters_of_eta_le
        hFRelativeSource hSourceEtaLeThird
  obtain ⟨rawDelta0, hRawDelta0, hLongDatum⟩ :=
    hEndpoint targetEpsilon hTargetEpsilon etaKT sourceEta delta0
      hetaKT hetaKTCap hSourceEtaPos hSourceEtaCap
      hdelta0 hdelta0Half hKTExact hKTRelative
      hFExactSourceCapped hFRelativeSourceCapped
  let finalRawDelta0 : NNReal :=
    min rawDelta0
      (min (endpointIdentityFirstCrossingImpossibleThreshold P)
        (allFrostmanFixedNuThreshold P targetEpsilon))
  have hFinalRawDelta0 : 0 < finalRawDelta0 := by
    dsimp only [finalRawDelta0]
    exact lt_min hRawDelta0
      (lt_min (endpointIdentityFirstCrossingImpossibleThreshold_pos P)
        (allFrostmanFixedNuThreshold_pos P))
  refine ⟨sourceEta, finalRawDelta0, hSourceEtaPos,
    hFinalRawDelta0, ?_⟩
  intro delta index _ _ D hD hdelta hFOutput hmass
  have hdeltaRaw : delta <= rawDelta0 :=
    hdelta.trans (min_le_left _ _)
  have hdeltaRest : delta <=
      min (endpointIdentityFirstCrossingImpossibleThreshold P)
        (allFrostmanFixedNuThreshold P targetEpsilon) :=
    hdelta.trans (min_le_right _ _)
  have hdeltaFirst : delta <=
      endpointIdentityFirstCrossingImpossibleThreshold P :=
    hdeltaRest.trans (min_le_left _ _)
  have hdeltaAll : delta <=
      allFrostmanFixedNuThreshold P targetEpsilon :=
    hdeltaRest.trans (min_le_right _ _)
  have hLong :=
    hLongDatum delta index D hD hdeltaRaw hFOutput hmass
  have hFirst : forall _W : FirstActualNormalizedCrossingWitness
      (fullRefinementDatum D)
        (fullRefinementDatum_isAdmissible hD)
        (identityRadiusCoherentCover (fullRefinementDatum D).family)
        (endpointScaleSequence delta
          (hD.delta_le_half.trans (by norm_num)))
        P.epsilon P.epsilon_pos.le P.eta P.N,
      DividingScaleOutput D P
        (4 * sectionEightSourceLoss P targetEpsilon) := by
    intro W
    exact False.elim
      ((endpointIdentity_fullRefinement_not_firstCrossing
        D hD P hTargetPos hSourceOne hmass hdeltaFirst) ⟨W⟩)
  have hEffective : DividingScaleOutput D P
      (4 * sectionEightSourceLoss P targetEpsilon) :=
    dividingScaleOutput_of_endpointIdentity_fullRefinement_branches
      D hD P hTargetPos hSourceOne hLong hFirst
  have hEffectiveLe :
      4 * sectionEightSourceLoss P targetEpsilon <= targetEpsilon := by
    nlinarith [sectionEightSourceLoss_le_targetQuarter P targetEpsilon]
  have hRequested : DividingScaleOutput D P targetEpsilon :=
    dividingScaleOutput_mono_targetEpsilon
      D hD P hEffectiveLe hEffective
  rcases hRequested with hUnion | ⟨j, outerLoss, hStage,
      hOuterLoss, hAverage⟩
  · exact averageMultiplicity_le_fixedNuRHS_of_allFrostman
      P hTargetPos.le (by linarith) (by linarith) D hD hdeltaAll
        hTargetEpsilon hUnion
  · exact Family8OuterMiddleFixedNuEndpointOrchestrationV1.averageMultiplicity_le_fixedNuRHS_of_outerThree_middleTen
      P j hStage hTargetPos.le hSourceOne D hD hSourceEtaCap
        hFOutput hTargetEpsilon outerLoss hOuterLoss hAverage

#print axioms
  mainLemmaOne_of_parameter_cappedOutputEta_strongFrostman_longCoreOnlyDSO

end
end Family8ParameterCappedOutputEtaStrongFrostmanLongCoreOnlyMainLemmaV1
