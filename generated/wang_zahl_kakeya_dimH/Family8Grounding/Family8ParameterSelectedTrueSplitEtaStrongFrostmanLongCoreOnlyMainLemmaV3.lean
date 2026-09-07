import Family8Grounding.Family8ParameterCappedOutputEtaStrongFrostmanLongCoreOnlyMainLemmaV1
import Family8Grounding.Family8CanonicalGlobalOuterParameterAllocationV1

/-!
# Budgeted selected split-eta LongCore orchestration

The earlier true-split checkpoint exposed every pair
`outputEta < thirdEta`.  That interface was stronger than the top theorem
uses, and its provisional choice `outputEta = thirdEta / 2` leaves no room for
the correlated B2 budget

`2 * outputEta + cardScaleEta + absorbEta <=
  (1 - P.epsilon) * thirdEta`.

This successor selects one pair only.  The literal source exponent is

`((1 - P.epsilon) * thirdEta) / 8`,

so two source copies consume exactly one quarter of the available third
budget.  The provider receives only that selected exponent; there is no
universal `outputEta` binder.
-/

set_option autoImplicit false
set_option warningAsError true

open MeasureTheory
open scoped ENNReal NNReal

namespace Family8ParameterSelectedTrueSplitEtaStrongFrostmanLongCoreOnlyMainLemmaV3

open Submission.Kakeya.ConvexGeometry
open Family8AllFrostmanFixedNuBranchOrchestrationV2
open Family8SectionEightOutputEtaV1
open Family8CanonicalGlobalOuterParameterAllocationV1
open Family8DividingScaleOutputTargetMonotonicityV1
open Family8EndpointIdentityDividingScaleOutputOrchestrationV4
open Family8EndpointIdentityFirstCrossingImpossibleV1
open Family8EndpointIdentityFullRefinementDividingScaleOutputOrchestrationV1
open Family8FullRefinementActualDatumV1
open Family8GeneralizedScaleTrivialBranchV1
open Family8KatzTaoFrostmanPropertiesV1
open Family8NormalizedFirstCrossingFullRefinementAssemblyV1
open Family8NormalizedLongIntervalCoreConsumerV1
open Family8ParameterCappedOutputEtaStrongFrostmanLongCoreOnlyMainLemmaV1
open Family8ParameterLadderV1
open Family8RelativeScaleFixedNuEndpointOrchestrationV1
open Family8Section8FixedPositiveSelfImprovementBudgetV3
open FamilyStickyScaleChainCappedSeedSequenceV2
open FamilyStickyScaleChainSelectedCanonicalCoverCoordinatesProducerV1

noncomputable section

/-- The one literal source exponent selected for the correlated B2 route. -/
def selectedTrueSplitOutputEta
    {epsilon0 beta gamma : Real}
    (P : ParameterLadder epsilon0 beta gamma)
    (thirdEta : Real) : Real :=
  ((1 - P.epsilon) * thirdEta) / 8

theorem selectedTrueSplitOutputEta_pos
    {epsilon0 beta gamma thirdEta : Real}
    (P : ParameterLadder epsilon0 beta gamma)
    (hEpsilonOne : P.epsilon < 1)
    (hThirdEta : 0 < thirdEta) :
    0 < selectedTrueSplitOutputEta P thirdEta := by
  unfold selectedTrueSplitOutputEta
  positivity

theorem selectedTrueSplitOutputEta_lt_thirdEta
    {epsilon0 beta gamma thirdEta : Real}
    (P : ParameterLadder epsilon0 beta gamma)
    (hThirdEta : 0 < thirdEta) :
    selectedTrueSplitOutputEta P thirdEta < thirdEta := by
  unfold selectedTrueSplitOutputEta
  have hEpsilonPos := P.epsilon_pos
  nlinarith

theorem selectedTrueSplitOutputEta_le_eta_zero
    {epsilon0 beta gamma thirdEta : Real}
    (P : ParameterLadder epsilon0 beta gamma)
    (hThirdEta : 0 < thirdEta)
    (hThirdCap : thirdEta <= P.eta 0) :
    selectedTrueSplitOutputEta P thirdEta <= P.eta 0 := by
  exact (selectedTrueSplitOutputEta_lt_thirdEta
    P hThirdEta).le.trans hThirdCap

/-- The two source copies in the correlated base consume exactly one quarter
of the available endpoint third budget. -/
theorem two_mul_selectedTrueSplitOutputEta_eq_quarter_budget
    {epsilon0 beta gamma thirdEta : Real}
    (P : ParameterLadder epsilon0 beta gamma) :
    2 * selectedTrueSplitOutputEta P thirdEta =
      ((1 - P.epsilon) * thirdEta) / 4 := by
  unfold selectedTrueSplitOutputEta
  ring

/-- The largest card-scale exponent allowed by the exact correlated-density
consumer.  This is deliberately not fixed to the much smaller `s + q` power
available from an older conditional producer. -/
def selectedTrueSplitCardScaleEta
    {epsilon0 beta gamma : Real}
    (P : ParameterLadder epsilon0 beta gamma) (thirdEta : Real) : Real :=
  let outputEta := selectedTrueSplitOutputEta P thirdEta
  let s := sectionEightOutputEta P outputEta
  let q := canonicalGlobalOuterQuantum P s
  (1 - P.epsilon) * thirdEta - 3 * outputEta - 2 * q

theorem selectedTrueSplitCardScaleEta_pos
    {epsilon0 beta gamma thirdEta : Real}
    (P : ParameterLadder epsilon0 beta gamma)
    (hEpsilonOne : P.epsilon < 1)
    (hThirdEta : 0 < thirdEta) :
    0 < selectedTrueSplitCardScaleEta P thirdEta := by
  have hs := sectionEightOutputEta_le_source P
    (selectedTrueSplitOutputEta P thirdEta)
  have hq := canonicalGlobalOuterQuantum_le_property_div
    (P := P)
    (propertyEta := sectionEightOutputEta P
      (selectedTrueSplitOutputEta P thirdEta))
  have hBudgetPos : 0 < (1 - P.epsilon) * thirdEta :=
    mul_pos (by linarith) hThirdEta
  unfold selectedTrueSplitCardScaleEta
  dsimp only
  unfold selectedTrueSplitOutputEta at hs hq ⊢
  nlinarith

/-- The literal exponent ledger read by the correlated-base consumer.  The
card exponent is the weakest one shared with the density consumer. -/
theorem selectedTrueSplitOutputEta_correlated_base_budget
    {epsilon0 beta gamma thirdEta : Real}
    (P : ParameterLadder epsilon0 beta gamma)
    (hEpsilonOne : P.epsilon < 1)
    (hThirdEta : 0 < thirdEta) :
    let outputEta := selectedTrueSplitOutputEta P thirdEta
    let q := canonicalGlobalOuterQuantum P
      (sectionEightOutputEta P outputEta)
    let cardScaleEta := selectedTrueSplitCardScaleEta P thirdEta
    2 * outputEta + cardScaleEta + q <=
      (1 - P.epsilon) * thirdEta := by
  dsimp only
  have hOutput := selectedTrueSplitOutputEta_pos P hEpsilonOne hThirdEta
  have hSection := sectionEightOutputEta_pos P hOutput
  have hq := canonicalGlobalOuterQuantum_pos P hSection
  unfold selectedTrueSplitCardScaleEta
  dsimp only
  nlinarith

/-- The correlated density ledger pays three selected source powers, the
maximal shared card exponent, and two copies of the canonical quantum. -/
theorem selectedTrueSplitOutputEta_correlated_density_budget
    {epsilon0 beta gamma thirdEta : Real}
    (P : ParameterLadder epsilon0 beta gamma) :
    let outputEta := selectedTrueSplitOutputEta P thirdEta
    let q := canonicalGlobalOuterQuantum P
      (sectionEightOutputEta P outputEta)
    let cardScaleEta := selectedTrueSplitCardScaleEta P thirdEta
    3 * outputEta + cardScaleEta + 2 * q <=
      (1 - P.epsilon) * thirdEta := by
  dsimp only
  unfold selectedTrueSplitCardScaleEta
  dsimp only
  ring_nf
  exact le_rfl

/-- Main Lemma 1 from a provider for the single budgeted exponent pair selected
above.  Exact and relative Frostman estimates stay at `thirdEta`; datum
hypotheses and the final conclusion use `selectedTrueSplitOutputEta`. -/
theorem mainLemmaOne_of_parameter_selectedTrueSplitEta_strongFrostman_longCoreOnlyDSO
    (hLongGeometry : forall (beta gamma : Real)
      (hBeta : 0 < beta) (hGap : beta < gamma) (hGamma : gamma <= 1),
      exists epsilon0 : Real,
      exists P : ParameterLadder epsilon0 beta gamma,
      forall targetEpsilon : Real, 0 < targetEpsilon ->
      forall etaKT thirdEta : Real, forall delta0 : NNReal,
        0 < etaKT ->
        etaKT <= P.epsilon ^ 2 * P.eta 0 / 32 ->
        0 < thirdEta -> thirdEta <= P.eta 0 ->
        0 < delta0 -> delta0 <= (2 : NNReal)⁻¹ ->
        KatzTaoAtParameters
          beta (sectionEightFixedNu P) etaKT delta0 ->
        KatzTaoAtRelativeScaleParameters
          beta (sectionEightFixedNu P) etaKT delta0 ->
        FrostmanAtParameters gamma
          (sectionEightSourceLoss P targetEpsilon) thirdEta delta0 ->
        FrostmanAtRelativeScaleParameters gamma
          (sectionEightSourceLoss P targetEpsilon) thirdEta delta0 ->
          exists rawDelta0 : NNReal, 0 < rawDelta0 /\
            forall (delta : NNReal) (index : Type)
              [Fintype index] [DecidableEq index]
              (D : ActualTubeDatum delta index)
              (hD : D.IsAdmissible),
                delta <= rawDelta0 ->
                FrostmanHypotheses D
                  (selectedTrueSplitOutputEta P thirdEta) ->
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
  obtain ⟨etaKT, etaThirdRaw, delta0,
      hetaKT, hetaKTCap, hetaThirdRaw, hdelta0, hdelta0Half,
      hKTExact, hKTRelative,
      _hFExactQuarter, _hFRelativeQuarter,
      hFExactSourceRaw, hFRelativeSourceRaw⟩ :=
    exists_cappedOutputEta_split_source_parameters_with_strong_frostman
      P hKT hF hTargetPos.le hSourceZero hSourceOne hTargetEpsilon
  let thirdEta : Real := min etaThirdRaw (P.eta 0)
  have hThirdEtaPos : 0 < thirdEta := by
    dsimp only [thirdEta]
    exact lt_min hetaThirdRaw (P.eta_pos 0)
  have hThirdEtaLeRaw : thirdEta <= etaThirdRaw := by
    dsimp only [thirdEta]
    exact min_le_left _ _
  have hThirdEtaCap : thirdEta <= P.eta 0 := by
    dsimp only [thirdEta]
    exact min_le_right _ _
  have hFExactThird : FrostmanAtParameters source
      (sectionEightSourceLoss P targetEpsilon) thirdEta delta0 :=
    Family8FrostmanHypothesesLossMonotonicityV1.frostmanAtParameters_of_eta_le
      hFExactSourceRaw hThirdEtaLeRaw
  have hFRelativeThird : FrostmanAtRelativeScaleParameters source
      (sectionEightSourceLoss P targetEpsilon) thirdEta delta0 :=
    Family8RelativeScaleParameterMonotonicityV2.frostmanAtRelativeScaleParameters_of_eta_le
      hFRelativeSourceRaw hThirdEtaLeRaw
  have hEpsilonOne : P.epsilon < 1 :=
    Family8EndpointIdentityCoreSelectorV2.parameterLadder_epsilon_lt_one
      P hTargetPos hSourceOne
  have hOutputEtaPos :
      0 < selectedTrueSplitOutputEta P thirdEta :=
    selectedTrueSplitOutputEta_pos P hEpsilonOne hThirdEtaPos
  have hOutputEtaCap :
      selectedTrueSplitOutputEta P thirdEta <= P.eta 0 :=
    selectedTrueSplitOutputEta_le_eta_zero
      P hThirdEtaPos hThirdEtaCap
  obtain ⟨rawDelta0, hRawDelta0, hLongDatum⟩ :=
    hEndpoint targetEpsilon hTargetEpsilon etaKT thirdEta delta0
      hetaKT hetaKTCap hThirdEtaPos hThirdEtaCap hdelta0 hdelta0Half
      hKTExact hKTRelative hFExactThird hFRelativeThird
  let finalRawDelta0 : NNReal :=
    min rawDelta0
      (min (endpointIdentityFirstCrossingImpossibleThreshold P)
        (allFrostmanFixedNuThreshold P targetEpsilon))
  have hFinalRawDelta0 : 0 < finalRawDelta0 := by
    dsimp only [finalRawDelta0]
    exact lt_min hRawDelta0
      (lt_min (endpointIdentityFirstCrossingImpossibleThreshold_pos P)
        (allFrostmanFixedNuThreshold_pos P))
  refine ⟨selectedTrueSplitOutputEta P thirdEta, finalRawDelta0,
    hOutputEtaPos, hFinalRawDelta0, ?_⟩
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
    hLongDatum delta index D hD hdeltaRaw hFOutput
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
      P j hStage hTargetPos.le hSourceOne D hD hOutputEtaCap
        hFOutput hTargetEpsilon outerLoss hOuterLoss hAverage

#print axioms selectedTrueSplitOutputEta_pos
#print axioms selectedTrueSplitOutputEta_lt_thirdEta
#print axioms selectedTrueSplitOutputEta_le_eta_zero
#print axioms two_mul_selectedTrueSplitOutputEta_eq_quarter_budget
#print axioms selectedTrueSplitCardScaleEta
#print axioms selectedTrueSplitCardScaleEta_pos
#print axioms selectedTrueSplitOutputEta_correlated_base_budget
#print axioms selectedTrueSplitOutputEta_correlated_density_budget
#print axioms
  mainLemmaOne_of_parameter_selectedTrueSplitEta_strongFrostman_longCoreOnlyDSO

end
end Family8ParameterSelectedTrueSplitEtaStrongFrostmanLongCoreOnlyMainLemmaV3
