import Family8Grounding.Family8OuterMiddleFixedNuEndpointOrchestrationV1
import Family8Grounding.Family8AllFrostmanBranchFromCommonPointPackingV1
import Family8Grounding.Family8FrostmanExponentMonotonicityV1

open scoped ENNReal NNReal
open MeasureTheory

namespace Family8AllFrostmanFixedNuBranchOrchestrationV2

open Submission.Kakeya.ConvexGeometry
open Family8KatzTaoFrostmanPropertiesV1
open Family8GeneralizedScaleTrivialBranchV1
open Family8ParameterLadderV1
open Family8Section8FixedPositiveSelfImprovementBudgetV3
open Family8CommonPointTubePackingV1
open Family8AllFrostmanBranchFromCommonPointPackingV1
open Family8FrostmanExponentMonotonicityV1
open Family8RelativeScaleFixedNuEndpointOrchestrationV1
open Family8OuterMiddleFixedNuEndpointOrchestrationV1

noncomputable section

set_option autoImplicit false
set_option warningAsError true

/-!
# The all-Frostman branch at the fixed Section 8 decrement

The all-Frostman alternative first gives the exponent `gamma / 2` at half
the requested displayed loss.  The ladder places its fixed decrement below
`gamma / 2`.  Common-point family-volume packing and the proved exponent
transport estimate therefore upgrade that branch to `gamma - fixedNu`.

The final theorem joins this automatic branch with the factorized long
interval branch.  Its remaining geometric input is the literal dichotomy
produced by a dividing scale: a union-volume lower bound, or a stage and
outer-loss factorization.
-/

/-- The fixed decrement lies below half of the source exponent. -/
theorem sectionEightFixedNu_le_gamma_half
    {epsilon0 beta gamma : Real}
    (P : ParameterLadder epsilon0 beta gamma)
    (hBeta0 : 0 <= beta) :
    sectionEightFixedNu P <= gamma / 2 := by
  have hEta := P.eta_le_epsilon_div_five 0
  have hGap := P.epsilon_gap
  have hEpsilon := P.epsilon_pos
  dsimp only [sectionEightFixedNu]
  linarith

/-- Common terminal scale for the all-Frostman estimate and its exponent
transport to the fixed-decrement target. -/
def allFrostmanFixedNuThreshold
    {epsilon0 beta gamma : Real}
    (P : ParameterLadder epsilon0 beta gamma)
    (targetEpsilon : Real) : NNReal :=
  min
    (allFrostmanCommonPointPackingThreshold
      (targetEpsilon / 2) gamma)
    (frostmanExponentTransportThreshold
      commonPointFamilyVolumeConstant targetEpsilon
        (gamma / 2) (gamma - sectionEightFixedNu P))

theorem allFrostmanFixedNuThreshold_pos
    {epsilon0 beta gamma targetEpsilon : Real}
    (P : ParameterLadder epsilon0 beta gamma) :
    0 < allFrostmanFixedNuThreshold P targetEpsilon := by
  rw [allFrostmanFixedNuThreshold, lt_min_iff]
  exact ⟨
    allFrostmanCommonPointPackingThreshold_pos
      (targetEpsilon / 2) gamma,
    frostmanExponentTransportThreshold_pos
      commonPointFamilyVolumeConstant targetEpsilon
        (gamma / 2) (gamma - sectionEightFixedNu P)⟩

theorem allFrostmanFixedNuThreshold_le_half
    {epsilon0 beta gamma targetEpsilon : Real}
    (P : ParameterLadder epsilon0 beta gamma) :
    allFrostmanFixedNuThreshold P targetEpsilon <=
      (2 : NNReal)⁻¹ := by
  exact (min_le_left _ _).trans
    (allFrostmanCommonPointPackingThreshold_le_half
      (targetEpsilon / 2) gamma)

/-- The union-volume alternative already implies the desired fixed-decrement
Frostman bound; no long-interval witness is needed in this branch. -/
theorem averageMultiplicity_le_fixedNuRHS_of_allFrostman
    {epsilon0 beta gamma targetEpsilon : Real}
    (P : ParameterLadder epsilon0 beta gamma)
    (hBeta0 : 0 <= beta)
    (hGamma0 : 0 <= gamma) (hGamma4 : gamma <= 4)
    {delta : NNReal} {index : Type}
    [Fintype index] [DecidableEq index]
    (D : ActualTubeDatum delta index) (hD : D.IsAdmissible)
    (hdelta : delta <= allFrostmanFixedNuThreshold P targetEpsilon)
    (hTarget : 0 < targetEpsilon)
    (hunion :
      (delta : ENNReal) ^ (gamma / 2) <=
        volume D.shading.shadedUnion) :
    D.shading.averageMultiplicity <=
      frostmanMultiplicityRHS delta D.actualFamilyVolume targetEpsilon
        (gamma - sectionEightFixedNu P) := by
  have hdeltaAll :
      delta <= allFrostmanCommonPointPackingThreshold
        (targetEpsilon / 2) gamma :=
    hdelta.trans (min_le_left _ _)
  have hHalf :
      D.shading.averageMultiplicity <=
        frostmanMultiplicityRHS delta D.actualFamilyVolume
          (targetEpsilon / 2) (gamma / 2) :=
    averageMultiplicity_le_frostmanRHS_of_allFrostman_commonPointPacking
      D hD hdeltaAll (by linarith) hGamma0 hGamma4 hunion
  have hdeltaTransport :
      delta <= frostmanExponentTransportThreshold
        commonPointFamilyVolumeConstant targetEpsilon
          (gamma / 2) (gamma - sectionEightFixedNu P) :=
    hdelta.trans (min_le_right _ _)
  have hdeltaGeometric : delta <= (1 / 100 : NNReal) :=
    hdeltaAll.trans (min_le_right _ _)
  have hvolume :
      D.actualFamilyVolume <= commonPointFamilyVolumeConstant *
        (delta : ENNReal) ^ (-2 : Real) :=
    actualFamilyVolume_le_commonPointPacking D hD hdeltaGeometric
  have hLowerUpper :
      gamma / 2 <= gamma - sectionEightFixedNu P := by
    have hNu := sectionEightFixedNu_le_gamma_half P hBeta0
    linarith
  exact hHalf.trans
    (frostmanMultiplicityRHS_lower_le_upper_of_volumePacking
      hD.delta_pos (hD.delta_le_half.trans (by norm_num))
      hdeltaTransport commonPointFamilyVolumeConstant_ne_top
      hTarget hLowerUpper hvolume)

/-- Main Lemma 1 from the honest dividing-scale dichotomy.  Terminal-scale
restriction, the all-Frostman branch, exponent transport, the zero-mass
case, and the final global closure are all handled here. -/
theorem mainLemmaOne_of_allFrostman_or_outerThree_middleTen
    (hDividingScale : forall beta gamma : Real,
      0 < beta -> beta < gamma -> gamma <= 1 ->
        exists epsilon0 : Real, exists P : ParameterLadder epsilon0 beta gamma,
          forall targetEpsilon : Real, 0 < targetEpsilon ->
          forall eta : Real, forall delta0 : NNReal,
            0 < eta -> 0 < delta0 -> delta0 <= (2 : NNReal)⁻¹ ->
            KatzTaoAtParameters
              beta (sectionEightFixedNu P) eta delta0 ->
            FrostmanAtParameters gamma (targetEpsilon / 4) eta delta0 ->
            KatzTaoAtRelativeScaleParameters
              beta (sectionEightFixedNu P) eta delta0 ->
            FrostmanAtRelativeScaleParameters
              gamma (targetEpsilon / 4) eta delta0 ->
              exists outputEta : Real, exists rawDelta0 : NNReal,
                0 < outputEta /\
                outputEta <= sectionEightFixedNu P /\
                0 < rawDelta0 /\
                  forall (delta : NNReal) (index : Type)
                    [Fintype index] [DecidableEq index]
                    (D : ActualTubeDatum delta index),
                      D.IsAdmissible ->
                      delta <= rawDelta0 ->
                      FrostmanHypotheses D outputEta ->
                      D.shading.shadingMass ≠ 0 ->
                        ((delta : ENNReal) ^ (gamma / 2) <=
                            volume D.shading.shadedUnion) \/
                        (exists j : Nat, exists outerLoss : ENNReal,
                          j <= P.N /\
                          outerLoss <=
                            (delta : ENNReal) ^ (-3 * P.eta j) /\
                          D.shading.averageMultiplicity <=
                            (outerLoss *
                              (delta : ENNReal) ^ (10 * P.eta j)) *
                            frostmanMultiplicityRHS
                              delta D.actualFamilyVolume
                                (targetEpsilon / 4) gamma))
    (beta : Real) :
    KatzTaoProperty beta -> FrostmanProperty beta := by
  apply mainLemmaOne_of_relativeScale_fixedNu_nonzeroMassEndpoint
  intro target source hTargetPos hTargetSource hSourceOne
  obtain ⟨epsilon0, P, hEndpoint⟩ :=
    hDividingScale target source hTargetPos hTargetSource hSourceOne
  refine ⟨epsilon0, P, ?_⟩
  intro targetEpsilon hTargetEpsilon eta delta0 heta hdelta0 hdelta0Half
    hKTExact hFExact hKTRelative hFRelative
  obtain ⟨outputEta, rawDelta0, hOutputEta, hOutputEtaNu,
      hRawDelta0, hBranches⟩ :=
    hEndpoint targetEpsilon hTargetEpsilon eta delta0
      heta hdelta0 hdelta0Half hKTExact hFExact hKTRelative hFRelative
  let finalDelta0 : NNReal :=
    min rawDelta0 (allFrostmanFixedNuThreshold P targetEpsilon)
  have hFinalDelta0 : 0 < finalDelta0 := by
    dsimp only [finalDelta0]
    rw [lt_min_iff]
    exact ⟨hRawDelta0,
      allFrostmanFixedNuThreshold_pos P⟩
  refine ⟨outputEta, finalDelta0, hOutputEta, hFinalDelta0, ?_⟩
  intro delta index _ _ D hD hdelta hF hmass
  have hdeltaRaw : delta <= rawDelta0 :=
    hdelta.trans (min_le_left _ _)
  have hdeltaAll :
      delta <= allFrostmanFixedNuThreshold P targetEpsilon :=
    hdelta.trans (min_le_right _ _)
  rcases hBranches delta index D hD hdeltaRaw hF hmass with
    hUnion | ⟨j, outerLoss, hStage, hOuter, hFactorized⟩
  · exact averageMultiplicity_le_fixedNuRHS_of_allFrostman
      P hTargetPos.le (by linarith) (by linarith) D hD hdeltaAll
        hTargetEpsilon hUnion
  · exact averageMultiplicity_le_fixedNuRHS_of_outerThree_middleTen
      P j hStage hTargetPos.le hSourceOne D hD hOutputEtaNu hF
        hTargetEpsilon outerLoss hOuter hFactorized

#print axioms sectionEightFixedNu_le_gamma_half
#print axioms allFrostmanFixedNuThreshold_pos
#print axioms allFrostmanFixedNuThreshold_le_half
#print axioms averageMultiplicity_le_fixedNuRHS_of_allFrostman
#print axioms mainLemmaOne_of_allFrostman_or_outerThree_middleTen

end

end Family8AllFrostmanFixedNuBranchOrchestrationV2
