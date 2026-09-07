import Family8Grounding.Family8CommonKatzTaoFrostmanParametersV2
import Family8Grounding.Family8CommonRelativeScaleKatzTaoFrostmanParametersV2

open scoped NNReal

namespace Family8CommonExactAndRelativeScaleParametersV1

open Family8KatzTaoFrostmanPropertiesV1
open Family8GeneralizedKatzTaoPropertyV1
open Family8FrostmanHypothesesLossMonotonicityV1
open Family8GeneralizedScaleTrivialBranchV1
open Family8RelativeScaleParameterMonotonicityV2
open Family8CommonKatzTaoFrostmanParametersV2
open Family8CommonRelativeScaleKatzTaoFrostmanParametersV2

noncomputable section

set_option autoImplicit false
set_option warningAsError true

/-!
# One parameter pair for exact and relative-scale source estimates

The exact-scale and full relative-scale adapters each return a common
Katz--Tao/Frostman parameter pair, but those two pairs are initially
independent.  Taking their positive minima and applying the two monotonicity
APIs yields all four estimates at one loss exponent and one terminal scale.
-/

/-- Four independently requested source losses share one positive loss
exponent and one positive terminal scale. -/
theorem exists_common_exactAndRelativeScale_parameters
    {beta gamma exactKatzTaoEpsilon exactFrostmanEpsilon
      relativeKatzTaoEpsilon relativeFrostmanEpsilon : Real}
    (hKT : KatzTaoProperty beta)
    (hF : FrostmanProperty gamma)
    (hBeta0 : 0 <= beta)
    (hGamma0 : 0 <= gamma)
    (hGamma1 : gamma <= 1)
    (hExactKTEpsilon : 0 < exactKatzTaoEpsilon)
    (hExactFEpsilon : 0 < exactFrostmanEpsilon)
    (hRelativeKTEpsilon : 0 < relativeKatzTaoEpsilon)
    (hRelativeFEpsilon : 0 < relativeFrostmanEpsilon) :
    exists eta : Real, exists delta0 : NNReal,
      0 < eta /\ 0 < delta0 /\ delta0 <= (2 : NNReal)⁻¹ /\
        KatzTaoAtParameters beta exactKatzTaoEpsilon eta delta0 /\
        FrostmanAtParameters gamma exactFrostmanEpsilon eta delta0 /\
        KatzTaoAtRelativeScaleParameters
          beta relativeKatzTaoEpsilon eta delta0 /\
        FrostmanAtRelativeScaleParameters
          gamma relativeFrostmanEpsilon eta delta0 := by
  obtain ⟨etaExact, deltaExact, hetaExact, hdeltaExact,
      hdeltaExactHalf, hKTExact, hFExact⟩ :=
    exists_common_katzTao_frostman_parameters
      hKT hF hExactKTEpsilon hExactFEpsilon
  obtain ⟨etaRelative, deltaRelative, hetaRelative, hdeltaRelative,
      _hdeltaRelativeHalf, hKTRelative, hFRelative⟩ :=
    exists_common_relativeScale_katzTao_frostman_parameters
      hKT hF hBeta0 hGamma0 hGamma1
      hRelativeKTEpsilon hRelativeFEpsilon
  let eta : Real := min etaExact etaRelative
  let delta0 : NNReal := min deltaExact deltaRelative
  have heta : 0 < eta := by
    dsimp only [eta]
    exact lt_min hetaExact hetaRelative
  have hdelta0 : 0 < delta0 := by
    dsimp only [delta0]
    exact lt_min hdeltaExact hdeltaRelative
  have hdelta0Half : delta0 <= (2 : NNReal)⁻¹ := by
    exact (min_le_left deltaExact deltaRelative).trans hdeltaExactHalf
  have hKTExactEta :
      KatzTaoAtParameters beta exactKatzTaoEpsilon eta deltaExact := by
    exact katzTaoAtParameters_of_eta_le hKTExact
      (min_le_left etaExact etaRelative)
  have hFExactEta :
      FrostmanAtParameters gamma exactFrostmanEpsilon eta deltaExact := by
    exact frostmanAtParameters_of_eta_le hFExact
      (min_le_left etaExact etaRelative)
  have hKTRelativeEta :
      KatzTaoAtRelativeScaleParameters
        beta relativeKatzTaoEpsilon eta deltaRelative := by
    exact katzTaoAtRelativeScaleParameters_of_eta_le hKTRelative
      (min_le_right etaExact etaRelative)
  have hFRelativeEta :
      FrostmanAtRelativeScaleParameters
        gamma relativeFrostmanEpsilon eta deltaRelative := by
    exact frostmanAtRelativeScaleParameters_of_eta_le hFRelative
      (min_le_right etaExact etaRelative)
  refine ⟨eta, delta0, heta, hdelta0, hdelta0Half, ?_, ?_, ?_, ?_⟩
  · exact hKTExactEta.mono_delta0 (min_le_left deltaExact deltaRelative)
  · exact hFExactEta.mono_delta0 (min_le_left deltaExact deltaRelative)
  · exact katzTaoAtRelativeScaleParameters_mono_delta0
      hKTRelativeEta (min_le_right deltaExact deltaRelative)
  · exact frostmanAtRelativeScaleParameters_mono_delta0
      hFRelativeEta (min_le_right deltaExact deltaRelative)

/-- One requested loss shared by all four source estimates. -/
theorem exists_common_exactAndRelativeScale_parameters_same_epsilon
    {beta gamma epsilon : Real}
    (hKT : KatzTaoProperty beta)
    (hF : FrostmanProperty gamma)
    (hBeta0 : 0 <= beta)
    (hGamma0 : 0 <= gamma)
    (hGamma1 : gamma <= 1)
    (hEpsilon : 0 < epsilon) :
    exists eta : Real, exists delta0 : NNReal,
      0 < eta /\ 0 < delta0 /\ delta0 <= (2 : NNReal)⁻¹ /\
        KatzTaoAtParameters beta epsilon eta delta0 /\
        FrostmanAtParameters gamma epsilon eta delta0 /\
        KatzTaoAtRelativeScaleParameters beta epsilon eta delta0 /\
        FrostmanAtRelativeScaleParameters gamma epsilon eta delta0 := by
  exact exists_common_exactAndRelativeScale_parameters
    hKT hF hBeta0 hGamma0 hGamma1
    hEpsilon hEpsilon hEpsilon hEpsilon

#print axioms exists_common_exactAndRelativeScale_parameters
#print axioms exists_common_exactAndRelativeScale_parameters_same_epsilon

end

end Family8CommonExactAndRelativeScaleParametersV1
