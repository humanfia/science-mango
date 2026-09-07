import Family8Grounding.Family8RelativeScaleParameterMonotonicityV2
import Family8Grounding.Family8CommonPointTubePackingV1
import Mathlib.Tactic

open scoped ENNReal NNReal

namespace Family8CommonRelativeScaleKatzTaoFrostmanParametersV2

open Family8KatzTaoFrostmanPropertiesV1
open Family8GeneralizedScaleTrivialBranchV1
open Family8RelativeScaleParameterMonotonicityV2
open Family8CommonPointTubePackingV1

noncomputable section

set_option autoImplicit false
set_option warningAsError true

/-!
# Common full relative-scale parameters

The explicit common-point tube packing theorem supplies the packing input of
both full generalized-scale adapters.  Their independently chosen loss
exponents and terminal scales are then replaced by their positive minima.
Consequently the later Section 8 argument receives the Katz--Tao and
Frostman estimates at one common pair of parameters, without carrying a
packing function or synchronizing the two property witnesses.

V1 used an unavailable short dot spelling for the nested adapter names and
is not imported here.
-/

/-- At independently requested multiplicity losses, the two source
properties share one positive pair of full relative-scale parameters. -/
theorem exists_common_relativeScale_katzTao_frostman_parameters
    {beta gamma katzTaoEpsilon frostmanEpsilon : Real}
    (hKT : KatzTaoProperty beta)
    (hF : FrostmanProperty gamma)
    (hBeta0 : 0 <= beta)
    (hGamma0 : 0 <= gamma)
    (hGamma1 : gamma <= 1)
    (hKTEpsilon : 0 < katzTaoEpsilon)
    (hFEpsilon : 0 < frostmanEpsilon) :
    exists eta : Real, exists delta0 : NNReal,
      0 < eta /\ 0 < delta0 /\ delta0 <= (2 : NNReal)⁻¹ /\
        KatzTaoAtRelativeScaleParameters
          beta katzTaoEpsilon eta delta0 /\
        FrostmanAtRelativeScaleParameters
          gamma frostmanEpsilon eta delta0 := by
  have hpackingDelta0 : 0 < (1 / 100 : NNReal) := by norm_num
  have hpacking :
      forall {delta : NNReal} {index : Type}
        [Fintype index] [DecidableEq index]
        (D : ActualTubeDatum delta index),
        D.IsAdmissible -> delta <= (1 / 100 : NNReal) ->
          exists M : Nat,
            (forall x,
              (Family8PointwisePackingVolumeV1.actualCarrierShading D).pointMultiplicity x <= M) /\
            (M : ENNReal) <=
              commonPointTubePackingConstant *
                (delta : ENNReal) ^ (-2 : Real) := by
    intro delta index _ _ D hD hdelta
    exact exists_actualCarrierShading_commonPointTubePackingNatCap
      D hD hdelta
  obtain ⟨etaKT, deltaKT, hetaKT, hdeltaKT, hdeltaKTHalf, hKTAt⟩ :=
    Family8GeneralizedScaleTrivialBranchV1.KatzTaoProperty.exists_relativeScale_parameters_of_commonPointPacking
      hKT hKTEpsilon hBeta0
      commonPointTubePackingConstant commonPointTubePackingConstant_ne_top
      (1 / 100 : NNReal) hpackingDelta0 hpacking
  obtain ⟨etaF, deltaF, hetaF, hdeltaF, _hdeltaFHalf, hFAt⟩ :=
    Family8GeneralizedScaleTrivialBranchV1.FrostmanProperty.exists_relativeScale_parameters_of_commonPointPacking
      hF hFEpsilon hGamma0 hGamma1
      commonPointTubePackingConstant commonPointTubePackingConstant_ne_top
      (1 / 100 : NNReal) hpackingDelta0 hpacking
  let eta : Real := min etaKT etaF
  let delta0 : NNReal := min deltaKT deltaF
  have heta : 0 < eta := by
    dsimp only [eta]
    exact lt_min hetaKT hetaF
  have hdelta0 : 0 < delta0 := by
    dsimp only [delta0]
    exact lt_min hdeltaKT hdeltaF
  have hdelta0Half : delta0 <= (2 : NNReal)⁻¹ := by
    exact (min_le_left deltaKT deltaF).trans hdeltaKTHalf
  have hKTCommonEta :
      KatzTaoAtRelativeScaleParameters
        beta katzTaoEpsilon eta deltaKT := by
    exact katzTaoAtRelativeScaleParameters_of_eta_le hKTAt
      (min_le_left etaKT etaF)
  have hFCommonEta :
      FrostmanAtRelativeScaleParameters
        gamma frostmanEpsilon eta deltaF := by
    exact frostmanAtRelativeScaleParameters_of_eta_le hFAt
      (min_le_right etaKT etaF)
  refine ⟨eta, delta0, heta, hdelta0, hdelta0Half, ?_, ?_⟩
  · exact katzTaoAtRelativeScaleParameters_mono_delta0
      hKTCommonEta (min_le_left deltaKT deltaF)
  · exact frostmanAtRelativeScaleParameters_mono_delta0
      hFCommonEta (min_le_right deltaKT deltaF)

/-- Same requested loss on both full relative-scale estimates. -/
theorem exists_common_relativeScale_katzTao_frostman_parameters_same_epsilon
    {beta gamma epsilon : Real}
    (hKT : KatzTaoProperty beta)
    (hF : FrostmanProperty gamma)
    (hBeta0 : 0 <= beta)
    (hGamma0 : 0 <= gamma)
    (hGamma1 : gamma <= 1)
    (hEpsilon : 0 < epsilon) :
    exists eta : Real, exists delta0 : NNReal,
      0 < eta /\ 0 < delta0 /\ delta0 <= (2 : NNReal)⁻¹ /\
        KatzTaoAtRelativeScaleParameters beta epsilon eta delta0 /\
        FrostmanAtRelativeScaleParameters gamma epsilon eta delta0 := by
  exact exists_common_relativeScale_katzTao_frostman_parameters
    hKT hF hBeta0 hGamma0 hGamma1 hEpsilon hEpsilon

#print axioms exists_common_relativeScale_katzTao_frostman_parameters
#print axioms exists_common_relativeScale_katzTao_frostman_parameters_same_epsilon

end

end Family8CommonRelativeScaleKatzTaoFrostmanParametersV2
