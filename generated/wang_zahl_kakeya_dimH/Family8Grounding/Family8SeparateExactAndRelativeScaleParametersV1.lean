import Family8Grounding.Family8GeneralizedKatzTaoPropertyV1
import Family8Grounding.Family8FrostmanHypothesesLossMonotonicityV1
import Family8Grounding.Family8GeneralizedScaleTrivialBranchV1
import Family8Grounding.Family8RelativeScaleParameterMonotonicityV2
import Family8Grounding.Family8CommonPointTubePackingV1
import Mathlib.Tactic

/-!
# Separate exact and relative-scale source parameters

The Section 8 third factor and strict-crossing count estimate need different
hypothesis-loss exponents.  This module synchronizes exact and relative-scale
parameters for each property separately, without taking a minimum between
the Katz--Tao and Frostman exponents.
-/

set_option autoImplicit false
set_option warningAsError true

open scoped ENNReal NNReal

namespace Family8SeparateExactAndRelativeScaleParametersV1

open Family8CommonPointTubePackingV1
open Family8FrostmanHypothesesLossMonotonicityV1
open Family8GeneralizedKatzTaoPropertyV1
open Family8GeneralizedScaleTrivialBranchV1
open Family8KatzTaoFrostmanPropertiesV1
open Family8RelativeScaleParameterMonotonicityV2

noncomputable section

private theorem commonPointPackingInput :
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

/-- Exact and relative-scale Katz--Tao estimates share one positive
hypothesis exponent and terminal scale, independently of Frostman. -/
theorem exists_exactAndRelativeScale_katzTao_parameters
    {beta epsilon : Real}
    (hKT : KatzTaoProperty beta)
    (hBeta0 : 0 <= beta) (hEpsilon : 0 < epsilon) :
    exists etaKT : Real, exists deltaKT : NNReal,
      0 < etaKT /\ 0 < deltaKT /\ deltaKT <= (2 : NNReal)⁻¹ /\
        KatzTaoAtParameters beta epsilon etaKT deltaKT /\
        KatzTaoAtRelativeScaleParameters beta epsilon etaKT deltaKT := by
  obtain ⟨etaExact, deltaExact, hetaExact, hdeltaExact,
      hdeltaExactHalf, hExact⟩ := hKT epsilon hEpsilon
  have hpackingDelta0 : 0 < (1 / 100 : NNReal) := by norm_num
  obtain ⟨etaRelative, deltaRelative, hetaRelative, hdeltaRelative,
      _hdeltaRelativeHalf, hRelative⟩ :=
    Family8GeneralizedScaleTrivialBranchV1.KatzTaoProperty.exists_relativeScale_parameters_of_commonPointPacking
      hKT hEpsilon hBeta0
      commonPointTubePackingConstant commonPointTubePackingConstant_ne_top
      (1 / 100 : NNReal) hpackingDelta0 commonPointPackingInput
  let etaKT : Real := min etaExact etaRelative
  let deltaKT : NNReal := min deltaExact deltaRelative
  have hetaKT : 0 < etaKT := by
    dsimp only [etaKT]
    exact lt_min hetaExact hetaRelative
  have hdeltaKT : 0 < deltaKT := by
    dsimp only [deltaKT]
    exact lt_min hdeltaExact hdeltaRelative
  have hdeltaKTHalf : deltaKT <= (2 : NNReal)⁻¹ :=
    (min_le_left deltaExact deltaRelative).trans hdeltaExactHalf
  have hExactEta : KatzTaoAtParameters beta epsilon etaKT deltaExact :=
    Family8GeneralizedKatzTaoPropertyV1.katzTaoAtParameters_of_eta_le
      hExact (min_le_left etaExact etaRelative)
  have hRelativeEta :
      KatzTaoAtRelativeScaleParameters beta epsilon etaKT deltaRelative :=
    katzTaoAtRelativeScaleParameters_of_eta_le
      hRelative (min_le_right etaExact etaRelative)
  exact ⟨etaKT, deltaKT, hetaKT, hdeltaKT, hdeltaKTHalf,
    hExactEta.mono_delta0 (min_le_left deltaExact deltaRelative),
    katzTaoAtRelativeScaleParameters_mono_delta0
      hRelativeEta (min_le_right deltaExact deltaRelative)⟩

/-- Exact and relative-scale Frostman estimates share one positive
hypothesis exponent and terminal scale, independently of Katz--Tao. -/
theorem exists_exactAndRelativeScale_frostman_parameters
    {gamma epsilon : Real}
    (hF : FrostmanProperty gamma)
    (hGamma0 : 0 <= gamma) (hGamma1 : gamma <= 1)
    (hEpsilon : 0 < epsilon) :
    exists etaThird : Real, exists deltaF : NNReal,
      0 < etaThird /\ 0 < deltaF /\ deltaF <= (2 : NNReal)⁻¹ /\
        FrostmanAtParameters gamma epsilon etaThird deltaF /\
        FrostmanAtRelativeScaleParameters gamma epsilon etaThird deltaF := by
  obtain ⟨etaExact, deltaExact, hetaExact, hdeltaExact,
      hdeltaExactHalf, hExact⟩ := hF epsilon hEpsilon
  have hpackingDelta0 : 0 < (1 / 100 : NNReal) := by norm_num
  obtain ⟨etaRelative, deltaRelative, hetaRelative, hdeltaRelative,
      _hdeltaRelativeHalf, hRelative⟩ :=
    Family8GeneralizedScaleTrivialBranchV1.FrostmanProperty.exists_relativeScale_parameters_of_commonPointPacking
      hF hEpsilon hGamma0 hGamma1
      commonPointTubePackingConstant commonPointTubePackingConstant_ne_top
      (1 / 100 : NNReal) hpackingDelta0 commonPointPackingInput
  let etaThird : Real := min etaExact etaRelative
  let deltaF : NNReal := min deltaExact deltaRelative
  have hetaThird : 0 < etaThird := by
    dsimp only [etaThird]
    exact lt_min hetaExact hetaRelative
  have hdeltaF : 0 < deltaF := by
    dsimp only [deltaF]
    exact lt_min hdeltaExact hdeltaRelative
  have hdeltaFHalf : deltaF <= (2 : NNReal)⁻¹ :=
    (min_le_left deltaExact deltaRelative).trans hdeltaExactHalf
  have hExactEta : FrostmanAtParameters gamma epsilon etaThird deltaExact :=
    Family8FrostmanHypothesesLossMonotonicityV1.frostmanAtParameters_of_eta_le
      hExact (min_le_left etaExact etaRelative)
  have hRelativeEta :
      FrostmanAtRelativeScaleParameters gamma epsilon etaThird deltaRelative :=
    frostmanAtRelativeScaleParameters_of_eta_le
      hRelative (min_le_right etaExact etaRelative)
  exact ⟨etaThird, deltaF, hetaThird, hdeltaF, hdeltaFHalf,
    hExactEta.mono_delta0 (min_le_left deltaExact deltaRelative),
    frostmanAtRelativeScaleParameters_mono_delta0
      hRelativeEta (min_le_right deltaExact deltaRelative)⟩

#print axioms exists_exactAndRelativeScale_katzTao_parameters
#print axioms exists_exactAndRelativeScale_frostman_parameters

end
end Family8SeparateExactAndRelativeScaleParametersV1
