import Family8Grounding.Family8ActualFamilyVolumePackingV1
import Family8Grounding.Family8AmbientFamilyVolumeDensityV2
import Family8Grounding.Family8FullRefinementActualDatumV1
import Family8Grounding.Family8IdentityRadiusSourceKatzTaoTransportV1
import Family8Grounding.Family8NormalizedLongIntervalFrostmanInheritanceV1
import Family8Grounding.Family8ParentAggregatedShadingActiveCoarseXUpperV3
import Mathlib.Tactic

/-!
# Source-Frostman cancellation for the identity coarse Katz--Tao constant

The exact source Frostman-to-Katz--Tao constant contains the source indexed
family-volume density. After transport to an identity radius, its radius
factor is cancelled by the source family-volume square.
-/

set_option autoImplicit false
set_option warningAsError true
set_option linter.unusedSectionVars false
set_option maxHeartbeats 4000000

open Set MeasureTheory
open scoped BigOperators ENNReal NNReal

namespace Family8IdentitySourceFrostmanKatzTaoCardScaleCancellationV2

open LeanEval.Analysis.WangZahlKakeya
open Submission.Kakeya.ConvexGeometry
open Submission.Kakeya.ConvexFactoring
open Submission.Kakeya.Uniformity
open Family8ActualFamilyVolumePackingV1
open Family8AmbientFamilyVolumeDensityV2
open Family8FullRefinementActualDatumV1
open Family8IdentityRadiusSourceKatzTaoTransportV1
open Family8KatzTaoFrostmanPropertiesV1
open Family8NormalizedLongIntervalFrostmanInheritanceV1
open Family8ParentAggregatedShadingActiveCoarseXUpperV3.StickyScaleCover
open FamilyStickyAtEveryScaleCoreV1
open FamilyStickyScaleChainSelectedCanonicalCoverCoordinatesProducerV1

noncomputable section

variable {delta : NNReal} {index : Type}
  [Fintype index] [DecidableEq index]

/-- The literal source Frostman-to-Katz--Tao coefficient, transported to an
identity radius. The full-refinement datum changes no analytic object. -/
def identitySourceFrostmanKatzTaoConstant
    (D : ActualTubeDatum delta index) (rho : NNReal) (eta : Real) : ENNReal :=
  identityRadiusKatzTaoVolumeRatio delta rho *
    ((delta : ENNReal) ^ (-eta) *
      ambientFamilyVolumeDensity
        (fullRefinementDatum D).family.bodyFamily unitBallBody)

/-- The radius ratio cancels the full source tube-volume square. -/
theorem identityRadiusKatzTaoVolumeRatio_mul_eight_delta_sq
    (rho : NNReal) (hdelta : 0 < delta) :
    identityRadiusKatzTaoVolumeRatio delta rho *
        (8 * (delta : ENNReal) ^ 2) =
      128 * (rho : ENNReal) ^ 2 := by
  have hNN :
      ((8 * rho ^ (2 : Nat)) / (delta ^ (2 : Nat) / 2)) *
          (8 * delta ^ (2 : Nat)) = 128 * rho ^ (2 : Nat) := by
    field_simp [hdelta.ne']
    ring
  have hcast := congrArg (fun x : NNReal => (x : ENNReal)) hNN
  simpa only [identityRadiusKatzTaoVolumeRatio, ENNReal.coe_mul,
    ENNReal.coe_div (by positivity : delta ^ (2 : Nat) / 2 ≠ 0),
    ENNReal.coe_div (by norm_num : (2 : NNReal) ≠ 0),
    ENNReal.coe_pow, ENNReal.coe_ofNat] using hcast

/-- Source Frostman control gives the exact global Katz--Tao estimate which
is then transported to the identity cover. -/
theorem identityRadiusScaleCover_isKatzTaoAtScale_of_sourceFrostman
    (D : ActualTubeDatum delta index) (hD : D.IsAdmissible)
    (rho : NNReal) (hdeltaRho : delta ≤ rho)
    (hrhoHalf : rho ≤ (2 : NNReal)⁻¹)
    {eta : Real} (hF : FrostmanHypotheses D eta) :
    (identityRadiusScaleCover (fullRefinementDatum D).family rho hdeltaRho
      ).IsKatzTaoAtScale
        (identitySourceFrostmanKatzTaoConstant D rho eta) := by
  let E := fullRefinementDatum D
  have hunitOne : (1 : ENNReal) ≤ volume (unitBallBody : Set Space) := by
    rw [coe_unitBallBody, EuclideanSpace.volume_closedBall_fin_three]
    norm_num
    nlinarith [Real.pi_gt_three]
  have hunit0 : volume (unitBallBody : Set Space) ≠ 0 :=
    ne_of_gt ((zero_lt_one : (0 : ENNReal) < 1).trans_le hunitOne)
  have hunitTop : volume (unitBallBody : Set Space) ≠ ∞ :=
    unitBallBody.isCompact.measure_lt_top.ne
  have hFE : FrostmanHypotheses E eta := by
    exact (fullRefinementDatum_frostmanHypotheses_iff D eta).2 hF
  have hsourceKT : IsKatzTao
      ((delta : ENNReal) ^ (-eta) *
        ambientFamilyVolumeDensity E.family.bodyFamily unitBallBody)
      E.family.bodyFamily :=
    isKatzTao_of_isFrostmanIn_familyVolumeDensity hFE.2 hunit0 hunitTop
  simpa only [identitySourceFrostmanKatzTaoConstant, E] using
    identityRadiusScaleCover_isKatzTaoAtScale_of_sourceKatzTao
      E.family rho hdeltaRho hD.delta_pos hD.delta_le_half hrhoHalf hsourceKT

/-- The transported exact source constant is finite. -/
theorem identitySourceFrostmanKatzTaoConstant_ne_top
    (D : ActualTubeDatum delta index) (rho : NNReal)
    (hdelta : 0 < delta) (eta : Real) :
    identitySourceFrostmanKatzTaoConstant D rho eta ≠ ∞ := by
  have hunitOne : (1 : ENNReal) ≤ volume (unitBallBody : Set Space) := by
    rw [coe_unitBallBody, EuclideanSpace.volume_closedBall_fin_three]
    norm_num
    nlinarith [Real.pi_gt_three]
  have hunit0 : volume (unitBallBody : Set Space) ≠ 0 :=
    ne_of_gt ((zero_lt_one : (0 : ENNReal) < 1).trans_le hunitOne)
  unfold identitySourceFrostmanKatzTaoConstant
  apply ENNReal.mul_ne_top
  · unfold identityRadiusKatzTaoVolumeRatio
    exact ENNReal.div_ne_top
      (ENNReal.mul_ne_top (by norm_num)
        (ENNReal.pow_ne_top ENNReal.coe_ne_top))
      (ENNReal.div_ne_zero.mpr
        ⟨pow_ne_zero 2 (ENNReal.coe_ne_zero.mpr hdelta.ne'), by norm_num⟩)
  · exact ENNReal.mul_ne_top
      (ENNReal.rpow_ne_top_of_ne_zero
        (ENNReal.coe_ne_zero.mpr hdelta.ne') ENNReal.coe_ne_top)
      (ambientFamilyVolumeDensity_ne_top
        (fullRefinementDatum D).family.bodyFamily unitBallBody hunit0)

/-- Exact cancellation of the source ambient density and identity radius
ratio. This is the card-scale base coefficient needed by the normalized B2
third selector. -/
theorem identitySourceFrostmanKatzTaoConstant_mul_unitBallVolume_le_cardScale
    (D : ActualTubeDatum delta index) (hD : D.IsAdmissible)
    (rho : NNReal) (hdeltaRho : delta ≤ rho)
    {eta : Real} :
    identitySourceFrostmanKatzTaoConstant D rho eta *
        volume (unitBallBody : Set Space) ≤
      128 * (delta : ENNReal) ^ (-eta) *
        (activeCoarseCardScaleMass
          (identityRadiusScaleCover
            (fullRefinementDatum D).family rho hdeltaRho) : ENNReal) := by
  let E := fullRefinementDatum D
  let S := identityRadiusScaleCover E.family rho hdeltaRho
  have hunitOne : (1 : ENNReal) ≤ volume (unitBallBody : Set Space) := by
    rw [coe_unitBallBody, EuclideanSpace.volume_closedBall_fin_three]
    norm_num
    nlinarith [Real.pi_gt_three]
  have hunit0 : volume (unitBallBody : Set Space) ≠ 0 :=
    ne_of_gt ((zero_lt_one : (0 : ENNReal) < 1).trans_le hunitOne)
  have hunitTop : volume (unitBallBody : Set Space) ≠ ∞ :=
    unitBallBody.isCompact.measure_lt_top.ne
  have hcancel :
      ambientFamilyVolumeDensity E.family.bodyFamily unitBallBody *
          volume (unitBallBody : Set Space) =
        familyVolume E.family.bodyFamily := by
    unfold ambientFamilyVolumeDensity
    exact ENNReal.div_mul_cancel hunit0 hunitTop
  have hvolume : familyVolume E.family.bodyFamily ≤
      (Fintype.card index : ENNReal) *
        (8 * (delta : ENNReal) ^ 2) := by
    simpa only [ActualTubeDatum.actualFamilyVolume, E] using
      actualFamilyVolume_le_card_mul_eight_sq E hD.delta_le_half
  have hscale := identityRadiusKatzTaoVolumeRatio_mul_eight_delta_sq
    (delta := delta) rho hD.delta_pos
  have hactiveCard : S.activeCoarse.card = Fintype.card index := by
    simp only [S, E, identityRadiusScaleCover,
      fullRefinementDatum_refined, Finset.card_map, Finset.card_univ]
  unfold identitySourceFrostmanKatzTaoConstant
  calc
    (identityRadiusKatzTaoVolumeRatio delta rho *
        ((delta : ENNReal) ^ (-eta) *
          ambientFamilyVolumeDensity E.family.bodyFamily unitBallBody)) *
        volume (unitBallBody : Set Space) =
      identityRadiusKatzTaoVolumeRatio delta rho *
        (delta : ENNReal) ^ (-eta) *
          (ambientFamilyVolumeDensity E.family.bodyFamily unitBallBody *
            volume (unitBallBody : Set Space)) := by ac_rfl
    _ = identityRadiusKatzTaoVolumeRatio delta rho *
        (delta : ENNReal) ^ (-eta) * familyVolume E.family.bodyFamily := by
      rw [hcancel]
    _ ≤ identityRadiusKatzTaoVolumeRatio delta rho *
        (delta : ENNReal) ^ (-eta) *
          ((Fintype.card index : ENNReal) *
            (8 * (delta : ENNReal) ^ 2)) :=
      mul_le_mul' le_rfl hvolume
    _ = 128 * (delta : ENNReal) ^ (-eta) *
        ((Fintype.card index : ENNReal) * (rho : ENNReal) ^ 2) := by
      calc
        identityRadiusKatzTaoVolumeRatio delta rho *
            (delta : ENNReal) ^ (-eta) *
              ((Fintype.card index : ENNReal) *
                (8 * (delta : ENNReal) ^ 2)) =
          ((delta : ENNReal) ^ (-eta) *
            (Fintype.card index : ENNReal)) *
              (identityRadiusKatzTaoVolumeRatio delta rho *
                (8 * (delta : ENNReal) ^ 2)) := by ac_rfl
        _ = ((delta : ENNReal) ^ (-eta) *
            (Fintype.card index : ENNReal)) *
              (128 * (rho : ENNReal) ^ 2) := by rw [hscale]
        _ = 128 * (delta : ENNReal) ^ (-eta) *
            ((Fintype.card index : ENNReal) * (rho : ENNReal) ^ 2) := by
          ac_rfl
    _ = 128 * (delta : ENNReal) ^ (-eta) *
        (activeCoarseCardScaleMass S : ENNReal) := by
      simp only [activeCoarseCardScaleMass, ENNReal.coe_mul,
        ENNReal.coe_natCast, ENNReal.coe_pow, hactiveCard]

#print axioms identitySourceFrostmanKatzTaoConstant
#print axioms identityRadiusKatzTaoVolumeRatio_mul_eight_delta_sq
#print axioms identityRadiusScaleCover_isKatzTaoAtScale_of_sourceFrostman
#print axioms identitySourceFrostmanKatzTaoConstant_ne_top
#print axioms
  identitySourceFrostmanKatzTaoConstant_mul_unitBallVolume_le_cardScale

end
end Family8IdentitySourceFrostmanKatzTaoCardScaleCancellationV2
