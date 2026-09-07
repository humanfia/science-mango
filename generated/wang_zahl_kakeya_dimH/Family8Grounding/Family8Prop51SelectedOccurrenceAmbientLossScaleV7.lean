import Family8Grounding.Family8Prop51SelectedOccurrenceAmbientLossScaleV5
import Family8Grounding.Family8Prop51SelectedOccurrenceUniformTubeAmbientLossV10
import Mathlib.Tactic

/-!
# Scale-explicit canonical selected-source Frostman certificate

The active-cardinality loss is replaced by the actual admissible tube-packing
fallback.  The resulting `delta^(-4)` cost remains explicit for the final
scalar audit.
-/

open Set MeasureTheory
open scoped BigOperators ENNReal NNReal

namespace Family8Prop51SelectedOccurrenceAmbientLossScaleV7

open LeanEval.Analysis.WangZahlKakeya
open Submission.Kakeya.ConvexGeometry
open Submission.Kakeya.ConvexFactoring
open Submission.Kakeya.ConvexFactoring.FullConvexMaximalDensity
open Submission.Kakeya.ConvexFactoring.GreedyOccurrenceFactorization
open Submission.Kakeya.Uniformity
open Family8KatzTaoFrostmanPropertiesV1
open Family8CommonPointTubePackingV1
open Family8SelectedOccurrenceDensityFrostmanV1
open Family8SelectedOccurrenceAverageRetentionV1
open Family8Prop51SelectedOccurrenceSourceFrostmanV1
open Family8Prop51SelectedOccurrenceAmbientMassRatioV1
open Family8Prop51SelectedOccurrenceUniformTubeAmbientLossV8
open Family8Prop51SelectedOccurrenceUniformTubeAmbientLossV10
open Family8Prop51SelectedOccurrenceAmbientLossScaleV5

noncomputable section

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 3000000

variable {delta : NNReal} {index kappa : Type}
  [Fintype index] [DecidableEq index]
  {candidates : Finset kappa}
  {container : kappa -> ConvexBody Space} {active : Finset index}

theorem max_activeCard_le_commonPoint_rpow_neg_four
    (D : ActualTubeDatum delta index) (hD : D.IsAdmissible)
    (active : Finset index)
    (hdeltaSmall : delta ≤ (1 / 100 : NNReal)) :
    max 1 (16 * (active.card : ENNReal)) ≤
      max 1 ((32 * commonPointFamilyVolumeConstant) *
        (delta : ENNReal) ^ (-4 : Real)) := by
  have hactive := activeCard_le_commonPoint_rpow_neg_four
    D hD active hdeltaSmall
  apply max_le_max le_rfl
  calc
    16 * (active.card : ENNReal) ≤
        16 * ((2 * commonPointFamilyVolumeConstant) *
          (delta : ENNReal) ^ (-4 : Real)) := mul_le_mul' le_rfl hactive
    _ = ((16 : ENNReal) * 2) * commonPointFamilyVolumeConstant *
        (delta : ENNReal) ^ (-4 : Real) := by ac_rfl
    _ = (32 * commonPointFamilyVolumeConstant) *
        (delta : ENNReal) ^ (-4 : Real) := by
      rw [show (16 : ENNReal) * 2 = 32 by norm_num]

theorem prop51SelectedAmbientMassLoss_le_commonPoint_rpow_neg_four
    (D : ActualTubeDatum delta index) (hD : D.IsAdmissible)
    (P : GreedyDensityPartition D.family.bodyFamily
      candidates container active)
    (Y : Shading D.family.bodyFamily) (base : ENNReal) (M : Nat)
    (K : ConvexBody Space) {C : ENNReal}
    (hglobal : IsFrostmanOn C D.family.bodyFamily active K)
    (hfull : (fullOccurrenceInducedShading P Y).shadingMass ≠ 0)
    (hdeltaSmall : delta ≤ (1 / 100 : NNReal)) :
    prop51SelectedAmbientMassLoss P Y base M K ≤
      max 1 ((32 * commonPointFamilyVolumeConstant) *
        (delta : ENNReal) ^ (-4 : Real)) := by
  exact (prop51SelectedAmbientMassLoss_le_max_activeCardinality
    P Y base M K hglobal hfull hD.delta_le_half).trans
      (max_activeCard_le_commonPoint_rpow_neg_four
        D hD active hdeltaSmall)

theorem prop51SelectedOccurrences_source_fine_frostman_commonPointScale
    (D : ActualTubeDatum delta index) (hD : D.IsAdmissible)
    (P : GreedyDensityPartition D.family.bodyFamily
      candidates container active)
    (Y : Shading D.family.bodyFamily) (base : ENNReal) (M : Nat)
    (K : ConvexBody Space) {C : ENNReal}
    (hglobal : IsFrostmanOn C D.family.bodyFamily active K)
    (hfull : (fullOccurrenceInducedShading P Y).shadingMass ≠ 0)
    (hdeltaSmall : delta ≤ (1 / 100 : NNReal)) :
    IsFrostmanOn
      (C * max 1 ((32 * commonPointFamilyVolumeConstant) *
        (delta : ENNReal) ^ (-4 : Real)))
      D.family.bodyFamily (prop51SelectedFineIndices P Y base M) K := by
  have hactiveCertificate :=
    prop51SelectedOccurrences_source_fine_frostman_activeCardinality
      P Y base M K hglobal hfull hD.delta_le_half
  exact hactiveCertificate.mono (mul_le_mul' le_rfl
    (max_activeCard_le_commonPoint_rpow_neg_four
      D hD active hdeltaSmall))

#print axioms max_activeCard_le_commonPoint_rpow_neg_four
#print axioms prop51SelectedAmbientMassLoss_le_commonPoint_rpow_neg_four
#print axioms prop51SelectedOccurrences_source_fine_frostman_commonPointScale

end
end Family8Prop51SelectedOccurrenceAmbientLossScaleV7
