import Family8Grounding.Family8StickySourceCardFallbackV1

open scoped ENNReal NNReal

namespace Family8Prop51SelectedOccurrenceAmbientLossScaleV5

open LeanEval.Analysis.WangZahlKakeya
open Family8KatzTaoFrostmanPropertiesV1
open Family8CommonPointTubePackingV1
open Family8StickySourceCardFallbackV1

noncomputable section

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 2000000

variable {delta : NNReal} {index : Type}
  [Fintype index] [DecidableEq index]

/-- Any actual active subset inherits the proved admissible source-card
packing estimate. -/
theorem activeCard_le_commonPoint_rpow_neg_four
    (D : ActualTubeDatum delta index) (hD : D.IsAdmissible)
    (active : Finset index)
    (hdeltaSmall : delta ≤ (1 / 100 : NNReal)) :
    (active.card : ENNReal) ≤
      (2 * commonPointFamilyVolumeConstant) *
        (delta : ENNReal) ^ (-4 : Real) := by
  calc
    (active.card : ENNReal) ≤ (Fintype.card index : ENNReal) := by
      exact_mod_cast Finset.card_le_univ active
    _ ≤ (2 * commonPointFamilyVolumeConstant) *
        (delta : ENNReal) ^ (-4 : Real) :=
      actualTubeDatum_indexCard_le_two_mul_commonPointConstant_rpow_neg_four
        D hD hdeltaSmall

#print axioms activeCard_le_commonPoint_rpow_neg_four

end
end Family8Prop51SelectedOccurrenceAmbientLossScaleV5
