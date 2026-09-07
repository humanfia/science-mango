import Family8Grounding.Family8UniformTubeCardRetentionFrostmanV2
import Family8Grounding.Family8RestrictedActualDatumMassBridgeV1
import Family8Grounding.Family8FrostmanInOnUnivBridgeV2

/-!
# Frostman retention for a cardinality-retained actual subtype, V2

V1 quantified the actual-datum index in an arbitrary universe even though
`ActualTubeDatum` uses `Type`.  This successor fixes that type-level mismatch
and otherwise keeps the exact restricted datum, constant, and proof.
-/

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 1800000

open Set MeasureTheory
open scoped BigOperators ENNReal NNReal

namespace Family8ActualDatumCardRetentionFrostmanV2

open LeanEval.Analysis.WangZahlKakeya
open Submission.Kakeya.ConvexGeometry
open Submission.Kakeya.ConvexFactoring
open Submission.Kakeya.Uniformity
open Family8KatzTaoFrostmanPropertiesV1
open Family8GeneralizedKatzTaoMultiplicityV1
open Family8FrostmanInOnUnivBridgeV2
open Family8Prop51SelectedOccurrenceSourceFrostmanV1
open Family8RestrictedActualDatumMassBridgeV1
open Family8UniformTubeCardRetentionFrostmanV2

noncomputable section

/-- A cardinality-retained restriction of one equal-radius actual tube datum
inherits its source Frostman certificate with the exact geometric loss
`16 * L`. -/
theorem restrictActualTubeDatum_isFrostmanIn_of_card_retention
    {delta : NNReal} {iota : Type}
    [Fintype iota] [DecidableEq iota]
    (D : ActualTubeDatum delta iota) (selected : Finset iota)
    (K : ConvexBody Space) {C L : ENNReal}
    (hF : IsFrostmanIn C D.family.bodyFamily K)
    (hdeltaHalf : delta ≤ (2 : NNReal)⁻¹)
    (hcard : (Fintype.card iota : ENNReal) ≤
      L * (selected.card : ENNReal)) :
    IsFrostmanIn (C * (16 * L))
      (restrictActualTubeDatum D selected).family.bodyFamily K := by
  have hOn : IsFrostmanOn C D.family.bodyFamily Finset.univ K :=
    (isFrostmanOn_univ_iff_isFrostmanIn D.family.bodyFamily K).2 hF
  have hretained : containedMassOn D.family.bodyFamily Finset.univ K ≤
      (16 * L) * containedMassOn D.family.bodyFamily selected K := by
    exact containedMassOn_le_sixteen_mul_cardLoss_mul_selected
      D.family Finset.univ selected K (Finset.subset_univ selected)
        (fun i _hi ↦ hOn.1 i (Finset.mem_univ i)) hdeltaHalf (by
          simpa using hcard)
  have hSelected : IsFrostmanOn (C * (16 * L))
      D.family.bodyFamily selected K :=
    isFrostmanOn_subset_of_ambientMass_retention
      (Finset.subset_univ selected) hOn hretained
  refine ⟨?_, ?_⟩
  · intro i
    exact hSelected.1 i.1 i.2
  · intro K' hK'
    rw [restrictActualTubeDatum_containedMass,
      restrictActualTubeDatum_containedMass]
    exact hSelected.2 K' hK'

#print axioms restrictActualTubeDatum_isFrostmanIn_of_card_retention

end
end Family8ActualDatumCardRetentionFrostmanV2
