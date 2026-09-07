import Family8Grounding.Family8PlankCertificateLongTubeCoverV2
import Family6Grounding.Family6CanonicalFrostmanConstantCoreV1
import Mathlib.Tactic

set_option autoImplicit false
set_option warningAsError true
set_option linter.unusedSectionVars false
set_option maxHeartbeats 5000000

open Set MeasureTheory
open scoped BigOperators ENNReal NNReal

namespace Family8PlankLongTubeFrostmanTransferV3

open LeanEval.Analysis.WangZahlKakeya
open Submission.Kakeya.ConvexGeometry
open Submission.Kakeya.ConvexFactoring
open Submission.Kakeya.Uniformity
open Family6AffinePlankAnalyticHypothesesStableV1
open Family6CanonicalFrostmanConstantCoreV1
open Family8PlankThickControlCanonicalSeedNormalizationV3
open Family8PlankCertificateLongTubeCoverV2

noncomputable section

universe u

variable {iota : Type u} [Fintype iota] [DecidableEq iota]
variable {a b : NNReal}

/-!
# Frostman transfer to the genuine long-tube cover

This file proves the construction-level part of the plank-to-tube Frostman
transfer. A source plank and its long-tube cover use the same index. Thus a
test body containing the cover tube also contains the source plank, while the
certified plank-volume lower bound pays only the explicit aspect-ratio loss
below. The final theorem deliberately requires a *common ambient*: changing
the ambient normalization is a separate geometric step.

V1 and V2 were failed drafts and are not imported.
-/

/-- Explicit loss between a certified `a x b x 1` plank and its genuine
radius-`b` long-tube cover. -/
def plankLongTubeFrostmanCopyLoss (C a b : NNReal) : ENNReal :=
  ((8 * C ^ 3 * (b / a) : NNReal) : ENNReal)

/-- Exact cancellation of the certified plank-volume lower bound against the
aspect-ratio copy loss. -/
theorem eight_mul_sq_eq_copyLoss_mul_plankLower
    {C a b : NNReal} (hC : 0 < C) (ha : 0 < a) :
    8 * (b : ENNReal) ^ 2 =
      plankLongTubeFrostmanCopyLoss C a b *
        ((((C⁻¹ : NNReal) : ENNReal) ^ 3) *
          ((a : ENNReal) * (b : ENNReal))) := by
  unfold plankLongTubeFrostmanCopyLoss
  norm_cast
  field_simp

/-- Each genuine long-tube cover member has volume at most the explicit
aspect-ratio loss times the volume of the plank it covers. -/
theorem longTubeCover_volume_le_copyLoss_mul_source
    (D : ShadedConvexPlankFamily iota a b)
    (hb : b ≤ (2 : NNReal)⁻¹) (i : iota) :
    volume ((plankLongTubeCoverFamily D).bodyFamily i : Set Space) ≤
      plankLongTubeFrostmanCopyLoss D.comparisonConstant a b *
        volume (D.family i : Set Space) := by
  have hplank := D.all_isPlank i
  calc
    volume ((plankLongTubeCoverFamily D).bodyFamily i : Set Space) ≤
        8 * (b : ENNReal) ^ 2 :=
      ((plankLongTubeCoverFamily D).tubes i).volume_le_eight_mul_sq_of_le_half hb
    _ = plankLongTubeFrostmanCopyLoss D.comparisonConstant a b *
        ((((D.comparisonConstant⁻¹ : NNReal) : ENNReal) ^ 3) *
          ((a : ENNReal) * (b : ENNReal))) :=
      eight_mul_sq_eq_copyLoss_mul_plankLower
        (lt_of_lt_of_le zero_lt_one hplank.2.2.2.1) hplank.1
    _ ≤ plankLongTubeFrostmanCopyLoss D.comparisonConstant a b *
        volume (D.family i : Set Space) := by
      exact mul_le_mul' le_rfl hplank.volume_lower_bound

/-- Same-index body enlargement transfers contained mass with the memberwise
volume ratio. The containment implication is in the useful direction:
`G i ⊆ K` forces `F i ⊆ K` whenever `F i ⊆ G i`. -/
theorem containedMass_bodyCover_le_mul
    {F G : ConvexFamily iota} {R : ENNReal}
    (hsubset : ∀ i, (F i : Set Space) ⊆ (G i : Set Space))
    (hvolume : ∀ i,
      volume (G i : Set Space) ≤ R * volume (F i : Set Space))
    (K : ConvexBody Space) :
    containedMass G K ≤ R * containedMass F K := by
  classical
  unfold containedMass
  calc
    (∑ i ∈ containedIndices G K, volume (G i : Set Space)) ≤
        ∑ i ∈ containedIndices G K,
          R * volume (F i : Set Space) := by
      apply Finset.sum_le_sum
      intro i _hi
      exact hvolume i
    _ = R * ∑ i ∈ containedIndices G K,
          volume (F i : Set Space) := by
      rw [Finset.mul_sum]
    _ ≤ R * ∑ i ∈ containedIndices F K,
          volume (F i : Set Space) := by
      gcongr
      intro i hi
      rw [mem_containedIndices] at hi ⊢
      exact (hsubset i).trans hi

/-- A same-index enlargement inside one common ambient transfers a Frostman
certificate with exactly the memberwise volume-ratio loss. -/
theorem isFrostmanIn_bodyCover
    {F G : ConvexFamily iota} {ambient : ConvexBody Space}
    {C R : ENNReal}
    (hF : IsFrostmanIn C F ambient)
    (hsubset : ∀ i, (F i : Set Space) ⊆ (G i : Set Space))
    (hvolume : ∀ i,
      volume (G i : Set Space) ≤ R * volume (F i : Set Space))
    (hGambient : ∀ i, (G i : Set Space) ⊆ (ambient : Set Space)) :
    IsFrostmanIn (R * C) G ambient := by
  refine ⟨hGambient, ?_⟩
  intro K hK
  have hsourceAmbient :
      containedMass F ambient ≤ containedMass G ambient := by
    rw [containedMass_eq_familyVolume_of_contained F ambient hF.1,
      containedMass_eq_familyVolume_of_contained G ambient hGambient]
    unfold familyVolume
    apply Finset.sum_le_sum
    intro i _hi
    exact measure_mono (hsubset i)
  calc
    containedMass G K * volume (ambient : Set Space) ≤
        (R * containedMass F K) * volume (ambient : Set Space) := by
      exact mul_le_mul' (containedMass_bodyCover_le_mul hsubset hvolume K) le_rfl
    _ = R *
        (containedMass F K * volume (ambient : Set Space)) := by
      ac_rfl
    _ ≤ R *
        (C * containedMass F ambient * volume (K : Set Space)) := by
      exact mul_le_mul' le_rfl (hF.2 K hK)
    _ = (R * C) * containedMass F ambient * volume (K : Set Space) := by
      ac_rfl
    _ ≤ (R * C) * containedMass G ambient * volume (K : Set Space) := by
      exact mul_le_mul' (mul_le_mul' le_rfl hsourceAmbient) le_rfl

/-- Concrete Frostman transfer from an actual shaded plank family to its
same-index genuine long-tube cover, provided both live in the displayed
common ambient. -/
theorem plankLongTubeCover_isFrostmanIn
    (D : ShadedConvexPlankFamily iota a b)
    (hb : b ≤ (2 : NNReal)⁻¹) {C : ENNReal}
    (hF : IsFrostmanIn C D.family D.ambient)
    (hcoverAmbient : ∀ i,
      ((plankLongTubeCoverFamily D).bodyFamily i : Set Space) ⊆
        (D.ambient : Set Space)) :
    IsFrostmanIn
      (plankLongTubeFrostmanCopyLoss D.comparisonConstant a b * C)
      (plankLongTubeCoverFamily D).bodyFamily D.ambient := by
  exact isFrostmanIn_bodyCover hF
    (sourcePlank_subset_longTubeCover D)
    (longTubeCover_volume_le_copyLoss_mul_source D hb)
    hcoverAmbient

#print axioms eight_mul_sq_eq_copyLoss_mul_plankLower
#print axioms longTubeCover_volume_le_copyLoss_mul_source
#print axioms containedMass_bodyCover_le_mul
#print axioms isFrostmanIn_bodyCover
#print axioms plankLongTubeCover_isFrostmanIn

end
end Family8PlankLongTubeFrostmanTransferV3
