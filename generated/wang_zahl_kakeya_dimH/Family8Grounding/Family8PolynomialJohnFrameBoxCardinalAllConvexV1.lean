import Family8Grounding.Family8Def212ConvexWolffAtEveryScaleV2
import Family8Grounding.Family8PolynomialJohnFrameBoxAllConvexV1
import Mathlib.Tactic

set_option autoImplicit false
set_option warningAsError true
set_option linter.unusedSectionVars false
set_option maxHeartbeats 2000000

open Set MeasureTheory
open scoped ENNReal NNReal

namespace Family8PolynomialJohnFrameBoxCardinalAllConvexV1

open LeanEval.Analysis.WangZahlKakeya
open Submission.Kakeya.ConvexGeometry
open Family8Def212ConvexWolffAtEveryScaleV2
open Family8PolynomialJohnFrameBoxTestNetV1
open Family8PolynomialJohnFrameBoxContainmentV1
open Family8PolynomialJohnFrameBoxVolumeV2
open Family8PolynomialJohnFrameBoxAllConvexV1

noncomputable section

/-!
# Cardinal John-catalogue tests control all convex containers

This is the cardinal-normalized analogue of
`isKatzTao_of_polynomialJohnCatalogue`.  It is the exact bridge needed by
Definition 2.12: controlling the number of family members captured by every
finite John-catalogue test controls the number captured by an arbitrary
convex body, with only the already proved universal catalogue-volume loss.
-/

/-- Fixed cardinal control on the polynomial occupied catalogue implies the
literal cardinal-normalized Convex Wolff axioms for every convex body. -/
theorem satisfiesConvexWolffAxioms_of_polynomialJohnCatalogue
    {delta : NNReal} (hdelta : 0 < delta)
    {index : Type*} [Fintype index] [DecidableEq index]
    (T : index → Tube delta)
    (hunit : ∀ i, (T i).carrier ⊆ Metric.closedBall (0 : Space) 1)
    (A : ENNReal)
    (hfinite : ∀ q : CatalogueIndex delta hdelta,
      ((containedIndices (tubeBodyFamily T)
          (representativeTestBody delta hdelta q)).card : ENNReal) ≤
        A *
          volume (representativeTestBody delta hdelta q : Set Space) *
          (Fintype.card index : ENNReal)) :
    SatisfiesConvexWolffAxioms
      (A * johnCatalogueVolumeConstant) (tubeBodyFamily T) := by
  classical
  intro K
  let captured := containedIndices (tubeBodyFamily T) K
  by_cases hcaptured : captured.Nonempty
  · obtain ⟨i, hi⟩ := hcaptured
    have hiK : (T i).carrier ⊆ (K : Set Space) := by
      have hi' : i ∈ containedIndices (tubeBodyFamily T) K := hi
      rw [Submission.Kakeya.ConvexFactoring.mem_containedIndices] at hi'
      simpa only [coe_tubeBodyFamily] using hi'
    let p := CapturedJohnParameter.ofCapturedTube hdelta K (T i) hiK (hunit i)
    let q : CatalogueIndex delta hdelta := parameterCode hdelta p
    have hsubset : containedIndices (tubeBodyFamily T) K ⊆
        containedIndices (tubeBodyFamily T)
          (representativeTestBody delta hdelta q) := by
      intro j hj
      rw [Submission.Kakeya.ConvexFactoring.mem_containedIndices] at hj ⊢
      rw [coe_tubeBodyFamily] at hj ⊢
      exact capturedTube_subset_catalogueTest hdelta K (T i) hiK
        (hunit i) (T j) hj (hunit j)
    have hcard :
        ((containedIndices (tubeBodyFamily T) K).card : ENNReal) ≤
          ((containedIndices (tubeBodyFamily T)
            (representativeTestBody delta hdelta q)).card : ENNReal) := by
      exact_mod_cast Finset.card_le_card hsubset
    have htestVolume :
        volume (representativeTestBody delta hdelta q : Set Space) ≤
          johnCatalogueVolumeConstant * volume (K : Set Space) := by
      exact catalogueTest_volume_le_originalBody hdelta K (T i) hiK (hunit i)
    calc
      ((containedIndices (tubeBodyFamily T) K).card : ENNReal) ≤
          ((containedIndices (tubeBodyFamily T)
            (representativeTestBody delta hdelta q)).card : ENNReal) := hcard
      _ ≤ A * volume
            (representativeTestBody delta hdelta q : Set Space) *
          (Fintype.card index : ENNReal) := hfinite q
      _ ≤ A * (johnCatalogueVolumeConstant * volume (K : Set Space)) *
          (Fintype.card index : ENNReal) := by
        gcongr
      _ = (A * johnCatalogueVolumeConstant) * volume (K : Set Space) *
          (Fintype.card index : ENNReal) := by
        ring
  · have hcapturedEmpty : captured = ∅ :=
      Finset.not_nonempty_iff_eq_empty.mp hcaptured
    change ((containedIndices (tubeBodyFamily T) K).card : ENNReal) ≤ _
    rw [show containedIndices (tubeBodyFamily T) K = ∅ from hcapturedEmpty]
    simp

#print axioms satisfiesConvexWolffAxioms_of_polynomialJohnCatalogue

end
end Family8PolynomialJohnFrameBoxCardinalAllConvexV1
