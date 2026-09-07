import Family8Grounding.Family8FiniteRandomRigidMotionPaperFixedJohnCatalogueCardIdentityV2
import Family8Grounding.Family8FiniteRandomRigidMotionPaperFixedJohnCapVsLongMeanV2
import Mathlib.Tactic

set_option autoImplicit false
set_option warningAsError true

open Set MeasureTheory
open scoped ENNReal NNReal BigOperators

namespace Family8FiniteRandomRigidMotionPaperFixedJohnCatalogueCapIdentityV1

open LeanEval.Analysis.WangZahlKakeya
open Submission.Kakeya.ConvexGeometry
open Family8KatzTaoFrostmanPropertiesV1
open Family8FiniteRandomRigidMotionPaperTranslationBodyGridV1
open Family8FiniteRandomRigidMotionPaperFixedJohnConflictGridV4
open Family8FiniteRandomRigidMotionPaperFixedJohnAutomaticConflictCapV2
open Family8FiniteRandomRigidMotionPaperFixedJohnBoundedPackingMeanV5
open Family8FiniteRandomRigidMotionPaperFixedJohnCapVsLongMeanV2
open Family8PolynomialJohnFrameBoxTestNetV1
open FamilyStickyActualPaperSingleLoadProducerV1.ActualTubeTranslationGrid

noncomputable section

/-- Exact maximal-concentration formula for a fixed-John catalogue test,
before converting the selector's real tail estimate back to `ENNReal`. -/
theorem fixedJohnTranslationPaperCap_catalogueIndex
    {delta : NNReal} {iota : Type}
    [Fintype iota] [DecidableEq iota]
    (D : ActualTubeDatum delta iota) (hD : D.IsAdmissible)
    (q : CatalogueIndex (delta / 8)
      (admissibleNormalizedRadiusPos hD)) :
    fixedJohnTranslationPaperCap
        (fixedJohnPackingGridVector D hD) D hD
        (normalizedJohnCatalogueIndex q) =
      (fixedJohnPackingMaximalConcentration D hD *
        volume (representativeTestBody (delta / 8)
          (admissibleNormalizedRadiusPos hD) q : Set Space) /
        (((delta / 8 : NNReal) : ENNReal) ^ 2 / 2)).toReal := by
  unfold fixedJohnTranslationPaperCap normalizedTranslationBodyPaperCap
  change
    (maximalConcentration
        (activeFamily (fixedJohnPackingNormalizedGrid D hD)) *
      volume (fixedJohnCatalogueBody hD
        (normalizedJohnCatalogueIndex q) : Set Space) /
      (((delta / 8 : NNReal) : ENNReal) ^ 2 / 2)).toReal = _
  rw [fixedJohnPacking_maximalConcentration_eq_normalized,
    fixedJohnCatalogueBody, normalizedJohnCatalogueBody_index]

#print axioms fixedJohnTranslationPaperCap_catalogueIndex

end
end Family8FiniteRandomRigidMotionPaperFixedJohnCatalogueCapIdentityV1
