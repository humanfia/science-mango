import Family8Grounding.Family8FiniteRandomRigidMotionPaperFixedJohnCopyTransportCoreV1
import Family8Grounding.Family8PolynomialJohnFrameBoxCardinalAllConvexV1
import Mathlib.Tactic

set_option autoImplicit false
set_option warningAsError true

open Set MeasureTheory
open scoped ENNReal NNReal BigOperators

namespace Family8FiniteRandomRigidMotionPaperFixedJohnCatalogueCardIdentityV2

open LeanEval.Analysis.WangZahlKakeya
open Submission.Kakeya.ConvexGeometry
open Submission.Kakeya.ConvexFactoring
open Submission.Kakeya.Uniformity
open Family8KatzTaoFrostmanPropertiesV1
open Family8GeneralizedFrostmanMultiplicityV1
open Family8FiniteRandomRigidMotionIncidenceV1
open Family8FiniteRandomRigidMotionB2NormalizedDatumV1
open Family8FiniteRandomRigidMotionPaperTranslationBodyGridV1
open Family8FiniteRandomRigidMotionPaperFixedJohnConflictGridV4
open Family8FiniteRandomRigidMotionPaperFixedJohnAutomaticConflictCapV2
open Family8PolynomialJohnFrameBoxTestNetV1

noncomputable section

/-! Exact identity between the selector's summed loads and the cardinality
captured from the literal normalized copied family. -/

theorem normalizedTranslationBodyIndices_eq_containedIndices
    {translation iota : Type}
    [Fintype translation] [DecidableEq translation]
    [Fintype iota] [DecidableEq iota]
    {delta : NNReal} {testCard repetitions : Nat}
    (gridVector : translation -> Space)
    (D : ActualTubeDatum delta iota)
    (testBody : Fin testCard -> ConvexBody Space)
    (omega : Fin repetitions -> translation)
    (K : Fin testCard) :
    normalizedTranslationBodyIndices gridVector D testBody omega K =
      containedIndices
        (eighthNormalizedDatum
          (indexedRigidCopyDatum
            (fun j => translationRigidMotion (gridVector (omega j))) D)).family.bodyFamily
        (testBody K) := by
  classical
  ext b
  simp only [normalizedTranslationBodyIndices, Finset.mem_filter,
    Finset.mem_univ, true_and, mem_containedIndices,
    UniformTubeFamily.bodyFamily_apply, Tube.coe_body,
    eighthNormalizedDatum_family, eighthNormalizedTubeFamily_tubes,
    indexedRigidCopyDatum, indexedRigidCopyTubeFamily_tubes]

theorem containedIndices_card_eq_sum_normalizedTranslationBodyLoadNat
    {translation iota : Type}
    [Fintype translation] [DecidableEq translation]
    [Fintype iota] [DecidableEq iota]
    {delta : NNReal} {testCard repetitions : Nat}
    (gridVector : translation -> Space)
    (D : ActualTubeDatum delta iota)
    (testBody : Fin testCard -> ConvexBody Space)
    (omega : Fin repetitions -> translation)
    (K : Fin testCard) :
    (containedIndices
      (eighthNormalizedDatum
        (indexedRigidCopyDatum
          (fun j => translationRigidMotion (gridVector (omega j))) D)).family.bodyFamily
      (testBody K)).card =
        ∑ j, normalizedTranslationBodyLoadNat
          gridVector D testBody K (omega j) := by
  rw [← normalizedTranslationBodyIndices_eq_containedIndices]
  exact normalizedTranslationBodyIndices_card_eq_sum_load
    gridVector D testBody omega K

theorem fixedJohnCatalogue_containedIndices_card_eq_sum_load
    {translation iota : Type}
    [Fintype translation] [DecidableEq translation]
    [Fintype iota] [DecidableEq iota]
    {delta : NNReal} {repetitions : Nat}
    (gridVector : translation -> Space)
    (D : ActualTubeDatum delta iota) (hD : D.IsAdmissible)
    (omega : Fin repetitions -> translation)
    (q : CatalogueIndex (delta / 8)
      (admissibleNormalizedRadiusPos hD)) :
    (containedIndices
      (eighthNormalizedDatum
        (indexedRigidCopyDatum
          (fun j => translationRigidMotion (gridVector (omega j))) D)).family.bodyFamily
      (representativeTestBody (delta / 8)
        (admissibleNormalizedRadiusPos hD) q)).card =
      ∑ j, normalizedTranslationBodyLoadNat gridVector D
        (fixedJohnCatalogueBody hD) (normalizedJohnCatalogueIndex q)
        (omega j) := by
  simpa only [fixedJohnCatalogueBody, normalizedJohnCatalogueBody_index] using
    containedIndices_card_eq_sum_normalizedTranslationBodyLoadNat
      gridVector D (fixedJohnCatalogueBody hD) omega
        (normalizedJohnCatalogueIndex q)

#print axioms normalizedTranslationBodyIndices_eq_containedIndices
#print axioms containedIndices_card_eq_sum_normalizedTranslationBodyLoadNat
#print axioms fixedJohnCatalogue_containedIndices_card_eq_sum_load

end
end Family8FiniteRandomRigidMotionPaperFixedJohnCatalogueCardIdentityV2
