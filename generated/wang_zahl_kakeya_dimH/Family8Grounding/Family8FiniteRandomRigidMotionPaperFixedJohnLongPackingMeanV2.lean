import Family8Grounding.Family8FiniteRandomRigidMotionPaperFixedJohnLongAxisRelabelV4
import Mathlib.Tactic

open Set MeasureTheory
open scoped ENNReal NNReal BigOperators InnerProductSpace

namespace Family8FiniteRandomRigidMotionPaperFixedJohnLongPackingMeanV2

open LeanEval.Analysis.WangZahlKakeya
open Submission.Kakeya.ConvexGeometry
open Family8KatzTaoFrostmanPropertiesV1
open Family8FiniteRandomRigidMotionPaperTranslationBodyGridV1
open Family8FiniteRandomRigidMotionPaperFixedJohnAutomaticConflictCapV2
open Family8FiniteRandomRigidMotionPaperFixedJohnExactMeanSelectorV4
open Family8FiniteRandomRigidMotionPaperFixedJohnBoundedPackingMeanV5
open Family8FiniteRandomRigidMotionPaperFixedJohnLongAxisRelabelV4
open FamilyStickySharedTranslationPackingIncidenceV1.ActualTubeTranslationGrid

noncomputable section

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 4000000

/-! The carrier-preserving relabeling puts a constant-length side in
coordinate `2`; this is the honest two-short-side shared-packing mean. -/

def fixedJohnLongPackingMean
    {delta : NNReal} {iota : Type}
    [Fintype iota] [DecidableEq iota]
    (D : ActualTubeDatum delta iota) (hD : D.IsAdmissible)
    (K : FixedJohnTest D hD) : Real :=
  (297 * (Fintype.card iota : Real) *
      (fixedJohnLongSide D hD K 0 : Real) *
      (fixedJohnLongSide D hD K 1 : Real)) /
    (((1 / 8 : NNReal) : Real) ^ 2)

theorem fixedJohnLongPackingMean_nonneg
    {delta : NNReal} {iota : Type}
    [Fintype iota] [DecidableEq iota]
    (D : ActualTubeDatum delta iota) (hD : D.IsAdmissible)
    (K : FixedJohnTest D hD) :
    0 <= fixedJohnLongPackingMean D hD K := by
  unfold fixedJohnLongPackingMean
  positivity

theorem fixedJohnPackingFiniteMean_le_longPackingMean
    {delta : NNReal} {iota : Type}
    [Fintype iota] [DecidableEq iota]
    (D : ActualTubeDatum delta iota) (hD : D.IsAdmissible)
    (K : FixedJohnTest D hD) :
    fixedJohnFiniteMean (fixedJohnPackingGridVector D hD) D hD K <=
      fixedJohnLongPackingMean D hD K := by
  let G := fixedJohnPackingNormalizedGrid D hD
  let P : IsSharedTranslationPacking G (delta / 8) (1 / 8 : NNReal) :=
    fixedJohnPacking_isSharedTranslationPacking D hD
  have hdim : forall L, HasBoxDimensions 1
      (fixedJohnLongSide D hD L) (G.testBody L) := by
    intro L
    simpa only [G, fixedJohnPackingNormalizedGrid,
      normalizedTranslationBodyGrid] using
      fixedJohnCatalogueBody_hasLongBoxDimensions D hD L
  have hnormalized :
      297 * (G.tubes.card : Real) *
          (fixedJohnLongSide D hD K 0 : Real) *
          (fixedJohnLongSide D hD K 1 : Real) <=
        (((1 / 8 : NNReal) : Real) ^ 2) *
          fixedJohnLongPackingMean D hD K := by
    simp only [G, fixedJohnPackingNormalizedGrid,
      normalizedTranslationBodyGrid, Finset.card_univ]
    unfold fixedJohnLongPackingMean
    norm_num [div_eq_mul_inv]
    ring_nf
    exact le_rfl
  have havg :=
    FamilyStickyActualSharedLocalExpectationV1.average_singleLoad_le_mean
      P hdim K (Finset.mem_univ K)
      (fixedJohnLongPackingMean_nonneg D hD K)
      (normalizedRadius_le_fixedJohnLongSide D hD K 0)
      (normalizedRadius_le_fixedJohnLongSide D hD K 1)
      (normalizedRadius_le_eighth hD) hnormalized
  have hload (g : FixedJohnPackingTranslation D hD) :
      G.singleLoad K g =
        normalizedTranslationBodyLoadNat
          (fixedJohnPackingGridVector D hD) D
          (fixedJohnCatalogueBody hD) K g := by
    exact normalizedTranslationBodyGrid_singleLoad
      (fixedJohnPackingGridVector D hD) D
      (fixedJohnCatalogueBody hD) Finset.univ K g
  simpa only [fixedJohnFiniteMean, hload] using havg

#print axioms fixedJohnLongPackingMean_nonneg
#print axioms fixedJohnPackingFiniteMean_le_longPackingMean

end
end Family8FiniteRandomRigidMotionPaperFixedJohnLongPackingMeanV2
