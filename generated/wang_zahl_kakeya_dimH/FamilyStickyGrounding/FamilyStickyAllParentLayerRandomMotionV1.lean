import FamilyStickyGrounding.FamilyStickyAllParentLayerNumericsV1
import FamilyStickyGrounding.FamilyStickyRandomTestDependentChernoffV1
import FamilyStickyGrounding.FamilyStickySharedTranslationPackingExistenceV1
import FamilyStickyGrounding.FamilyStickySharedTranslationPackingNonemptyV1
import FamilyStickyGrounding.FamilyStickyActualSharedLocalExpectationV1
import FamilyStickyGrounding.FamilyStickyActualPaperSingleLoadAutomaticV1
import FamilyStickyGrounding.FamilyStickyPaperRandomMotionNondegeneracyV1

open Set MeasureTheory
open scoped BigOperators ENNReal NNReal

namespace FamilyStickyAllParentLayerRandomMotionV1

open LeanEval.Analysis.WangZahlKakeya
open Submission.Kakeya.ConvexGeometry
open Submission.Kakeya.ConvexGeometry.FrameBoxInducedCoveringGrowth
open FamilyStickyActualTubeTranslationV1
open FamilyStickyActualTubeTranslationGridV1
open FamilyStickyActualTubeTestDataV1
open FamilyStickyActualTubeTestDataV1.ActualTubeTestData
open FamilyStickyBoxCertifiedTubeTestDataV1.BoxCertifiedTubeTestData
open FamilyStickyAllParentLayerDataV1
open FamilyStickyAllParentLayerDataV1.AllParentLayerData
open FamilyStickyAllParentLayerNumericsV1.AllParentLayerData
open FamilyStickySharedTranslationPackingIncidenceV1.ActualTubeTranslationGrid
open FamilyStickySharedTranslationPackingExistenceV1
open FamilyStickySharedTranslationPackingExistenceV1.ActualTubeTranslationGrid
open FamilyStickyPaperRandomMotionNumericalChoicesV1.ActualTubeTestData
open FamilyStickyPaperRandomMotionNondegeneracyV1.ActualTubeTestData

noncomputable section
set_option linter.style.haveILetI false

/-!
# One shared random-motion family for every parent at a scale

This is the formal union-bound architecture of GWZ lines 1520--1524.  A single
maximal packing of `B_rho` supplies one outcome type.  Parent-local loads,
means, maximal concentrations, and caps remain test-dependent; the finite
Chernoff union runs over the dependent sum `(parent,test)`.  Thus every parent
is controlled by the same selected vectors, not by independently chosen
translation families.
-/

namespace AllParentLayerData

variable {delta : NNReal} {parent tubeIndex : Type*}
  [Fintype parent] [DecidableEq parent] [DecidableEq tubeIndex]

theorem exists_shared_vectors_good_for_all_parents
    (L : AllParentLayerData delta parent tubeIndex)
    (motionRadius : NNReal)
    (hdelta : delta <= (2 : NNReal)⁻¹) (hdeltaPos : 0 < delta)
    (hdeltaRadius : delta <= motionRadius)
    (hdelta0 : forall q, q ∈ L.activeTests ->
      delta <= (L.parentData q.1).side q.2 0)
    (hdelta1 : forall q, q ∈ L.activeTests ->
      delta <= (L.parentData q.1).side q.2 1)
    (hsourceScale : forall q, q ∈ L.activeTests ->
      SourceMeanScale (L.parentData q.1).data
        (L.parentData q.1).Cbox (L.parentData q.1).side
        motionRadius q.2) :
    (1 <= paperRepetitions L (L.paperMean motionRadius)) ∧
      exists omega : Fin (paperRepetitions L (L.paperMean motionRadius)) -> Space,
        (forall q, q ∈ L.activeTests ->
          (∑ j, (L.singleLoadAt q (omega j) : Real)) <=
            sourceTailParameter L * L.paperCap q) ∧
        (forall j, ‖omega j‖ <= (motionRadius : Real)) := by
  let C : PackingCertificate
      (Metric.closedBall (0 : Space) (motionRadius : Real)) delta :=
    Classical.choice
      (exists_motionBallPackingCertificate motionRadius delta hdeltaPos)
  haveI : Nonempty (↥C.centers) :=
    FamilyStickySharedTranslationPackingNonemptyV1.motionBallPackingCertificate_translation_nonempty C
  have hRadius : 0 < motionRadius := hdeltaPos.trans_le hdeltaRadius
  let mean : L.Test -> Real := L.paperMean motionRadius
  let J : Nat := paperRepetitions L mean
  let A : Real := sourceTailParameter L
  have hmean : forall q, q ∈ L.activeTests -> 0 <= mean q := by
    intro q _hq
    exact L.paperMean_nonneg motionRadius q
  have hunit : forall q, q ∈ L.activeTests -> mean q <= L.paperCap q := by
    intro q hq
    have hq' := (L.mem_activeTests_iff q).1 hq
    exact paperIncidenceMean_le_canonicalPaperSingleLoadCap
      (L.parentData q.1).data (L.parentData q.1).hasBoxDimensions
      hdeltaPos hRadius q.2 (hsourceScale q hq)
  have hJ : 1 <= J := by
    exact one_le_paperRepetitions_of_mean_le_cap L mean hunit
  have hcap : forall q, q ∈ L.activeTests -> 0 <= L.paperCap q := by
    intro q _hq
    unfold AllParentLayerData.paperCap
    unfold canonicalPaperSingleLoadCap
    exact ENNReal.toReal_nonneg
  obtain ⟨choice, hchoice⟩ :=
    FamilyStickyRandomTestDependentChernoffV1.exists_product_choice_load_le_A_mul_cap
      L.activeTests J
      (fun q (g : ↥C.centers) => (L.singleLoadAt q (g.1 : Space) : Real))
      L.paperCap mean A
      hcap hmean
      (fun _q _hq _g => Nat.cast_nonneg _)
      (fun q hq g => by
        let G := ofMotionBallPackingCertificate
          (L.parentSeedGrid q.1) C
        have hload :=
          FamilyStickyActualPaperSingleLoadAutomaticV1.ActualTubeTranslationGrid.singleLoad_real_le_paperSingleLoadCap
            G q.2 g hdelta hdeltaPos
        simpa [G, AllParentLayerData.singleLoadAt,
          AllParentLayerData.paperCap, parentSeedGrid] using hload)
      (fun q hq => by
        have hq' := (L.mem_activeTests_iff q).1 hq
        let G := ofMotionBallPackingCertificate
          (L.parentSeedGrid q.1) C
        have P : IsSharedTranslationPacking G delta motionRadius :=
          ofMotionBallPackingCertificate_isSharedTranslationPacking
            (L.parentSeedGrid q.1) hdeltaPos C
        have hsum :=
          FamilyStickyActualSharedLocalExpectationV1.sum_singleLoad_le_card_mul_mean
            P (L.parentData q.1).hasBoxDimensions q.2 hq'.2
            (L.paperMean_nonneg motionRadius q)
            (hdelta0 q hq) (hdelta1 q hq) hdeltaRadius
            (explicit_297_le_motionRadius_sq_mul_paperIncidenceMean
              (L.parentData q.1).data (L.parentData q.1).side hRadius q.2)
        simpa [G, mean, AllParentLayerData.paperMean,
          AllParentLayerData.singleLoadAt, parentSeedGrid] using hsum)
      (paperRepetitions_mul_mean_le_cap L mean hmean)
      (sourceTailRoom L)
  refine ⟨hJ, fun j => ((choice j).1 : Space), ?_, ?_⟩
  · intro q hq
    simpa [J, A, FamilyStickyRandomFiniteChernoffV3.productLoad] using hchoice q hq
  · intro j
    have hj : ((choice j).1 : Space) ∈
        Metric.closedBall (0 : Space) (motionRadius : Real) :=
      C.centers_subset (choice j).2
    simpa [Metric.mem_closedBall, dist_zero_right] using hj

#print axioms exists_shared_vectors_good_for_all_parents

end AllParentLayerData

end
end FamilyStickyAllParentLayerRandomMotionV1
