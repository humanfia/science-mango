import FamilyStickyGrounding.FamilyStickyActualSharedPaperRandomMotionV1
import FamilyStickyGrounding.FamilyStickyActualPaperSingleLoadAutomaticV1

open Set MeasureTheory
open scoped BigOperators ENNReal NNReal

namespace FamilyStickyActualSharedPaperRandomMotionAutomaticV1

open LeanEval.Analysis.WangZahlKakeya
open Submission.Kakeya.ConvexGeometry
open FamilyStickyActualTubeTranslationV1
open FamilyStickyActualTubeTranslationGridV1
open FamilyStickyActualPaperSingleLoadProducerV1.ActualTubeTranslationGrid
open FamilyStickySharedTranslationPackingIncidenceV1.ActualTubeTranslationGrid

noncomputable section

/-!
# Callback-free faithful shared random motion

This is the fully produced endpoint: finite-family cardinality automatically
discharges maximal-concentration finiteness, so no global cap, per-outcome
concentration bound, mass budget, or finiteness callback remains.
-/

namespace ActualTubeTranslationGrid

variable {delta : NNReal} {translation tubeIndex : Type*}
  [Fintype translation] [Nonempty translation]
  [DecidableEq translation] [DecidableEq tubeIndex]

theorem exists_shared_translations_with_automaticPaperCaps_and_radius
    (G : ActualTubeTranslationGrid delta translation tubeIndex)
    {mesh motionRadius : NNReal}
    (P : IsSharedTranslationPacking G mesh motionRadius)
    {C : NNReal} {side : Fin G.testCard -> Fin 3 -> NNReal}
    (hdim : forall K, HasBoxDimensions C (side K) (G.testBody K))
    (repetitions : Nat) (mean : Fin G.testCard -> Real) (A : Real)
    (hdelta : delta <= (2 : NNReal)⁻¹) (hdeltaPos : 0 < delta)
    (hmean : forall K, K ∈ G.activeTests -> 0 <= mean K)
    (hscale : forall K, K ∈ G.activeTests ->
      (repetitions : Real) * mean K <= paperSingleLoadCap G K)
    (hmesh0 : forall K, K ∈ G.activeTests -> mesh <= side K 0)
    (hmesh1 : forall K, K ∈ G.activeTests -> mesh <= side K 1)
    (hmeshR : mesh <= motionRadius)
    (hnormalized : forall K, K ∈ G.activeTests ->
      297 * (G.tubes.card : Real) * (side K 0 : Real) *
          (side K 1 : Real) <=
        (motionRadius : Real) ^ 2 * mean K)
    (htailRoom :
      (G.activeTests.card : Real) * Real.exp (Real.exp 1 - 1) <
        Real.exp A) :
    exists omega : Fin repetitions -> translation,
      (forall K, K ∈ G.activeTests ->
        (∑ j, (G.singleLoad K (omega j) : Real)) <=
          A * paperSingleLoadCap G K) ∧
      (forall j i,
        (translateTube (G.tube i) (G.gridVector (omega j))).carrier ⊆
          Metric.cthickening (motionRadius : Real) (G.tube i).carrier) := by
  exact
    FamilyStickyActualSharedPaperRandomMotionV1.ActualTubeTranslationGrid.exists_shared_translations_with_paperCaps_and_radius
      G P hdim repetitions mean A hdelta hdeltaPos
      (FamilyStickyActualPaperSingleLoadAutomaticV1.ActualTubeTranslationGrid.activeFamily_maximalConcentration_lt_top G)
      hmean hscale hmesh0 hmesh1 hmeshR hnormalized htailRoom

/-- Source scale-order wrapper with `mesh <= scaleDelta <= k_i <= rho`. -/
theorem exists_shared_translations_with_automaticPaperCaps_of_scaleOrder
    (G : ActualTubeTranslationGrid delta translation tubeIndex)
    {mesh motionRadius scaleDelta : NNReal}
    (P : IsSharedTranslationPacking G mesh motionRadius)
    {C : NNReal} {side : Fin G.testCard -> Fin 3 -> NNReal}
    (hdim : forall K, HasBoxDimensions C (side K) (G.testBody K))
    (repetitions : Nat) (mean : Fin G.testCard -> Real) (A : Real)
    (hdelta : delta <= (2 : NNReal)⁻¹) (hdeltaPos : 0 < delta)
    (hmean : forall K, K ∈ G.activeTests -> 0 <= mean K)
    (hscale : forall K, K ∈ G.activeTests ->
      (repetitions : Real) * mean K <= paperSingleLoadCap G K)
    (hmeshDelta : mesh <= scaleDelta) (hmeshR : mesh <= motionRadius)
    (hdelta0 : forall K, K ∈ G.activeTests -> scaleDelta <= side K 0)
    (hdelta1 : forall K, K ∈ G.activeTests -> scaleDelta <= side K 1)
    (_hzeroR : forall K, K ∈ G.activeTests -> side K 0 <= motionRadius)
    (_honeR : forall K, K ∈ G.activeTests -> side K 1 <= motionRadius)
    (hnormalized : forall K, K ∈ G.activeTests ->
      297 * (G.tubes.card : Real) * (side K 0 : Real) *
          (side K 1 : Real) <=
        (motionRadius : Real) ^ 2 * mean K)
    (htailRoom :
      (G.activeTests.card : Real) * Real.exp (Real.exp 1 - 1) <
        Real.exp A) :
    exists omega : Fin repetitions -> translation,
      (forall K, K ∈ G.activeTests ->
        (∑ j, (G.singleLoad K (omega j) : Real)) <=
          A * paperSingleLoadCap G K) ∧
      (forall j i,
        (translateTube (G.tube i) (G.gridVector (omega j))).carrier ⊆
          Metric.cthickening (motionRadius : Real) (G.tube i).carrier) := by
  apply exists_shared_translations_with_automaticPaperCaps_and_radius
    G P hdim repetitions mean A hdelta hdeltaPos hmean hscale
  · intro K hK
    exact hmeshDelta.trans (hdelta0 K hK)
  · intro K hK
    exact hmeshDelta.trans (hdelta1 K hK)
  · exact hmeshR
  · exact hnormalized
  · exact htailRoom

#print axioms exists_shared_translations_with_automaticPaperCaps_and_radius
#print axioms exists_shared_translations_with_automaticPaperCaps_of_scaleOrder

end ActualTubeTranslationGrid

end
end FamilyStickyActualSharedPaperRandomMotionAutomaticV1
