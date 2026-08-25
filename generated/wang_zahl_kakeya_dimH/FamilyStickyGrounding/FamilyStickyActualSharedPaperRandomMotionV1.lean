import FamilyStickyGrounding.FamilyStickyActualPaperSingleLoadProducerV1
import FamilyStickyGrounding.FamilyStickyActualSharedLocalExpectationV1
import FamilyStickyGrounding.FamilyStickyRandomTestDependentChernoffV1

open Set MeasureTheory
open scoped BigOperators ENNReal NNReal

namespace FamilyStickyActualSharedPaperRandomMotionV1

open LeanEval.Analysis.WangZahlKakeya
open Submission.Kakeya.ConvexGeometry
open FamilyStickyActualTubeTranslationV1
open FamilyStickyActualTubeTranslationGridV1
open FamilyStickyActualPaperSingleLoadProducerV1.ActualTubeTranslationGrid
open FamilyStickySharedTranslationPackingIncidenceV1.ActualTubeTranslationGrid

noncomputable section

/-!
# Faithful shared random motion with the paper's test-dependent caps

This endpoint follows GWZ Appendix lines 2681--2706 literally at the level of
finite translations.  For each active test `K` it uses

`cap K = toReal (Delta_max(T) * |K| / (delta^2 / 2))`.

The cap is produced from the untranslated active family; common translation
invariance removes every per-outcome concentration/mass assumption.  The mean
sum is produced by actual translation--tube double counting and the local
`k_0 k_1 rho` incidence estimate.  Test-dependent Chernoff normalization then
selects one `omega` which has both all-test load bounds and the motion-radius
property.

In particular the signature contains no global worst-case `cap`, no per-`g`
`hmax`, and no `hmassBudget`.
-/

namespace ActualTubeTranslationGrid

variable {delta : NNReal} {translation tubeIndex : Type*}
  [Fintype translation] [Nonempty translation]
  [DecidableEq translation] [DecidableEq tubeIndex]

theorem exists_shared_translations_with_paperCaps_and_radius
    (G : ActualTubeTranslationGrid delta translation tubeIndex)
    {mesh motionRadius : NNReal}
    (P : IsSharedTranslationPacking G mesh motionRadius)
    {C : NNReal} {side : Fin G.testCard -> Fin 3 -> NNReal}
    (hdim : forall K, HasBoxDimensions C (side K) (G.testBody K))
    (repetitions : Nat) (mean : Fin G.testCard -> Real) (A : Real)
    (hdelta : delta <= (2 : NNReal)⁻¹) (hdeltaPos : 0 < delta)
    (hbase : maximalConcentration
      (FamilyStickyActualPaperSingleLoadProducerV1.ActualTubeTranslationGrid.activeFamily G) < ∞)
    (hmean : forall K, K ∈ G.activeTests -> 0 <= mean K)
    (hscale : forall K, K ∈ G.activeTests ->
      (repetitions : Real) * mean K <=
        paperSingleLoadCap G K)
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
  obtain ⟨omega, hload⟩ :=
    FamilyStickyRandomTestDependentChernoffV1.exists_product_choice_load_le_A_mul_cap
      G.activeTests repetitions
      (fun K g => (G.singleLoad K g : Real))
      (paperSingleLoadCap G) mean A
      (fun _K _hK => ENNReal.toReal_nonneg)
      hmean
      (fun _K _hK _g => Nat.cast_nonneg _)
      (fun K _hK g =>
        singleLoad_real_le_paperSingleLoadCap
          G K g hdelta hdeltaPos hbase)
      (fun K hK =>
        FamilyStickyActualSharedLocalExpectationV1.sum_singleLoad_le_card_mul_mean
          P hdim K hK (hmean K hK) (hmesh0 K hK) (hmesh1 K hK)
          hmeshR (hnormalized K hK))
      hscale htailRoom
  refine ⟨omega, hload, ?_⟩
  intro j i
  exact
    FamilyStickyActualSharedLocalPointBudgetV1.ActualTubeTranslationGrid.IsSharedTranslationPacking.translateTube_carrier_subset_cthickening
      P i (omega j)

/-- Source scale-order wrapper with `mesh <= scaleDelta <= k_i <= rho`. -/
theorem exists_shared_translations_with_paperCaps_of_scaleOrder
    (G : ActualTubeTranslationGrid delta translation tubeIndex)
    {mesh motionRadius scaleDelta : NNReal}
    (P : IsSharedTranslationPacking G mesh motionRadius)
    {C : NNReal} {side : Fin G.testCard -> Fin 3 -> NNReal}
    (hdim : forall K, HasBoxDimensions C (side K) (G.testBody K))
    (repetitions : Nat) (mean : Fin G.testCard -> Real) (A : Real)
    (hdelta : delta <= (2 : NNReal)⁻¹) (hdeltaPos : 0 < delta)
    (hbase : maximalConcentration
      (FamilyStickyActualPaperSingleLoadProducerV1.ActualTubeTranslationGrid.activeFamily G) < ∞)
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
  apply exists_shared_translations_with_paperCaps_and_radius
    G P hdim repetitions mean A hdelta hdeltaPos hbase hmean hscale
  · intro K hK
    exact hmeshDelta.trans (hdelta0 K hK)
  · intro K hK
    exact hmeshDelta.trans (hdelta1 K hK)
  · exact hmeshR
  · exact hnormalized
  · exact htailRoom

#print axioms exists_shared_translations_with_paperCaps_and_radius
#print axioms exists_shared_translations_with_paperCaps_of_scaleOrder

end ActualTubeTranslationGrid

end


end FamilyStickyActualSharedPaperRandomMotionV1
