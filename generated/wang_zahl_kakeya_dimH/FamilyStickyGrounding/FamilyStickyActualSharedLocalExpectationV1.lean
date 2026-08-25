import FamilyStickyGrounding.FamilyStickyActualSharedLocalFeasibilityV1

open Set MeasureTheory
open scoped BigOperators ENNReal NNReal

namespace FamilyStickyActualSharedLocalExpectationV1

open LeanEval.Analysis.WangZahlKakeya
open Submission.Kakeya.ConvexGeometry
open FamilyStickyActualTubeTranslationGridV1
open FamilyStickySharedTranslationPackingIncidenceV1.ActualTubeTranslationGrid
open FamilyStickyRandomTranslationGridAdapterV1

noncomputable section

/-!
# Fixed-test expectation budget from actual shared-grid incidences

For a fixed Appendix test body `K`, finite uniform expectation is the sum of
the literal actual loads divided by the number of shared packing centers.
Double counting turns this into the per-tube grid hit count.  The local
`k_0 k_1 rho` packing bound and the explicit `297` feasibility inequality then
produce the desired mean bound.  No expectation estimate is accepted as a
callback.
-/

variable {delta : NNReal} {translation tubeIndex : Type*}
  [Fintype translation]
  [DecidableEq translation] [DecidableEq tubeIndex]
  {G : ActualTubeTranslationGrid delta translation tubeIndex}
  {mesh motionRadius : NNReal}

/-- Sum form of the fixed-K expectation bound. -/
theorem sum_singleLoad_le_card_mul_mean
    (P : IsSharedTranslationPacking G mesh motionRadius)
    {C : NNReal} {side : Fin G.testCard -> Fin 3 -> NNReal}
    (hdim : forall K, HasBoxDimensions C (side K) (G.testBody K))
    (K : Fin G.testCard) (hK : K ∈ G.activeTests)
    {mean : Real} (hmean : 0 ≤ mean)
    (hmesh0 : mesh ≤ side K 0) (hmesh1 : mesh ≤ side K 1)
    (hmeshR : mesh ≤ motionRadius)
    (hnormalized :
      297 * (G.tubes.card : Real) * (side K 0 : Real) *
          (side K 1 : Real) ≤
        (motionRadius : Real) ^ 2 * mean) :
    (∑ g : translation, (G.singleLoad K g : Real)) ≤
      (Fintype.card translation : Real) * mean := by
  let B :=
    FamilyStickyFrameBoxCertificateExtractionV1.ActualTubeTranslationGrid.testOuterBox
      G hdim K
  have hside : B.side = side K :=
    FamilyStickyFrameBoxCertificateExtractionV1.ActualTubeTranslationGrid.testOuterBox_side
      G hdim K
  have hgrid : forall i, i ∈ G.tubes ->
      G.toIncidenceModel.gridHitsTube K i ≤
        FamilyStickyActualSharedLocalPointBudgetV1.ActualTubeTranslationGrid.IsSharedTranslationPacking.localPointBudget
          P B := by
    intro i hi
    rw [G.toIncidenceModel_gridHitsTube]
    exact
      FamilyStickyActualSharedLocalPointBudgetV1.ActualTubeTranslationGrid.IsSharedTranslationPacking.tubeHitCount_le_localPointBudget_of_boxDimensions
        P hdim K hK i hi
  have hbalance :
      (G.toIncidenceModel.tubes.card : Real) *
          (FamilyStickyActualSharedLocalPointBudgetV1.ActualTubeTranslationGrid.IsSharedTranslationPacking.localPointBudget
            P B : Real) ≤
        (Fintype.card translation : Real) * mean := by
    rw [G.toIncidenceModel_tubes]
    apply FamilyStickyActualSharedLocalFeasibilityV1.balance_of_explicit_297
      P B
    · rw [hside]
      exact hmesh0
    · rw [hside]
      exact hmesh1
    · exact hmeshR
    · exact hmean
    · rw [hside]
      exact hnormalized
  have hsum :=
    FamilyStickyRandomTranslationGridAdapterV1.TranslationIncidenceModel.sum_load_le_of_gridHitsTube_le
      G.toIncidenceModel K
      (FamilyStickyActualSharedLocalPointBudgetV1.ActualTubeTranslationGrid.IsSharedTranslationPacking.localPointBudget
        P B)
      mean hgrid hbalance
  simpa only [G.toIncidenceModel_load] using hsum

/-- Literal finite-uniform expectation form. -/
theorem average_singleLoad_le_mean
    [Nonempty translation]
    (P : IsSharedTranslationPacking G mesh motionRadius)
    {C : NNReal} {side : Fin G.testCard -> Fin 3 -> NNReal}
    (hdim : forall K, HasBoxDimensions C (side K) (G.testBody K))
    (K : Fin G.testCard) (hK : K ∈ G.activeTests)
    {mean : Real} (hmean : 0 ≤ mean)
    (hmesh0 : mesh ≤ side K 0) (hmesh1 : mesh ≤ side K 1)
    (hmeshR : mesh ≤ motionRadius)
    (hnormalized :
      297 * (G.tubes.card : Real) * (side K 0 : Real) *
          (side K 1 : Real) ≤
        (motionRadius : Real) ^ 2 * mean) :
    (∑ g : translation, (G.singleLoad K g : Real)) /
        (Fintype.card translation : Real) ≤ mean := by
  have hcard : 0 < (Fintype.card translation : Real) := by
    exact_mod_cast Fintype.card_pos
  apply (div_le_iff₀ hcard).2
  simpa [mul_comm] using
    (sum_singleLoad_le_card_mul_mean P hdim K hK hmean
      hmesh0 hmesh1 hmeshR hnormalized)

#print axioms sum_singleLoad_le_card_mul_mean
#print axioms average_singleLoad_le_mean

end


end FamilyStickyActualSharedLocalExpectationV1
