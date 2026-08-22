import FamilyStickyGrounding.FamilyStickyActualSingleLoadCapV1

open Set MeasureTheory
open scoped BigOperators ENNReal NNReal

namespace FamilyStickyActualSingleLoadNumericsV1

open LeanEval.Analysis.WangZahlKakeya
open Submission.Kakeya.ConvexGeometry
open FamilyStickyActualTubeTranslationGridV1
open FamilyStickyActualSingleLoadCapV1

noncomputable section

/-!
# Real single-load caps from the appendix mass budget

The deterministic geometry gives
`singleLoad * (delta^2 / 2) <= maximalConcentration * volume K`.
This module performs only the positive finite-factor cancellation needed to
turn an explicit right-hand mass budget into the `Real` load cap consumed by
the finite Chernoff adapter.  No probability or tail conclusion is assumed.
-/

namespace ActualTubeTranslationGrid

variable {delta : NNReal} {translation tubeIndex : Type*}
  [Fintype translation] [DecidableEq translation]
  [DecidableEq tubeIndex]

/-- Cancel the actual tube-volume lower scale from a single test-body mass
budget.  The conclusion has exactly the scalar type used by `hloadCap` in the
finite random-translation adapter. -/
theorem singleLoad_real_le_of_maximalConcentration_massBudget
    (G : ActualTubeTranslationGrid delta translation tubeIndex)
    (K : Fin G.testCard) (g : translation) {cap : Real}
    (hdelta : delta <= (2 : NNReal)⁻¹) (hdeltaPos : 0 < delta)
    (hcap : 0 <= cap)
    (hmax : maximalConcentration
      (ActualTubeTranslationGrid.translatedActiveFamily G g) < ∞)
    (hbudget :
      maximalConcentration
          (ActualTubeTranslationGrid.translatedActiveFamily G g) *
          volume (G.testBody K : Set Space) <=
        ENNReal.ofReal cap * ((delta : ENNReal) ^ 2 / 2)) :
    (G.singleLoad K g : Real) <= cap := by
  let lower : ENNReal := (delta : ENNReal) ^ 2 / 2
  have hdeltaENN : (0 : ENNReal) < (delta : ENNReal) :=
    ENNReal.coe_pos.mpr hdeltaPos
  have hlowerPos : 0 < lower := by
    exact ENNReal.div_pos (ENNReal.pow_pos hdeltaENN 2).ne' (by norm_num)
  have hlowerNeTop : lower ≠ ∞ := by
    exact ENNReal.div_ne_top (ENNReal.pow_ne_top ENNReal.coe_ne_top) (by norm_num)
  have hmass :
      (G.singleLoad K g : ENNReal) * lower <=
        maximalConcentration
            (ActualTubeTranslationGrid.translatedActiveFamily G g) *
          volume (G.testBody K : Set Space) := by
    simpa only [lower] using
      ActualTubeTranslationGrid.singleLoad_mul_half_sq_le_maximalConcentration_mul_volume
        G K g hdelta hmax
  have hmul :
      lower * (G.singleLoad K g : ENNReal) <=
        lower * ENNReal.ofReal cap := by
    simpa only [mul_comm] using hmass.trans hbudget
  have hloadENN :
      (G.singleLoad K g : ENNReal) <= ENNReal.ofReal cap := by
    by_contra hnot
    have hlt : ENNReal.ofReal cap < (G.singleLoad K g : ENNReal) :=
      lt_of_not_ge hnot
    have hstrict :=
      ENNReal.mul_lt_mul_right hlowerPos.ne' hlowerNeTop hlt
    exact (not_lt_of_ge hmul) hstrict
  have hofReal :
      ENNReal.ofReal (G.singleLoad K g : Real) <= ENNReal.ofReal cap := by
    simpa using hloadENN
  exact (ENNReal.ofReal_le_ofReal_iff hcap).mp hofReal

/-- Uniform wrapper matching the `hloadCap` argument of
`exists_grid_translations_singleLoad_le_A_mul_cap`. -/
theorem singleLoad_real_le_of_massBudget_all
    (G : ActualTubeTranslationGrid delta translation tubeIndex)
    {cap : Real}
    (hdelta : delta <= (2 : NNReal)⁻¹) (hdeltaPos : 0 < delta)
    (hcap : 0 <= cap)
    (hmax : forall K, K ∈ G.activeTests -> forall g,
      maximalConcentration
        (ActualTubeTranslationGrid.translatedActiveFamily G g) < ∞)
    (hbudget : forall K, K ∈ G.activeTests -> forall g,
      maximalConcentration
          (ActualTubeTranslationGrid.translatedActiveFamily G g) *
          volume (G.testBody K : Set Space) <=
        ENNReal.ofReal cap * ((delta : ENNReal) ^ 2 / 2)) :
    forall K, K ∈ G.activeTests -> forall g,
      (G.singleLoad K g : Real) <= cap := by
  intro K hK g
  exact singleLoad_real_le_of_maximalConcentration_massBudget
    G K g hdelta hdeltaPos hcap (hmax K hK g) (hbudget K hK g)

#print axioms singleLoad_real_le_of_maximalConcentration_massBudget
#print axioms singleLoad_real_le_of_massBudget_all

end ActualTubeTranslationGrid

end

end FamilyStickyActualSingleLoadNumericsV1
