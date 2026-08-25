import FamilyStickyGrounding.FamilyStickySharedTranslationLocalIncidenceV1
import FamilyStickyGrounding.FamilyStickyActualTranslationPointHitV1
import FamilyStickyGrounding.FamilyStickyFrameBoxCertificateExtractionV1
import FamilyStickyGrounding.FamilyStickyLatticeMotionRadiusV1
import Mathlib.MeasureTheory.Measure.OpenPos

open Set MeasureTheory
open scoped BigOperators ENNReal NNReal

namespace FamilyStickyActualSharedLocalPointBudgetV1

open LeanEval.Analysis.WangZahlKakeya
open Submission.Kakeya.ConvexGeometry
open FamilyStickyActualTubeTranslationV1
open FamilyStickyActualTubeTranslationGridV1
open FamilyStickyActualTranslationPointHitV1
open FamilyStickySharedTranslationPackingIncidenceV1.ActualTubeTranslationGrid
open FamilyStickySharedTranslationPackingIncidenceV1.ActualTubeTranslationGrid.IsSharedTranslationPacking
open FamilyStickySharedTranslationLocalIncidenceV1

noncomputable section

/-!
# Canonical local point budget for one shared translation net

This is the faithful replacement for the earlier full-widened-box budget.  Its
numerator is the proved local axial cap

`(side0+2s)(side1+2s) 2(rho+s)`,

so the long direction is controlled by the shared motion radius.  The Nat
budget is obtained by an actual ceiling after cancelling the positive finite
mesh-ball volume; it is not supplied as a callback.
-/

namespace ActualTubeTranslationGrid.IsSharedTranslationPacking

variable {delta : NNReal} {translation tubeIndex : Type*}
  [Fintype translation] [DecidableEq translation]
  [DecidableEq tubeIndex]
  {G : ActualTubeTranslationGrid delta translation tubeIndex}
  {mesh motionRadius : NNReal}

def meshBallVolume
    (_P : IsSharedTranslationPacking G mesh motionRadius) : ENNReal :=
  volume (Metric.ball (0 : Space) (mesh : Real))

def localAxialVolume
    (_P : IsSharedTranslationPacking G mesh motionRadius)
    (B : FrameBox) : ENNReal :=
  ((B.side 0 : ENNReal) + 2 * (mesh : ENNReal)) *
    ((B.side 1 : ENNReal) + 2 * (mesh : ENNReal)) *
      (2 * ((motionRadius : ENNReal) + (mesh : ENNReal)))

/-- Canonical finite hit budget for the local axial cap. -/
def localPointBudget
    (P : IsSharedTranslationPacking G mesh motionRadius)
    (B : FrameBox) : Nat :=
  Nat.ceil ((localAxialVolume P B).toReal / (meshBallVolume P).toReal)

theorem meshBallVolume_pos
    (P : IsSharedTranslationPacking G mesh motionRadius) :
    0 < meshBallVolume P := by
  exact Metric.measure_ball_pos volume (0 : Space)
    (by exact_mod_cast P.mesh_pos)

theorem meshBallVolume_ne_top
    (P : IsSharedTranslationPacking G mesh motionRadius) :
    meshBallVolume P ≠ ∞ :=
  measure_ball_lt_top.ne

theorem localAxialVolume_ne_top
    (P : IsSharedTranslationPacking G mesh motionRadius) (B : FrameBox) :
    localAxialVolume P B ≠ ∞ := by
  unfold localAxialVolume
  apply ENNReal.mul_ne_top
  · apply ENNReal.mul_ne_top
    · rw [ENNReal.add_ne_top]
      exact ⟨ENNReal.coe_ne_top,
        ENNReal.mul_ne_top (by norm_num) ENNReal.coe_ne_top⟩
    · rw [ENNReal.add_ne_top]
      exact ⟨ENNReal.coe_ne_top,
        ENNReal.mul_ne_top (by norm_num) ENNReal.coe_ne_top⟩
  · exact ENNReal.mul_ne_top (by norm_num)
      (ENNReal.add_ne_top.mpr ⟨ENNReal.coe_ne_top, ENNReal.coe_ne_top⟩)

/-- The local packing-volume inequality yields the canonical ceiling count. -/
theorem card_pointHits_le_localPointBudget
    (P : IsSharedTranslationPacking G mesh motionRadius)
    (A : Set Space) (B : FrameBox) (hA : A ⊆ B.carrier) (x : Space) :
    (P.pointHits A x).card ≤ localPointBudget P B := by
  have hpack :=
    card_pointHits_nsmul_ballVolume_le_axialCap P A B hA x
  have hreal := ENNReal.toReal_mono (localAxialVolume_ne_top P B) hpack
  have hmul :
      ((P.pointHits A x).card : Real) * (meshBallVolume P).toReal ≤
        (localAxialVolume P B).toReal := by
    simpa only [meshBallVolume, localAxialVolume, nsmul_eq_mul,
      ENNReal.toReal_mul, ENNReal.toReal_natCast] using hreal
  have hvReal : 0 < (meshBallVolume P).toReal :=
    ENNReal.toReal_pos (meshBallVolume_pos P).ne' (meshBallVolume_ne_top P)
  have hratio :
      ((P.pointHits A x).card : Real) ≤
        (localAxialVolume P B).toReal / (meshBallVolume P).toReal :=
    (le_div_iff₀ hvReal).2 hmul
  have hceil :
      ((P.pointHits A x).card : Real) ≤
        (Nat.ceil ((localAxialVolume P B).toReal /
          (meshBallVolume P).toReal) : Real) :=
    hratio.trans (Nat.le_ceil _)
  exact_mod_cast hceil

theorem pointHitCount_eq_card_pointHits
    (P : IsSharedTranslationPacking G mesh motionRadius)
    (K : Fin G.testCard) (x : Space) :
    FamilyStickyActualTranslationPointHitV1.ActualTubeTranslationGrid.pointHitCount
        G K x =
      (P.pointHits (G.testBody K : Set Space) x).card := by
  rfl

theorem hasPointHitCap_of_outerBoxes
    (P : IsSharedTranslationPacking G mesh motionRadius)
    (box : Fin G.testCard -> FrameBox)
    (hbox : forall K, (G.testBody K : Set Space) ⊆ (box K).carrier) :
    FamilyStickyActualTranslationPointHitV1.ActualTubeTranslationGrid.HasPointHitCap
      G (fun K => localPointBudget P (box K)) := by
  intro K _hK x
  rw [pointHitCount_eq_card_pointHits P K x]
  exact card_pointHits_le_localPointBudget P
    (G.testBody K : Set Space) (box K) (hbox K) x

/-- Actual per-tube incidence cap extracted from declared box dimensions. -/
theorem tubeHitCount_le_localPointBudget_of_boxDimensions
    (P : IsSharedTranslationPacking G mesh motionRadius)
    {C : NNReal} {side : Fin G.testCard -> Fin 3 -> NNReal}
    (hdim : forall K, HasBoxDimensions C (side K) (G.testBody K)) :
    forall K, K ∈ G.activeTests -> forall i, i ∈ G.tubes ->
      G.tubeHitCount K i ≤
        localPointBudget P
          (FamilyStickyFrameBoxCertificateExtractionV1.ActualTubeTranslationGrid.testOuterBox
            G hdim K) := by
  apply
    FamilyStickyActualTranslationPointHitV1.ActualTubeTranslationGrid.tubeHitCount_le_of_hasPointHitCap
  exact hasPointHitCap_of_outerBoxes P
    (FamilyStickyFrameBoxCertificateExtractionV1.ActualTubeTranslationGrid.testOuterBox
      G hdim)
    (FamilyStickyFrameBoxCertificateExtractionV1.ActualTubeTranslationGrid.testBody_subset_testOuterBox
      G hdim)

/-- The same shared outcome retains the already proved motion-radius control. -/
theorem translateTube_carrier_subset_cthickening
    (P : IsSharedTranslationPacking G mesh motionRadius)
    (i : tubeIndex) (g : translation) :
    (translateTube (G.tube i) (G.gridVector g)).carrier ⊆
      Metric.cthickening (motionRadius : Real) (G.tube i).carrier := by
  exact
    FamilyStickyLatticeMotionRadiusV1.translateTube_carrier_subset_cthickening_of_norm_le
      (G.tube i) (G.gridVector g) motionRadius (P.gridVector_norm_le g)

#print axioms meshBallVolume_pos
#print axioms localAxialVolume_ne_top
#print axioms card_pointHits_le_localPointBudget
#print axioms hasPointHitCap_of_outerBoxes
#print axioms tubeHitCount_le_localPointBudget_of_boxDimensions
#print axioms translateTube_carrier_subset_cthickening

end ActualTubeTranslationGrid.IsSharedTranslationPacking

end


end FamilyStickyActualSharedLocalPointBudgetV1
