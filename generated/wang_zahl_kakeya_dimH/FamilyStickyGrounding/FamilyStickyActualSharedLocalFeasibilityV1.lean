import FamilyStickyGrounding.FamilyStickyActualSharedLocalBalanceV1

open Set MeasureTheory
open scoped BigOperators ENNReal NNReal

namespace FamilyStickyActualSharedLocalFeasibilityV1

open LeanEval.Analysis.WangZahlKakeya
open Submission.Kakeya.ConvexGeometry
open FamilyStickyActualTubeTranslationGridV1
open FamilyStickySharedTranslationPackingIncidenceV1.ActualTubeTranslationGrid
open FamilyStickySharedTranslationPackingIncidenceV1.ActualTubeTranslationGrid.IsSharedTranslationPacking
open FamilyStickyActualSharedLocalBalanceV1.ActualTubeTranslationGrid.IsSharedTranslationPacking

noncomputable section

/-!
# Explicit feasibility of the faithful local shared-grid balance

This module performs the remaining cancellation in real numbers.  It records
both useful forms of the sufficient condition:

* `1188 #T k_0 k_1 rho <= vol(B_rho) mean`;
* `297 #T k_0 k_1 <= rho^2 mean`.

The constants are transparent: `44 = 36 + 8` is the local axial window plus
the literal ceiling remainder, and `1188 = 27 * 44` is the exact R³ cover-ball
scaling.  The second form uses the proved lower bound `4 rho^3 <= vol(B_rho)`.
-/

variable {delta : NNReal} {translation tubeIndex : Type*}
  [Fintype translation] [DecidableEq translation]
  [DecidableEq tubeIndex]
  {G : ActualTubeTranslationGrid delta translation tubeIndex}
  {mesh motionRadius : NNReal}

private theorem sourceLocalAxialVolume_ne_top
    (P : IsSharedTranslationPacking G mesh motionRadius)
    (side : Fin 3 -> NNReal) :
    sourceLocalAxialVolume P side ≠ ∞ := by
  unfold sourceLocalAxialVolume
  finiteness

/-- Real form of the `44 k_0 k_1 rho` numerator-plus-ceiling estimate. -/
theorem sourceLocalAxialVolume_toReal_add_meshBallVolume_toReal_le
    (P : IsSharedTranslationPacking G mesh motionRadius)
    (side : Fin 3 -> NNReal)
    (hmesh0 : mesh ≤ side 0) (hmesh1 : mesh ≤ side 1)
    (hmeshR : mesh ≤ motionRadius) :
    (sourceLocalAxialVolume P side).toReal +
        (FamilyStickyActualSharedLocalPointBudgetV1.ActualTubeTranslationGrid.IsSharedTranslationPacking.meshBallVolume
          P).toReal ≤
      44 * (side 0 : Real) * (side 1 : Real) *
        (motionRadius : Real) := by
  have h :=
    sourceLocalAxialVolume_add_meshBallVolume_le_fortyFour_mul
      P side hmesh0 hmesh1 hmeshR
  have htop :
      44 * (side 0 : ENNReal) * (side 1 : ENNReal) *
          (motionRadius : ENNReal) ≠ ∞ := by
    finiteness
  have hreal := ENNReal.toReal_mono htop h
  rw [ENNReal.toReal_add (sourceLocalAxialVolume_ne_top P side)
      (FamilyStickyActualSharedLocalPointBudgetV1.ActualTubeTranslationGrid.IsSharedTranslationPacking.meshBallVolume_ne_top
        P)] at hreal
  simpa only [ENNReal.toReal_mul, ENNReal.toReal_ofNat,
    ENNReal.coe_toReal] using hreal

/-- Direct source-volume feasibility, with all net and ceiling constants
already absorbed. -/
theorem balance_of_explicit_1188
    (P : IsSharedTranslationPacking G mesh motionRadius)
    (B : FrameBox) {mean : Real}
    (hmesh0 : mesh ≤ B.side 0) (hmesh1 : mesh ≤ B.side 1)
    (hmeshR : mesh ≤ motionRadius) (hmean : 0 ≤ mean)
    (hnumerical :
      1188 * (G.tubes.card : Real) * (B.side 0 : Real) *
          (B.side 1 : Real) * (motionRadius : Real) ≤
        (motionBallVolume P).toReal * mean) :
    (G.tubes.card : Real) *
        (FamilyStickyActualSharedLocalPointBudgetV1.ActualTubeTranslationGrid.IsSharedTranslationPacking.localPointBudget
          P B : Real) ≤
      (Fintype.card translation : Real) * mean := by
  apply balance_of_localAxialVolume P B hmean
  have hbPos :
      0 <
        (FamilyStickyActualSharedLocalPointBudgetV1.ActualTubeTranslationGrid.IsSharedTranslationPacking.meshBallVolume
          P).toReal :=
    ENNReal.toReal_pos
      (FamilyStickyActualSharedLocalPointBudgetV1.ActualTubeTranslationGrid.IsSharedTranslationPacking.meshBallVolume_pos
        P).ne'
      (FamilyStickyActualSharedLocalPointBudgetV1.ActualTubeTranslationGrid.IsSharedTranslationPacking.meshBallVolume_ne_top
        P)
  have hthree :
      (threeMeshBallVolume P).toReal =
        27 *
          (FamilyStickyActualSharedLocalPointBudgetV1.ActualTubeTranslationGrid.IsSharedTranslationPacking.meshBallVolume
            P).toReal := by
    have h := congrArg ENNReal.toReal
      (threeMeshBallVolume_eq_twentySeven_mul_meshBallVolume P)
    simpa only [ENNReal.toReal_mul, ENNReal.toReal_ofNat] using h
  have hsum :=
    sourceLocalAxialVolume_toReal_add_meshBallVolume_toReal_le
      P B.side hmesh0 hmesh1 hmeshR
  change
    (G.tubes.card : Real) *
        ((FamilyStickyActualSharedLocalPointBudgetV1.ActualTubeTranslationGrid.IsSharedTranslationPacking.localAxialVolume
            P B).toReal /
          (FamilyStickyActualSharedLocalPointBudgetV1.ActualTubeTranslationGrid.IsSharedTranslationPacking.meshBallVolume
            P).toReal + 1) *
        (threeMeshBallVolume P).toReal ≤
      (motionBallVolume P).toReal * mean
  have hlocal :
      (FamilyStickyActualSharedLocalPointBudgetV1.ActualTubeTranslationGrid.IsSharedTranslationPacking.localAxialVolume
          P B).toReal +
          (FamilyStickyActualSharedLocalPointBudgetV1.ActualTubeTranslationGrid.IsSharedTranslationPacking.meshBallVolume
            P).toReal ≤
        44 * (B.side 0 : Real) * (B.side 1 : Real) *
          (motionRadius : Real) := by
    simpa [FamilyStickyActualSharedLocalPointBudgetV1.ActualTubeTranslationGrid.IsSharedTranslationPacking.localAxialVolume,
      sourceLocalAxialVolume] using hsum
  calc
    (G.tubes.card : Real) *
        ((FamilyStickyActualSharedLocalPointBudgetV1.ActualTubeTranslationGrid.IsSharedTranslationPacking.localAxialVolume
            P B).toReal /
          (FamilyStickyActualSharedLocalPointBudgetV1.ActualTubeTranslationGrid.IsSharedTranslationPacking.meshBallVolume
            P).toReal + 1) *
        (threeMeshBallVolume P).toReal =
      27 * (G.tubes.card : Real) *
        ((FamilyStickyActualSharedLocalPointBudgetV1.ActualTubeTranslationGrid.IsSharedTranslationPacking.localAxialVolume
            P B).toReal +
          (FamilyStickyActualSharedLocalPointBudgetV1.ActualTubeTranslationGrid.IsSharedTranslationPacking.meshBallVolume
            P).toReal) := by
      rw [hthree]
      field_simp [hbPos.ne']
    _ ≤ 27 * (G.tubes.card : Real) *
        (44 * (B.side 0 : Real) * (B.side 1 : Real) *
          (motionRadius : Real)) := by
      gcongr
    _ = 1188 * (G.tubes.card : Real) * (B.side 0 : Real) *
          (B.side 1 : Real) * (motionRadius : Real) := by ring
    _ ≤ (motionBallVolume P).toReal * mean := hnumerical

/-- The closed motion ball contains at least `4 rho^3` volume. -/
theorem four_mul_cube_le_motionBallVolume
    (P : IsSharedTranslationPacking G mesh motionRadius) :
    4 * (motionRadius : ENNReal) ^ 3 ≤ motionBallVolume P := by
  rw [motionBallVolume, EuclideanSpace.volume_closedBall_fin_three]
  simp only [ENNReal.ofReal_coe_nnreal]
  have hcoeff : 4 ≤ ENNReal.ofReal (Real.pi * 4 / 3) := by
    rw [← ENNReal.ofReal_ofNat 4]
    exact ENNReal.ofReal_le_ofReal (by nlinarith [Real.pi_gt_three])
  calc
    4 * (motionRadius : ENNReal) ^ 3 =
        (motionRadius : ENNReal) ^ 3 * 4 := by ac_rfl
    _ ≤ (motionRadius : ENNReal) ^ 3 *
        ENNReal.ofReal (Real.pi * 4 / 3) :=
      mul_le_mul_of_nonneg_left hcoeff bot_le

theorem four_mul_cube_le_motionBallVolume_toReal
    (P : IsSharedTranslationPacking G mesh motionRadius) :
    4 * (motionRadius : Real) ^ 3 ≤ (motionBallVolume P).toReal := by
  have hreal := ENNReal.toReal_mono (motionBallVolume_ne_top P)
    (four_mul_cube_le_motionBallVolume P)
  simpa only [ENNReal.toReal_mul, ENNReal.toReal_ofNat,
    ENNReal.toReal_pow, ENNReal.coe_toReal] using hreal

/-- Scale-normalized feasibility: this is the explicit `k_0 k_1 / rho^2`
condition corresponding to the paper's local intersection probability. -/
theorem balance_of_explicit_297
    (P : IsSharedTranslationPacking G mesh motionRadius)
    (B : FrameBox) {mean : Real}
    (hmesh0 : mesh ≤ B.side 0) (hmesh1 : mesh ≤ B.side 1)
    (hmeshR : mesh ≤ motionRadius) (hmean : 0 ≤ mean)
    (hnormalized :
      297 * (G.tubes.card : Real) * (B.side 0 : Real) *
          (B.side 1 : Real) ≤
        (motionRadius : Real) ^ 2 * mean) :
    (G.tubes.card : Real) *
        (FamilyStickyActualSharedLocalPointBudgetV1.ActualTubeTranslationGrid.IsSharedTranslationPacking.localPointBudget
          P B : Real) ≤
      (Fintype.card translation : Real) * mean := by
  apply balance_of_explicit_1188 P B hmesh0 hmesh1 hmeshR hmean
  have hr : 0 ≤ (motionRadius : Real) := NNReal.zero_le_coe
  have hscaled := mul_le_mul_of_nonneg_left hnormalized
    (mul_nonneg (by norm_num : (0 : Real) ≤ 4) hr)
  calc
    1188 * (G.tubes.card : Real) * (B.side 0 : Real) *
        (B.side 1 : Real) * (motionRadius : Real) =
      (4 * (motionRadius : Real)) *
        (297 * (G.tubes.card : Real) * (B.side 0 : Real) *
          (B.side 1 : Real)) := by ring
    _ ≤ (4 * (motionRadius : Real)) *
        ((motionRadius : Real) ^ 2 * mean) := hscaled
    _ = (4 * (motionRadius : Real) ^ 3) * mean := by ring
    _ ≤ (motionBallVolume P).toReal * mean :=
      mul_le_mul_of_nonneg_right
        (four_mul_cube_le_motionBallVolume_toReal P) hmean

/-- Explicit paper scale-order wrapper.  Taking `mesh = scaleDelta` specializes
the assumptions to `delta <= k_i <= rho`. -/
theorem balance_of_delta_le_shortSides_le_motionRadius
    (P : IsSharedTranslationPacking G mesh motionRadius)
    (B : FrameBox) (scaleDelta : NNReal) {mean : Real}
    (hmeshDelta : mesh ≤ scaleDelta)
    (hdelta0 : scaleDelta ≤ B.side 0)
    (hdelta1 : scaleDelta ≤ B.side 1)
    (hzeroR : B.side 0 ≤ motionRadius)
    (_honeR : B.side 1 ≤ motionRadius)
    (hmean : 0 ≤ mean)
    (hnormalized :
      297 * (G.tubes.card : Real) * (B.side 0 : Real) *
          (B.side 1 : Real) ≤
        (motionRadius : Real) ^ 2 * mean) :
    (G.tubes.card : Real) *
        (FamilyStickyActualSharedLocalPointBudgetV1.ActualTubeTranslationGrid.IsSharedTranslationPacking.localPointBudget
          P B : Real) ≤
      (Fintype.card translation : Real) * mean := by
  exact balance_of_explicit_297 P B
    (hmeshDelta.trans hdelta0) (hmeshDelta.trans hdelta1)
    ((hmeshDelta.trans hdelta0).trans hzeroR) hmean hnormalized

#print axioms sourceLocalAxialVolume_toReal_add_meshBallVolume_toReal_le
#print axioms balance_of_explicit_1188
#print axioms four_mul_cube_le_motionBallVolume
#print axioms balance_of_explicit_297
#print axioms balance_of_delta_le_shortSides_le_motionRadius

end


end FamilyStickyActualSharedLocalFeasibilityV1
