import FamilyStickyGrounding.FamilyStickyActualSharedLocalPointBudgetV1
import FamilyStickyGrounding.FamilyStickyBallVolumeScalingThreeV1

open Set MeasureTheory
open scoped BigOperators ENNReal NNReal

namespace FamilyStickyActualSharedLocalBalanceV1

open LeanEval.Analysis.WangZahlKakeya
open Submission.Kakeya.ConvexGeometry
open FamilyStickyActualTubeTranslationGridV1
open FamilyStickySharedTranslationPackingIncidenceV1.ActualTubeTranslationGrid
open FamilyStickySharedTranslationPackingIncidenceV1.ActualTubeTranslationGrid.IsSharedTranslationPacking
open FamilyStickyActualSharedLocalPointBudgetV1

noncomputable section

/-!
# Source-scale balance for the faithful shared translation net

The local hit numerator is now `O(k_0 k_1 rho)`, rather than the full
frame-box volume.  The net-cover loss is made exact by the three-dimensional
identity `vol(B_(3s)) = 27 vol(B_s)`.  Under `s <= k_0,k_1,rho`, the ceiling
loss and local window are absorbed into the explicit sufficient inequality

`1188 * #tubes * k_0 * k_1 * rho <= vol(B_rho) * mean`.

Using `4 rho^3 <= vol(B_rho)`, it is enough to require

`297 * #tubes * k_0 * k_1 <= rho^2 * mean`.

All constants include the finite-net cover and the literal Nat ceiling; no
probability conclusion is stored as a hypothesis.
-/

namespace ActualTubeTranslationGrid.IsSharedTranslationPacking

variable {delta : NNReal} {translation tubeIndex : Type*}
  [Fintype translation] [DecidableEq translation]
  [DecidableEq tubeIndex]
  {G : ActualTubeTranslationGrid delta translation tubeIndex}
  {mesh motionRadius : NNReal}

def threeMeshBallVolume
    (_P : IsSharedTranslationPacking G mesh motionRadius) : ENNReal :=
  volume (Metric.ball (0 : Space) ((3 * mesh : NNReal) : Real))

def motionBallVolume
    (_P : IsSharedTranslationPacking G mesh motionRadius) : ENNReal :=
  volume (Metric.closedBall (0 : Space) (motionRadius : Real))

def sourceLocalAxialVolume
    (_P : IsSharedTranslationPacking G mesh motionRadius)
    (side : Fin 3 -> NNReal) : ENNReal :=
  ((side 0 : ENNReal) + 2 * (mesh : ENNReal)) *
    ((side 1 : ENNReal) + 2 * (mesh : ENNReal)) *
      (2 * ((motionRadius : ENNReal) + (mesh : ENNReal)))

theorem threeMeshBallVolume_pos
    (P : IsSharedTranslationPacking G mesh motionRadius) :
    0 < threeMeshBallVolume P := by
  exact Metric.measure_ball_pos volume (0 : Space) (by
    exact_mod_cast mul_pos (show (0 : NNReal) < 3 by norm_num) P.mesh_pos)

theorem threeMeshBallVolume_ne_top
    (P : IsSharedTranslationPacking G mesh motionRadius) :
    threeMeshBallVolume P ≠ ∞ :=
  measure_ball_lt_top.ne

theorem motionBallVolume_ne_top
    (P : IsSharedTranslationPacking G mesh motionRadius) :
    motionBallVolume P ≠ ∞ :=
  measure_closedBall_lt_top.ne

/-- Exact factor incurred by using an open `3s` cover ball. -/
theorem threeMeshBallVolume_eq_twentySeven_mul_meshBallVolume
    (P : IsSharedTranslationPacking G mesh motionRadius) :
    threeMeshBallVolume P =
      27 *
        FamilyStickyActualSharedLocalPointBudgetV1.ActualTubeTranslationGrid.IsSharedTranslationPacking.meshBallVolume
          P := by
  exact FamilyStickyBallVolumeScalingThreeV1.volume_ball_three_mul mesh

theorem localPointBudget_lt_ratio_add_one
    (P : IsSharedTranslationPacking G mesh motionRadius) (B : FrameBox) :
    (FamilyStickyActualSharedLocalPointBudgetV1.ActualTubeTranslationGrid.IsSharedTranslationPacking.localPointBudget
        P B : Real) <
      (FamilyStickyActualSharedLocalPointBudgetV1.ActualTubeTranslationGrid.IsSharedTranslationPacking.localAxialVolume
          P B).toReal /
        (FamilyStickyActualSharedLocalPointBudgetV1.ActualTubeTranslationGrid.IsSharedTranslationPacking.meshBallVolume
          P).toReal + 1 := by
  exact Nat.ceil_lt_add_one (by positivity)

theorem motionBallVolume_real_le_card_mul_threeMeshBallVolume_real
    (P : IsSharedTranslationPacking G mesh motionRadius) :
    (motionBallVolume P).toReal ≤
      (Fintype.card translation : Real) * (threeMeshBallVolume P).toReal := by
  have hcover := P.volume_motionBall_le_card_smul_ballVolume_three
  have htop :
      Fintype.card translation • threeMeshBallVolume P ≠ ∞ := by
    rw [nsmul_eq_mul]
    exact ENNReal.mul_ne_top ENNReal.coe_ne_top (threeMeshBallVolume_ne_top P)
  have hreal := ENNReal.toReal_mono htop hcover
  simpa only [motionBallVolume, threeMeshBallVolume, nsmul_eq_mul,
    ENNReal.toReal_mul, ENNReal.toReal_natCast] using hreal

/-- Exact division-free balance adapter for the local Nat ceiling budget. -/
theorem balance_of_localAxialVolume
    (P : IsSharedTranslationPacking G mesh motionRadius)
    (B : FrameBox) {mean : Real} (hmean : 0 ≤ mean)
    (hvolumeBalance :
      (G.tubes.card : Real) *
          ((FamilyStickyActualSharedLocalPointBudgetV1.ActualTubeTranslationGrid.IsSharedTranslationPacking.localAxialVolume
              P B).toReal /
            (FamilyStickyActualSharedLocalPointBudgetV1.ActualTubeTranslationGrid.IsSharedTranslationPacking.meshBallVolume
              P).toReal + 1) *
          (threeMeshBallVolume P).toReal ≤
        (motionBallVolume P).toReal * mean) :
    (G.tubes.card : Real) *
        (FamilyStickyActualSharedLocalPointBudgetV1.ActualTubeTranslationGrid.IsSharedTranslationPacking.localPointBudget
          P B : Real) ≤
      (Fintype.card translation : Real) * mean := by
  have htube : 0 ≤ (G.tubes.card : Real) := Nat.cast_nonneg _
  have hthreeNonneg : 0 ≤ (threeMeshBallVolume P).toReal := by positivity
  have hthreePos : 0 < (threeMeshBallVolume P).toReal :=
    ENNReal.toReal_pos (threeMeshBallVolume_pos P).ne'
      (threeMeshBallVolume_ne_top P)
  have hbudget :
      (FamilyStickyActualSharedLocalPointBudgetV1.ActualTubeTranslationGrid.IsSharedTranslationPacking.localPointBudget
          P B : Real) ≤
        (FamilyStickyActualSharedLocalPointBudgetV1.ActualTubeTranslationGrid.IsSharedTranslationPacking.localAxialVolume
            P B).toReal /
          (FamilyStickyActualSharedLocalPointBudgetV1.ActualTubeTranslationGrid.IsSharedTranslationPacking.meshBallVolume
            P).toReal + 1 :=
    (localPointBudget_lt_ratio_add_one P B).le
  have hglobal :=
    motionBallVolume_real_le_card_mul_threeMeshBallVolume_real P
  have hmul :
      ((G.tubes.card : Real) *
          (FamilyStickyActualSharedLocalPointBudgetV1.ActualTubeTranslationGrid.IsSharedTranslationPacking.localPointBudget
            P B : Real)) * (threeMeshBallVolume P).toReal ≤
        ((Fintype.card translation : Real) * mean) *
          (threeMeshBallVolume P).toReal := by
    calc
      ((G.tubes.card : Real) *
          (FamilyStickyActualSharedLocalPointBudgetV1.ActualTubeTranslationGrid.IsSharedTranslationPacking.localPointBudget
            P B : Real)) * (threeMeshBallVolume P).toReal ≤
        ((G.tubes.card : Real) *
          ((FamilyStickyActualSharedLocalPointBudgetV1.ActualTubeTranslationGrid.IsSharedTranslationPacking.localAxialVolume
              P B).toReal /
            (FamilyStickyActualSharedLocalPointBudgetV1.ActualTubeTranslationGrid.IsSharedTranslationPacking.meshBallVolume
              P).toReal + 1)) *
          (threeMeshBallVolume P).toReal :=
        mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_left hbudget htube) hthreeNonneg
      _ ≤ (motionBallVolume P).toReal * mean := hvolumeBalance
      _ ≤ ((Fintype.card translation : Real) *
          (threeMeshBallVolume P).toReal) * mean :=
        mul_le_mul_of_nonneg_right hglobal hmean
      _ = ((Fintype.card translation : Real) * mean) *
          (threeMeshBallVolume P).toReal := by ring
  exact le_of_mul_le_mul_right hmul hthreePos

theorem localAxialVolume_testOuterBox
    (P : IsSharedTranslationPacking G mesh motionRadius)
    {C : NNReal} {side : Fin G.testCard -> Fin 3 -> NNReal}
    (hdim : forall K, HasBoxDimensions C (side K) (G.testBody K))
    (K : Fin G.testCard) :
    FamilyStickyActualSharedLocalPointBudgetV1.ActualTubeTranslationGrid.IsSharedTranslationPacking.localAxialVolume
        P
        (FamilyStickyFrameBoxCertificateExtractionV1.ActualTubeTranslationGrid.testOuterBox
          G hdim K) =
      sourceLocalAxialVolume P (side K) := by
  unfold
    FamilyStickyActualSharedLocalPointBudgetV1.ActualTubeTranslationGrid.IsSharedTranslationPacking.localAxialVolume
    sourceLocalAxialVolume
  rw [FamilyStickyFrameBoxCertificateExtractionV1.ActualTubeTranslationGrid.testOuterBox_side
    G hdim K]

/-- At source scales `mesh <= k_0,k_1,rho`, the local axial numerator is at
most `36 k_0 k_1 rho`. -/
theorem sourceLocalAxialVolume_le_thirtySix_mul
    (P : IsSharedTranslationPacking G mesh motionRadius)
    (side : Fin 3 -> NNReal)
    (hmesh0 : mesh ≤ side 0) (hmesh1 : mesh ≤ side 1)
    (hmeshR : mesh ≤ motionRadius) :
    sourceLocalAxialVolume P side ≤
      36 * (side 0 : ENNReal) * (side 1 : ENNReal) *
        (motionRadius : ENNReal) := by
  have h0 : (mesh : ENNReal) ≤ (side 0 : ENNReal) := by
    exact_mod_cast hmesh0
  have h1 : (mesh : ENNReal) ≤ (side 1 : ENNReal) := by
    exact_mod_cast hmesh1
  have hR : (mesh : ENNReal) ≤ (motionRadius : ENNReal) := by
    exact_mod_cast hmeshR
  have hw0 :
      (side 0 : ENNReal) + 2 * (mesh : ENNReal) ≤
        3 * (side 0 : ENNReal) := by
    calc
      (side 0 : ENNReal) + 2 * (mesh : ENNReal) ≤
          (side 0 : ENNReal) + 2 * (side 0 : ENNReal) := by gcongr
      _ = 3 * (side 0 : ENNReal) := by ring
  have hw1 :
      (side 1 : ENNReal) + 2 * (mesh : ENNReal) ≤
        3 * (side 1 : ENNReal) := by
    calc
      (side 1 : ENNReal) + 2 * (mesh : ENNReal) ≤
          (side 1 : ENNReal) + 2 * (side 1 : ENNReal) := by gcongr
      _ = 3 * (side 1 : ENNReal) := by ring
  have hwR :
      2 * ((motionRadius : ENNReal) + (mesh : ENNReal)) ≤
        4 * (motionRadius : ENNReal) := by
    calc
      2 * ((motionRadius : ENNReal) + (mesh : ENNReal)) ≤
          2 * ((motionRadius : ENNReal) + (motionRadius : ENNReal)) := by
            gcongr
      _ = 4 * (motionRadius : ENNReal) := by ring
  unfold sourceLocalAxialVolume
  calc
    ((side 0 : ENNReal) + 2 * (mesh : ENNReal)) *
        ((side 1 : ENNReal) + 2 * (mesh : ENNReal)) *
          (2 * ((motionRadius : ENNReal) + (mesh : ENNReal))) ≤
      (3 * (side 0 : ENNReal)) * (3 * (side 1 : ENNReal)) *
        (4 * (motionRadius : ENNReal)) := by gcongr
    _ = 36 * (side 0 : ENNReal) * (side 1 : ENNReal) *
        (motionRadius : ENNReal) := by ring

/-- A mesh ball is bounded by the enclosing cube of side `2*mesh`; the
constant `8` is proved from Mathlib's exact R³ formula and `pi <= 4`. -/
theorem meshBallVolume_le_eight_mul_cube
    (P : IsSharedTranslationPacking G mesh motionRadius) :
    FamilyStickyActualSharedLocalPointBudgetV1.ActualTubeTranslationGrid.IsSharedTranslationPacking.meshBallVolume
        P ≤ 8 * (mesh : ENNReal) ^ 3 := by
  rw [FamilyStickyActualSharedLocalPointBudgetV1.ActualTubeTranslationGrid.IsSharedTranslationPacking.meshBallVolume,
    EuclideanSpace.volume_ball_fin_three]
  simp only [ENNReal.ofReal_coe_nnreal]
  have hcoeff : ENNReal.ofReal (Real.pi * 4 / 3) ≤ 8 := by
    rw [← ENNReal.ofReal_ofNat 8]
    exact ENNReal.ofReal_le_ofReal (by nlinarith [Real.pi_le_four])
  calc
    (mesh : ENNReal) ^ 3 * ENNReal.ofReal (Real.pi * 4 / 3) ≤
        (mesh : ENNReal) ^ 3 * 8 := mul_le_mul_of_nonneg_left hcoeff bot_le
    _ = 8 * (mesh : ENNReal) ^ 3 := by ac_rfl

theorem meshBallVolume_le_eight_mul_sourceProduct
    (P : IsSharedTranslationPacking G mesh motionRadius)
    (side : Fin 3 -> NNReal)
    (hmesh0 : mesh ≤ side 0) (hmesh1 : mesh ≤ side 1)
    (hmeshR : mesh ≤ motionRadius) :
    FamilyStickyActualSharedLocalPointBudgetV1.ActualTubeTranslationGrid.IsSharedTranslationPacking.meshBallVolume
        P ≤
      8 * (side 0 : ENNReal) * (side 1 : ENNReal) *
        (motionRadius : ENNReal) := by
  calc
    FamilyStickyActualSharedLocalPointBudgetV1.ActualTubeTranslationGrid.IsSharedTranslationPacking.meshBallVolume
        P ≤ 8 * (mesh : ENNReal) ^ 3 := meshBallVolume_le_eight_mul_cube P
    _ ≤ 8 * (side 0 : ENNReal) * (side 1 : ENNReal) *
        (motionRadius : ENNReal) := by
      have h0 : (mesh : ENNReal) ≤ (side 0 : ENNReal) := by exact_mod_cast hmesh0
      have h1 : (mesh : ENNReal) ≤ (side 1 : ENNReal) := by exact_mod_cast hmesh1
      have hR : (mesh : ENNReal) ≤ (motionRadius : ENNReal) := by exact_mod_cast hmeshR
      rw [pow_three]
      calc
        8 * ((mesh : ENNReal) * ((mesh : ENNReal) * (mesh : ENNReal))) ≤
            8 * ((side 0 : ENNReal) * ((side 1 : ENNReal) *
              (motionRadius : ENNReal))) := by gcongr
        _ = 8 * (side 0 : ENNReal) * (side 1 : ENNReal) *
            (motionRadius : ENNReal) := by ring

/-- Local numerator plus the literal ceiling remainder. -/
theorem sourceLocalAxialVolume_add_meshBallVolume_le_fortyFour_mul
    (P : IsSharedTranslationPacking G mesh motionRadius)
    (side : Fin 3 -> NNReal)
    (hmesh0 : mesh ≤ side 0) (hmesh1 : mesh ≤ side 1)
    (hmeshR : mesh ≤ motionRadius) :
    sourceLocalAxialVolume P side +
        FamilyStickyActualSharedLocalPointBudgetV1.ActualTubeTranslationGrid.IsSharedTranslationPacking.meshBallVolume P ≤
      44 * (side 0 : ENNReal) * (side 1 : ENNReal) *
        (motionRadius : ENNReal) := by
  calc
    sourceLocalAxialVolume P side +
        FamilyStickyActualSharedLocalPointBudgetV1.ActualTubeTranslationGrid.IsSharedTranslationPacking.meshBallVolume P ≤
      (36 * (side 0 : ENNReal) * (side 1 : ENNReal) *
          (motionRadius : ENNReal)) +
        (8 * (side 0 : ENNReal) * (side 1 : ENNReal) *
          (motionRadius : ENNReal)) :=
      add_le_add
        (sourceLocalAxialVolume_le_thirtySix_mul P side hmesh0 hmesh1 hmeshR)
        (meshBallVolume_le_eight_mul_sourceProduct P side hmesh0 hmesh1 hmeshR)
    _ = 44 * (side 0 : ENNReal) * (side 1 : ENNReal) *
        (motionRadius : ENNReal) := by ring

#print axioms threeMeshBallVolume_eq_twentySeven_mul_meshBallVolume
#print axioms balance_of_localAxialVolume
#print axioms localAxialVolume_testOuterBox
#print axioms sourceLocalAxialVolume_le_thirtySix_mul
#print axioms meshBallVolume_le_eight_mul_cube
#print axioms sourceLocalAxialVolume_add_meshBallVolume_le_fortyFour_mul

end ActualTubeTranslationGrid.IsSharedTranslationPacking

end


end FamilyStickyActualSharedLocalBalanceV1
