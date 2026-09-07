import Family8Grounding.Family8Family7NativeHighCriticalScaleProxyDatumV1
import Mathlib.Tactic

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 1000000

open Set MeasureTheory
open scoped ENNReal NNReal

namespace Family8Family7NativeHighCriticalScaleProxySupportCoreV1

open LeanEval.Analysis.WangZahlKakeya
open Submission.Kakeya.ConvexGeometry
open Family8ContractedJohnActualTubeProxyV1
open Family8SelectedParentPlankFineProxyDatumV1

noncomputable section

/-!
# Unit-ball support for a centered affine-axis proxy

If both transformed endpoints lie in the quarter ball, their midpoint lies
there too.  The centered unit extension is then contained in the
three-quarter ball, and its `s ≤ 1/5` tube is contained in the unit ball.
-/

theorem norm_affineImageAxisCenter_le_quarter
    {radius : NNReal} (e : Space ≃ᵃ[Real] Space) (T : Tube radius)
    (hbase : ‖e T.axis.base‖ ≤ (1 / 4 : Real))
    (hend : ‖e T.axis.endpoint‖ ≤ (1 / 4 : Real)) :
    ‖affineImageAxisCenter e T‖ ≤ (1 / 4 : Real) := by
  unfold affineImageAxisCenter
  calc
    ‖(1 / 2 : Real) • (e T.axis.base + e T.axis.endpoint)‖ =
        (1 / 2 : Real) * ‖e T.axis.base + e T.axis.endpoint‖ := by
      rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (by norm_num)]
    _ ≤ (1 / 2 : Real) *
        (‖e T.axis.base‖ + ‖e T.axis.endpoint‖) := by
      gcongr
      exact norm_add_le _ _
    _ ≤ (1 / 2 : Real) * ((1 / 4 : Real) + (1 / 4 : Real)) := by
      gcongr
    _ = (1 / 4 : Real) := by norm_num

theorem affineImageUnitExtensionAxis_carrier_subset_closedBall_three_fourths
    {radius : NNReal} (e : Space ≃ᵃ[Real] Space) (T : Tube radius)
    (hbase : ‖e T.axis.base‖ ≤ (1 / 4 : Real))
    (hend : ‖e T.axis.endpoint‖ ≤ (1 / 4 : Real)) :
    (affineImageUnitExtensionAxis e T).carrier ⊆
      Metric.closedBall (0 : Space) (3 / 4 : Real) := by
  intro x hx
  rw [(affineImageUnitExtensionAxis e T).carrier_eq_image] at hx
  obtain ⟨u, hu, rfl⟩ := hx
  have hcenter := norm_affineImageAxisCenter_le_quarter e T hbase hend
  have huabs : |u - (1 / 2 : Real)| ≤ 1 / 2 := by
    rcases hu with ⟨hu0, hu1⟩
    rw [abs_le]
    constructor <;> linarith
  rw [Metric.mem_closedBall, dist_zero_right]
  rw [affineImageUnitExtensionAxis_base,
    affineImageUnitExtensionAxis_direction]
  have hrearrange :
      affineImageAxisCenter e T -
          (1 / 2 : Real) • affineImageAxisDirection e T +
          u • affineImageAxisDirection e T =
        affineImageAxisCenter e T +
          (u - 1 / 2 : Real) • affineImageAxisDirection e T := by
    module
  change ‖affineImageAxisCenter e T -
      (1 / 2 : Real) • affineImageAxisDirection e T +
      u • affineImageAxisDirection e T‖ ≤ 3 / 4
  rw [hrearrange]
  calc
    ‖affineImageAxisCenter e T +
        (u - 1 / 2 : Real) • affineImageAxisDirection e T‖ ≤
      ‖affineImageAxisCenter e T‖ +
        ‖(u - 1 / 2 : Real) • affineImageAxisDirection e T‖ :=
      norm_add_le _ _
    _ = ‖affineImageAxisCenter e T‖ + |u - 1 / 2| := by
      rw [norm_smul, Real.norm_eq_abs, norm_affineImageAxisDirection,
        mul_one]
    _ ≤ (1 / 4 : Real) + 1 / 2 := by gcongr
    _ = (3 / 4 : Real) := by norm_num

theorem affineAxisProxyTube_carrier_subset_closedBall_one
    {radius s : NNReal} (e : Space ≃ᵃ[Real] Space) (T : Tube radius)
    (hbase : ‖e T.axis.base‖ ≤ (1 / 4 : Real))
    (hend : ‖e T.axis.endpoint‖ ≤ (1 / 4 : Real))
    (hs : s ≤ (1 / 5 : NNReal)) :
    (affineAxisProxyTube s e T).carrier ⊆
      Metric.closedBall (0 : Space) 1 := by
  intro x hx
  change x ∈ Metric.cthickening (s : Real)
    (affineImageUnitExtensionAxis e T).carrier at hx
  rw [IsCompact.cthickening_eq_biUnion_closedBall
    (affineImageUnitExtensionAxis e T).isCompact_carrier
      (by positivity)] at hx
  rcases Set.mem_iUnion.mp hx with ⟨y, hy⟩
  rcases Set.mem_iUnion.mp hy with ⟨hyAxis, hxy⟩
  have hyBall :=
    affineImageUnitExtensionAxis_carrier_subset_closedBall_three_fourths
      e T hbase hend hyAxis
  rw [Metric.mem_closedBall, dist_zero_right] at hyBall ⊢
  rw [Metric.mem_closedBall] at hxy
  have hsReal : (s : Real) ≤ 1 / 5 := by exact_mod_cast hs
  calc
    ‖x‖ = ‖y + (x - y)‖ := by congr 1; abel
    _ ≤ ‖y‖ + ‖x - y‖ := norm_add_le _ _
    _ = ‖y‖ + dist x y := by rw [dist_eq_norm]
    _ ≤ (3 / 4 : Real) + 1 / 5 :=
      add_le_add hyBall (hxy.trans hsReal)
    _ ≤ 1 := by norm_num

#print axioms norm_affineImageAxisCenter_le_quarter
#print axioms affineImageUnitExtensionAxis_carrier_subset_closedBall_three_fourths
#print axioms affineAxisProxyTube_carrier_subset_closedBall_one

end

end Family8Family7NativeHighCriticalScaleProxySupportCoreV1
