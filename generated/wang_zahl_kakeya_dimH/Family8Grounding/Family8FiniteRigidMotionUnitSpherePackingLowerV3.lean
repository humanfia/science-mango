import Family8Grounding.Family8FiniteRigidMotionUnitSpherePackingV3
import Mathlib.MeasureTheory.Measure.Lebesgue.VolumeOfBalls
import Mathlib.Tactic

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 2000000

open Set MeasureTheory
open scoped ENNReal NNReal BigOperators InnerProductSpace

namespace Family8FiniteRigidMotionUnitSpherePackingLowerV3

open LeanEval.Analysis.WangZahlKakeya
open Family8FiniteRigidMotionUnitSpherePackingV3

noncomputable section

/-!
# The complementary lower cardinality bound for the maximal sphere net

The maximal `2*mesh`-separated set covers the unit sphere at radius `2*mesh`.
Radially projecting the shell of thickness `mesh` to the sphere therefore
covers that three-dimensional shell by `3*mesh` balls.  Exact ball volumes
then give a dimension-two lower bound on the number of directions.
-/

theorem norm_inv_norm_smul (x : Space) (hx : x ≠ 0) :
    ‖(‖x‖ : Real)⁻¹ • x‖ = 1 := by
  have hnorm : ‖x‖ ≠ 0 := norm_ne_zero_iff.mpr hx
  rw [norm_smul, Real.norm_eq_abs, abs_inv, abs_of_nonneg (norm_nonneg x)]
  exact inv_mul_cancel₀ hnorm

theorem dist_inv_norm_smul (x : Space) (hx : x ≠ 0) :
    dist x ((‖x‖ : Real)⁻¹ • x) = |‖x‖ - 1| := by
  have hnorm : ‖x‖ ≠ 0 := norm_ne_zero_iff.mpr hx
  have hsub : x - (‖x‖ : Real)⁻¹ • x =
      (1 - (‖x‖ : Real)⁻¹) • x := by
    rw [sub_smul, one_smul]
  rw [dist_eq_norm, hsub, norm_smul, Real.norm_eq_abs]
  calc
    |1 - (‖x‖ : Real)⁻¹| * ‖x‖ =
        |1 - (‖x‖ : Real)⁻¹| * |‖x‖| := by
          rw [abs_of_nonneg (norm_nonneg x)]
    _ = |(1 - (‖x‖ : Real)⁻¹) * ‖x‖| := by
      rw [abs_mul]
    _ = |‖x‖ - 1| := by
      congr 1
      field_simp

theorem unitSphereShell_subset_choiceBalls
    (mesh : NNReal) (hmesh : 0 < mesh) (hmeshHalf : mesh ≤ 1 / 2) :
    Metric.ball (0 : Space) (1 + (mesh : Real)) \
        Metric.closedBall (0 : Space) (1 - (mesh : Real)) ⊆
      ⋃ g : UnitDirectionChoice mesh hmesh,
        Metric.ball (g.1 : Space) (3 * (mesh : Real)) := by
  intro x hx
  have hmeshReal : 0 < (mesh : Real) := NNReal.coe_pos.mpr hmesh
  have hmeshRealHalf : (mesh : Real) ≤ 1 / 2 := by exact_mod_cast hmeshHalf
  have hxUpper : ‖x‖ < 1 + (mesh : Real) := by
    simpa [Metric.mem_ball, dist_zero_left] using hx.1
  have hxNotInner := hx.2
  have hxLower : 1 - (mesh : Real) < ‖x‖ := by
    rw [Metric.mem_closedBall, dist_zero_right] at hxNotInner
    exact lt_of_not_ge hxNotInner
  have hxNormPos : 0 < ‖x‖ := by linarith
  have hxne : x ≠ 0 := norm_ne_zero_iff.mp hxNormPos.ne'
  let v : Space := (‖x‖ : Real)⁻¹ • x
  have hvNorm : ‖v‖ = 1 := by
    simpa only [v] using norm_inv_norm_smul x hxne
  obtain ⟨g, hvg⟩ := unitDirectionChoice_cover mesh hmesh v hvNorm
  have hvgReal : dist v (g.1 : Space) ≤ ((2 * mesh : NNReal) : Real) := by
    have htoReal := ENNReal.toReal_mono ENNReal.coe_ne_top hvg
    simpa [edist_dist] using htoReal
  have hradial : dist x v < (mesh : Real) := by
    rw [show dist x v = |‖x‖ - 1| by
      simpa only [v] using dist_inv_norm_smul x hxne]
    rw [abs_lt]
    constructor <;> linarith
  apply Set.mem_iUnion.mpr
  refine ⟨g, ?_⟩
  rw [Metric.mem_ball]
  calc
    dist x (g.1 : Space) ≤ dist x v + dist v (g.1 : Space) :=
      dist_triangle _ _ _
    _ < (mesh : Real) + ((2 * mesh : NNReal) : Real) :=
      add_lt_add_of_lt_of_le hradial hvgReal
    _ = 3 * (mesh : Real) := by
      push_cast
      ring

theorem two_le_nine_card_mul_mesh_sq
    (mesh : NNReal) (hmesh : 0 < mesh) (hmeshHalf : mesh ≤ 1 / 2) :
    2 ≤ 9 * (Fintype.card (UnitDirectionChoice mesh hmesh) : Real) *
      (mesh : Real) ^ 2 := by
  let r : Real := mesh
  let outer : Set Space := Metric.ball (0 : Space) (1 + r)
  let inner : Set Space := Metric.closedBall (0 : Space) (1 - r)
  let shell : Set Space := outer \ inner
  let covering : Set Space :=
    ⋃ g : UnitDirectionChoice mesh hmesh,
      Metric.ball (g.1 : Space) (3 * r)
  have hr : 0 < r := NNReal.coe_pos.mpr hmesh
  have hrHalf : r ≤ 1 / 2 := by exact_mod_cast hmeshHalf
  have hinnerRadius : 0 ≤ 1 - r := by linarith
  have houterRadius : 0 ≤ 1 + r := by linarith
  have hshellCover : shell ⊆ covering := by
    simpa only [shell, outer, inner, covering, r] using
      unitSphereShell_subset_choiceBalls mesh hmesh hmeshHalf
  have hinnerOuter : inner ⊆ outer := by
    intro x hx
    rw [Metric.mem_closedBall] at hx
    rw [Metric.mem_ball]
    exact lt_of_le_of_lt hx (by linarith)
  have hshellVolume :
      volume shell = volume outer - volume inner := by
    exact measure_sdiff hinnerOuter measurableSet_closedBall.nullMeasurableSet
      measure_closedBall_lt_top.ne
  have hmeasure : volume shell ≤
      ∑' g : UnitDirectionChoice mesh hmesh,
        volume (Metric.ball (g.1 : Space) (3 * r)) :=
    (measure_mono hshellCover).trans (measure_iUnion_le _)
  have hsumNeTop :
      (∑' g : UnitDirectionChoice mesh hmesh,
        volume (Metric.ball (g.1 : Space) (3 * r))) ≠ ∞ := by
    rw [tsum_fintype, ENNReal.sum_ne_top]
    intro g hg
    exact measure_ball_lt_top.ne
  have hmeasureReal := ENNReal.toReal_mono hsumNeTop hmeasure
  have hinnerVolumeLe : volume inner ≤ volume outer := measure_mono hinnerOuter
  have hshellReal :
      (volume shell).toReal =
        (1 + r) ^ 3 * (Real.pi * 4 / 3) -
          (1 - r) ^ 3 * (Real.pi * 4 / 3) := by
    rw [hshellVolume,
      ENNReal.toReal_sub_of_le hinnerVolumeLe measure_ball_lt_top.ne]
    simp only [outer, inner, EuclideanSpace.volume_ball_fin_three,
      EuclideanSpace.volume_closedBall_fin_three]
    rw [ENNReal.toReal_mul, ENNReal.toReal_pow,
      ENNReal.toReal_mul, ENNReal.toReal_pow]
    · simp only [ENNReal.toReal_ofReal houterRadius,
        ENNReal.toReal_ofReal hinnerRadius]
      rw [ENNReal.toReal_ofReal (by positivity :
        0 ≤ Real.pi * 4 / 3)]
  have hthreeNonneg : 0 ≤ 3 * r := by positivity
  have hpiNonneg : 0 ≤ Real.pi * 4 / 3 := by positivity
  have hcoverReal :
      (∑' g : UnitDirectionChoice mesh hmesh,
        volume (Metric.ball (g.1 : Space) (3 * r))).toReal =
      (Fintype.card (UnitDirectionChoice mesh hmesh) : Real) *
        (3 * r) ^ 3 * (Real.pi * 4 / 3) := by
    simp only [EuclideanSpace.volume_ball_fin_three, tsum_fintype,
      Finset.sum_const, nsmul_eq_mul]
    rw [ENNReal.toReal_mul, ENNReal.toReal_mul, ENNReal.toReal_pow]
    · simp only [ENNReal.toReal_natCast,
        ENNReal.toReal_ofReal hthreeNonneg,
        ENNReal.toReal_ofReal hpiNonneg, Finset.card_univ]
      ring
  rw [hshellReal, hcoverReal] at hmeasureReal
  have hpi : 0 < Real.pi * 4 / 3 := by positivity
  have hcore :
      (1 + r) ^ 3 - (1 - r) ^ 3 ≤
        (Fintype.card (UnitDirectionChoice mesh hmesh) : Real) *
          (3 * r) ^ 3 := by
    apply (mul_le_mul_iff_right₀ hpi).mp
    nlinarith
  have hresult : 2 ≤
      9 * (Fintype.card (UnitDirectionChoice mesh hmesh) : Real) * r ^ 2 := by
    have hcard : 0 ≤
        (Fintype.card (UnitDirectionChoice mesh hmesh) : Real) :=
      Nat.cast_nonneg _
    nlinarith
  simpa only [r] using hresult

#print axioms norm_inv_norm_smul
#print axioms dist_inv_norm_smul
#print axioms unitSphereShell_subset_choiceBalls
#print axioms two_le_nine_card_mul_mesh_sq

end
end Family8FiniteRigidMotionUnitSpherePackingLowerV3
