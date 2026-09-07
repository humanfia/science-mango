import Family8Grounding.Family8PolynomialJohnFrameBoxTestNetV1

set_option autoImplicit false
set_option warningAsError true
set_option linter.unusedSectionVars false

open Set
open scoped NNReal InnerProductSpace BigOperators

namespace Family8PolynomialJohnFrameBoxPerturbationCoreV4

open LeanEval.Analysis.WangZahlKakeya
open Submission.Kakeya.ConvexGeometry
open Family8PolynomialJohnFrameBoxTestNetV1

noncomputable section

theorem abs_apply_le_one_of_mem_unitBall {x : Space}
    (hx : x ∈ Metric.closedBall (0 : Space) 1) (j : Fin 3) :
    |x j| ≤ 1 := by
  have hnorm : ‖x‖ ≤ 1 := by
    simpa [Metric.mem_closedBall, dist_eq_norm] using hx
  have hj := PiLp.norm_apply_le x j
  rw [Real.norm_eq_abs] at hj
  exact hj.trans hnorm

theorem abs_apply_sub_apply_le_two {x y : Space}
    (hx : x ∈ Metric.closedBall (0 : Space) 1)
    (hy : y ∈ Metric.closedBall (0 : Space) 1) (j : Fin 3) :
    |x j - y j| ≤ 2 := by
  calc
    |x j - y j| ≤ |x j| + |y j| := abs_sub _ _
    _ ≤ 1 + 1 := add_le_add
      (abs_apply_le_one_of_mem_unitBall hx j)
      (abs_apply_le_one_of_mem_unitBall hy j)
    _ = 2 := by norm_num

theorem abs_inner_lt_three_mul
    {u v : Space} {mesh bound : Real} (hbound : 0 < bound)
    (hu : ∀ j, |u j| < mesh) (hv : ∀ j, |v j| ≤ bound) :
    |⟪u, v⟫_Real| < 3 * mesh * bound := by
  rw [show ⟪u, v⟫_Real = ∑ j : Fin 3, u j * v j by
    simp [PiLp.inner_apply, RCLike.inner_apply, mul_comm],
    Fin.sum_univ_three]
  have hterm (j : Fin 3) : |u j| * |v j| < mesh * bound := by
    calc
      |u j| * |v j| ≤ |u j| * bound :=
        mul_le_mul_of_nonneg_left (hv j) (abs_nonneg _)
      _ < mesh * bound := mul_lt_mul_of_pos_right (hu j) hbound
  calc
    |u 0 * v 0 + u 1 * v 1 + u 2 * v 2| ≤
        |u 0 * v 0| + |u 1 * v 1| + |u 2 * v 2| :=
      abs_add_three _ _ _
    _ < mesh * bound + mesh * bound + mesh * bound := by
      exact add_lt_add
        (add_lt_add (by simpa only [abs_mul] using hterm 0)
          (by simpa only [abs_mul] using hterm 1))
        (by simpa only [abs_mul] using hterm 2)
    _ = 3 * mesh * bound := by ring

theorem frame_error_inner_lt_six_mesh
    {delta : NNReal} (hdelta : 0 < delta)
    (p : CapturedJohnParameter delta) (i : Fin 3)
    {x : Space} (hx : x ∈ Metric.closedBall (0 : Space) 1) :
    let r := representativeParameter delta hdelta (parameterCode hdelta p)
    |⟪r.certificate.box.frame i - p.certificate.box.frame i,
        x - p.certificate.box.center⟫_Real| < 6 * parameterMesh delta := by
  let r := representativeParameter delta hdelta (parameterCode hdelta p)
  have hframe (j : Fin 3) :
      |(r.certificate.box.frame i - p.certificate.box.frame i) j| <
        parameterMesh delta := by
    simpa only [PiLp.sub_apply, abs_sub_comm] using
      frame_coordinate_close hdelta p i j
  have hpoint (j : Fin 3) :
      |(x - p.certificate.box.center) j| ≤ 2 := by
    simpa only [PiLp.sub_apply] using
      abs_apply_sub_apply_le_two hx p.center_mem_unitBall j
  have h := abs_inner_lt_three_mul
    (by norm_num : (0 : Real) < 2) hframe hpoint
  simpa only [show (3 : Real) * parameterMesh delta * 2 =
      6 * parameterMesh delta by ring] using h

theorem center_error_inner_lt_three_mesh
    {delta : NNReal} (hdelta : 0 < delta)
    (p : CapturedJohnParameter delta) (i : Fin 3) :
    let r := representativeParameter delta hdelta (parameterCode hdelta p)
    |⟪r.certificate.box.frame i,
        p.certificate.box.center - r.certificate.box.center⟫_Real| <
      3 * parameterMesh delta := by
  let r := representativeParameter delta hdelta (parameterCode hdelta p)
  have hcenter (j : Fin 3) :
      |(p.certificate.box.center - r.certificate.box.center) j| <
        parameterMesh delta := by
    simpa only [PiLp.sub_apply] using center_coordinate_close hdelta p j
  have hframe (j : Fin 3) : |(r.certificate.box.frame i) j| ≤ 1 :=
    r.abs_frame_apply_le_one i j
  dsimp only
  rw [real_inner_comm]
  have h := abs_inner_lt_three_mul
    (by norm_num : (0 : Real) < 1) hcenter hframe
  simpa using h

#print axioms abs_apply_le_one_of_mem_unitBall
#print axioms abs_apply_sub_apply_le_two
#print axioms abs_inner_lt_three_mul
#print axioms frame_error_inner_lt_six_mesh
#print axioms center_error_inner_lt_three_mesh

end
end Family8PolynomialJohnFrameBoxPerturbationCoreV4
