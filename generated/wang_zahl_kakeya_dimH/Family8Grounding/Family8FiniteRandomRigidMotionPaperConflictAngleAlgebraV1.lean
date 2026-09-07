import Family8Grounding.Family8FiniteRandomRigidMotionPaperConflictOverlapLowerV1
import Mathlib.Tactic

set_option autoImplicit false
set_option warningAsError true

open Set MeasureTheory
open scoped ENNReal NNReal InnerProductSpace

namespace Family8FiniteRandomRigidMotionPaperConflictAngleAlgebraV1

open LeanEval.Analysis.WangZahlKakeya
open Submission.Kakeya.ConvexGeometry
open Family4GlobalExtremalUpstream
open Family8FiniteRandomRigidMotionPaperConflictOverlapLowerV1

noncomputable section

/-!
# Algebraic extraction of the conflict angle

The geometric transverse-frame calculation should produce the cross-multiplied
upper bound `sin(angle) * |T ∩ U| ≤ 8 rho^3`.  This module combines that
single statement with the already proved conflict overlap lower bound and
cancels `rho^2`, leaving no probability or geometry in the deduction.
-/

/-- The paper-scale transverse overlap upper bound forces a `32 rho` sine
angle for every non-essentially-distinct positive-radius pair. -/
theorem sin_angle_le_thirtyTwo_mul_of_conflict_overlap_upper
    {rho : NNReal} (T U : Tube rho)
    (hrhoPos : 0 < rho) (hrho : rho ≤ (2 : NNReal)⁻¹)
    (hconflict : ¬ EssentiallyDistinct T U)
    (hupper :
      Real.sin (InnerProductGeometry.angle
          T.axis.direction U.axis.direction) *
          (volume (T.carrier ∩ U.carrier)).toReal ≤
        8 * (rho : Real) ^ 3) :
    Real.sin (InnerProductGeometry.angle
        T.axis.direction U.axis.direction) ≤
      32 * (rho : Real) := by
  have hlower :=
    half_half_sq_lt_volume_inter_of_not_essentiallyDistinct
      T U hrho hconflict
  have hinterTop : volume (T.carrier ∩ U.carrier) ≠ ∞ := by
    exact ne_of_lt
      ((measure_mono inter_subset_left).trans_lt T.volume_lt_top)
  have hlowerReal :=
    (ENNReal.toReal_lt_toReal (by finiteness) hinterTop).mpr hlower
  simp only [ENNReal.toReal_mul, ENNReal.toReal_inv,
    ENNReal.toReal_ofNat, ENNReal.toReal_div, ENNReal.toReal_pow,
    ENNReal.coe_toReal] at hlowerReal
  norm_num at hlowerReal
  have hsinNonneg :
      0 ≤ Real.sin (InnerProductGeometry.angle
        T.axis.direction U.axis.direction) :=
    InnerProductGeometry.sin_angle_nonneg _ _
  have hmul := mul_le_mul_of_nonneg_left hlowerReal.le hsinNonneg
  have hquarter :
      (1 / 2 : Real) * ((rho : Real) ^ 2 / 2) =
        (rho : Real) ^ 2 / 4 := by
    ring
  rw [hquarter] at hmul
  have hpoly :
      Real.sin (InnerProductGeometry.angle
          T.axis.direction U.axis.direction) *
          ((rho : Real) ^ 2 / 4) ≤
        8 * (rho : Real) ^ 3 :=
    by exact hmul.trans hupper
  have hrhoRealPos : 0 < (rho : Real) := NNReal.coe_pos.mpr hrhoPos
  nlinarith [sq_pos_of_pos hrhoRealPos]

#print axioms sin_angle_le_thirtyTwo_mul_of_conflict_overlap_upper

end
end Family8FiniteRandomRigidMotionPaperConflictAngleAlgebraV1
