import Family8Grounding.Family8FiniteRandomRigidMotionPaperConflictOverlapLowerV1
import Family8Grounding.Family8FiniteRandomRigidMotionPaperTransverseCoordinateAngleV1
import Family8Grounding.Family8FiniteRandomRigidMotionPaperCommonPointElongatedBudgetV1
import Mathlib.Tactic

set_option autoImplicit false
set_option warningAsError true

open Set MeasureTheory
open scoped ENNReal NNReal InnerProductSpace

namespace Family8FiniteRandomRigidMotionPaperConflictToElongatedViaAngleV1

open LeanEval.Analysis.WangZahlKakeya
open Submission.Kakeya.ConvexGeometry
open Family4GlobalExtremalUpstream
open Family8FiniteRandomRigidMotionPaperElongatedFrameTestV1
open Family8FiniteRandomRigidMotionPaperConflictOverlapLowerV1
open Family8FiniteRandomRigidMotionPaperTransverseCoordinateAngleV1
open Family8FiniteRandomRigidMotionPaperCommonPointElongatedBudgetV1

noncomputable section

/-!
# The exact remaining angular seam

The volume conflict already gives a common carrier point.  Once the sine of
the unoriented axis angle is at most `90 rho`, the side-six elongated body
contains the whole conflicting tube.  Thus the only remaining geometry is
the transverse-overlap comparison producing that sine bound.
-/

theorem carrier_subset_paperElongatedBody_of_not_essentiallyDistinct_of_sin_le
    {rho : NNReal} (T U : Tube rho)
    (frame : OrthonormalBasis (Fin 3) Real Space)
    (hframe : frame 2 = T.axis.direction)
    (hrhoPos : 0 < rho) (hrho : rho ≤ (1 / 100 : NNReal))
    (hconflict : ¬ EssentiallyDistinct T U)
    (hsin : Real.sin
      (InnerProductGeometry.angle T.axis.direction U.axis.direction) ≤
        90 * (rho : Real)) :
    U.carrier ⊆ (paperElongatedBody T frame : Set Space) := by
  have hrhoHalf : rho ≤ (2 : NNReal)⁻¹ := by
    calc
      rho ≤ (1 / 100 : NNReal) := hrho
      _ ≤ (2 : NNReal)⁻¹ := by
        simpa only [one_div] using
          (inv_anti₀ (show (0 : NNReal) < 2 by norm_num)
            (show (2 : NNReal) ≤ 100 by norm_num))
  obtain ⟨x, hxT, hxU⟩ :=
    inter_carrier_nonempty_of_not_essentiallyDistinct
      T U hrhoPos hrhoHalf hconflict
  apply carrier_subset_paperElongatedBody_of_commonPoint
    T U x frame hframe hrho hxT hxU
  intro k hk
  exact (abs_inner_frame_le_sin_angle_of_ne_two
    frame T.axis.direction U.axis.direction hframe
      T.axis.norm_direction U.axis.norm_direction k hk).trans hsin

#print axioms
  carrier_subset_paperElongatedBody_of_not_essentiallyDistinct_of_sin_le

end
end Family8FiniteRandomRigidMotionPaperConflictToElongatedViaAngleV1
