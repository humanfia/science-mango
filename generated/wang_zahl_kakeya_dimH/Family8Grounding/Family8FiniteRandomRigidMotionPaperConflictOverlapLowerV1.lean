import Family8Grounding.Family8FiniteRandomRigidMotionB2FreshGreedyV1
import Submission.Kakeya.ConvexFactoring.TubeVolumeBounds
import Mathlib.Tactic

set_option autoImplicit false
set_option warningAsError true

open Set MeasureTheory
open scoped ENNReal NNReal

namespace Family8FiniteRandomRigidMotionPaperConflictOverlapLowerV1

open LeanEval.Analysis.WangZahlKakeya
open Submission.Kakeya.ConvexGeometry
open Family4GlobalExtremalUpstream

noncomputable section

/-!
# Quantitative overlap forced by a normalized conflict

Failure of WZ essential distinctness gives more than a common point: it gives
a strict lower bound for the overlap volume at the square of the tube radius.
This is the lower half of the angle comparison with the existing transverse
frame-box overlap bound.
-/

/-- A non-essentially-distinct pair overlaps by more than one half of the
standard lower tube-volume bound. -/
theorem half_half_sq_lt_volume_inter_of_not_essentiallyDistinct
    {rho : NNReal} (T U : Tube rho)
    (hrho : rho ≤ (2 : NNReal)⁻¹)
    (hconflict : ¬ EssentiallyDistinct T U) :
    (2 : ENNReal)⁻¹ * ((rho : ENNReal) ^ 2 / 2) <
      volume (T.carrier ∩ U.carrier) := by
  have hoverlap :
      (2 : ENNReal)⁻¹ *
          max (volume T.carrier) (volume U.carrier) <
        volume (T.carrier ∩ U.carrier) := by
    exact lt_of_not_ge hconflict
  have hlower :
      (rho : ENNReal) ^ 2 / 2 ≤
        max (volume T.carrier) (volume U.carrier) :=
    (T.half_sq_le_volume_of_le_half hrho).trans (le_max_left _ _)
  have hscaled := mul_le_mul' (le_refl ((2 : ENNReal)⁻¹)) hlower
  exact hscaled.trans_lt hoverlap

/-- With positive radius, every conflict has an actual common point. -/
theorem inter_carrier_nonempty_of_not_essentiallyDistinct
    {rho : NNReal} (T U : Tube rho)
    (hrhoPos : 0 < rho) (hrho : rho ≤ (2 : NNReal)⁻¹)
    (hconflict : ¬ EssentiallyDistinct T U) :
    (T.carrier ∩ U.carrier).Nonempty := by
  have hlower :=
    half_half_sq_lt_volume_inter_of_not_essentiallyDistinct
      T U hrho hconflict
  have hpos : 0 < (2 : ENNReal)⁻¹ * ((rho : ENNReal) ^ 2 / 2) := by
    have hrho0 : (rho : ENNReal) ≠ 0 := ENNReal.coe_ne_zero.mpr hrhoPos.ne'
    have hfloorPos : 0 < (rho : ENNReal) ^ 2 / 2 :=
      ENNReal.div_pos (pow_ne_zero 2 hrho0) (by norm_num)
    exact ENNReal.mul_pos (by norm_num) hfloorPos.ne'
  exact nonempty_of_measure_ne_zero (ne_of_gt (hpos.trans hlower))

#print axioms half_half_sq_lt_volume_inter_of_not_essentiallyDistinct
#print axioms inter_carrier_nonempty_of_not_essentiallyDistinct

end
end Family8FiniteRandomRigidMotionPaperConflictOverlapLowerV1
