import Family8Grounding.Family8Family7NativeHighCriticalBallAffineProxyV1
import FamilyStickyGrounding.Cinematic.FamilyStickyCinematicL32Prop41ActualTubeCNormalizationV1
import Mathlib.Tactic

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 500000

open Set MeasureTheory
open scoped ENNReal NNReal

namespace Family8Family7NativeHighCriticalScaleAffineMapV1

open LeanEval.Analysis.WangZahlKakeya
open Submission.Kakeya.ConvexGeometry
open Family8ContractedJohnActualTubeProxyV1
open Family8Family7NativeHighCriticalBallAffineProxyV1
open FamilyStickyCinematicL32ActualTubeCoefficientDistancesV1
open FamilyStickyCinematicL32Prop41ActualTubeCNormalizationV1
open FamilyStickyWZ2ProjectionSliceRetentionV1

noncomputable section

/-!
# Concrete affine normalization around one critical tube

The map subtracts the four graph coefficients of a reference tube, divides
the two transverse coordinates by the critical scale, and applies a common
factor `1/16` in all three coordinates.  The common contraction is what lets
the honest affine image fit in a unit-axis proxy while preserving graph-slope
ratios and the final-coordinate chart.
-/

/-- Linear part of the critical-scale graph normalization. -/
def criticalScaleLinearEquiv
    (t : Real) (ht : 0 < t) (c0 d0 : Real) : Space ≃ₗ[Real] Space where
  toFun p := point3
    ((p 0 - c0 * p 2) / (16 * t))
    ((p 1 - d0 * p 2) / (16 * t))
    (p 2 / 16)
  invFun p := point3
    (16 * t * p 0 + 16 * c0 * p 2)
    (16 * t * p 1 + 16 * d0 * p 2)
    (16 * p 2)
  left_inv p := by
    ext i
    fin_cases i <;>
      simp [point3]
    all_goals field_simp [ht.ne'] <;> ring
  right_inv p := by
    ext i
    fin_cases i <;>
      simp [point3]
    all_goals field_simp [ht.ne']; ring
  map_add' p q := by
    ext i
    fin_cases i <;> simp [point3] <;> ring
  map_smul' a p := by
    ext i
    fin_cases i <;> simp [point3] <;> ring

@[simp] theorem criticalScaleLinearEquiv_apply
    (t : Real) (ht : 0 < t) (c0 d0 : Real) (p : Space) :
    criticalScaleLinearEquiv t ht c0 d0 p = point3
      ((p 0 - c0 * p 2) / (16 * t))
      ((p 1 - d0 * p 2) / (16 * t))
      (p 2 / 16) :=
  rfl

/-- Affine normalization subtracting graph intercepts `a0,b0` as well. -/
def criticalScaleAffineEquiv
    (t : Real) (ht : 0 < t) (a0 b0 c0 d0 : Real) :
    Space ≃ᵃ[Real] Space :=
  AffineEquiv.mk'
    (fun p => point3
      ((p 0 - a0 - c0 * p 2) / (16 * t))
      ((p 1 - b0 - d0 * p 2) / (16 * t))
      (p 2 / 16))
    (criticalScaleLinearEquiv t ht c0 d0) 0 (by
      intro p
      ext i
      fin_cases i <;>
        simp [criticalScaleLinearEquiv, point3] <;>
        ring)

@[simp] theorem criticalScaleAffineEquiv_apply
    (t : Real) (ht : 0 < t) (a0 b0 c0 d0 : Real) (p : Space) :
    criticalScaleAffineEquiv t ht a0 b0 c0 d0 p = point3
      ((p 0 - a0 - c0 * p 2) / (16 * t))
      ((p 1 - b0 - d0 * p 2) / (16 * t))
      (p 2 / 16) :=
  rfl

@[simp] theorem criticalScaleAffineEquiv_linear
    (t : Real) (ht : 0 < t) (a0 b0 c0 d0 : Real) :
    (criticalScaleAffineEquiv t ht a0 b0 c0 d0).linear =
      criticalScaleLinearEquiv t ht c0 d0 :=
  rfl

theorem affineImageAxisVector_criticalScale_apply_zero
    {radius : NNReal} (t : Real) (ht : 0 < t)
    (a0 b0 c0 d0 : Real) (T : Tube radius) :
    (affineImageAxisVector
      (criticalScaleAffineEquiv t ht a0 b0 c0 d0) T) 0 =
      (T.axis.direction 0 - c0 * T.axis.direction 2) / (16 * t) := by
  rw [affineImageAxisVector_eq_linear]
  rfl

theorem affineImageAxisVector_criticalScale_apply_one
    {radius : NNReal} (t : Real) (ht : 0 < t)
    (a0 b0 c0 d0 : Real) (T : Tube radius) :
    (affineImageAxisVector
      (criticalScaleAffineEquiv t ht a0 b0 c0 d0) T) 1 =
      (T.axis.direction 1 - d0 * T.axis.direction 2) / (16 * t) := by
  rw [affineImageAxisVector_eq_linear]
  rfl

theorem affineImageAxisVector_criticalScale_apply_two
    {radius : NNReal} (t : Real) (ht : 0 < t)
    (a0 b0 c0 d0 : Real) (T : Tube radius) :
    (affineImageAxisVector
      (criticalScaleAffineEquiv t ht a0 b0 c0 d0) T) 2 =
      T.axis.direction 2 / 16 := by
  rw [affineImageAxisVector_eq_linear]
  rfl

#print axioms criticalScaleLinearEquiv
#print axioms criticalScaleAffineEquiv
#print axioms affineImageAxisVector_criticalScale_apply_zero
#print axioms affineImageAxisVector_criticalScale_apply_one
#print axioms affineImageAxisVector_criticalScale_apply_two

end

end Family8Family7NativeHighCriticalScaleAffineMapV1
