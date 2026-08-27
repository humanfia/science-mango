import Mathlib.Tactic

set_option autoImplicit false
set_option warningAsError true

namespace FamilyStickyCinematicL32Prop41SampledLensCardinalityAssemblyV1

/-!
# Numerical assembly of sampling survival and the actual lens bound

This module isolates the final monotone-cardinality calculation.  It converts
the one-eighth sampling survival, the explicit three-kind lens estimate, and
the sampled-curve load bound into a single rectangle-count inequality.
-/

/-- The explicit three-kind lens right-hand side, extended to real inputs. -/
noncomputable def sampledLensBound (depth curveCount : Real) : Real :=
  curveCount + 3 *
    (16 * depth * curveCount * Real.sqrt curveCount +
      105 * curveCount * Real.sqrt curveCount)

theorem sampledLensBound_mono_curveCount
    {depth curveCount load : Real}
    (hdepth : 0 <= depth) (hcurve : 0 <= curveCount)
    (hcurveLoad : curveCount <= load) :
    sampledLensBound depth curveCount <= sampledLensBound depth load := by
  have hload : 0 <= load := hcurve.trans hcurveLoad
  have hsqrt : Real.sqrt curveCount <= Real.sqrt load :=
    Real.sqrt_le_sqrt hcurveLoad
  have hproduct :
      curveCount * Real.sqrt curveCount <= load * Real.sqrt load := by
    calc
      curveCount * Real.sqrt curveCount <=
          load * Real.sqrt curveCount :=
        mul_le_mul_of_nonneg_right hcurveLoad (Real.sqrt_nonneg curveCount)
      _ <= load * Real.sqrt load :=
        mul_le_mul_of_nonneg_left hsqrt hload
  unfold sampledLensBound
  have hweighted :
      16 * depth * (curveCount * Real.sqrt curveCount) <=
        16 * depth * (load * Real.sqrt load) :=
    mul_le_mul_of_nonneg_left hproduct (by positivity)
  have hunweighted :
      105 * (curveCount * Real.sqrt curveCount) <=
        105 * (load * Real.sqrt load) :=
    mul_le_mul_of_nonneg_left hproduct (by norm_num)
  nlinarith

/-- Real-valued endpoint: survival plus the actual lens estimate and curve
load monotonicity give the final explicit sampled bound. -/
theorem rectangleCount_le_eight_mul_sampledLensBound
    {rectangleCount itemCount curveCount depth load : Real}
    (hdepth : 0 <= depth) (hcurve : 0 <= curveCount)
    (hsurvival : rectangleCount / 8 <= itemCount)
    (hlens : itemCount <= sampledLensBound depth curveCount)
    (hcurveLoad : curveCount <= load) :
    rectangleCount <= 8 * sampledLensBound depth load := by
  have hmono := sampledLensBound_mono_curveCount hdepth hcurve hcurveLoad
  linarith

/-- Natural-cardinality form matching the sampling and selected-lens
interfaces used in the Family7 pipeline. -/
theorem rectangleCard_le_eight_mul_sampledLensBound
    (rectangleCard itemCard curveCard depth : Nat) (load : Real)
    (hsurvival : (rectangleCard : Real) / 8 <= (itemCard : Real))
    (hlens : (itemCard : Real) <=
      (curveCard : Real) + 3 *
        (16 * (depth : Real) * (curveCard : Real) *
            Real.sqrt (curveCard : Real) +
          105 * (curveCard : Real) * Real.sqrt (curveCard : Real)))
    (hcurveLoad : (curveCard : Real) <= load) :
    (rectangleCard : Real) <=
      8 * sampledLensBound (depth : Real) load := by
  apply rectangleCount_le_eight_mul_sampledLensBound
      (rectangleCount := (rectangleCard : Real))
      (itemCount := (itemCard : Real))
      (curveCount := (curveCard : Real))
      (depth := (depth : Real)) (load := load)
  · positivity
  · positivity
  · exact hsurvival
  · simpa only [sampledLensBound] using hlens
  · exact hcurveLoad

#print axioms sampledLensBound_mono_curveCount
#print axioms rectangleCount_le_eight_mul_sampledLensBound
#print axioms rectangleCard_le_eight_mul_sampledLensBound

end FamilyStickyCinematicL32Prop41SampledLensCardinalityAssemblyV1
