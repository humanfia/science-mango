import FamilyStickyCinematicL32PyzActualAllCenterBinUniformityV1
import FamilyStickyCinematicL32PyzCriticalBinUniformityV1

set_option autoImplicit false

open scoped ENNReal

namespace FamilyStickyCinematicL32PyzFixedBandBinLossCompressionCleanV1

open FamilyStickyCinematicL32ContinuumCriticalSingleDyadicSelectionV1
open FamilyStickyCinematicL32PyzActualAllCenterBinUniformityV1
open FamilyStickyCinematicL32PyzCriticalBinUniformityV1

noncomputable section

/-!
# Exact compression of the three fixed-band dyadic losses

The norm and tangency critical-scale losses have the same radius-dependent
upper bound.  The last positive-multiplicity loss is already independent of
the norm-cover centre, but it is kept literally as the input ambient-card
factor.  Thus no unproved comparison between the ambient cardinality and a
logarithmic budget is hidden in this module.
-/

/-- The literal norm loss multiplied by the common two-stage post-norm loss. -/
def actualFixedBandThreeBinLoss
    (radius : NNReal) (globalScale : Real) (ambientCard : Nat) : ENNReal :=
  (continuumCriticalSingleDyadicBinFactor (radius : Real) 16 : ENNReal) *
    actualAllCenterPostNormBinLoss radius globalScale ambientCard

/-- Only the norm and tangency factors cost the square of the common critical
bin slack.  The final ambient-card factor remains exact. -/
theorem actualFixedBandThreeBinLoss_le_uniformSlack_sq_mul_final
    {radius : NNReal} {globalScale : Real} {ambientCard : Nat}
    (hradius : 0 < radius)
    (hradiusTangency : (radius : Real) ≤ 36 * globalScale)
    (hglobalScale : globalScale ≤ 32) :
    actualFixedBandThreeBinLoss radius globalScale ambientCard ≤
      (pyzCriticalBinUniformSlack (radius : Real) : ENNReal) ^ 2 *
        (continuumCriticalSingleDyadicBinFactor 1
          (ambientCard : Real) : ENNReal) := by
  have hcritical :=
    norm_mul_tangencyCriticalBinFactors_cast_le_uniformSlack_sq
      (by exact_mod_cast hradius) hradiusTangency hglobalScale
  unfold actualFixedBandThreeBinLoss actualAllCenterPostNormBinLoss
  simpa only [mul_assoc] using
    (mul_le_mul_left hcritical
      (continuumCriticalSingleDyadicBinFactor 1
        (ambientCard : Real) : ENNReal))

/-- If the paper's preallocated natural logarithmic count dominates the
common critical-bin slack, the two radius-dependent losses cost at most its
square.  No condition on the final ambient-card factor is added. -/
theorem actualFixedBandThreeBinLoss_le_logCount_sq_mul_final
    {radius : NNReal} {globalScale : Real} {ambientCard logCount : Nat}
    (hradius : 0 < radius)
    (hradiusTangency : (radius : Real) ≤ 36 * globalScale)
    (hglobalScale : globalScale ≤ 32)
    (hslack : pyzCriticalBinUniformSlack (radius : Real) ≤ logCount) :
    actualFixedBandThreeBinLoss radius globalScale ambientCard ≤
      (logCount : ENNReal) ^ 2 *
        (continuumCriticalSingleDyadicBinFactor 1
          (ambientCard : Real) : ENNReal) := by
  have hbase := actualFixedBandThreeBinLoss_le_uniformSlack_sq_mul_final
    hradius hradiusTangency hglobalScale (ambientCard := ambientCard)
  have hslackCast :
      (pyzCriticalBinUniformSlack (radius : Real) : ENNReal) ≤
        (logCount : ENNReal) := by
    exact_mod_cast hslack
  have hsquare :
      (pyzCriticalBinUniformSlack (radius : Real) : ENNReal) ^ 2 ≤
        (logCount : ENNReal) ^ 2 :=
    pow_le_pow_left' hslackCast 2
  exact hbase.trans (mul_le_mul_left hsquare _)

#print axioms actualFixedBandThreeBinLoss
#print axioms actualFixedBandThreeBinLoss_le_uniformSlack_sq_mul_final
#print axioms actualFixedBandThreeBinLoss_le_logCount_sq_mul_final

end

end FamilyStickyCinematicL32PyzFixedBandBinLossCompressionCleanV1
