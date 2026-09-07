import Family8Grounding.Family8Family7CriticalScaleAffineJacobianV4
import Family8Grounding.Family8SelectedParentPlankFineProxyKatzTaoV3
import Family8Grounding.Family8Family7NativeHighCriticalScaleProxyGeometryV1

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 1200000

open scoped ENNReal NNReal

namespace Family8Family7CriticalScaleProxyVolumeLossV2

open LeanEval.Analysis.WangZahlKakeya
open Family6AffineConvexVolumeCoreV1
open Family8Family7CriticalScaleAffineJacobianV4
open Family8Family7NativeHighCriticalScaleAffineMapV1
open Family8Family7NativeHighCriticalScaleProxyGeometryV1
open Family8SelectedParentPlankFineProxyKatzTaoV3

noncomputable section

/-!
# Fixed volume loss of the critical-scale round proxy, V2

V1 omitted one `toReal_ofReal` normalization and is not imported.
-/

def criticalScaleAffineProxyVolumeLoss : ENNReal := 262144

theorem affineAxisProxyVolumeRatio_criticalScale_eq_loss_mul_jacobian
    (radius : NNReal) (hradius : 0 < radius)
    (t : Real) (ht : 0 < t) (a0 b0 c0 d0 : Real) :
    affineAxisProxyVolumeRatio radius
        (criticalScaleProxyRadius radius t ht) =
      criticalScaleAffineProxyVolumeLoss *
        affineJacobian (criticalScaleAffineEquiv t ht a0 b0 c0 d0) := by
  have hleftTop : affineAxisProxyVolumeRatio radius
      (criticalScaleProxyRadius radius t ht) ≠ ∞ := by
    unfold affineAxisProxyVolumeRatio
    apply ENNReal.div_ne_top
    · exact ENNReal.mul_ne_top (by norm_num)
        (ENNReal.pow_ne_top ENNReal.coe_ne_top)
    · exact ENNReal.div_ne_zero.mpr
        ⟨pow_ne_zero 2 (ENNReal.coe_ne_zero.mpr hradius.ne'), by norm_num⟩
  have hrightTop : criticalScaleAffineProxyVolumeLoss *
      affineJacobian (criticalScaleAffineEquiv t ht a0 b0 c0 d0) ≠ ∞ := by
    exact ENNReal.mul_ne_top (by norm_num [criticalScaleAffineProxyVolumeLoss])
      (affineJacobian_ne_top _)
  apply (ENNReal.toReal_eq_toReal_iff' hleftTop hrightTop).mp
  have hradiusReal : (0 : Real) < (radius : Real) := by exact_mod_cast hradius
  norm_num [affineAxisProxyVolumeRatio, criticalScaleProxyRadius_coe,
    criticalScaleAffineProxyVolumeLoss,
    affineJacobian_criticalScaleAffineEquiv,
    ENNReal.toReal_div, ENNReal.toReal_mul, ENNReal.toReal_pow,
    ENNReal.toReal_ofReal ht.le]
  field_simp [hradiusReal.ne', ht.ne']
  ring

#print axioms
  affineAxisProxyVolumeRatio_criticalScale_eq_loss_mul_jacobian

end
end Family8Family7CriticalScaleProxyVolumeLossV2
