import Family8Grounding.Family8EighthNormalizedFamilyVolumeLowerV1
import Family8Grounding.Family8EighthNormalizedKatzTaoAmbientFrostmanV2
import Family8Grounding.Family8AmbientFamilyVolumeDensityV2
import Mathlib.Tactic

/-!
# Ambient-density cancellation in the eighth-normalized Frostman constant

When the source Katz--Tao constant is obtained by multiplying a base
constant by the literal family-volume density in an ambient body, the source
family volume cancels against the denominator introduced by eighth
normalization.  The normalized tube is larger than the exact eighth-dilation,
so the cancellation is an upper bound with the dimensional factor `512`.
-/

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 3000000

open Set MeasureTheory
open scoped ENNReal NNReal BigOperators

namespace Family8EighthNormalizedAmbientDensityCancellationV1

open LeanEval.Analysis.WangZahlKakeya
open Submission.Kakeya.ConvexGeometry
open Submission.Kakeya.Uniformity
open Family8AmbientFamilyVolumeDensityV2
open Family8EighthNormalizedFamilyVolumeLowerV1
open Family8EighthNormalizedKatzTaoAmbientFrostmanV2
open Family8FiniteRandomRigidMotionB2NormalizedDatumV1
open Family8FrozenCoarseB2DensityTransportScaleOnlyV1
open Family8KatzTaoFrostmanPropertiesV1

noncomputable section

/-- The family-volume normalization in the ambient Katz--Tao constant
cancels before any cardinality envelope is introduced. -/
theorem eighthNormalizedKatzTaoAmbientFrostmanConstant_ambientDensity_le
    {delta : NNReal} {iota : Type}
    [Fintype iota] [Nonempty iota] [DecidableEq iota]
    (D : ActualTubeDatum delta iota) (ambient : ConvexBody Space)
    (CF : ENNReal) (hdelta : 0 < delta) :
    eighthNormalizedKatzTaoAmbientFrostmanConstant
        (CF * ambientFamilyVolumeDensity D.family.bodyFamily ambient) D ≤
      (65536 * CF) * volume (unitBallBody : Set Space) /
        volume (ambient : Set Space) := by
  let sourceVolume := familyVolume D.family.bodyFamily
  let normalizedVolume :=
    familyVolume (eighthNormalizedDatum D).family.bodyFamily
  let ambientVolume := volume (ambient : Set Space)
  let unitVolume := volume (unitBallBody : Set Space)
  have hnormalized0 : normalizedVolume ≠ 0 := by
    dsimp only [normalizedVolume]
    exact (actualDatum_familyVolume_pos_of_scale
      (eighthNormalizedDatum D) (div_pos hdelta (by norm_num))).ne'
  have hnormalizedTop : normalizedVolume ≠ ∞ := by
    dsimp only [normalizedVolume]
    exact familyVolume_ne_top (eighthNormalizedDatum D).family.bodyFamily
  have hlower : (1 / 512 : ENNReal) * sourceVolume ≤ normalizedVolume := by
    simpa only [sourceVolume, normalizedVolume] using
      one_div_512_mul_familyVolume_le_eighthNormalized D
  have hnumeric : (512 : ENNReal)⁻¹ * 65536 = 128 := by
    have hnn : (512 : NNReal)⁻¹ * 65536 = 128 := by norm_num
    have hcast := congrArg (fun x : NNReal => (x : ENNReal)) hnn
    simpa only [ENNReal.coe_mul,
      ENNReal.coe_inv (by norm_num : (512 : NNReal) ≠ 0),
      ENNReal.coe_ofNat] using hcast
  unfold eighthNormalizedKatzTaoAmbientFrostmanConstant
  unfold ambientFamilyVolumeDensity
  change (128 * (CF * (sourceVolume / ambientVolume))) * unitVolume /
      normalizedVolume ≤ (65536 * CF) * unitVolume / ambientVolume
  apply (ENNReal.div_le_iff hnormalized0 hnormalizedTop).2
  calc
    (128 * (CF * (sourceVolume / ambientVolume))) * unitVolume =
        ((65536 * CF) * unitVolume / ambientVolume) *
          ((1 / 512 : ENNReal) * sourceVolume) := by
      simp only [div_eq_mul_inv, one_mul]
      calc
        128 * (CF * (sourceVolume * ambientVolume⁻¹)) * unitVolume =
            (CF * sourceVolume * unitVolume * ambientVolume⁻¹) * 128 := by
          ac_rfl
        _ = (CF * sourceVolume * unitVolume * ambientVolume⁻¹) *
            ((512 : ENNReal)⁻¹ * 65536) := by rw [hnumeric]
        _ = 65536 * CF * unitVolume * ambientVolume⁻¹ *
            ((512 : ENNReal)⁻¹ * sourceVolume) := by
          ac_rfl
    _ ≤ ((65536 * CF) * unitVolume / ambientVolume) * normalizedVolume :=
      mul_le_mul' le_rfl hlower

#print axioms
  eighthNormalizedKatzTaoAmbientFrostmanConstant_ambientDensity_le

end
end Family8EighthNormalizedAmbientDensityCancellationV1
