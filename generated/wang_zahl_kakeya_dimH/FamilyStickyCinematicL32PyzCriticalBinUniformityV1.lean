import FamilyStickyCinematicL32CriticalSingleDyadicBinFactorPositiveV1
import Mathlib.Tactic

set_option autoImplicit false

open scoped ENNReal

namespace FamilyStickyCinematicL32PyzCriticalBinUniformityV1

open FamilyStickyCinematicL32ContinuumCriticalSingleDyadicSelectionV1
open FamilyStickyCinematicL32Lemma57DyadicCeilBucketV1

noncomputable section

/-!
# One uniform budget for the norm and tangency dyadic losses

The norm ceiling is `16`.  If the selected norm scale is at most `32`, then
the dependent tangency ceiling `36 * globalScale` is at most `1152`.  Thus
both single-dyadic losses are bounded by the same radius-dependent loss with
ceiling `1152`.  No radius-independent finite bound is possible as the
positive radius tends to zero.
-/

/-- Enlarging a positive ceiling can only enlarge the admitted dyadic-label
interval.  The lower endpoint need not satisfy an additional hypothesis. -/
theorem continuumCriticalSingleDyadicBinFactor_mono_ceiling
    {delta ceiling₁ ceiling₂ : Real}
    (hceiling₁ : 0 < ceiling₁) (hceilings : ceiling₁ ≤ ceiling₂) :
    continuumCriticalSingleDyadicBinFactor delta ceiling₁ ≤
      continuumCriticalSingleDyadicBinFactor delta ceiling₂ := by
  unfold continuumCriticalSingleDyadicBinFactor
  apply Int.toNat_le_toNat
  have hbucket : dyadicCeilBucket ceiling₁ ≤ dyadicCeilBucket ceiling₂ :=
    dyadicCeilBucket_mono hceiling₁ hceilings
  omega

/-- Common natural-number slack for both geometric critical-scale bins. -/
def pyzCriticalBinUniformSlack (radius : Real) : Nat :=
  continuumCriticalSingleDyadicBinFactor radius 1152

theorem normCriticalBinFactor_le_uniformSlack (radius : Real) :
    continuumCriticalSingleDyadicBinFactor radius 16 ≤
      pyzCriticalBinUniformSlack radius := by
  exact continuumCriticalSingleDyadicBinFactor_mono_ceiling
    (by norm_num) (by norm_num)

theorem tangencyCriticalBinFactor_le_uniformSlack
    {radius globalScale : Real} (hradius : 0 < radius)
    (hradiusTangency : radius ≤ 36 * globalScale)
    (hglobalScale : globalScale ≤ 32) :
    continuumCriticalSingleDyadicBinFactor radius (36 * globalScale) ≤
      pyzCriticalBinUniformSlack radius := by
  have hceilingPos : 0 < 36 * globalScale :=
    hradius.trans_le hradiusTangency
  have hceilingUpper : 36 * globalScale ≤ (1152 : Real) := by
    nlinarith
  exact continuumCriticalSingleDyadicBinFactor_mono_ceiling
    hceilingPos hceilingUpper

/-- The two literal factors share one natural-number upper bound. -/
theorem norm_and_tangencyCriticalBinFactors_le_uniformSlack
    {radius globalScale : Real} (hradius : 0 < radius)
    (hradiusTangency : radius ≤ 36 * globalScale)
    (hglobalScale : globalScale ≤ 32) :
    continuumCriticalSingleDyadicBinFactor radius 16 ≤
        pyzCriticalBinUniformSlack radius ∧
      continuumCriticalSingleDyadicBinFactor radius (36 * globalScale) ≤
        pyzCriticalBinUniformSlack radius := by
  exact ⟨normCriticalBinFactor_le_uniformSlack radius,
    tangencyCriticalBinFactor_le_uniformSlack hradius hradiusTangency
      hglobalScale⟩

/-- ENNReal form of the common upper bound. -/
theorem norm_and_tangencyCriticalBinFactors_cast_le_uniformSlack
    {radius globalScale : Real} (hradius : 0 < radius)
    (hradiusTangency : radius ≤ 36 * globalScale)
    (hglobalScale : globalScale ≤ 32) :
    (continuumCriticalSingleDyadicBinFactor radius 16 : ENNReal) ≤
        (pyzCriticalBinUniformSlack radius : ENNReal) ∧
      (continuumCriticalSingleDyadicBinFactor radius (36 * globalScale) :
          ENNReal) ≤ (pyzCriticalBinUniformSlack radius : ENNReal) := by
  obtain ⟨hnorm, htangency⟩ :=
    norm_and_tangencyCriticalBinFactors_le_uniformSlack hradius
      hradiusTangency hglobalScale
  exact ⟨by exact_mod_cast hnorm, by exact_mod_cast htangency⟩

/-- Consequently the product of the two selection losses costs at most the
square of the common slack. -/
theorem norm_mul_tangencyCriticalBinFactors_cast_le_uniformSlack_sq
    {radius globalScale : Real} (hradius : 0 < radius)
    (hradiusTangency : radius ≤ 36 * globalScale)
    (hglobalScale : globalScale ≤ 32) :
    (continuumCriticalSingleDyadicBinFactor radius 16 : ENNReal) *
        (continuumCriticalSingleDyadicBinFactor radius (36 * globalScale) :
          ENNReal) ≤
      (pyzCriticalBinUniformSlack radius : ENNReal) ^ 2 := by
  obtain ⟨hnorm, htangency⟩ :=
    norm_and_tangencyCriticalBinFactors_cast_le_uniformSlack hradius
      hradiusTangency hglobalScale
  simpa [pow_two] using mul_le_mul hnorm htangency

/-- Adapter to any preallocated `logCount` budget that dominates the common
slack. -/
theorem norm_and_tangencyCriticalBinFactors_le_logCount
    {radius globalScale : Real} {logCount : Nat}
    (hradius : 0 < radius)
    (hradiusTangency : radius ≤ 36 * globalScale)
    (hglobalScale : globalScale ≤ 32)
    (hslack : pyzCriticalBinUniformSlack radius ≤ logCount) :
    continuumCriticalSingleDyadicBinFactor radius 16 ≤ logCount ∧
      continuumCriticalSingleDyadicBinFactor radius (36 * globalScale) ≤
        logCount := by
  obtain ⟨hnorm, htangency⟩ :=
    norm_and_tangencyCriticalBinFactors_le_uniformSlack hradius
      hradiusTangency hglobalScale
  exact ⟨hnorm.trans hslack, htangency.trans hslack⟩

#print axioms continuumCriticalSingleDyadicBinFactor_mono_ceiling
#print axioms pyzCriticalBinUniformSlack
#print axioms normCriticalBinFactor_le_uniformSlack
#print axioms tangencyCriticalBinFactor_le_uniformSlack
#print axioms norm_and_tangencyCriticalBinFactors_le_uniformSlack
#print axioms norm_and_tangencyCriticalBinFactors_cast_le_uniformSlack
#print axioms norm_mul_tangencyCriticalBinFactors_cast_le_uniformSlack_sq
#print axioms norm_and_tangencyCriticalBinFactors_le_logCount

end

end FamilyStickyCinematicL32PyzCriticalBinUniformityV1
