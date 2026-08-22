import FamilyStickyGrounding.FamilyStickyVolumeRatioTelescopingV1
import FamilyStickyGrounding.FamilyStickyDividingScalesChainAtEveryAdapterV1

set_option autoImplicit false

open scoped BigOperators ENNReal NNReal

namespace FamilyStickyScaleChainNormalizedIntegrationV1

open FamilyStickyDeltaMaxFiniteChainV2
open FamilyStickyVolumeRatioTelescopingV1

noncomputable section

/-!
# Sticky Kakeya: honest normalized scale-chain integration

Each adjacent step retains the exact test-body and tube-volume normalization.
After the step is denominator-cleared, the resulting body-growth/tube-decay
ratios are multiplied and telescope to the endpoint ratio.  No unnormalized
adjacent cross estimate is assumed or reconstructed.
-/

/-- Denominator-clearing one honest normalized adjacent step. -/
theorem step_le_ratio_of_normalized
    {current next stepFactor bodyCurrent bodyNext tubeCurrent tubeNext : ENNReal}
    (hbodyNext0 : bodyNext ≠ 0) (hbodyNextTop : bodyNext ≠ ∞)
    (htubeNext0 : tubeNext ≠ 0) (htubeNextTop : tubeNext ≠ ∞)
    (hstep : current * tubeNext / bodyNext ≤
      stepFactor * (next * tubeCurrent / bodyCurrent)) :
    current ≤
      (stepFactor * ((bodyNext / bodyCurrent) *
        (tubeCurrent / tubeNext))) * next := by
  apply (ENNReal.mul_le_mul_iff_right htubeNext0 htubeNextTop).mp
  have hcleared :=
    (ENNReal.div_le_iff_le_mul
      (Or.inl hbodyNext0) (Or.inl hbodyNextTop)).1 hstep
  calc
    tubeNext * current = current * tubeNext := by ac_rfl
    _ ≤
        (stepFactor * (next * tubeCurrent / bodyCurrent)) * bodyNext := hcleared
    _ = stepFactor * next * (bodyNext / bodyCurrent) * tubeCurrent := by
      simp only [div_eq_mul_inv]
      ring
    _ = stepFactor * next * (bodyNext / bodyCurrent) *
        ((tubeCurrent / tubeNext) * tubeNext) := by
      rw [ENNReal.div_mul_cancel htubeNext0 htubeNextTop]
    _ = tubeNext * (stepFactor * ((bodyNext / bodyCurrent) *
        (tubeCurrent / tubeNext)) * next) := by
      ac_rfl

/-- A finite chain whose primitive step is the normalized geometric estimate.
The positivity/finiteness fields are exactly the hypotheses needed to clear
and telescope the `ENNReal` ratios. -/
structure NormalizedScaleChain (depth : Nat) where
  value : Nat → ENNReal
  localFactor : Nat → ENNReal
  bodyVolume : Nat → ENNReal
  tubeVolume : Nat → ENNReal
  bodyVolume_ne_zero : ∀ m, m ≤ depth → bodyVolume m ≠ 0
  bodyVolume_ne_top : ∀ m, m ≤ depth → bodyVolume m ≠ ∞
  tubeVolume_ne_zero : ∀ m, m ≤ depth → tubeVolume m ≠ 0
  tubeVolume_ne_top : ∀ m, m ≤ depth → tubeVolume m ≠ ∞
  normalized_step : ∀ m, m < depth →
    value m * tubeVolume (m + 1) / bodyVolume (m + 1) ≤
      localFactor m *
        (value (m + 1) * tubeVolume m / bodyVolume m)
  top_le_one : value depth ≤ 1

namespace NormalizedScaleChain

/-- The exact per-step ratio left after denominator-clearing. -/
def volumeRatio {depth : Nat} (C : NormalizedScaleChain depth)
    (m : Nat) : ENNReal :=
  (C.bodyVolume (m + 1) / C.bodyVolume m) *
    (C.tubeVolume m / C.tubeVolume (m + 1))

/-- Every normalized step gives the recurrence with its explicit volume
ratio; this is the honest replacement for the old callback-based step. -/
theorem step_le {depth : Nat} (C : NormalizedScaleChain depth)
    (m : Nat) (hm : m < depth) :
    C.value m ≤
      (C.localFactor m * C.volumeRatio m) * C.value (m + 1) := by
  exact step_le_ratio_of_normalized
    (C.bodyVolume_ne_zero (m + 1) (Nat.succ_le_of_lt hm))
    (C.bodyVolume_ne_top (m + 1) (Nat.succ_le_of_lt hm))
    (C.tubeVolume_ne_zero (m + 1) (Nat.succ_le_of_lt hm))
    (C.tubeVolume_ne_top (m + 1) (Nat.succ_le_of_lt hm))
    (C.normalized_step m hm)

/-- The full chain bound after exact telescoping: only the product of actual
stepFactor factors and the two endpoint volume ratios remain. -/
theorem global_le_endpointRatio {depth : Nat}
    (C : NormalizedScaleChain depth) :
    C.value 0 ≤
      (∏ m ∈ Finset.range depth, C.localFactor m) *
        ((C.bodyVolume depth / C.bodyVolume 0) *
          (C.tubeVolume 0 / C.tubeVolume depth)) := by
  have hchain := deltaMax_le_prod_local depth C.value
    (fun m => C.localFactor m * C.volumeRatio m) C.step_le
  calc
    C.value 0 ≤
        (∏ m ∈ Finset.range depth,
          C.localFactor m * C.volumeRatio m) * C.value depth := hchain
    _ ≤ (∏ m ∈ Finset.range depth,
          C.localFactor m * C.volumeRatio m) * 1 := by
      gcongr
      exact C.top_le_one
    _ = (∏ m ∈ Finset.range depth, C.localFactor m) *
        (∏ m ∈ Finset.range depth, C.volumeRatio m) := by
      rw [mul_one, Finset.prod_mul_distrib]
    _ = (∏ m ∈ Finset.range depth, C.localFactor m) *
        ((C.bodyVolume depth / C.bodyVolume 0) *
          (C.tubeVolume 0 / C.tubeVolume depth)) := by
      rw [show (∏ m ∈ Finset.range depth, C.volumeRatio m) =
          (C.bodyVolume depth / C.bodyVolume 0) *
            (C.tubeVolume 0 / C.tubeVolume depth) by
        exact prod_bodyGrowth_mul_tubeDecay depth C.bodyVolume C.tubeVolume
          C.bodyVolume_ne_zero C.bodyVolume_ne_top
          C.tubeVolume_ne_zero C.tubeVolume_ne_top]

/-- If the endpoint normalization costs at most one, the whole geometric
normalization disappears and only the actual stepFactor-factor product remains. -/
theorem global_le_prod_local_of_endpointRatio_le_one {depth : Nat}
    (C : NormalizedScaleChain depth)
    (hendpoint :
      (C.bodyVolume depth / C.bodyVolume 0) *
        (C.tubeVolume 0 / C.tubeVolume depth) ≤ 1) :
    C.value 0 ≤ ∏ m ∈ Finset.range depth, C.localFactor m := by
  calc
    C.value 0 ≤
        (∏ m ∈ Finset.range depth, C.localFactor m) *
          ((C.bodyVolume depth / C.bodyVolume 0) *
            (C.tubeVolume 0 / C.tubeVolume depth)) := C.global_le_endpointRatio
    _ ≤ (∏ m ∈ Finset.range depth, C.localFactor m) * 1 := by
      gcongr
    _ = ∏ m ∈ Finset.range depth, C.localFactor m := mul_one _

end NormalizedScaleChain

#print axioms step_le_ratio_of_normalized
#print axioms NormalizedScaleChain.step_le
#print axioms NormalizedScaleChain.global_le_endpointRatio
#print axioms NormalizedScaleChain.global_le_prod_local_of_endpointRatio_le_one

end
end FamilyStickyScaleChainNormalizedIntegrationV1
