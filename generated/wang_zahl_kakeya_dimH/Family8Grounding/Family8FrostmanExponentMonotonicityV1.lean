import Family8Grounding.Family8KatzTaoFrostmanPropertiesV1
import FamilyStickyGrounding.FamilyStickyScaleChainSmallDeltaExponentBudgetProducerV1

open scoped ENNReal NNReal

namespace Family8FrostmanExponentMonotonicityV1

open Family8KatzTaoFrostmanPropertiesV1
open FamilyStickyScaleChainSmallDeltaExponentBudgetProducerV1

noncomputable section

set_option autoImplicit false
set_option warningAsError true

/-!
# Frostman exponent monotonicity from actual family-volume packing

Direct monotonicity in the Frostman exponent is not formal algebra without a
global packing estimate.  This file supplies the missing honest hypothesis:

`actualFamilyVolume ≤ K * delta ^ (-2)`

with one finite constant `K`.  If `lower ≤ upper` and
`s = upper - lower`, the ratio between the lower-exponent RHS at loss
`epsilon / 2` and the upper-exponent RHS at loss `epsilon` is bounded by

`K ^ (s / 2) * delta ^ (epsilon / 2 + s)`.

An explicit small-scale threshold absorbs that finite constant.  The zero
volume case is proved separately by exponent monotonicity, while infinite
volume is ruled out by the displayed finite packing estimate rather than by
an input premise.
-/

/-- Explicit threshold which absorbs the exponent-transport volume constant. -/
def frostmanExponentTransportThreshold
    (K : ENNReal) (epsilon lower upper : Real) : NNReal :=
  finiteConstantSmallDeltaThreshold
    (K ^ ((upper - lower) / 2))
    (epsilon / 2 + (upper - lower))

theorem frostmanExponentTransportThreshold_pos
    (K : ENNReal) (epsilon lower upper : Real) :
    0 < frostmanExponentTransportThreshold K epsilon lower upper :=
  finiteConstantSmallDeltaThreshold_pos _ _

/-- Numerical Frostman-RHS exponent transport with all constant absorption
proved at the displayed threshold. -/
theorem frostmanMultiplicityRHS_lower_le_upper_of_volumePacking
    {delta : NNReal} {actualVolume K : ENNReal}
    {epsilon lower upper : Real}
    (hdelta : 0 < delta) (hdeltaOne : delta ≤ 1)
    (hdeltaThreshold :
      delta ≤ frostmanExponentTransportThreshold K epsilon lower upper)
    (hKtop : K ≠ ∞) (hepsilon : 0 < epsilon)
    (hlowerUpper : lower ≤ upper)
    (hvolume :
      actualVolume ≤ K * (delta : ENNReal) ^ (-2 : Real)) :
    frostmanMultiplicityRHS delta actualVolume (epsilon / 2) lower ≤
      frostmanMultiplicityRHS delta actualVolume epsilon upper := by
  let d : ENNReal := (delta : ENNReal)
  let s : Real := upper - lower
  have hs : 0 ≤ s := by dsimp only [s]; linarith
  have hsHalf : 0 ≤ s / 2 := by linarith
  have hexponent : 0 < epsilon / 2 + s := by positivity
  have hd0 : d ≠ 0 := ENNReal.coe_ne_zero.mpr hdelta.ne'
  have hdTop : d ≠ ∞ := ENNReal.coe_ne_top
  have hdOne : d ≤ 1 := by
    dsimp only [d]
    exact_mod_cast hdeltaOne
  by_cases hvolume0 : actualVolume = 0
  · have hdFactor :
        d ^ (-(epsilon / 2)) * d ^ (-2 * lower) ≤
          d ^ (-epsilon) * d ^ (-2 * upper) := by
      calc
        d ^ (-(epsilon / 2)) * d ^ (-2 * lower) =
            d ^ (-(epsilon / 2) + (-2 * lower)) :=
          (ENNReal.rpow_add (-(epsilon / 2)) (-2 * lower)
            hd0 hdTop).symm
        _ ≤ d ^ ((-epsilon) + (-2 * upper)) := by
          apply ENNReal.rpow_le_rpow_of_exponent_ge hdOne
          dsimp only [s] at hs
          linarith
        _ = d ^ (-epsilon) * d ^ (-2 * upper) :=
          ENNReal.rpow_add (-epsilon) (-2 * upper) hd0 hdTop
    have hvolumeFactor :
        actualVolume ^ (1 - lower / 2) ≤
          actualVolume ^ (1 - upper / 2) := by
      apply ENNReal.rpow_le_rpow_of_exponent_ge
      · simp [hvolume0]
      · linarith
    unfold frostmanMultiplicityRHS
    exact mul_le_mul' hdFactor hvolumeFactor
  · have hdpowTop : d ^ (-2 : Real) ≠ ∞ :=
      ENNReal.rpow_ne_top_of_ne_zero hd0 hdTop
    have hpackingTop : K * d ^ (-2 : Real) ≠ ∞ :=
      ENNReal.mul_ne_top hKtop hdpowTop
    have hactualVolumeTop : actualVolume ≠ ∞ := by
      exact (hvolume.trans_lt
        (lt_top_iff_ne_top.mpr hpackingTop)).ne
    have hconstantTop : K ^ (s / 2) ≠ ∞ :=
      ENNReal.rpow_ne_top_of_nonneg hsHalf hKtop
    have hconstant :
        K ^ (s / 2) ≤ d ^ (-(epsilon / 2 + s)) := by
      apply finiteConstant_le_delta_negativePower
        hconstantTop hexponent hdelta
      simpa only [frostmanExponentTransportThreshold, s] using
        hdeltaThreshold
    have habsorb :
        d ^ (epsilon / 2 + s) * K ^ (s / 2) ≤ 1 := by
      calc
        d ^ (epsilon / 2 + s) * K ^ (s / 2) ≤
            d ^ (epsilon / 2 + s) *
              d ^ (-(epsilon / 2 + s)) :=
          mul_le_mul_right hconstant _
        _ = d ^ ((epsilon / 2 + s) + (-(epsilon / 2 + s))) := by
          rw [ENNReal.rpow_add (epsilon / 2 + s)
            (-(epsilon / 2 + s)) hd0 hdTop]
        _ = 1 := by simp
    have hvolumePow :
        actualVolume ^ (s / 2) ≤
          (K * d ^ (-2 : Real)) ^ (s / 2) :=
      ENNReal.rpow_le_rpow hvolume hsHalf
    have hfactor :
        d ^ (epsilon / 2 + 2 * s) * actualVolume ^ (s / 2) ≤ 1 := by
      calc
        d ^ (epsilon / 2 + 2 * s) * actualVolume ^ (s / 2) ≤
            d ^ (epsilon / 2 + 2 * s) *
              (K * d ^ (-2 : Real)) ^ (s / 2) :=
          mul_le_mul_right hvolumePow _
        _ = d ^ (epsilon / 2 + 2 * s) *
              (K ^ (s / 2) *
                (d ^ (-2 : Real)) ^ (s / 2)) := by
          rw [ENNReal.mul_rpow_of_nonneg _ _ hsHalf]
        _ = K ^ (s / 2) *
              (d ^ (epsilon / 2 + 2 * s) *
                d ^ ((-2 : Real) * (s / 2))) := by
          rw [ENNReal.rpow_mul]
          ac_rfl
        _ = K ^ (s / 2) *
              d ^ ((epsilon / 2 + 2 * s) +
                ((-2 : Real) * (s / 2))) := by
          rw [ENNReal.rpow_add (epsilon / 2 + 2 * s)
            ((-2 : Real) * (s / 2)) hd0 hdTop]
        _ = d ^ (epsilon / 2 + s) * K ^ (s / 2) := by
          have hpower :
              (epsilon / 2 + 2 * s) + ((-2 : Real) * (s / 2)) =
                epsilon / 2 + s := by
            ring
          rw [hpower]
          ac_rfl
        _ ≤ 1 := habsorb
    have hlowerCombined :
        frostmanMultiplicityRHS delta actualVolume (epsilon / 2) lower =
          d ^ (-(epsilon / 2) - 2 * lower) *
            actualVolume ^ (1 - lower / 2) := by
      unfold frostmanMultiplicityRHS
      dsimp only [d]
      calc
        (delta : ENNReal) ^ (-(epsilon / 2)) *
              (delta : ENNReal) ^ (-2 * lower) *
              actualVolume ^ (1 - lower / 2) =
            (delta : ENNReal) ^
                (-(epsilon / 2) + (-2 * lower)) *
              actualVolume ^ (1 - lower / 2) := by
          rw [ENNReal.rpow_add (-(epsilon / 2)) (-2 * lower)
            hd0 hdTop]
        _ = d ^ (-(epsilon / 2) - 2 * lower) *
              actualVolume ^ (1 - lower / 2) := by
          congr 2
          ring
    have hupperCombined :
        frostmanMultiplicityRHS delta actualVolume epsilon upper =
          d ^ (-epsilon - 2 * upper) *
            actualVolume ^ (1 - upper / 2) := by
      unfold frostmanMultiplicityRHS
      dsimp only [d]
      calc
        (delta : ENNReal) ^ (-epsilon) *
              (delta : ENNReal) ^ (-2 * upper) *
              actualVolume ^ (1 - upper / 2) =
            (delta : ENNReal) ^ ((-epsilon) + (-2 * upper)) *
              actualVolume ^ (1 - upper / 2) := by
          rw [ENNReal.rpow_add (-epsilon) (-2 * upper) hd0 hdTop]
        _ = d ^ (-epsilon - 2 * upper) *
              actualVolume ^ (1 - upper / 2) := by
          congr 2
          ring
    have hdExponent :
        -(epsilon / 2) - 2 * lower =
          (-epsilon - 2 * upper) + (epsilon / 2 + 2 * s) := by
      dsimp only [s]
      ring
    have hvolumeExponent :
        1 - lower / 2 = (1 - upper / 2) + s / 2 := by
      dsimp only [s]
      ring
    have hfactorization :
        frostmanMultiplicityRHS delta actualVolume (epsilon / 2) lower =
          frostmanMultiplicityRHS delta actualVolume epsilon upper *
            (d ^ (epsilon / 2 + 2 * s) *
              actualVolume ^ (s / 2)) := by
      rw [hlowerCombined, hupperCombined, hdExponent,
        ENNReal.rpow_add (-epsilon - 2 * upper)
          (epsilon / 2 + 2 * s) hd0 hdTop,
        hvolumeExponent,
        ENNReal.rpow_add (1 - upper / 2) (s / 2)
          hvolume0 hactualVolumeTop]
      ac_rfl
    calc
      frostmanMultiplicityRHS delta actualVolume (epsilon / 2) lower =
          frostmanMultiplicityRHS delta actualVolume epsilon upper *
            (d ^ (epsilon / 2 + 2 * s) *
              actualVolume ^ (s / 2)) := hfactorization
      _ ≤ frostmanMultiplicityRHS delta actualVolume epsilon upper * 1 :=
        by
          simpa only [mul_comm] using
            mul_le_mul_left hfactor
              (frostmanMultiplicityRHS delta actualVolume epsilon upper)
      _ = frostmanMultiplicityRHS delta actualVolume epsilon upper := by simp

/-- A single finite global family-volume packing producer makes
`FrostmanProperty` monotone in its exponent. -/
theorem frostmanProperty_mono_of_familyVolumePacking
    (K : ENNReal) (hKtop : K ≠ ∞)
    (hvolume :
      ∀ {delta : NNReal} {index : Type}
        [Fintype index] [DecidableEq index]
        (D : ActualTubeDatum delta index),
        D.IsAdmissible →
          D.actualFamilyVolume ≤
            K * (delta : ENNReal) ^ (-2 : Real))
    {lower upper : Real} (hlowerUpper : lower ≤ upper)
    (hlower : FrostmanProperty lower) :
    FrostmanProperty upper := by
  intro epsilon hepsilon
  have hhalfEpsilon : 0 < epsilon / 2 := by positivity
  obtain ⟨eta, delta0, heta, hdelta0, hdelta0Half, hsource⟩ :=
    hlower.exists_parameters hhalfEpsilon
  let threshold : NNReal :=
    frostmanExponentTransportThreshold K epsilon lower upper
  let delta1 : NNReal := min delta0 threshold
  have hthresholdPos : 0 < threshold := by
    dsimp only [threshold]
    exact frostmanExponentTransportThreshold_pos K epsilon lower upper
  have hdelta1 : 0 < delta1 := by
    dsimp only [delta1]
    rw [lt_min_iff]
    exact ⟨hdelta0, hthresholdPos⟩
  have hdelta1Half : delta1 ≤ (2 : NNReal)⁻¹ :=
    (min_le_left delta0 threshold).trans hdelta0Half
  refine ⟨eta, delta1, heta, hdelta1, hdelta1Half, ?_⟩
  intro delta index _ _ D hD hdelta hF
  have hlowerBound :
      D.shading.averageMultiplicity ≤
        frostmanMultiplicityRHS delta D.actualFamilyVolume
          (epsilon / 2) lower :=
    hsource delta index D hD
      (hdelta.trans (min_le_left delta0 threshold)) hF
  have hnumeric :
      frostmanMultiplicityRHS delta D.actualFamilyVolume
          (epsilon / 2) lower ≤
        frostmanMultiplicityRHS delta D.actualFamilyVolume epsilon upper := by
    apply frostmanMultiplicityRHS_lower_le_upper_of_volumePacking
      hD.delta_pos
      (hD.delta_le_half.trans (by norm_num))
      (hdelta.trans (min_le_right delta0 threshold))
      hKtop hepsilon hlowerUpper
    exact hvolume D hD
  exact hlowerBound.trans hnumeric

#print axioms frostmanExponentTransportThreshold_pos
#print axioms frostmanMultiplicityRHS_lower_le_upper_of_volumePacking
#print axioms frostmanProperty_mono_of_familyVolumePacking

end

end Family8FrostmanExponentMonotonicityV1
