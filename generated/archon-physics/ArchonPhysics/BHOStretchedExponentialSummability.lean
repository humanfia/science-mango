import ArchonPhysics.BHORandomMassLocalizationSchedule
import Mathlib.Analysis.PSeries

/-!
# Summability of the BHO stretched-exponential schedule

Positive stretched-exponential decay dominates every real polynomial along
the physical volumes `n + 2`.  This deterministic fact is the summability
input needed by a first Borel--Cantelli localization argument.
-/

namespace ArchonPhysics.BHOStretchedExponentialSummability

open Filter Asymptotics
open ArchonPhysics.BHORandomMassLocalizationSchedule

noncomputable section

/-- A positive stretched exponential remains summable after multiplication
by an arbitrary real power of the volume. -/
theorem summable_shiftedVolume_rpow_mul_stretchedExponential
    {power decayRate polynomialPower : Real}
    (hpower : 0 < power) (hdecay : 0 < decayRate) :
    Summable (fun n : Nat =>
      (((n + 2 : Nat) : Real)) ^ polynomialPower *
        Real.exp (-decayRate *
          (((n + 2 : Nat) : Real)) ^ power)) := by
  let comparisonPower : Real := (-2 - polynomialPower) / power
  have hpowerLimit : Tendsto (fun x : Real => x ^ power) atTop atTop :=
    tendsto_rpow_atTop hpower
  have hdecayBase :=
    isLittleO_exp_neg_mul_rpow_atTop hdecay comparisonPower
  have hdecayComposed := hdecayBase.comp_tendsto hpowerLimit
  have hpowerIdentity : power * comparisonPower = -2 - polynomialPower := by
    dsimp only [comparisonPower]
    field_simp
  have hdecayRpow :
      (fun x : Real => Real.exp (-decayRate * x ^ power)) =o[atTop]
        (fun x : Real => x ^ (-2 - polynomialPower)) := by
    refine hdecayComposed.congr' (Eventually.of_forall fun _ => rfl) ?_
    filter_upwards [eventually_gt_atTop (0 : Real)] with x hx
    rw [Function.comp_apply, ← Real.rpow_mul hx.le, hpowerIdentity]
  have hproduct :=
    (isBigO_refl (fun x : Real => x ^ polynomialPower) atTop).mul_isLittleO
      hdecayRpow
  have hproductRpow :
      (fun x : Real => x ^ polynomialPower *
        Real.exp (-decayRate * x ^ power)) =o[atTop]
        (fun x : Real => x ^ (-2 : Real)) := by
    refine hproduct.congr' (Eventually.of_forall fun _ => rfl) ?_
    filter_upwards [eventually_gt_atTop (0 : Real)] with x hx
    rw [← Real.rpow_add hx]
    congr 1
    ring
  have hsequenceBigO := (hproductRpow.isBigO).comp_tendsto
    tendsto_shiftedVolume_atTop
  have hpSeries : Summable (fun n : Nat =>
      (((n + 2 : Nat) : Real)) ^ (-2 : Real)) := by
    have h := (Real.summable_one_div_nat_add_rpow 2 2).2 (by norm_num)
    apply h.congr
    intro n
    have hn : 0 < (n : Real) + 2 := by positivity
    simp only [Nat.cast_add, Nat.cast_ofNat, abs_of_pos hn,
      Real.rpow_neg hn.le, Real.rpow_two, one_div]
  exact summable_of_isBigO_nat hpSeries hsequenceBigO

/-- The deterministic BHO EFC tail is summable even after any polynomial
union/Markov loss when `2 * alpha < gamma`. -/
theorem summable_polynomial_mul_bhoEFCWindowTail
    {alpha gamma decayRate polynomialPower : Real}
    (hscale : 2 * alpha < gamma) (hdecay : 0 < decayRate) :
    Summable (fun n : Nat =>
      (((n + 2 : Nat) : Real)) ^ polynomialPower *
        bhoEFCWindowTail alpha gamma decayRate (n + 2)) := by
  simpa only [bhoEFCWindowTail] using
    summable_shiftedVolume_rpow_mul_stretchedExponential
      (sub_pos.mpr hscale) hdecay

end

end ArchonPhysics.BHOStretchedExponentialSummability
