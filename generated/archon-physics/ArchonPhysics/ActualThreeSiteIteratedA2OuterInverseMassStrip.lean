import ArchonPhysics.ActualThreeSiteIteratedA2OuterQuantitativeBridges
import ArchonPhysics.FrozenAndersonOneSiteSpectralAveraging

/-!
# Quantitative inverse-mass strip for the actual three-site outer channel

This module isolates the bad-set estimate used by the quantitative outer
history argument.  On the compact iid support `[4/5,6/5]`, an inverse-mass
strip is contained in a raw-mass strip with a uniform Lipschitz constant.
The sharp one-coordinate density ceiling and Fubini then give an explicit
linear bound.  This estimate is independent of the inverse-function atlas.
-/

namespace ArchonPhysics.ActualThreeSiteIteratedA2OuterInverseMassStrip

open ArchonPhysics
open ArchonPhysics.FrozenAndersonOneSiteSpectralAveraging
open ArchonPhysics.RandomEnsemble
open ArchonPhysics.ThreeParameterSpectralAveragingDensity
open ArchonPhysics.TwoParameterSpectralAveragingAtlas
open MeasureTheory Set
open scoped ENNReal

noncomputable section

/-- The bad strip where the first and third inverse masses are closer than
`delta`.  The middle mass is retained as an independent parameter. -/
def threeSiteOuterInverseMassStrip (delta : Real) : Set MassTriple :=
  {triple | |triple.1.1⁻¹ - triple.2⁻¹| < delta}

theorem measurableSet_threeSiteOuterInverseMassStrip (delta : Real) :
    MeasurableSet (threeSiteOuterInverseMassStrip delta) := by
  exact measurableSet_lt
    (((measurable_fst.comp measurable_fst).inv.sub measurable_snd.inv).abs)
    measurable_const

/-- On the mass support, inverse separation controls raw-mass separation.
The deliberately rounded constant `2` is larger than `(6/5)^2`. -/
theorem abs_sub_lt_two_mul_of_inverse_sub_lt
    {first third delta : Real}
    (hfirst : first ∈ massSupport) (hthird : third ∈ massSupport)
    (hdelta : 0 ≤ delta)
    (hinverse : |first⁻¹ - third⁻¹| < delta) :
    |first - third| < 2 * delta := by
  have hfirstPos : 0 < first := massLower_pos.trans_le hfirst.1
  have hthirdPos : 0 < third := massLower_pos.trans_le hthird.1
  have hidentity :
      first - third = -(first * third) * (first⁻¹ - third⁻¹) := by
    field_simp [ne_of_gt hfirstPos, ne_of_gt hthirdPos]
    ring
  have hproductPos : 0 < first * third := mul_pos hfirstPos hthirdPos
  have hproductUpper : first * third ≤ (36 / 25 : Real) := by
    calc
      first * third ≤ massUpper * third :=
        mul_le_mul_of_nonneg_right hfirst.2 (le_of_lt hthirdPos)
      _ ≤ massUpper * massUpper :=
        mul_le_mul_of_nonneg_left hthird.2 (by
          exact le_of_lt (massLower_pos.trans_le massLower_le_massUpper))
      _ = 36 / 25 := by norm_num [massUpper]
  calc
    |first - third| = (first * third) * |first⁻¹ - third⁻¹| := by
      rw [hidentity, abs_mul, abs_neg, abs_of_pos hproductPos]
    _ < (first * third) * delta :=
      mul_lt_mul_of_pos_left hinverse hproductPos
    _ ≤ (36 / 25 : Real) * delta :=
      mul_le_mul_of_nonneg_right hproductUpper hdelta
    _ ≤ 2 * delta := by nlinarith

/-- A single conditional inverse-mass strip has mass at most `10 delta`.
Only the first mass needs to lie in the iid support. -/
theorem massCoordinateLaw_inverseMassStripFiber_le
    {first delta : Real} (hfirst : first ∈ massSupport)
    (hdelta : 0 ≤ delta) :
    massCoordinateLaw {third | |first⁻¹ - third⁻¹| < delta} ≤
      10 * ENNReal.ofReal delta := by
  let rawStrip : Set Real := Ioo (first - 2 * delta) (first + 2 * delta)
  have hmono :
      massCoordinateLaw {third | |first⁻¹ - third⁻¹| < delta} ≤
        massCoordinateLaw rawStrip := by
    apply measure_mono_ae
    filter_upwards [massCoordinate_mem_support_ae] with third hthird
    intro hinverse
    have hraw := abs_sub_lt_two_mul_of_inverse_sub_lt
      hfirst hthird hdelta hinverse
    change first - 2 * delta < third ∧ third < first + 2 * delta
    rcases (abs_lt.mp hraw) with ⟨hlower, hupper⟩
    constructor <;> nlinarith
  have hdensity := Measure.le_iff.mp
    massCoordinateLaw_le_fiveHalves_smul_volume rawStrip measurableSet_Ioo
  calc
    massCoordinateLaw {third | |first⁻¹ - third⁻¹| < delta} ≤
        massCoordinateLaw rawStrip := hmono
    _ ≤ (5 / 2 : ENNReal) * (volume : Measure Real) rawStrip := by
      simpa [Measure.smul_apply] using hdensity
    _ = 10 * ENNReal.ofReal delta := by
      rw [Real.volume_Ioo]
      have hfour : first + 2 * delta - (first - 2 * delta) = 4 * delta := by
        ring
      rw [hfour, ENNReal.ofReal_mul (by norm_num : (0 : Real) ≤ 4)]
      have hconstant : (5 / 2 : ENNReal) * 4 = 10 := by
        apply (ENNReal.toReal_eq_toReal_iff'
          (by finiteness) (by norm_num)).mp
        norm_num
      rw [ENNReal.ofReal_ofNat, ← mul_assoc, hconstant]

/-- The complete iid three-mass inverse strip is `O(delta)`, with an
explicit constant independent of the later compact atlas. -/
theorem iidMassTripleLaw_threeSiteOuterInverseMassStrip_le
    {delta : Real} (hdelta : 0 ≤ delta) :
    iidMassTripleLaw (threeSiteOuterInverseMassStrip delta) ≤
      10 * ENNReal.ofReal delta := by
  have hpairSupport : ∀ᵐ pair ∂iidMassPairLaw,
      pair ∈ iidMassPairSupport := by
    rw [iidMassPairLaw, Measure.ae_prod_mem_iff_ae_ae_mem]
    · filter_upwards [massCoordinate_mem_support_ae] with first hfirst
      filter_upwards [massCoordinate_mem_support_ae] with second hsecond
      exact ⟨hfirst, hsecond⟩
    · exact measurableSet_Icc.prod measurableSet_Icc
  rw [iidMassTripleLaw,
    Measure.prod_apply (measurableSet_threeSiteOuterInverseMassStrip delta)]
  calc
    (∫⁻ pair, massCoordinateLaw
        (Prod.mk pair ⁻¹' threeSiteOuterInverseMassStrip delta)
        ∂iidMassPairLaw) ≤
      ∫⁻ _pair, 10 * ENNReal.ofReal delta ∂iidMassPairLaw := by
        apply lintegral_mono_ae
        filter_upwards [hpairSupport] with pair hpair
        simpa [threeSiteOuterInverseMassStrip] using
          massCoordinateLaw_inverseMassStripFiber_le hpair.1 hdelta
    _ = 10 * ENNReal.ofReal delta := by simp [iidMassPairLaw]

end

end ArchonPhysics.ActualThreeSiteIteratedA2OuterInverseMassStrip
