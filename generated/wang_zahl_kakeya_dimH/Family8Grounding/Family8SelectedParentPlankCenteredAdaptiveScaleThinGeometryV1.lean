import Family8Grounding.Family8SelectedParentPlankCenteredMassFreshAdaptiveSourcePowerThinCountV1
import Mathlib.Tactic

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 5000000

open scoped ENNReal NNReal

namespace Family8SelectedParentPlankCenteredAdaptiveScaleThinGeometryV1

open Family8SelectedParentJohnPlankSideWidthBridgeV7
open Family8SelectedParentPlankCanonicalThinCountV5
open Family8SelectedParentPlankCenteredHalfPostAdaptiveScalePackingV1
open Family8SelectedParentPlankCenteredMassFreshKatzTaoEndpointV6
open Family8SelectedParentPlankCenteredSourcePowerBudgetsV3

noncomputable section

/-!
# Concrete thin-count geometry from an adaptive scale power

The thin-count consumer needs both `s / 8 <= 1 / 100` and its literal
two-coordinate quadratic inequality.  They are produced here from one
positive threshold built from the actual dyadic aspect
`bucketShortB label / bucketShortA label`; no target proposition is passed
as a callback.
-/

def adaptiveThinGeometryThreshold (label : Fin 3 → Int) : NNReal :=
  1 / (100 * (1 + bucketShortB label / bucketShortA label))

theorem adaptiveThinGeometryThreshold_pos (label : Fin 3 → Int) :
    0 < adaptiveThinGeometryThreshold label := by
  unfold adaptiveThinGeometryThreshold
  positivity

theorem small_and_thin_of_le_adaptiveThinGeometryThreshold
    {s : NNReal} (label : Fin 3 → Int)
    (hs : s ≤ adaptiveThinGeometryThreshold label) :
    s / 8 ≤ (1 / 100 : NNReal) ∧
      ((((s / 8 : NNReal) : Real) ^ 2 +
        (selectedPlankFineCanonicalAspect label *
          ((s / 8 : NNReal) : Real)) ^ 2 ≤ (3 : Real) / 4)) := by
  let A : NNReal := bucketShortB label / bucketShortA label
  have hA0 : (0 : Real) ≤ (A : Real) := by positivity
  have hdenPos : (0 : Real) < 100 * (1 + (A : Real)) := by positivity
  have hsReal : (s : Real) ≤ 1 / (100 * (1 + (A : Real))) := by
    exact_mod_cast hs
  have hsHundred : (s : Real) ≤ 1 / 100 := by
    calc
      (s : Real) ≤ 1 / (100 * (1 + (A : Real))) := hsReal
      _ ≤ 1 / 100 := one_div_le_one_div_of_le (by norm_num)
        (by nlinarith)
  have hAsHundred : (A : Real) * (s : Real) ≤ 1 / 100 := by
    calc
      (A : Real) * (s : Real) ≤
          (A : Real) * (1 / (100 * (1 + (A : Real)))) := by
        gcongr
      _ = (A : Real) / (100 * (1 + (A : Real))) := by ring
      _ ≤ 1 / 100 := by
        apply (div_le_iff₀ hdenPos).2
        nlinarith
  constructor
  · exact (div_le_self (show 0 ≤ s from bot_le)
      (by norm_num : (1 : NNReal) ≤ 8)).trans
        (by exact_mod_cast hsHundred)
  · let x : Real := ((s / 8 : NNReal) : Real)
    let y : Real := selectedPlankFineCanonicalAspect label * x
    have hx0 : 0 ≤ x := by positivity
    have hx : x ≤ 1 / 800 := by
      dsimp only [x]
      norm_num [NNReal.coe_div]
      nlinarith
    have hy0 : 0 ≤ y := by
      dsimp only [y, x, selectedPlankFineCanonicalAspect]
      positivity
    have hy : y ≤ 1 / 800 := by
      dsimp only [y, x, selectedPlankFineCanonicalAspect, A] at *
      norm_num [NNReal.coe_div] at *
      nlinarith
    dsimp only [x, y] at hx0 hx hy0 hy ⊢
    nlinarith [mul_nonneg hx0 (sub_nonneg.mpr hx),
      mul_nonneg hy0 (sub_nonneg.mpr hy)]

def adaptiveThinCountScaleThreshold
    (delta0 : NNReal) (freshAbsorbEta densityAbsorbEta
      coefficientAbsorbEta : Real) (label : Fin 3 → Int) : NNReal :=
  min (centeredHalfPostFreshLossThreshold freshAbsorbEta)
    (min (centeredMassFreshKatzTaoThreshold
      delta0 densityAbsorbEta coefficientAbsorbEta)
      (adaptiveThinGeometryThreshold label))

theorem adaptiveThinCountScaleThreshold_pos
    {delta0 : NNReal} (hdelta0 : 0 < delta0)
    (freshAbsorbEta densityAbsorbEta coefficientAbsorbEta : Real)
    (label : Fin 3 → Int) :
    0 < adaptiveThinCountScaleThreshold delta0 freshAbsorbEta
      densityAbsorbEta coefficientAbsorbEta label := by
  unfold adaptiveThinCountScaleThreshold
  exact lt_min (centeredHalfPostFreshLossThreshold_pos _)
    (lt_min (centeredMassFreshKatzTaoThreshold_pos hdelta0 _ _)
      (adaptiveThinGeometryThreshold_pos label))

theorem scale_le_of_power_le
    {s delta threshold : NNReal} {q : Real}
    (hq : 0 < q)
    (hpower : (s : ENNReal) ^ q ≤ (delta : ENNReal))
    (hdelta : delta ≤ threshold ^ q)
    (hthreshold : 0 < threshold) :
    s ≤ threshold := by
  have hdeltaENN : (delta : ENNReal) ≤ (threshold : ENNReal) ^ q := by
    rw [← ENNReal.coe_rpow_of_ne_zero hthreshold.ne' q,
      ENNReal.coe_le_coe]
    exact hdelta
  have hsENN : (s : ENNReal) ≤ (threshold : ENNReal) := by
    apply (ENNReal.rpow_le_rpow_iff hq).mp
    exact hpower.trans hdeltaENN
  exact_mod_cast hsENN

theorem adaptive_smallness_of_power
    {s delta delta0 : NNReal}
    {freshAbsorbEta densityAbsorbEta coefficientAbsorbEta q : Real}
    (label : Fin 3 → Int) (hdelta0 : 0 < delta0) (hq : 0 < q)
    (hpower : (s : ENNReal) ^ q ≤ (delta : ENNReal))
    (hdelta : delta ≤
      (adaptiveThinCountScaleThreshold delta0 freshAbsorbEta
        densityAbsorbEta coefficientAbsorbEta label) ^ q) :
    s ≤ centeredHalfPostFreshLossThreshold freshAbsorbEta ∧
      s ≤ centeredMassFreshKatzTaoThreshold delta0
        densityAbsorbEta coefficientAbsorbEta ∧
      s / 8 ≤ (1 / 100 : NNReal) ∧
      ((((s / 8 : NNReal) : Real) ^ 2 +
        (selectedPlankFineCanonicalAspect label *
          ((s / 8 : NNReal) : Real)) ^ 2 ≤ (3 : Real) / 4)) := by
  let threshold := adaptiveThinCountScaleThreshold delta0 freshAbsorbEta
    densityAbsorbEta coefficientAbsorbEta label
  have hs : s ≤ threshold := scale_le_of_power_le hq hpower
    (by simpa only [threshold] using hdelta)
    (adaptiveThinCountScaleThreshold_pos hdelta0 _ _ _ _)
  have hgeometry : s ≤ adaptiveThinGeometryThreshold label :=
    hs.trans (by
      dsimp only [threshold, adaptiveThinCountScaleThreshold]
      exact (min_le_right _ _).trans (min_le_right _ _))
  exact ⟨
    hs.trans (by
      dsimp only [threshold, adaptiveThinCountScaleThreshold]
      exact min_le_left _ _),
    hs.trans (by
      dsimp only [threshold, adaptiveThinCountScaleThreshold]
      exact (min_le_right _ _).trans (min_le_left _ _)),
    (small_and_thin_of_le_adaptiveThinGeometryThreshold label hgeometry).1,
    (small_and_thin_of_le_adaptiveThinGeometryThreshold label hgeometry).2⟩

#print axioms adaptiveThinGeometryThreshold_pos
#print axioms small_and_thin_of_le_adaptiveThinGeometryThreshold
#print axioms adaptiveThinCountScaleThreshold_pos
#print axioms scale_le_of_power_le
#print axioms adaptive_smallness_of_power

end
end Family8SelectedParentPlankCenteredAdaptiveScaleThinGeometryV1
