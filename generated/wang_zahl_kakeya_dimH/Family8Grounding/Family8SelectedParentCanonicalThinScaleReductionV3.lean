import Family8Grounding.Family8SelectedParentPlankCanonicalThinCountV5
import Mathlib.Tactic

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 5000000

open scoped NNReal

namespace Family8SelectedParentCanonicalThinScaleReductionV3

open Family8SelectedParentJohnPlankSideWidthBridgeV7
open Family8SelectedParentPlankCanonicalThinCountV5

/-!
# Scalar reduction for the canonical selected-plank thin scale

For the literal choices in `Family8SelectedParentPlankCanonicalThinCountV5`,
the two normalized transverse widths are exactly `a/q` and `b/q`, where
`q` is the already proved same-fibre affine-axis length floor.  Thus the
paper-strength small-angle and thin-plank conditions follow from the two
geometric scale separations `100*a <= q` and `2*b <= q`.
-/

theorem canonicalProxyScale_div_eight_eq_shortA_div_floor
    {r : NNReal} (hr : 0 < r) (label : Fin 3 → Int) :
    selectedPlankFineCanonicalProxyScale r label / 8 =
      bucketShortA label / selectedPlankFineAxisLengthFloor r label := by
  have hq : selectedPlankFineAxisLengthFloor r label ≠ 0 :=
    (selectedPlankFineAxisLengthFloor_pos hr label).ne'
  unfold selectedPlankFineCanonicalProxyScale
  field_simp [hq]

theorem canonicalAspect_mul_proxyScale_div_eight_eq_shortB_div_floor
    {r : NNReal} (hr : 0 < r) (label : Fin 3 → Int) :
    selectedPlankFineCanonicalAspect label *
        (((selectedPlankFineCanonicalProxyScale r label / 8 : NNReal) : Real)) =
      (bucketShortB label : Real) /
        (selectedPlankFineAxisLengthFloor r label : Real) := by
  have hq : selectedPlankFineAxisLengthFloor r label ≠ 0 :=
    (selectedPlankFineAxisLengthFloor_pos hr label).ne'
  have ha : bucketShortA label ≠ 0 := (bucketShortA_pos label).ne'
  unfold selectedPlankFineCanonicalAspect
  rw [canonicalProxyScale_div_eight_eq_shortA_div_floor hr label]
  norm_num [NNReal.coe_div]
  field_simp [show (bucketShortA label : Real) ≠ 0 by exact_mod_cast ha,
    show (selectedPlankFineAxisLengthFloor r label : Real) ≠ 0 by
      exact_mod_cast hq]

/-- The exact paper-scale hypotheses on the two actual normalized widths
automatically discharge both residual smallness premises of V5. -/
theorem canonicalProxyScale_small_and_thin_of_width_separation
    {r : NNReal} (hr : 0 < r) (label : Fin 3 → Int)
    (hshort : 100 * bucketShortA label ≤
      selectedPlankFineAxisLengthFloor r label)
    (hwide : 2 * bucketShortB label ≤
      selectedPlankFineAxisLengthFloor r label) :
    selectedPlankFineCanonicalProxyScale r label / 8 ≤
        (1 / 100 : NNReal) ∧
      (((selectedPlankFineCanonicalProxyScale r label / 8 : NNReal) : Real) ^ 2 +
        (selectedPlankFineCanonicalAspect label *
          ((selectedPlankFineCanonicalProxyScale r label / 8 : NNReal) : Real)) ^ 2 ≤
        (3 : Real) / 4) := by
  let q := selectedPlankFineAxisLengthFloor r label
  have hq : 0 < q := selectedPlankFineAxisLengthFloor_pos hr label
  have hqReal : (0 : Real) < (q : Real) := by exact_mod_cast hq
  have hshortReal : (100 : Real) * (bucketShortA label : Real) ≤
      (q : Real) := by exact_mod_cast hshort
  have hwideReal : (2 : Real) * (bucketShortB label : Real) ≤
      (q : Real) := by exact_mod_cast hwide
  have haRatio : (bucketShortA label : Real) / (q : Real) ≤
      (1 : Real) / 100 := by
    apply (div_le_iff₀ hqReal).2
    nlinarith
  have hbRatio : (bucketShortB label : Real) / (q : Real) ≤
      (1 : Real) / 2 := by
    apply (div_le_iff₀ hqReal).2
    nlinarith
  have haRatio0 : 0 ≤ (bucketShortA label : Real) / (q : Real) := by
    positivity
  have hbRatio0 : 0 ≤ (bucketShortB label : Real) / (q : Real) := by
    positivity
  have hproduct : selectedPlankFineCanonicalAspect label *
        (((bucketShortA label / q : NNReal) : Real)) =
      (bucketShortB label : Real) / (q : Real) := by
    dsimp only [q]
    rw [← canonicalProxyScale_div_eight_eq_shortA_div_floor hr label]
    exact canonicalAspect_mul_proxyScale_div_eight_eq_shortB_div_floor hr label
  constructor
  · rw [canonicalProxyScale_div_eight_eq_shortA_div_floor hr label]
    exact_mod_cast haRatio
  · rw [canonicalProxyScale_div_eight_eq_shortA_div_floor hr label,
      hproduct]
    norm_num [NNReal.coe_div] at ⊢
    nlinarith [mul_nonneg haRatio0 (sub_nonneg.mpr haRatio),
      mul_nonneg hbRatio0 (sub_nonneg.mpr hbRatio)]

#print axioms canonicalProxyScale_div_eight_eq_shortA_div_floor
#print axioms canonicalAspect_mul_proxyScale_div_eight_eq_shortB_div_floor
#print axioms canonicalProxyScale_small_and_thin_of_width_separation

end Family8SelectedParentCanonicalThinScaleReductionV3
