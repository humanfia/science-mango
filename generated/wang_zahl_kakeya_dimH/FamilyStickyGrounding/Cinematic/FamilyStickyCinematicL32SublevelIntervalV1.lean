import Mathlib.Analysis.Calculus.Deriv.MeanValue

set_option autoImplicit false

open Set

namespace FamilyStickyCinematicL32SublevelIntervalV1

/-!
# Explicit one-dimensional sublevel interval bounds

Provenance: the interval-length step in Pramanik--Yang--Zahl,
arXiv:2207.02259v3, Lemma 3.8(2b), especially equations (3.5)--(3.6).

The paper applies this step after obtaining a lower bound for `|h'|` on a
connected component of `{theta : |h theta| <= delta}`.  Here that analytic
step is isolated with no asymptotic notation: continuity and the nonvanishing
lower bound first produce a fixed derivative sign by the intermediate value
theorem, and Lagrange's mean value theorem then gives the sharp elementary
length bound `2 * delta / m`.

No component-length estimate, incidence bound, or cinematic maximal estimate
is assumed as a callback.
-/

/-- A continuous real function bounded away from zero on an interval has one
fixed quantitative sign there. -/
theorem continuous_fixed_sign_of_abs_lower_on_Icc
    (q : Real -> Real) {x y m : Real}
    (hxy : x <= y) (hm : 0 < m)
    (hqContinuous : ContinuousOn q (Icc x y))
    (habs : forall z, z ∈ Icc x y -> m <= |q z|) :
    (forall z, z ∈ Icc x y -> m <= q z) ∨
      (forall z, z ∈ Icc x y -> q z <= -m) := by
  have hxI : x ∈ Icc x y := left_mem_Icc.2 hxy
  have hsignAtX : m <= q x ∨ q x <= -m := by
    by_cases hxnonneg : 0 <= q x
    · left
      simpa [abs_of_nonneg hxnonneg] using habs x hxI
    · right
      have hxnonpos : q x <= 0 := le_of_not_ge hxnonneg
      have hxabs := habs x hxI
      rw [abs_of_nonpos hxnonpos] at hxabs
      linarith
  rcases hsignAtX with hxpositive | hxnegative
  · left
    intro z hzI
    by_contra hzpositive
    have hzlt : q z < m := lt_of_not_ge hzpositive
    have hznegative : q z <= -m := by
      by_cases hznonneg : 0 <= q z
      · have hzabs := habs z hzI
        rw [abs_of_nonneg hznonneg] at hzabs
        linarith
      · have hznonpos : q z <= 0 := le_of_not_ge hznonneg
        have hzabs := habs z hzI
        rw [abs_of_nonpos hznonpos] at hzabs
        linarith
    obtain ⟨w, hwI, hwzero⟩ :=
      isPreconnected_Icc.intermediate_value₂
        hzI hxI hqContinuous continuousOn_const
        (show q z <= (0 : Real) by linarith)
        (show (0 : Real) <= q x by linarith)
    have hwabs := habs w hwI
    rw [hwzero, abs_zero] at hwabs
    linarith
  · right
    intro z hzI
    by_contra hznegative
    have hzgt : -m < q z := lt_of_not_ge hznegative
    have hzpositive : m <= q z := by
      by_cases hznonpos : q z <= 0
      · have hzabs := habs z hzI
        rw [abs_of_nonpos hznonpos] at hzabs
        linarith
      · have hznonneg : 0 <= q z := le_of_not_ge hznonpos
        simpa [abs_of_nonneg hznonneg] using habs z hzI
    obtain ⟨w, hwI, hwzero⟩ :=
      isPreconnected_Icc.intermediate_value₂
        hxI hzI hqContinuous continuousOn_const
        (show q x <= (0 : Real) by linarith)
        (show (0 : Real) <= q z by linarith)
    have hwabs := habs w hwI
    rw [hwzero, abs_zero] at hwabs
    linarith

/-- If the derivative is at least `m > 0`, two points in the `delta`
sublevel set are separated by at most `2 * delta / m`. -/
theorem sublevel_interval_length_le_of_deriv_lower
    (h h1 : Real -> Real) {x y delta m : Real}
    (hxy : x <= y) (hm : 0 < m)
    (hx : |h x| <= delta) (hy : |h y| <= delta)
    (hderiv : forall z, z ∈ Icc x y -> HasDerivAt h (h1 z) z)
    (hlower : forall z, z ∈ Icc x y -> m <= h1 z) :
    y - x <= 2 * delta / m := by
  by_cases hxeq : x = y
  · subst y
    have hdelta : 0 <= delta := (abs_nonneg (h x)).trans hx
    have hquot : 0 <= 2 * delta / m :=
      div_nonneg (mul_nonneg (by norm_num) hdelta) (le_of_lt hm)
    simpa using hquot
  have hxylt : x < y := lt_of_le_of_ne hxy hxeq
  obtain ⟨z, hz, hslope⟩ := exists_hasDerivAt_eq_slope
    h h1 hxylt (HasDerivAt.continuousOn hderiv)
    (fun u hu => hderiv u (Ioo_subset_Icc_self hu))
  have hslopeLower := hlower z (Ioo_subset_Icc_self hz)
  rw [hslope] at hslopeLower
  have hgrowth : m * (y - x) <= h y - h x :=
    (le_div_iff₀ (sub_pos.2 hxylt)).1 hslopeLower
  have hendpoint : h y - h x <= 2 * delta := by
    calc
      h y - h x <= |h y - h x| := le_abs_self _
      _ = |h y + (-h x)| := by ring_nf
      _ <= |h y| + |-h x| := abs_add_le _ _
      _ = |h y| + |h x| := by rw [abs_neg]
      _ <= delta + delta := add_le_add hy hx
      _ = 2 * delta := by ring
  apply (le_div_iff₀ hm).2
  nlinarith

/-- Negative-derivative counterpart of the preceding sublevel bound. -/
theorem sublevel_interval_length_le_of_deriv_upper
    (h h1 : Real -> Real) {x y delta m : Real}
    (hxy : x <= y) (hm : 0 < m)
    (hx : |h x| <= delta) (hy : |h y| <= delta)
    (hderiv : forall z, z ∈ Icc x y -> HasDerivAt h (h1 z) z)
    (hupper : forall z, z ∈ Icc x y -> h1 z <= -m) :
    y - x <= 2 * delta / m := by
  apply sublevel_interval_length_le_of_deriv_lower
    (-h) (-h1) hxy hm
  · change |-h x| <= delta
    simpa only [abs_neg] using hx
  · change |-h y| <= delta
    simpa only [abs_neg] using hy
  · intro z hz
    exact (hderiv z hz).neg
  · intro z hz
    change m <= -h1 z
    linarith [hupper z hz]

/-- Callback-free form: continuity plus `m <= |h'|` produces the derivative
sign alternative internally, then bounds the sublevel interval length. -/
theorem sublevel_interval_length_le_of_abs_deriv_lower
    (h h1 : Real -> Real) {x y delta m : Real}
    (hxy : x <= y) (hm : 0 < m)
    (hx : |h x| <= delta) (hy : |h y| <= delta)
    (hderiv : forall z, z ∈ Icc x y -> HasDerivAt h (h1 z) z)
    (h1Continuous : ContinuousOn h1 (Icc x y))
    (habsLower : forall z, z ∈ Icc x y -> m <= |h1 z|) :
    y - x <= 2 * delta / m := by
  rcases continuous_fixed_sign_of_abs_lower_on_Icc
      h1 hxy hm h1Continuous habsLower with hlower | hupper
  · exact sublevel_interval_length_le_of_deriv_lower
      h h1 hxy hm hx hy hderiv hlower
  · exact sublevel_interval_length_le_of_deriv_upper
      h h1 hxy hm hx hy hderiv hupper

#print axioms continuous_fixed_sign_of_abs_lower_on_Icc
#print axioms sublevel_interval_length_le_of_deriv_lower
#print axioms sublevel_interval_length_le_of_deriv_upper
#print axioms sublevel_interval_length_le_of_abs_deriv_lower

end FamilyStickyCinematicL32SublevelIntervalV1
