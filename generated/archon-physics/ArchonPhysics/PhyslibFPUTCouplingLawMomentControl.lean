import ArchonPhysics.PhyslibFPUTRestartLawMomentPropagation

/-!
# Coupling criteria for restart-law and moment control

An explicit coupling on one probability space controls bounded Lipschitz test
expectations.  If `X` and `Y` are within `delta` outside a bad set of
probability at most `p`, then every real test bounded by one and Lipschitz with
constant `L` has expectation error at most `L * delta + 2 * p`.

For `delta > 0` this is a bounded-Lipschitz statement, not total variation:
arbitrary measurable tests need not be stable under a small displacement.
When the coupling is exact off the bad set, we do recover the stronger
`BoundedTestLawDistanceAtMost` condition with error `2 * p`.

On a radius-`M` complex amplitude ball, the same argument gives the explicit
second/fourth moment errors

* `2 M delta + 2 M^2 p`, and
* `4 M^3 delta + 2 M^4 p`.

The existence of such a Hamiltonian coupling remains a transparent input.
-/

namespace ArchonPhysics.PhyslibFPUTCouplingLawMomentControl

open MeasureTheory
open ArchonPhysics
open ArchonPhysics.PhyslibFPUTRestartLawMomentPropagation
open ArchonPhysics.PhyslibFPUTShortTimeRPAMomentStability

noncomputable section

/-! ## A reusable good/bad expectation estimate -/

/-- Split a bounded expectation difference into a good-set error `G` and a
bad-set probability cost `2 B p`. -/
theorem abs_integral_sub_integral_le_of_highProbability_good
    {Omega : Type*} [MeasurableSpace Omega]
    (mu : Measure Omega) [IsProbabilityMeasure mu]
    (bad : Set Omega) (hbadMeasurable : MeasurableSet bad)
    {p B G : Real}
    (hbadProbability : mu.real bad ≤ p)
    (hB : 0 ≤ B) (hG : 0 ≤ G)
    (a b : Omega → Real) (ha : Measurable a) (hb : Measurable b)
    (haBound : ∀ omega, |a omega| ≤ B)
    (hbBound : ∀ omega, |b omega| ≤ B)
    (hgood : ∀ omega, omega ∉ bad → |a omega - b omega| ≤ G) :
    |∫ omega, a omega ∂mu - ∫ omega, b omega ∂mu| ≤
      G + 2 * B * p := by
  have haIntegrable : Integrable a mu := by
    apply Integrable.of_bound ha.aestronglyMeasurable B
    filter_upwards with omega
    simpa only [Real.norm_eq_abs] using haBound omega
  have hbIntegrable : Integrable b mu := by
    apply Integrable.of_bound hb.aestronglyMeasurable B
    filter_upwards with omega
    simpa only [Real.norm_eq_abs] using hbBound omega
  have habIntegrable : Integrable (fun omega ↦ a omega - b omega) mu :=
    haIntegrable.sub hbIntegrable
  have hbadIntegral :
      ‖∫ omega in bad, a omega - b omega ∂mu‖ ≤
        (2 * B) * mu.real bad := by
    apply norm_setIntegral_le_of_norm_le_const (measure_lt_top mu bad)
    intro omega _homega
    calc
      ‖a omega - b omega‖ ≤ ‖a omega‖ + ‖b omega‖ :=
        norm_sub_le _ _
      _ ≤ B + B := by
        exact add_le_add
          (by simpa only [Real.norm_eq_abs] using haBound omega)
          (by simpa only [Real.norm_eq_abs] using hbBound omega)
      _ = 2 * B := by ring
  have hgoodIntegral :
      ‖∫ omega in badᶜ, a omega - b omega ∂mu‖ ≤
        G * mu.real badᶜ := by
    apply norm_setIntegral_le_of_norm_le_const (measure_lt_top mu badᶜ)
    intro omega homega
    simpa only [Real.norm_eq_abs] using hgood omega homega
  have hsplit := integral_add_compl hbadMeasurable habIntegrable
  calc
    |∫ omega, a omega ∂mu - ∫ omega, b omega ∂mu| =
        ‖∫ omega, a omega - b omega ∂mu‖ := by
      rw [integral_sub haIntegrable hbIntegrable, Real.norm_eq_abs]
    _ = ‖(∫ omega in bad, a omega - b omega ∂mu) +
          ∫ omega in badᶜ, a omega - b omega ∂mu‖ := by
      rw [hsplit]
    _ ≤ ‖∫ omega in bad, a omega - b omega ∂mu‖ +
          ‖∫ omega in badᶜ, a omega - b omega ∂mu‖ :=
      norm_add_le _ _
    _ ≤ (2 * B) * mu.real bad + G * mu.real badᶜ :=
      add_le_add hbadIntegral hgoodIntegral
    _ ≤ (2 * B) * p + G * 1 := by
      exact add_le_add
        (mul_le_mul_of_nonneg_left hbadProbability
          (mul_nonneg (by norm_num) hB))
        (mul_le_mul_of_nonneg_left measureReal_le_one hG)
    _ = G + 2 * B * p := by ring

/-! ## Bounded-Lipschitz law distance from an approximate coupling -/

/-- Dual law closeness for real tests bounded by one and having the displayed
Lipschitz constant. -/
def BoundedLipschitzTestLawDistanceAtMost
    {S : Type*} [MeasurableSpace S] [PseudoMetricSpace S]
    (mu nu : Measure S) (L eta : Real) : Prop :=
  ∀ f : S → Real, Measurable f → (∀ x, |f x| ≤ 1) →
    (∀ x y, |f x - f y| ≤ L * dist x y) →
    |∫ x, f x ∂mu - ∫ y, f y ∂nu| ≤ eta

/-- Same-space approximate coupling estimate for one bounded Lipschitz test. -/
theorem abs_coupled_expectation_sub_le
    {Omega S : Type*} [MeasurableSpace Omega]
    [MeasurableSpace S] [PseudoMetricSpace S]
    (mu : Measure Omega) [IsProbabilityMeasure mu]
    (X Y : Omega → S) (hX : Measurable X) (hY : Measurable Y)
    (bad : Set Omega) (hbadMeasurable : MeasurableSet bad)
    {delta p L : Real}
    (hdelta : 0 ≤ delta) (hL : 0 ≤ L)
    (hbadProbability : mu.real bad ≤ p)
    (hnear : ∀ omega, omega ∉ bad → dist (X omega) (Y omega) ≤ delta)
    (f : S → Real) (hf : Measurable f)
    (hfBound : ∀ x, |f x| ≤ 1)
    (hfLipschitz : ∀ x y, |f x - f y| ≤ L * dist x y) :
    |∫ omega, f (X omega) ∂mu - ∫ omega, f (Y omega) ∂mu| ≤
      L * delta + 2 * p := by
  have hgood : ∀ omega, omega ∉ bad →
      |f (X omega) - f (Y omega)| ≤ L * delta := by
    intro omega homega
    exact (hfLipschitz (X omega) (Y omega)).trans
      (mul_le_mul_of_nonneg_left (hnear omega homega) hL)
  simpa [mul_assoc] using
    abs_integral_sub_integral_le_of_highProbability_good
      mu bad hbadMeasurable hbadProbability (by norm_num) (mul_nonneg hL hdelta)
      (fun omega ↦ f (X omega)) (fun omega ↦ f (Y omega))
      (hf.comp hX) (hf.comp hY) (fun omega ↦ hfBound (X omega))
      (fun omega ↦ hfBound (Y omega)) hgood

/-- The pushforward laws of an approximate coupling are close for bounded
Lipschitz tests, with error `L delta + 2 p`. -/
theorem boundedLipschitzTestLawDistanceAtMost_map_of_coupling
    {Omega S : Type*} [MeasurableSpace Omega]
    [MeasurableSpace S] [PseudoMetricSpace S]
    (mu : Measure Omega) [IsProbabilityMeasure mu]
    (X Y : Omega → S) (hX : Measurable X) (hY : Measurable Y)
    (bad : Set Omega) (hbadMeasurable : MeasurableSet bad)
    {delta p L : Real}
    (hdelta : 0 ≤ delta) (hL : 0 ≤ L)
    (hbadProbability : mu.real bad ≤ p)
    (hnear : ∀ omega, omega ∉ bad → dist (X omega) (Y omega) ≤ delta) :
    BoundedLipschitzTestLawDistanceAtMost
      (Measure.map X mu) (Measure.map Y mu) L (L * delta + 2 * p) := by
  intro f hf hfBound hfLipschitz
  have hcoupled := abs_coupled_expectation_sub_le
    mu X Y hX hY bad hbadMeasurable hdelta hL hbadProbability hnear
      f hf hfBound hfLipschitz
  rw [integral_map_of_stronglyMeasurable hX hf.stronglyMeasurable,
    integral_map_of_stronglyMeasurable hY hf.stronglyMeasurable]
  exact hcoupled

/-! ## Exact coupling recovers the stronger bounded-test law distance -/

/-- If the coupled variables agree off a bad set, arbitrary bounded measurable
tests (not only Lipschitz tests) are controlled.  This is the precise coupling
route back to `BoundedTestLawDistanceAtMost`. -/
theorem boundedTestLawDistanceAtMost_map_of_exactCoupling
    {Omega S : Type*} [MeasurableSpace Omega] [MeasurableSpace S]
    (mu : Measure Omega) [IsProbabilityMeasure mu]
    (X Y : Omega → S) (hX : Measurable X) (hY : Measurable Y)
    (bad : Set Omega) (hbadMeasurable : MeasurableSet bad)
    {p : Real} (hbadProbability : mu.real bad ≤ p)
    (hagree : ∀ omega, omega ∉ bad → X omega = Y omega) :
    BoundedTestLawDistanceAtMost
      (Measure.map X mu) (Measure.map Y mu) (2 * p) := by
  intro f hf hfBound
  have hgood : ∀ omega, omega ∉ bad →
      |f (X omega) - f (Y omega)| ≤ 0 := by
    intro omega homega
    rw [hagree omega homega, sub_self, abs_zero]
  have hcoupled :=
    abs_integral_sub_integral_le_of_highProbability_good
      mu bad hbadMeasurable hbadProbability (by norm_num) (by norm_num)
      (fun omega ↦ f (X omega)) (fun omega ↦ f (Y omega))
      (hf.comp hX) (hf.comp hY) (fun omega ↦ hfBound (X omega))
      (fun omega ↦ hfBound (Y omega)) hgood
  rw [integral_map_of_stronglyMeasurable hX hf.stronglyMeasurable,
    integral_map_of_stronglyMeasurable hY hf.stronglyMeasurable]
  simpa using hcoupled

/-! ## Explicit coupled second and fourth amplitude moments -/

/-- A high-probability near coupling on a uniformly bounded complex amplitude
ball controls the second and fourth moments with the sharp deterministic
constants inherited from the one-block RPA product algebra. -/
theorem coupled_second_fourth_moment_errors
    {Omega : Type*} [MeasurableSpace Omega]
    (mu : Measure Omega) [IsProbabilityMeasure mu]
    (X Y : Omega → Complex) (hX : Measurable X) (hY : Measurable Y)
    (bad : Set Omega) (hbadMeasurable : MeasurableSet bad)
    {delta p M : Real}
    (hdelta : 0 ≤ delta) (hM : 0 ≤ M)
    (hbadProbability : mu.real bad ≤ p)
    (hnear : ∀ omega, omega ∉ bad → ‖X omega - Y omega‖ ≤ delta)
    (hXBound : ∀ omega, ‖X omega‖ ≤ M)
    (hYBound : ∀ omega, ‖Y omega‖ ≤ M) :
    |∫ omega, Complex.normSq (X omega) ∂mu -
        ∫ omega, Complex.normSq (Y omega) ∂mu| ≤
        2 * M * delta + 2 * M ^ 2 * p ∧
    |∫ omega, Complex.normSq (X omega) ^ 2 ∂mu -
        ∫ omega, Complex.normSq (Y omega) ^ 2 ∂mu| ≤
        4 * M ^ 3 * delta + 2 * M ^ 4 * p := by
  have hsecondGood : ∀ omega, omega ∉ bad →
      |Complex.normSq (X omega) - Complex.normSq (Y omega)| ≤
        2 * M * delta := by
    intro omega homega
    exact abs_normSq_sub_normSq_le hM hdelta
      (hXBound omega) (hYBound omega) (hnear omega homega)
  have hfourthGood : ∀ omega, omega ∉ bad →
      |Complex.normSq (X omega) ^ 2 - Complex.normSq (Y omega) ^ 2| ≤
        4 * M ^ 3 * delta := by
    intro omega homega
    exact abs_normSq_sq_sub_normSq_sq_le hM hdelta
      (hXBound omega) (hYBound omega) (hnear omega homega)
  constructor
  · simpa [amplitudeSecondMomentObservable] using
      abs_integral_sub_integral_le_of_highProbability_good
        mu bad hbadMeasurable hbadProbability (sq_nonneg M)
        (mul_nonneg (mul_nonneg (by norm_num) hM) hdelta)
        (amplitudeSecondMomentObservable X)
        (amplitudeSecondMomentObservable Y)
        (measurable_amplitudeSecondMomentObservable hX)
        (measurable_amplitudeSecondMomentObservable hY)
        (abs_amplitudeSecondMomentObservable_le hM hXBound)
        (abs_amplitudeSecondMomentObservable_le hM hYBound)
        hsecondGood
  · simpa [amplitudeFourthMomentObservable] using
      abs_integral_sub_integral_le_of_highProbability_good
        (G := 4 * M ^ 3 * delta)
        mu bad hbadMeasurable hbadProbability (pow_nonneg hM 4)
        (by positivity)
        (amplitudeFourthMomentObservable X)
        (amplitudeFourthMomentObservable Y)
        (measurable_amplitudeFourthMomentObservable hX)
        (measurable_amplitudeFourthMomentObservable hY)
        (abs_amplitudeFourthMomentObservable_le hM hXBound)
        (abs_amplitudeFourthMomentObservable_le hM hYBound)
        hfourthGood

/-- Pushforward-law formulation of the coupled moment bounds. -/
theorem pushforward_second_fourth_moment_errors
    {Omega : Type*} [MeasurableSpace Omega]
    (mu : Measure Omega) [IsProbabilityMeasure mu]
    (X Y : Omega → Complex) (hX : Measurable X) (hY : Measurable Y)
    (bad : Set Omega) (hbadMeasurable : MeasurableSet bad)
    {delta p M : Real}
    (hdelta : 0 ≤ delta) (hM : 0 ≤ M)
    (hbadProbability : mu.real bad ≤ p)
    (hnear : ∀ omega, omega ∉ bad → ‖X omega - Y omega‖ ≤ delta)
    (hXBound : ∀ omega, ‖X omega‖ ≤ M)
    (hYBound : ∀ omega, ‖Y omega‖ ≤ M) :
    |∫ z, Complex.normSq z ∂Measure.map X mu -
        ∫ z, Complex.normSq z ∂Measure.map Y mu| ≤
        2 * M * delta + 2 * M ^ 2 * p ∧
    |∫ z, Complex.normSq z ^ 2 ∂Measure.map X mu -
        ∫ z, Complex.normSq z ^ 2 ∂Measure.map Y mu| ≤
        4 * M ^ 3 * delta + 2 * M ^ 4 * p := by
  have hmoments := coupled_second_fourth_moment_errors
    mu X Y hX hY bad hbadMeasurable hdelta hM hbadProbability
      hnear hXBound hYBound
  rw [integral_map_of_stronglyMeasurable hX
      Complex.continuous_normSq.measurable.stronglyMeasurable,
    integral_map_of_stronglyMeasurable hY
      Complex.continuous_normSq.measurable.stronglyMeasurable,
    integral_map_of_stronglyMeasurable hX
      (Complex.continuous_normSq.measurable.pow_const 2).stronglyMeasurable,
    integral_map_of_stronglyMeasurable hY
      (Complex.continuous_normSq.measurable.pow_const 2).stronglyMeasurable]
  exact hmoments

end

end ArchonPhysics.PhyslibFPUTCouplingLawMomentControl
