import ArchonPhysics.CanonicalUniformAffineMassFourierDecay
import ArchonPhysics.WeightedMismatchCompactIntervalFourierDecay
import Mathlib.Analysis.Calculus.Deriv.Inverse

/-!
# Canonical uniform mass through an increasing smooth mismatch chart

This module supplies the one-dimensional change-of-variables layer that sits
between the canonical `Uniform[4/5,6/5]` mass coordinate and the existing
endpoint-aware compact-interval Fourier certificate.

A datum below is one increasing `C²` chart branch, together with a regular
inverse extension on the image interval.  A complex `C¹` mass weight is
pushed forward with density
`(5/2) * weight(inv y) / chart'(inv y)`.  The derivative of that density is
computed explicitly and the exact expectation change of variables is proved.

This is not an eigenfrequency theorem.  For an actual random FPUT spectral
mismatch one must still verify the displayed chart derivative, positive
Jacobian lower bound, inverse regularity, and weight derivative hypotheses.
A piecewise-`C²` mismatch is handled branch by branch; this file does not
silently cross an internal derivative jump.
-/

namespace ArchonPhysics.CanonicalUniformMassMonotoneChartFourierCertificate

open ArchonPhysics
open ArchonPhysics.CanonicalIIDCoerciveIteratedA2ExpectationFourierDecay
open ArchonPhysics.CanonicalUniformAffineMassFourierDecay
open scoped Topology
open ArchonPhysics.WeightedMismatchCompactIntervalFourierDecay
open MeasureTheory Set
open Filter

noncomputable section

/-- Data for one increasing smooth chart on the canonical uniform mass
interval.  The inverse is supplied as a regular extension because the target
Fourier certificate asks for ordinary derivatives also at the two endpoints. -/
structure IncreasingUniformMassC2ChartData where
  chart : Real → Real
  chartDeriv : Real → Real
  chartSecondDeriv : Real → Real
  inverse : Real → Real
  jacobianLower : Real
  jacobianLower_pos : 0 < jacobianLower
  chart_hasDeriv : ∀ mass : Real,
    HasDerivAt chart (chartDeriv mass) mass
  chartDeriv_hasDeriv : ∀ mass : Real,
    HasDerivAt chartDeriv (chartSecondDeriv mass) mass
  chartSecondDeriv_continuous : Continuous chartSecondDeriv
  jacobianLower_le : ∀ mass ∈ RandomEnsemble.massSupport,
    jacobianLower ≤ chartDeriv mass
  inverse_mapsTo_massSupport :
    MapsTo inverse
      (Icc (chart RandomEnsemble.massLower)
        (chart RandomEnsemble.massUpper))
      RandomEnsemble.massSupport
  inverse_chart : ∀ mass ∈ RandomEnsemble.massSupport,
    inverse (chart mass) = mass
  inverse_hasDeriv : ∀ mismatch ∈
      Icc (chart RandomEnsemble.massLower)
        (chart RandomEnsemble.massUpper),
    HasDerivAt inverse
      (chartDeriv (inverse mismatch))⁻¹ mismatch

/-- The chart derivative is positive throughout the physical mass support. -/
theorem IncreasingUniformMassC2ChartData.chartDeriv_pos
    (data : IncreasingUniformMassC2ChartData)
    {mass : Real} (hmass : mass ∈ RandomEnsemble.massSupport) :
    0 < data.chartDeriv mass :=
  data.jacobianLower_pos.trans_le (data.jacobianLower_le mass hmass)

/-- In particular, the chart Jacobian never vanishes on the mass support. -/
theorem IncreasingUniformMassC2ChartData.chartDeriv_ne_zero
    (data : IncreasingUniformMassC2ChartData)
    {mass : Real} (hmass : mass ∈ RandomEnsemble.massSupport) :
    data.chartDeriv mass ≠ 0 :=
  (data.chartDeriv_pos hmass).ne'

/-- The supplied derivative proves global continuity of the chart. -/
theorem IncreasingUniformMassC2ChartData.chart_continuous
    (data : IncreasingUniformMassC2ChartData) :
    Continuous data.chart :=
  continuous_iff_continuousAt.mpr fun mass =>
    (data.chart_hasDeriv mass).continuousAt

/-- The supplied second derivative proves global continuity of the first
chart derivative. -/
theorem IncreasingUniformMassC2ChartData.chartDeriv_continuous
    (data : IncreasingUniformMassC2ChartData) :
    Continuous data.chartDeriv :=
  continuous_iff_continuousAt.mpr fun mass =>
    (data.chartDeriv_hasDeriv mass).continuousAt

/-- The positive Jacobian bound implies strict monotonicity on
`[4/5,6/5]`; injectivity is therefore not an extra hidden assumption. -/
theorem IncreasingUniformMassC2ChartData.strictMonoOn_massSupport
    (data : IncreasingUniformMassC2ChartData) :
    StrictMonoOn data.chart RandomEnsemble.massSupport := by
  rw [RandomEnsemble.massSupport]
  apply strictMonoOn_of_hasDerivWithinAt_pos
    (D := Icc RandomEnsemble.massLower RandomEnsemble.massUpper) (convex_Icc _ _)
    data.chart_continuous.continuousOn
  · intro mass _hmass
    exact (data.chart_hasDeriv mass).hasDerivWithinAt
  · intro mass hmass
    exact data.chartDeriv_pos (interior_subset hmass)

/-- Explicit interval injectivity furnished by the Jacobian lower bound. -/
theorem IncreasingUniformMassC2ChartData.injOn_massSupport
    (data : IncreasingUniformMassC2ChartData) :
    Set.InjOn data.chart RandomEnsemble.massSupport :=
  data.strictMonoOn_massSupport.injOn

/-- The output interval is positively oriented. -/
theorem IncreasingUniformMassC2ChartData.chartLower_lt_chartUpper
    (data : IncreasingUniformMassC2ChartData) :
    data.chart RandomEnsemble.massLower <
      data.chart RandomEnsemble.massUpper := by
  apply data.strictMonoOn_massSupport
  · exact ⟨le_rfl, RandomEnsemble.massLower_le_massUpper⟩
  · exact ⟨RandomEnsemble.massLower_le_massUpper, le_rfl⟩
  · norm_num [RandomEnsemble.massLower, RandomEnsemble.massUpper]

theorem IncreasingUniformMassC2ChartData.chartLower_le_chartUpper
    (data : IncreasingUniformMassC2ChartData) :
    data.chart RandomEnsemble.massLower ≤
      data.chart RandomEnsemble.massUpper :=
  data.chartLower_lt_chartUpper.le

/-- The image of the physical mass interval is exactly the endpoint interval. -/
theorem IncreasingUniformMassC2ChartData.image_massSupport
    (data : IncreasingUniformMassC2ChartData) :
    data.chart '' RandomEnsemble.massSupport =
      Icc (data.chart RandomEnsemble.massLower)
        (data.chart RandomEnsemble.massUpper) := by
  have hcontinuous : ContinuousOn data.chart
      (uIcc RandomEnsemble.massLower RandomEnsemble.massUpper) := by
    simpa [RandomEnsemble.massSupport,
      uIcc_of_le RandomEnsemble.massLower_le_massUpper] using
        data.chart_continuous.continuousOn
  have hmonotone : MonotoneOn data.chart
      (uIcc RandomEnsemble.massLower RandomEnsemble.massUpper) := by
    simpa [RandomEnsemble.massSupport,
      uIcc_of_le RandomEnsemble.massLower_le_massUpper] using
        data.strictMonoOn_massSupport.monotoneOn
  simpa [RandomEnsemble.massSupport,
    uIcc_of_le RandomEnsemble.massLower_le_massUpper,
    uIcc_of_le data.chartLower_le_chartUpper] using
      hcontinuous.image_uIcc_of_monotoneOn hmonotone

/-- A useful constructor for the inverse-derivative field.  Thus an actual
chart may prove inverse regularity from continuity plus a local right-inverse,
rather than differentiating an opaque `Function.invFun`. -/
theorem IncreasingUniformMassC2ChartData.inverse_hasDeriv_of_local_rightInverse
    (data : IncreasingUniformMassC2ChartData)
    {mismatch : Real}
    (hmismatch : mismatch ∈
      Icc (data.chart RandomEnsemble.massLower)
        (data.chart RandomEnsemble.massUpper))
    (hinverseContinuous : ContinuousAt data.inverse mismatch)
    (hright : ∀ᶠ value in 𝓝 mismatch,
      data.chart (data.inverse value) = value) :
    HasDerivAt data.inverse
      (data.chartDeriv (data.inverse mismatch))⁻¹ mismatch := by
  exact (data.chart_hasDeriv (data.inverse mismatch)).of_local_left_inverse
    hinverseContinuous
    (data.chartDeriv_ne_zero
      (data.inverse_mapsTo_massSupport hmismatch))
    hright

/-- Push-forward density of the normalized uniform law and a complex mass
weight through one increasing chart. -/
def pushedDensity
    (data : IncreasingUniformMassC2ChartData)
    (weight : Real → Complex) (mismatch : Real) : Complex :=
  ((5 / 2 : Real) : Complex) * weight (data.inverse mismatch) /
    (data.chartDeriv (data.inverse mismatch) : Complex)

/-- The explicit derivative of `pushedDensity`. -/
def pushedDensityDeriv
    (data : IncreasingUniformMassC2ChartData)
    (weight weightDeriv : Real → Complex) (mismatch : Real) : Complex :=
  ((5 / 2 : Real) : Complex) *
    (weightDeriv (data.inverse mismatch) /
        (data.chartDeriv (data.inverse mismatch) : Complex) ^ 2 -
      weight (data.inverse mismatch) *
          (data.chartSecondDeriv (data.inverse mismatch) : Complex) /
        (data.chartDeriv (data.inverse mismatch) : Complex) ^ 3)

/-- Exact quotient-and-inverse derivative formula for the pushed density. -/
theorem pushedDensity_hasDeriv
    (data : IncreasingUniformMassC2ChartData)
    (weight weightDeriv : Real → Complex)
    (hweight : ∀ mass : Real,
      HasDerivAt weight (weightDeriv mass) mass)
    {mismatch : Real}
    (hmismatch : mismatch ∈
      Icc (data.chart RandomEnsemble.massLower)
        (data.chart RandomEnsemble.massUpper)) :
    HasDerivAt (pushedDensity data weight)
      (pushedDensityDeriv data weight weightDeriv mismatch) mismatch := by
  let mass := data.inverse mismatch
  have hmass : mass ∈ RandomEnsemble.massSupport :=
    data.inverse_mapsTo_massSupport hmismatch
  have hJacobian : data.chartDeriv mass ≠ 0 :=
    data.chartDeriv_ne_zero hmass
  have hinverse :
      HasDerivAt data.inverse (data.chartDeriv mass)⁻¹ mismatch := by
    simpa [mass] using data.inverse_hasDeriv mismatch hmismatch
  have hweightComp :
      HasDerivAt (weight ∘ data.inverse)
        ((data.chartDeriv mass)⁻¹ • weightDeriv mass) mismatch :=
    (hweight mass).scomp mismatch hinverse
  have hderivCompReal :
      HasDerivAt (data.chartDeriv ∘ data.inverse)
        (data.chartSecondDeriv mass * (data.chartDeriv mass)⁻¹) mismatch :=
    (data.chartDeriv_hasDeriv mass).comp mismatch hinverse
  have hderivCompComplex :
      HasDerivAt
        (fun value : Real =>
          (data.chartDeriv (data.inverse value) : Complex))
        ((data.chartSecondDeriv mass * (data.chartDeriv mass)⁻¹ : Real) :
          Complex) mismatch := by
    simpa [Function.comp_def] using hderivCompReal.ofReal_comp
  have hquotient := hweightComp.div hderivCompComplex
    (Complex.ofReal_ne_zero.mpr hJacobian)
  have hscaled :=
    hquotient.const_mul ((5 / 2 : Real) : Complex)
  refine (hscaled.congr_of_eventuallyEq ?_).congr_deriv ?_
  · filter_upwards with value
    simp [pushedDensity, Function.comp_def, div_eq_mul_inv, mul_assoc]
  · unfold pushedDensityDeriv
    dsimp [mass] at *
    push_cast
    field_simp [hJacobian]

/-- The explicit pushed-density derivative is continuous on the output
interval for a `C²` chart and a complex `C¹` weight. -/
theorem pushedDensityDeriv_continuousOn
    (data : IncreasingUniformMassC2ChartData)
    (weight weightDeriv : Real → Complex)
    (hweight : ∀ mass : Real,
      HasDerivAt weight (weightDeriv mass) mass)
    (hweightDerivContinuous : Continuous weightDeriv) :
    ContinuousOn (pushedDensityDeriv data weight weightDeriv)
      (Icc (data.chart RandomEnsemble.massLower)
        (data.chart RandomEnsemble.massUpper)) := by
  let output :=
    Icc (data.chart RandomEnsemble.massLower)
      (data.chart RandomEnsemble.massUpper)
  have hinverse : ContinuousOn data.inverse output := by
    intro mismatch hmismatch
    exact (data.inverse_hasDeriv mismatch hmismatch).continuousAt.continuousWithinAt
  have hweightContinuous : Continuous weight :=
    continuous_iff_continuousAt.mpr fun mass => (hweight mass).continuousAt
  have hweightComp : ContinuousOn (fun mismatch =>
      weight (data.inverse mismatch)) output :=
    hweightContinuous.continuousOn.comp hinverse (mapsTo_univ _ _)
  have hweightDerivComp : ContinuousOn (fun mismatch =>
      weightDeriv (data.inverse mismatch)) output :=
    hweightDerivContinuous.continuousOn.comp hinverse (mapsTo_univ _ _)
  have hchartDerivReal : ContinuousOn (fun mismatch =>
      data.chartDeriv (data.inverse mismatch)) output :=
    data.chartDeriv_continuous.continuousOn.comp hinverse (mapsTo_univ _ _)
  have hchartSecondReal : ContinuousOn (fun mismatch =>
      data.chartSecondDeriv (data.inverse mismatch)) output :=
    data.chartSecondDeriv_continuous.continuousOn.comp hinverse (mapsTo_univ _ _)
  have hchartDeriv : ContinuousOn (fun mismatch =>
      (data.chartDeriv (data.inverse mismatch) : Complex)) output :=
    Complex.continuous_ofReal.continuousOn.comp hchartDerivReal (mapsTo_univ _ _)
  have hchartSecond : ContinuousOn (fun mismatch =>
      (data.chartSecondDeriv (data.inverse mismatch) : Complex)) output :=
    Complex.continuous_ofReal.continuousOn.comp hchartSecondReal (mapsTo_univ _ _)
  have hJacobian : ∀ mismatch ∈ output,
      (data.chartDeriv (data.inverse mismatch) : Complex) ≠ 0 := by
    intro mismatch hmismatch
    exact Complex.ofReal_ne_zero.mpr
      (data.chartDeriv_ne_zero
        (data.inverse_mapsTo_massSupport hmismatch))
  unfold pushedDensityDeriv
  exact continuousOn_const.mul
    ((hweightDerivComp.div (hchartDeriv.pow 2)
        (fun mismatch hmismatch => pow_ne_zero 2 (hJacobian mismatch hmismatch))).sub
      ((hweightComp.mul hchartSecond).div (hchartDeriv.pow 3)
        (fun mismatch hmismatch => pow_ne_zero 3 (hJacobian mismatch hmismatch))))

/-- Consequently the displayed derivative is interval integrable. -/
theorem pushedDensityDeriv_intervalIntegrable
    (data : IncreasingUniformMassC2ChartData)
    (weight weightDeriv : Real → Complex)
    (hweight : ∀ mass : Real,
      HasDerivAt weight (weightDeriv mass) mass)
    (hweightDerivContinuous : Continuous weightDeriv) :
    IntervalIntegrable (pushedDensityDeriv data weight weightDeriv)
      volume
      (data.chart RandomEnsemble.massLower)
      (data.chart RandomEnsemble.massUpper) := by
  apply ContinuousOn.intervalIntegrable
  simpa [uIcc_of_le data.chartLower_le_chartUpper] using
    (pushedDensityDeriv_continuousOn data weight weightDeriv
      hweight hweightDerivContinuous)

/-- Exact change of variables from the canonical uniform mass expectation to
the pushed compact-interval density. -/
theorem uniformMass_weightedMismatchExpectation_eq_interval
    (data : IncreasingUniformMassC2ChartData)
    (weight weightDeriv : Real → Complex)
    (hweight : ∀ mass : Real,
      HasDerivAt weight (weightDeriv mass) mass)
    (time : Real) :
    weightedMismatchExpectation RandomEnsemble.massCoordinateLaw
        data.chart weight time =
      weightedMismatchIntervalOscillatoryIntegral
        (pushedDensity data weight)
        (data.chart RandomEnsemble.massLower)
        (data.chart RandomEnsemble.massUpper) time := by
  have hphaseDensity : ContinuousOn
      (fun mismatch : Real =>
        Complex.exp
            (Complex.I * ((time * mismatch : Real) : Complex)) *
          pushedDensity data weight mismatch)
      (Icc (data.chart RandomEnsemble.massLower)
        (data.chart RandomEnsemble.massUpper)) := by
    have hdensity : ContinuousOn (pushedDensity data weight)
        (Icc (data.chart RandomEnsemble.massLower)
          (data.chart RandomEnsemble.massUpper)) :=
      fun mismatch hmismatch =>
        (pushedDensity_hasDeriv data weight weightDeriv hweight
          hmismatch).continuousAt.continuousWithinAt
    exact (by fun_prop : Continuous
      (fun mismatch : Real =>
        Complex.exp
          (Complex.I * ((time * mismatch : Real) : Complex)))).continuousOn.mul hdensity
  have himage :
      data.chart ''
          uIcc RandomEnsemble.massLower RandomEnsemble.massUpper =
        Icc (data.chart RandomEnsemble.massLower)
          (data.chart RandomEnsemble.massUpper) := by
    simpa [RandomEnsemble.massSupport,
      uIcc_of_le RandomEnsemble.massLower_le_massUpper] using
        data.image_massSupport
  have hsubstitution :=
    intervalIntegral.integral_deriv_smul_comp'
      (a := RandomEnsemble.massLower)
      (b := RandomEnsemble.massUpper)
      (f := data.chart) (f' := data.chartDeriv)
      (g := fun mismatch : Real =>
        Complex.exp
            (Complex.I * ((time * mismatch : Real) : Complex)) *
          pushedDensity data weight mismatch)
      (fun mass _hmass => data.chart_hasDeriv mass)
      data.chartDeriv_continuous.continuousOn
      (by rw [himage]; exact hphaseDensity)
  rw [weightedMismatchExpectation,
    integral_massCoordinateLaw_eq_fiveHalves_smul_setIntegral,
    integral_massSupport_eq_intervalIntegral,
    weightedMismatchIntervalOscillatoryIntegral]
  rw [← hsubstitution]
  rw [← intervalIntegral.integral_smul]
  apply intervalIntegral.integral_congr
  intro mass hmassInterval
  have hmass : mass ∈ RandomEnsemble.massSupport := by
    simpa [RandomEnsemble.massSupport,
      uIcc_of_le RandomEnsemble.massLower_le_massUpper] using hmassInterval
  have hJacobian : data.chartDeriv mass ≠ 0 :=
    data.chartDeriv_ne_zero hmass
  simp only [Function.comp_apply]
  unfold pushedDensity
  rw [data.inverse_chart mass hmass]
  simp only [Complex.real_smul]
  push_cast
  field_simp [hJacobian]

/-- The promised constructor of the existing compact-interval Fourier
certificate.  No actual spectral chart is manufactured here: all model
content is visible in `IncreasingUniformMassC2ChartData` and the two `C¹`
weight hypotheses. -/
def compactIntervalCertificate
    (data : IncreasingUniformMassC2ChartData)
    (weight weightDeriv : Real → Complex)
    (hweight : ∀ mass : Real,
      HasDerivAt weight (weightDeriv mass) mass)
    (hweightDerivContinuous : Continuous weightDeriv) :
    WeightedMismatchCompactIntervalFourierCertificate
      RandomEnsemble.massCoordinateLaw data.chart weight where
  lower := data.chart RandomEnsemble.massLower
  upper := data.chart RandomEnsemble.massUpper
  lower_le_upper := data.chartLower_le_chartUpper
  density := pushedDensity data weight
  densityDeriv := pushedDensityDeriv data weight weightDeriv
  expectation_eq :=
    uniformMass_weightedMismatchExpectation_eq_interval
      data weight weightDeriv hweight
  density_hasDeriv := by
    intro mismatch hmismatch
    rw [uIcc_of_le data.chartLower_le_chartUpper] at hmismatch
    exact pushedDensity_hasDeriv data weight weightDeriv hweight hmismatch
  densityDeriv_intervalIntegrable :=
    pushedDensityDeriv_intervalIntegrable
      data weight weightDeriv hweight hweightDerivContinuous

/-- Immediate endpoint-aware decay once a concrete chart datum is supplied. -/
theorem norm_uniformMass_weightedMismatchExpectation_le_div_abs_time
    (data : IncreasingUniformMassC2ChartData)
    (weight weightDeriv : Real → Complex)
    (hweight : ∀ mass : Real,
      HasDerivAt weight (weightDeriv mass) mass)
    (hweightDerivContinuous : Continuous weightDeriv)
    {time : Real} (htime : time ≠ 0) :
    ‖weightedMismatchExpectation RandomEnsemble.massCoordinateLaw
      data.chart weight time‖ ≤
      (compactIntervalCertificate data weight weightDeriv
        hweight hweightDerivContinuous).variationCost / |time| :=
  (compactIntervalCertificate data weight weightDeriv
    hweight hweightDerivContinuous).norm_expectation_le_div_abs_time htime


/-! ## Orientation adapter -/

/-- Negating the chart is exactly compensated by negating time.  Thus the
increasing-chart constructor also controls a decreasing physical chart after
reorienting the chart by a minus sign. -/
theorem weightedMismatchExpectation_neg_chart
    {Omega : Type*} [MeasurableSpace Omega]
    (measure : Measure Omega) (chart : Omega -> Real)
    (weight : Omega -> Complex) (time : Real) :
    weightedMismatchExpectation measure (fun sample => -chart sample)
        weight time =
      weightedMismatchExpectation measure chart weight (-time) := by
  simp [weightedMismatchExpectation]

/-- Endpoint-aware decay for the oppositely oriented (decreasing) chart.
To apply this to a decreasing spectral mismatch `phi`, supply increasing
chart data for `-phi`. -/
theorem norm_uniformMass_weightedMismatchExpectation_neg_chart_le_div_abs_time
    (data : IncreasingUniformMassC2ChartData)
    (weight weightDeriv : Real -> Complex)
    (hweight : forall mass : Real,
      HasDerivAt weight (weightDeriv mass) mass)
    (hweightDerivContinuous : Continuous weightDeriv)
    {time : Real} (htime : Ne time 0) :
    norm (weightedMismatchExpectation RandomEnsemble.massCoordinateLaw
      (fun mass => -data.chart mass) weight time) <=
      (compactIntervalCertificate data weight weightDeriv
        hweight hweightDerivContinuous).variationCost / |time| := by
  rw [weightedMismatchExpectation_neg_chart]
  simpa only [abs_neg] using
    norm_uniformMass_weightedMismatchExpectation_le_div_abs_time
      data weight weightDeriv hweight hweightDerivContinuous (neg_ne_zero.mpr htime)
end

end ArchonPhysics.CanonicalUniformMassMonotoneChartFourierCertificate
