import ArchonPhysics.WeakCouplingLogarithmicKineticScale

/-!
# Finite compact-chart atlases for weighted mismatch decay

A nonlinear spectral mismatch need not be globally monotone in one mass
coordinate.  The natural replacement is a finite atlas of monotone patches.
This module isolates the exact analytic assembly step: if a weighted
expectation is the sum of finitely many compact-interval oscillatory charts,
then the chartwise endpoint and derivative costs add, the expectation has
`1 / |time|` decay, and its kinetically weighted accumulation vanishes on
the time scale `time = g^-2`.

The existence and uniform quality of such an atlas for the actual nonlinear
random-mass eigenfrequency mismatch remain explicit model-specific inputs.
No growing chart family, recollision estimate, or full nested-A2 closure is
claimed here.
-/

namespace ArchonPhysics.WeightedMismatchFiniteChartKineticClosure

open ArchonPhysics
open ArchonPhysics.CanonicalIIDCoerciveIteratedA2ExpectationFourierDecay
open ArchonPhysics.PhyslibFPUTIteratedQuadraticSecondPicardCharacterFamily
open ArchonPhysics.WeakCouplingLogarithmicKineticScale
open ArchonPhysics.WeightedMismatchCompactIntervalFourierDecay
open Filter MeasureTheory Set
open scoped Topology

noncomputable section

/-! ## One compact chart without an ambient expectation -/

/-- Density data for one compact mismatch chart. -/
structure CompactMismatchFourierChart where
  lower : Real
  upper : Real
  lower_le_upper : lower <= upper
  density : Real -> Complex
  densityDeriv : Real -> Complex
  density_hasDeriv : ∀ value ∈ Set.uIcc lower upper,
    HasDerivAt density (densityDeriv value) value
  densityDeriv_intervalIntegrable :
    IntervalIntegrable densityDeriv volume lower upper

/-- Oscillatory contribution of one chart. -/
def CompactMismatchFourierChart.oscillation
    (chart : CompactMismatchFourierChart) (time : Real) : Complex :=
  weightedMismatchIntervalOscillatoryIntegral chart.density
    chart.lower chart.upper time

/-- Interval `L1` size of one chart density. -/
def CompactMismatchFourierChart.densityL1Cost
    (chart : CompactMismatchFourierChart) : Real :=
  ∫ value in chart.lower..chart.upper, ‖chart.density value‖

/-- Endpoint-aware variation cost of one chart. -/
def CompactMismatchFourierChart.variationCost
    (chart : CompactMismatchFourierChart) : Real :=
  intervalFourierVariationCost chart.density chart.densityDeriv
    chart.lower chart.upper

theorem CompactMismatchFourierChart.density_continuousOn
    (chart : CompactMismatchFourierChart) :
    ContinuousOn chart.density (Set.uIcc chart.lower chart.upper) := by
  intro value hvalue
  exact (chart.density_hasDeriv value hvalue).continuousAt.continuousWithinAt

theorem CompactMismatchFourierChart.density_intervalIntegrable
    (chart : CompactMismatchFourierChart) :
    IntervalIntegrable chart.density volume chart.lower chart.upper :=
  chart.density_continuousOn.intervalIntegrable

theorem CompactMismatchFourierChart.densityL1Cost_nonneg
    (chart : CompactMismatchFourierChart) :
    0 <= chart.densityL1Cost := by
  exact intervalIntegral.integral_nonneg_of_forall chart.lower_le_upper
    (fun value => norm_nonneg (chart.density value))

theorem CompactMismatchFourierChart.variationCost_nonneg
    (chart : CompactMismatchFourierChart) :
    0 <= chart.variationCost := by
  exact intervalFourierVariationCost_nonneg chart.density chart.densityDeriv
    chart.lower_le_upper

/-- Uniform nonoscillatory ceiling for one chart. -/
theorem CompactMismatchFourierChart.norm_oscillation_le_densityL1Cost
    (chart : CompactMismatchFourierChart) (time : Real) :
    ‖chart.oscillation time‖ <= chart.densityL1Cost := by
  unfold CompactMismatchFourierChart.oscillation
    CompactMismatchFourierChart.densityL1Cost
    weightedMismatchIntervalOscillatoryIntegral
  calc
    _ <= ∫ value in chart.lower..chart.upper,
        ‖Complex.exp
            (Complex.I * ((time * value : Real) : Complex)) *
          chart.density value‖ :=
      intervalIntegral.norm_integral_le_integral_norm chart.lower_le_upper
    _ = ∫ value in chart.lower..chart.upper, ‖chart.density value‖ := by
      apply intervalIntegral.integral_congr
      intro value _hvalue
      change
        ‖Complex.exp
            (Complex.I * ((time * value : Real) : Complex)) *
          chart.density value‖ = ‖chart.density value‖
      rw [norm_mul, Complex.norm_exp_I_mul_ofReal, one_mul]

/-- Endpoint-aware `1 / |time|` decay for one chart. -/
theorem CompactMismatchFourierChart.norm_oscillation_le_variation_div_abs_time
    (chart : CompactMismatchFourierChart) {time : Real}
    (htime : time ≠ 0) :
    ‖chart.oscillation time‖ <= chart.variationCost / |time| := by
  exact
    norm_weightedMismatchIntervalOscillatoryIntegral_le_variation_div_abs_time
      chart.density chart.densityDeriv chart.lower_le_upper htime
      chart.density_hasDeriv chart.densityDeriv_intervalIntegrable

/-- The time signal of one compact chart is continuous. -/
theorem CompactMismatchFourierChart.continuous_oscillation
    (chart : CompactMismatchFourierChart) :
    Continuous chart.oscillation := by
  exact continuous_weightedMismatchIntervalOscillatoryIntegral
    chart.density chart.density_continuousOn

/-! ## Finite chart atlas -/

/-- A weighted mismatch expectation represented by finitely many compact
charts.  Overlaps, conditional weights, and partition-of-unity factors are
already included in the chart densities. -/
structure WeightedMismatchFiniteChartFourierCertificate
    {Omega : Type*} [MeasurableSpace Omega]
    (measure : Measure Omega) (mismatch : Omega -> Real)
    (weight : Omega -> Complex) (ChartIndex : Type*)
    [Fintype ChartIndex] where
  chart : ChartIndex -> CompactMismatchFourierChart
  expectation_eq : forall time,
    weightedMismatchExpectation measure mismatch weight time =
      ∑ index : ChartIndex, (chart index).oscillation time

/-- Sum of the chartwise interval-density costs. -/
def WeightedMismatchFiniteChartFourierCertificate.densityL1Cost
    {Omega : Type*} [MeasurableSpace Omega]
    {measure : Measure Omega} {mismatch : Omega -> Real}
    {weight : Omega -> Complex} {ChartIndex : Type*} [Fintype ChartIndex]
    (certificate : WeightedMismatchFiniteChartFourierCertificate
      measure mismatch weight ChartIndex) : Real :=
  ∑ index : ChartIndex, (certificate.chart index).densityL1Cost

/-- Sum of all endpoint-aware chart variation costs. -/
def WeightedMismatchFiniteChartFourierCertificate.variationCost
    {Omega : Type*} [MeasurableSpace Omega]
    {measure : Measure Omega} {mismatch : Omega -> Real}
    {weight : Omega -> Complex} {ChartIndex : Type*} [Fintype ChartIndex]
    (certificate : WeightedMismatchFiniteChartFourierCertificate
      measure mismatch weight ChartIndex) : Real :=
  ∑ index : ChartIndex, (certificate.chart index).variationCost

theorem WeightedMismatchFiniteChartFourierCertificate.densityL1Cost_nonneg
    {Omega : Type*} [MeasurableSpace Omega]
    {measure : Measure Omega} {mismatch : Omega -> Real}
    {weight : Omega -> Complex} {ChartIndex : Type*} [Fintype ChartIndex]
    (certificate : WeightedMismatchFiniteChartFourierCertificate
      measure mismatch weight ChartIndex) :
    0 <= certificate.densityL1Cost := by
  classical
  exact Finset.sum_nonneg fun index _ =>
    (certificate.chart index).densityL1Cost_nonneg

theorem WeightedMismatchFiniteChartFourierCertificate.variationCost_nonneg
    {Omega : Type*} [MeasurableSpace Omega]
    {measure : Measure Omega} {mismatch : Omega -> Real}
    {weight : Omega -> Complex} {ChartIndex : Type*} [Fintype ChartIndex]
    (certificate : WeightedMismatchFiniteChartFourierCertificate
      measure mismatch weight ChartIndex) :
    0 <= certificate.variationCost := by
  classical
  exact Finset.sum_nonneg fun index _ =>
    (certificate.chart index).variationCost_nonneg

/-- A finite atlas supplies a uniform density-`L1` ceiling. -/
theorem WeightedMismatchFiniteChartFourierCertificate.norm_expectation_le_densityL1
    {Omega : Type*} [MeasurableSpace Omega]
    {measure : Measure Omega} {mismatch : Omega -> Real}
    {weight : Omega -> Complex} {ChartIndex : Type*} [Fintype ChartIndex]
    (certificate : WeightedMismatchFiniteChartFourierCertificate
      measure mismatch weight ChartIndex) (time : Real) :
    ‖weightedMismatchExpectation measure mismatch weight time‖ <=
      certificate.densityL1Cost := by
  classical
  rw [certificate.expectation_eq]
  calc
    ‖∑ index : ChartIndex, (certificate.chart index).oscillation time‖ <=
        ∑ index : ChartIndex,
          ‖(certificate.chart index).oscillation time‖ :=
      norm_sum_le _ _
    _ <= ∑ index : ChartIndex,
        (certificate.chart index).densityL1Cost := by
      exact Finset.sum_le_sum fun index _ =>
        (certificate.chart index).norm_oscillation_le_densityL1Cost time
    _ = certificate.densityL1Cost := rfl

/-- A finite atlas supplies the summed `1 / |time|` bound. -/
theorem WeightedMismatchFiniteChartFourierCertificate.norm_expectation_le_variation_div_abs_time
    {Omega : Type*} [MeasurableSpace Omega]
    {measure : Measure Omega} {mismatch : Omega -> Real}
    {weight : Omega -> Complex} {ChartIndex : Type*} [Fintype ChartIndex]
    (certificate : WeightedMismatchFiniteChartFourierCertificate
      measure mismatch weight ChartIndex) {time : Real} (htime : time ≠ 0) :
    ‖weightedMismatchExpectation measure mismatch weight time‖ <=
      certificate.variationCost / |time| := by
  classical
  rw [certificate.expectation_eq]
  calc
    ‖∑ index : ChartIndex, (certificate.chart index).oscillation time‖ <=
        ∑ index : ChartIndex,
          ‖(certificate.chart index).oscillation time‖ :=
      norm_sum_le _ _
    _ <= ∑ index : ChartIndex,
        (certificate.chart index).variationCost / |time| := by
      exact Finset.sum_le_sum fun index _ =>
        (certificate.chart index).norm_oscillation_le_variation_div_abs_time
          htime
    _ = certificate.variationCost / |time| := by
      unfold WeightedMismatchFiniteChartFourierCertificate.variationCost
      rw [Finset.sum_div]

/-- The expectation represented by a fixed finite atlas is continuous. -/
theorem WeightedMismatchFiniteChartFourierCertificate.continuous_expectation
    {Omega : Type*} [MeasurableSpace Omega]
    {measure : Measure Omega} {mismatch : Omega -> Real}
    {weight : Omega -> Complex} {ChartIndex : Type*} [Fintype ChartIndex]
    (certificate : WeightedMismatchFiniteChartFourierCertificate
      measure mismatch weight ChartIndex) :
    Continuous (weightedMismatchExpectation measure mismatch weight) := by
  classical
  have heq : weightedMismatchExpectation measure mismatch weight =
      fun time =>
        ∑ index : ChartIndex, (certificate.chart index).oscillation time := by
    funext time
    exact certificate.expectation_eq time
  rw [heq]
  exact continuous_finsetSum Finset.univ fun index _ =>
    (certificate.chart index).continuous_oscillation

/-- A fixed finite compact atlas makes its weighted expectation negligible
after kinetic weighting on the `g^-2` time scale. -/
theorem WeightedMismatchFiniteChartFourierCertificate.tendsto_kineticAccumulation
    {Omega : Type*} [MeasurableSpace Omega]
    {measure : Measure Omega} {mismatch : Omega -> Real}
    {weight : Omega -> Complex} {ChartIndex : Type*} [Fintype ChartIndex]
    (certificate : WeightedMismatchFiniteChartFourierCertificate
      measure mismatch weight ChartIndex) :
    Tendsto
      (weakCouplingKineticAccumulation
        (weightedMismatchExpectation measure mismatch weight))
      (𝓝[>] 0) (𝓝 0) := by
  exact tendsto_weakCouplingKineticAccumulation_nhdsGT_zero
    (weightedMismatchExpectation measure mismatch weight)
    certificate.densityL1Cost certificate.variationCost
    certificate.continuous_expectation
    certificate.norm_expectation_le_densityL1
    (fun time htime =>
      certificate.norm_expectation_le_variation_div_abs_time htime)

/-! ## Actual iterated-A2 adapter -/

/-- Finite-chart certificate for one actual iterated-A2 weighted channel. -/
abbrev ActualIteratedA2WeightedChannelFiniteChartCertificate
    {Omega : Type*} [MeasurableSpace Omega]
    (ensemble : IIDMassPhaseEnsemble Omega)
    {N : Nat} [NeZero N] (channel : IteratedA2MismatchChannel)
    (weight : Omega -> Complex) (observed : Lattice.Site N)
    (term : IteratedQuadraticSecondPicardCharacterTerm N)
    (ChartIndex : Type*) [Fintype ChartIndex] :=
  WeightedMismatchFiniteChartFourierCertificate ensemble.probability
    (actualIteratedA2MismatchSample ensemble channel observed term) weight
      ChartIndex

/-- Actual-channel kinetic-scale closure under an explicit fixed finite atlas
certificate. -/
theorem tendsto_actualIteratedA2WeightedChannel_finiteChart_kineticAccumulation
    {Omega : Type*} [MeasurableSpace Omega]
    (ensemble : IIDMassPhaseEnsemble Omega)
    {N : Nat} [NeZero N] (channel : IteratedA2MismatchChannel)
    (weight : Omega -> Complex) (observed : Lattice.Site N)
    (term : IteratedQuadraticSecondPicardCharacterTerm N)
    (ChartIndex : Type*) [Fintype ChartIndex]
    (certificate : ActualIteratedA2WeightedChannelFiniteChartCertificate
      ensemble channel weight observed term ChartIndex) :
    Tendsto
      (weakCouplingKineticAccumulation
        (actualIteratedA2WeightedChannelExpectation ensemble channel weight
          observed term))
      (𝓝[>] 0) (𝓝 0) :=
  certificate.tendsto_kineticAccumulation

end

end ArchonPhysics.WeightedMismatchFiniteChartKineticClosure
