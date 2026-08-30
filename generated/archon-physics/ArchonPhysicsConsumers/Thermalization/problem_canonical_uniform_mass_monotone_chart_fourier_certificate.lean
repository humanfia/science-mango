import ArchonPhysics.CanonicalUniformMassMonotoneChartFourierCertificate

/-!
# Consumer: a concrete smooth canonical mass chart

The chart `mass ↦ 2 * mass - 1`, inverse `mismatch ↦ (mismatch + 1) / 2`,
and constant complex weight one instantiate every field of the general
uniform-mass monotone-chart certificate.  This is a compile-time witness that
the interface is substantive; it is still not an eigenfrequency chart.
-/

namespace ArchonPhysicsConsumers.Thermalization.CanonicalUniformMassMonotoneChartFourierCertificate

open ArchonPhysics
open ArchonPhysics.CanonicalIIDCoerciveIteratedA2ExpectationFourierDecay
open ArchonPhysics.CanonicalUniformMassMonotoneChartFourierCertificate
open ArchonPhysics.WeightedMismatchCompactIntervalFourierDecay
open MeasureTheory Set

noncomputable section

/-- A fully explicit increasing affine chart datum used to exercise the
nonlinear-chart API. -/
def doubleMinusOneChartData : IncreasingUniformMassC2ChartData where
  chart := fun mass => 2 * mass - 1
  chartDeriv := fun _mass => 2
  chartSecondDeriv := fun _mass => 0
  inverse := fun mismatch => (mismatch + 1) / 2
  jacobianLower := 2
  jacobianLower_pos := by norm_num
  chart_hasDeriv := by
    intro mass
    simpa using ((hasDerivAt_id mass).const_mul 2).sub_const 1
  chartDeriv_hasDeriv := by
    intro mass
    simpa using (hasDerivAt_const mass (2 : Real))
  chartSecondDeriv_continuous := by fun_prop
  jacobianLower_le := by
    intro mass hmass
    exact le_rfl
  inverse_mapsTo_massSupport := by
    intro mismatch hmismatch
    change
      2 * RandomEnsemble.massLower - 1 ≤ mismatch ∧
        mismatch ≤ 2 * RandomEnsemble.massUpper - 1 at hmismatch
    rw [RandomEnsemble.massSupport]
    change
      RandomEnsemble.massLower ≤ (mismatch + 1) / 2 ∧
        (mismatch + 1) / 2 ≤ RandomEnsemble.massUpper
    norm_num [RandomEnsemble.massLower, RandomEnsemble.massUpper] at hmismatch ⊢
    constructor <;> linarith [hmismatch.1, hmismatch.2]
  inverse_chart := by
    intro mass hmass
    ring
  inverse_hasDeriv := by
    intro mismatch hmismatch
    simpa using ((hasDerivAt_id mismatch).add_const 1).div_const 2

/-- A constant complex `C¹` mass weight for the concrete smoke test. -/
def affineComplexWeight (_mass : Real) : Complex :=
  1

def affineComplexWeightDeriv (_mass : Real) : Complex :=
  0

theorem affineComplexWeight_hasDeriv (mass : Real) :
    HasDerivAt affineComplexWeight (affineComplexWeightDeriv mass) mass := by
  change HasDerivAt (fun _ : Real => (1 : Complex)) 0 mass
  apply hasDerivAt_const

theorem affineComplexWeightDeriv_continuous :
    Continuous affineComplexWeightDeriv := by
  unfold affineComplexWeightDeriv
  fun_prop

/-- The explicit example has the expected image endpoints `3/5` and `7/5`. -/
example :
    doubleMinusOneChartData.chart RandomEnsemble.massLower = (3 / 5 : Real) ∧
      doubleMinusOneChartData.chart RandomEnsemble.massUpper = (7 / 5 : Real) := by
  norm_num [doubleMinusOneChartData, RandomEnsemble.massLower,
    RandomEnsemble.massUpper]

/-- The pushed density has the verified quotient/inverse derivative formula. -/
example {mismatch : Real}
    (hmismatch : mismatch ∈
      Icc (doubleMinusOneChartData.chart RandomEnsemble.massLower)
        (doubleMinusOneChartData.chart RandomEnsemble.massUpper)) :
    HasDerivAt
      (pushedDensity doubleMinusOneChartData affineComplexWeight)
      (pushedDensityDeriv doubleMinusOneChartData affineComplexWeight
        affineComplexWeightDeriv mismatch) mismatch :=
  pushedDensity_hasDeriv doubleMinusOneChartData affineComplexWeight
    affineComplexWeightDeriv affineComplexWeight_hasDeriv hmismatch

/-- Exact uniform-law change of variables for the concrete chart and weight. -/
example (time : Real) :
    weightedMismatchExpectation RandomEnsemble.massCoordinateLaw
        doubleMinusOneChartData.chart affineComplexWeight time =
      weightedMismatchIntervalOscillatoryIntegral
        (pushedDensity doubleMinusOneChartData affineComplexWeight)
        (doubleMinusOneChartData.chart RandomEnsemble.massLower)
        (doubleMinusOneChartData.chart RandomEnsemble.massUpper) time :=
  uniformMass_weightedMismatchExpectation_eq_interval
    doubleMinusOneChartData affineComplexWeight affineComplexWeightDeriv
    affineComplexWeight_hasDeriv time

/-- The actual compact-interval Fourier certificate produced by the general
constructor. -/
def doubleMinusOneCompactCertificate :
    WeightedMismatchCompactIntervalFourierCertificate
      RandomEnsemble.massCoordinateLaw doubleMinusOneChartData.chart
        affineComplexWeight :=
  compactIntervalCertificate doubleMinusOneChartData affineComplexWeight
    affineComplexWeightDeriv affineComplexWeight_hasDeriv
    affineComplexWeightDeriv_continuous

example {time : Real} (htime : time ≠ 0) :
    ‖weightedMismatchExpectation RandomEnsemble.massCoordinateLaw
      doubleMinusOneChartData.chart affineComplexWeight time‖ ≤
      doubleMinusOneCompactCertificate.variationCost / |time| :=
  doubleMinusOneCompactCertificate.norm_expectation_le_div_abs_time htime


/-- The same certificate controls the decreasing chart after sign
reorientation. -/
example {time : Real} (htime : Ne time 0) :
    norm (weightedMismatchExpectation RandomEnsemble.massCoordinateLaw
      (fun mass => -doubleMinusOneChartData.chart mass)
        affineComplexWeight time) <=
      doubleMinusOneCompactCertificate.variationCost / |time| :=
  norm_uniformMass_weightedMismatchExpectation_neg_chart_le_div_abs_time
    doubleMinusOneChartData affineComplexWeight affineComplexWeightDeriv
      affineComplexWeight_hasDeriv affineComplexWeightDeriv_continuous htime

#print axioms pushedDensity_hasDeriv
#print axioms uniformMass_weightedMismatchExpectation_eq_interval
#print axioms compactIntervalCertificate
#print axioms norm_uniformMass_weightedMismatchExpectation_le_div_abs_time
#print axioms norm_uniformMass_weightedMismatchExpectation_neg_chart_le_div_abs_time

end

end ArchonPhysicsConsumers.Thermalization.CanonicalUniformMassMonotoneChartFourierCertificate
