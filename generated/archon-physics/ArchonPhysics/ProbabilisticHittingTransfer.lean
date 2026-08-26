import ArchonPhysics.HittingTimeStability
import ArchonPhysics.ThermalizationTransfer

/-!
# Probabilistic transfer of stable threshold hitting times

This module combines the deterministic robust-crossing layer with the
measure-theoretic convergence interface.  A random local-uniform error gauge
is assumed to converge in probability to zero and to control the actual path
error.  The hitting-time conclusion is then derived; neither that conclusion
nor `G2TeqConvergesInProbability` is an input.
-/

namespace ArchonPhysics.ProbabilisticHittingTransfer

open Filter MeasureTheory Set Topology
open ArchonPhysics.ThermalizationTransfer

noncomputable section

/-- The event that a random threshold hitting time lies in an `epsilon` window. -/
def hittingTimeWindowEvent {Omega : Type*}
    (approximation : Nat → Omega → Real → Real)
    (delta tauStar epsilon : Real) (n : Nat) : Set Omega :=
  (fun omega => distanceThresholdHittingTime (approximation n omega) delta) ⁻¹'
    Icc
      (Real.toNNReal (tauStar - epsilon) : ENNReal)
      (Real.toNNReal (tauStar + epsilon) : ENNReal)

/-- Hitting-time windows are measurable when the random hitting time is measurable. -/
theorem measurableSet_hittingTimeWindowEvent
    {Omega : Type*} [MeasurableSpace Omega]
    (approximation : Nat → Omega → Real → Real)
    (delta tauStar epsilon : Real) (n : Nat)
    (hittingTime_measurable : Measurable
      (fun omega => distanceThresholdHittingTime
        (approximation n omega) delta)) :
    MeasurableSet
      (hittingTimeWindowEvent approximation delta tauStar epsilon n) := by
  exact measurableSet_Icc.preimage hittingTime_measurable

/-- The event that an extended nonnegative error gauge is below a real tolerance. -/
def errorBelowEvent {Omega : Type*}
    (errorGauge : Nat → Omega → ENNReal) (eta : Real) (n : Nat) :
    Set Omega :=
  errorGauge n ⁻¹' Iio (ENNReal.ofReal eta)

/-- Convergence in probability to zero puts asymptotic probability one below
every strictly positive finite tolerance. -/
theorem ConvergesInProbabilityTo.tendsto_measure_errorBelowEvent
    {Omega : Type*} [MeasurableSpace Omega] {P : Measure Omega}
    [IsProbabilityMeasure P]
    {errorGauge : Nat → Omega → ENNReal}
    (herror : ConvergesInProbabilityTo P errorGauge 0)
    {eta : Real} (heta : 0 < eta) :
    Tendsto (fun n => P (errorBelowEvent errorGauge eta n))
      atTop (nhds 1) := by
  exact herror.2 (Iio (ENNReal.ofReal eta)) measurableSet_Iio
    (Iio_mem_nhds (ENNReal.ofReal_pos.mpr heta))

/-- A probability-one limit transfers from an event sequence to pointwise
supersets. -/
theorem tendsto_measure_superset_atTop_one
    {Omega : Type*} [MeasurableSpace Omega] (P : Measure Omega)
    [IsProbabilityMeasure P]
    (smaller larger : Nat → Set Omega)
    (hsmaller : Tendsto (fun n => P (smaller n)) atTop (nhds 1))
    (hsubset : ∀ n, smaller n ⊆ larger n) :
    Tendsto (fun n => P (larger n)) atTop (nhds 1) := by
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le
    hsmaller tendsto_const_nhds
    (fun n => measure_mono (hsubset n))
    (fun n => by
      calc
        P (larger n) ≤ P (Set.univ : Set Omega) :=
          measure_mono (subset_univ _)
        _ = 1 := measure_univ)

/--
A robust first crossing admits one positive local-uniform error radius that
forces the threshold hitting time into the requested `epsilon` window.

This is the single-approximation event bound used by the probabilistic layer.
Its lower and upper bounds reuse the deterministic threshold lemmas from
`HittingTimeStability`.
-/
theorem exists_uniform_error_radius_for_hitting_window
    {limit : Real → Real} {delta tauStar epsilon : Real}
    (hcross : RobustKineticFirstCrossing limit delta tauStar)
    (hepsilon_pos : 0 < epsilon) (hepsilon_lt : epsilon < tauStar) :
    ∃ eta : Real, 0 < eta ∧
      ∀ approximation : Real → Real,
        UniformlyCloseOnNonnegativeWindow approximation limit
            (tauStar + epsilon) eta →
          (Real.toNNReal (tauStar - epsilon) : ENNReal) ≤
              distanceThresholdHittingTime approximation delta ∧
            distanceThresholdHittingTime approximation delta ≤
              (Real.toNNReal (tauStar + epsilon) : ENNReal) := by
  obtain ⟨beforeMargin, hbeforeMargin_pos, hbefore⟩ :=
    hcross.beforeMargin epsilon hepsilon_pos hepsilon_lt
  obtain
      ⟨hitTime, afterMargin, hhit_after, hhit_before,
        hafterMargin_pos, hlimit_hit⟩ :=
    hcross.afterMargin epsilon hepsilon_pos
  have hleft_pos : 0 < tauStar - epsilon := sub_pos.mpr hepsilon_lt
  have hright_pos : 0 < tauStar + epsilon := by
    linarith [hcross.tauStar_pos]
  have hleft_le_right : tauStar - epsilon ≤ tauStar + epsilon := by
    linarith [hepsilon_pos]
  refine ⟨min beforeMargin afterMargin,
    lt_min hbeforeMargin_pos hafterMargin_pos, ?_⟩
  intro approximation hclose
  have hno_hit_before :
      ∀ t, 0 < t → t ≤ tauStar - epsilon →
        delta < approximation t := by
    intro t ht_pos ht_le
    have hlimit_before := hbefore t ht_pos ht_le
    have hclose_min := hclose t (le_of_lt ht_pos)
      (ht_le.trans hleft_le_right)
    have hclose_before :
        |approximation t - limit t| < beforeMargin :=
      hclose_min.trans_le (min_le_left _ _)
    have hlower := neg_abs_le (approximation t - limit t)
    linarith
  have hhit_pos : 0 < hitTime :=
    lt_trans hcross.tauStar_pos hhit_after
  have hhit_le_right : hitTime ≤ tauStar + epsilon :=
    le_of_lt hhit_before
  have hclose_min :=
    hclose hitTime (le_of_lt hhit_pos) hhit_le_right
  have hclose_after :
      |approximation hitTime - limit hitTime| < afterMargin :=
    hclose_min.trans_le (min_le_right _ _)
  have hupper := le_abs_self (approximation hitTime - limit hitTime)
  have happrox_hit : approximation hitTime ≤ delta := by
    linarith
  constructor
  · exact
      coe_toNNReal_le_distanceThresholdHittingTime_of_no_hit_before
        (le_of_lt hleft_pos) hno_hit_before
  · calc
      distanceThresholdHittingTime approximation delta ≤
          (Real.toNNReal hitTime : ENNReal) :=
        distanceThresholdHittingTime_le_of_hit hhit_pos happrox_hit
      _ ≤ (Real.toNNReal (tauStar + epsilon) : ENNReal) :=
        ENNReal.coe_le_coe.mpr
          (Real.toNNReal_le_toNNReal hhit_le_right)

/--
Random local-uniform error convergence implies asymptotic probability one for
every positive hitting-time window around the robust kinetic crossing.

`localUniformError T n omega` is an upstream error certificate on `[0, T]`.
The `hcontrols` hypothesis connects that certificate to the actual path error;
`herror` states only convergence in probability of the certificate to zero.
-/
theorem random_local_uniform_error_implies_hitting_window
    {Omega : Type*} [MeasurableSpace Omega] (P : Measure Omega)
    [IsProbabilityMeasure P]
    {limit : Real → Real} (approximation : Nat → Omega → Real → Real)
    (localUniformError : Real → Nat → Omega → ENNReal)
    (delta tauStar : Real)
    (hcross : RobustKineticFirstCrossing limit delta tauStar)
    (herror : ∀ T, 0 < T →
      ConvergesInProbabilityTo P (localUniformError T) 0)
    (hcontrols : ∀ T eta, 0 < T → 0 < eta →
      ∀ n omega,
        localUniformError T n omega < ENNReal.ofReal eta →
          UniformlyCloseOnNonnegativeWindow
            (approximation n omega) limit T eta) :
    ∀ epsilon, 0 < epsilon → epsilon < tauStar →
      Tendsto
        (fun n => P (hittingTimeWindowEvent approximation
          delta tauStar epsilon n))
        atTop (nhds 1) := by
  intro epsilon hepsilon_pos hepsilon_lt
  obtain ⟨eta, heta_pos, hstable⟩ :=
    exists_uniform_error_radius_for_hitting_window
      hcross hepsilon_pos hepsilon_lt
  have hright_pos : 0 < tauStar + epsilon := by
    linarith [hcross.tauStar_pos]
  have hgood :
      Tendsto
        (fun n => P (errorBelowEvent
          (localUniformError (tauStar + epsilon)) eta n))
        atTop (nhds 1) :=
    ConvergesInProbabilityTo.tendsto_measure_errorBelowEvent
      (herror (tauStar + epsilon) hright_pos) heta_pos
  apply tendsto_measure_superset_atTop_one P
    (fun n => errorBelowEvent
      (localUniformError (tauStar + epsilon)) eta n)
    (hittingTimeWindowEvent approximation delta tauStar epsilon)
    hgood
  intro n omega homega
  exact hstable (approximation n omega)
    (hcontrols (tauStar + epsilon) eta hright_pos heta_pos n omega homega)

end

end ArchonPhysics.ProbabilisticHittingTransfer
