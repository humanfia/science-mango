import ArchonPhysics.ProbabilisticHittingTransfer
import ArchonPhysics.TwoTimeKineticHittingBounds

/-!
# Probabilistic transfer of two-time kinetic hitting bounds

This is the release-law counterpart of robust-crossing convergence.  A
random path converging locally uniformly in probability to a kinetic path
inherits any robust lower/upper hitting window.  No unique crossing time or
strict monotonicity is required.
-/

namespace ArchonPhysics.TwoTimeProbabilisticHittingTransfer

open ArchonPhysics
open ArchonPhysics.ProbabilisticHittingTransfer
open ArchonPhysics.ThermalizationTransfer
open ArchonPhysics.TwoTimeKineticHittingBounds
open Filter MeasureTheory Set Topology

noncomputable section

/-- The event that the first positive threshold hit lies between the supplied
kinetic lower and upper times. -/
def twoTimeHittingWindowEvent {Omega : Type*}
    (approximation : Nat -> Omega -> Real -> Real)
    (delta lower upper : Real) (n : Nat) : Set Omega :=
  (fun omega => distanceThresholdHittingTime
    (approximation n omega) delta) ⁻¹'
      Icc (Real.toNNReal lower : ENNReal)
        (Real.toNNReal upper : ENNReal)

theorem measurableSet_twoTimeHittingWindowEvent
    {Omega : Type*} [MeasurableSpace Omega]
    (approximation : Nat -> Omega -> Real -> Real)
    (delta lower upper : Real) (n : Nat)
    (hittingTime_measurable : Measurable
      (fun omega => distanceThresholdHittingTime
        (approximation n omega) delta)) :
    MeasurableSet
      (twoTimeHittingWindowEvent approximation delta lower upper n) := by
  exact measurableSet_Icc.preimage hittingTime_measurable

/-- Local-uniform path error converging to zero in probability transfers a
robust kinetic lower/upper window to a probability-one asymptotic hitting
window. -/
theorem random_local_uniform_error_implies_twoTime_hitting_window
    {Omega : Type*} [MeasurableSpace Omega]
    (probability : Measure Omega) [IsProbabilityMeasure probability]
    {limit : Real -> Real}
    (approximation : Nat -> Omega -> Real -> Real)
    (localUniformError : Nat -> Omega -> ENNReal)
    (delta lower upper : Real)
    (window : RobustKineticHittingWindow limit delta lower upper)
    (herror : ConvergesInProbabilityTo probability localUniformError 0)
    (hcontrols : forall eta : Real, 0 < eta -> forall n omega,
      localUniformError n omega < ENNReal.ofReal eta ->
        UniformlyCloseOnNonnegativeWindow
          (approximation n omega) limit upper eta) :
    Tendsto
      (fun n => probability
        (twoTimeHittingWindowEvent approximation delta lower upper n))
      atTop (nhds 1) := by
  obtain ⟨eta, heta, hstable⟩ := window.exists_uniform_error_radius
  have hgood : Tendsto
      (fun n => probability (errorBelowEvent localUniformError eta n))
      atTop (nhds 1) :=
    ConvergesInProbabilityTo.tendsto_measure_errorBelowEvent herror heta
  apply tendsto_measure_superset_atTop_one probability
    (fun n => errorBelowEvent localUniformError eta n)
    (twoTimeHittingWindowEvent approximation delta lower upper) hgood
  intro n omega homega
  exact hstable (approximation n omega)
    (hcontrols eta heta n omega homega)

/-- Continuity at zero and eventual kinetic relaxation are already enough
to produce some positive finite high-probability hitting window. -/
theorem exists_twoTime_hitting_window_of_relaxation
    {Omega : Type*} [MeasurableSpace Omega]
    (probability : Measure Omega) [IsProbabilityMeasure probability]
    {limit : Real -> Real} {delta : Real}
    (relaxation : RelaxationToTwoTimeWindow limit delta)
    (approximation : Nat -> Omega -> Real -> Real)
    (localUniformError : Real -> Nat -> Omega -> ENNReal)
    (herror : forall T, 0 < T ->
      ConvergesInProbabilityTo probability (localUniformError T) 0)
    (hcontrols : forall T eta : Real, 0 < T -> 0 < eta ->
      forall n omega,
        localUniformError T n omega < ENNReal.ofReal eta ->
          UniformlyCloseOnNonnegativeWindow
            (approximation n omega) limit T eta) :
    exists lower upper : Real,
      0 < lower /\ lower <= upper /\
      Tendsto
        (fun n => probability
          (twoTimeHittingWindowEvent approximation delta lower upper n))
        atTop (nhds 1) := by
  obtain ⟨lower, upper, window⟩ :=
    relaxation.exists_robustKineticHittingWindow
  refine ⟨lower, upper, window.lower_pos, window.lower_le_upper, ?_⟩
  exact random_local_uniform_error_implies_twoTime_hitting_window
    probability approximation (localUniformError upper)
    delta lower upper window
    (herror upper (window.lower_pos.trans_le window.lower_le_upper))
    (fun eta heta n omega homega =>
      hcontrols upper eta
        (window.lower_pos.trans_le window.lower_le_upper) heta
        n omega homega)

end

end ArchonPhysics.TwoTimeProbabilisticHittingTransfer
