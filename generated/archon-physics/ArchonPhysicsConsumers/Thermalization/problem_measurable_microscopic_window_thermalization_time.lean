import ArchonPhysics.MeasurableMicroscopicWindowThermalizationTime

/-!
# Consumer: measurable strict finite-window thermalization time

This target checks the measurable countable event, its continuous-time
semantics, and the order laws for its infimum-defined ensemble time.
-/

namespace ArchonPhysicsConsumers.Thermalization

open ArchonPhysics.ArbitrarilyLongMicroscopicKineticPersistence
open ArchonPhysics.MeasurableMicroscopicWindowThermalizationTime
open MeasureTheory

noncomputable section

variable {Omega : Type*} [MeasurableSpace Omega]

/-- Rational evaluation measurability suffices for an event, while pathwise
continuity upgrades that event to the literal real-time window. -/
theorem problem_strict_window_event_measurable_and_literal
    (distance : Omega -> Real -> Real)
    (start duration threshold : Real) (hduration : 0 < duration)
    (heval : forall q : Rat, Measurable fun omega => distance omega (q : Real))
    (hcontinuous : forall omega, Continuous (distance omega)) :
    MeasurableSet
        (rationalStrictWindowBadEvent distance start duration threshold) /\
      rationalStrictWindowBadEvent distance start duration threshold =
        realStrictWindowBadEvent distance start duration threshold := by
  exact ⟨
    measurableSet_rationalStrictWindowBadEvent
      distance start duration threshold heval,
    rationalStrictWindowBadEvent_eq_realStrictWindowBadEvent
      distance start duration threshold hduration hcontinuous⟩

/-- Distance tolerance and failure tolerance are antitone parameters; window
duration is a monotone parameter. -/
theorem problem_strict_window_time_parameter_monotonicity
    (mu : Measure Omega) [IsProbabilityMeasure mu]
    (distance : Omega -> Real -> Real)
    (thresholdSmall thresholdLarge durationSmall durationLarge
      failureToleranceSmall failureToleranceLarge : Real)
    (hthreshold : thresholdSmall <= thresholdLarge)
    (hduration : durationSmall <= durationLarge)
    (hfailure : failureToleranceSmall <= failureToleranceLarge) :
    rationalStrictWindowThermalizationTime mu distance thresholdLarge
        durationSmall failureToleranceSmall <=
      rationalStrictWindowThermalizationTime mu distance thresholdSmall
        durationSmall failureToleranceSmall /\
    rationalStrictWindowThermalizationTime mu distance thresholdSmall
        durationSmall failureToleranceSmall <=
      rationalStrictWindowThermalizationTime mu distance thresholdSmall
        durationLarge failureToleranceSmall /\
    rationalStrictWindowThermalizationTime mu distance thresholdSmall
        durationSmall failureToleranceLarge <=
      rationalStrictWindowThermalizationTime mu distance thresholdSmall
        durationSmall failureToleranceSmall := by
  exact ⟨
    rationalStrictWindowThermalizationTime_antitone_threshold
      mu distance thresholdSmall thresholdLarge durationSmall
        failureToleranceSmall hthreshold,
    rationalStrictWindowThermalizationTime_monotone_duration
      mu distance thresholdSmall durationSmall durationLarge
        failureToleranceSmall hduration,
    rationalStrictWindowThermalizationTime_antitone_failureTolerance
      mu distance thresholdSmall durationSmall failureToleranceSmall
        failureToleranceLarge hfailure⟩

/-- The measurable strict time is bounded above by the pre-existing time that
counts equality with the threshold as failure. -/
theorem problem_strict_window_time_le_closed_failure_time
    {E : Type*} [PseudoMetricSpace E]
    (mu : Measure Omega) [IsProbabilityMeasure mu]
    (micro : Nat -> Omega -> Real -> E) (equilibrium : E)
    (threshold duration failureTolerance : Real) (N : Nat) :
    rationalStrictWindowThermalizationTime mu
        (fun omega time => dist (micro N omega time) equilibrium)
        threshold duration failureTolerance <=
      microscopicWindowThermalizationTime mu micro equilibrium
        threshold duration failureTolerance N :=
  rationalStrictWindowThermalizationTime_le_microscopicWindowThermalizationTime
    mu micro equilibrium threshold duration failureTolerance N

#print axioms problem_strict_window_event_measurable_and_literal
#print axioms problem_strict_window_time_parameter_monotonicity
#print axioms problem_strict_window_time_le_closed_failure_time

end

end ArchonPhysicsConsumers.Thermalization
