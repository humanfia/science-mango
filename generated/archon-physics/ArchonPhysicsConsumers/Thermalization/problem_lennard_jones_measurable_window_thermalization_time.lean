import ArchonPhysics.LennardJonesMeasurableWindowThermalizationTime

/-!
# Consumer: measurable strict-window Tc for Lennard--Jones chains

This target locks the measurable event semantics, parameter order laws,
one-sided threshold-boundary comparison, and transparent conditional
`32 / 49` scaling bridge.
-/

namespace ArchonPhysicsConsumers.Thermalization

open Filter MeasureTheory
open ArchonPhysics
open ArchonPhysics.LennardJonesMeasurableWindowThermalizationTime
open ArchonPhysics.LennardJonesStrictWindowThermalizationTime
open ArchonPhysics.LennardJonesThermodynamicHittingTransfer
open ArchonPhysics.MeasurableMicroscopicWindowThermalizationTime
open ArchonPhysics.ThermalizationTransfer

noncomputable section

variable {Omega E : Type*} [MeasurableSpace Omega] [PseudoMetricSpace E]

/-- The LJ kinetic-scaled wrapper uses exactly `Lkin / gLJ(e)^2`. -/
theorem problem_lennardJones_measurableWindow_uses_kinetic_scaled_duration
    (P : Measure Omega)
    (micro : Nat -> Real -> Omega -> Real -> E) (equilibrium : E)
    (threshold kineticDuration failureTolerance depth r0 : Real)
    (N : Nat) (energyDensity : Real) :
    lennardJonesMeasurableKineticScaledWindowThermalizationTime P micro
        equilibrium threshold kineticDuration failureTolerance depth r0 N
        energyDensity =
      rationalStrictWindowThermalizationTime P
        (distanceAtCoupling micro equilibrium N
          (kineticCouplingMagnitude depth r0 energyDensity))
        threshold
        (kineticDuration /
          kineticCouplingMagnitude depth r0 energyDensity ^ 2)
        failureTolerance := rfl

/-- Rational evaluation measurability gives a measurable event, and positive
duration plus pathwise continuity gives literal real-time candidate semantics. -/
theorem problem_lennardJones_measurableWindow_event_and_literal_candidate
    (P : Measure Omega)
    (micro : Nat -> Real -> Omega -> Real -> E) (equilibrium : E)
    (startReal duration threshold failureTolerance depth r0 energyDensity : Real)
    (N : Nat) (start : ENNReal) (hduration : 0 < duration)
    (heval : forall q : Rat, Measurable fun omega =>
      distanceAtCoupling micro equilibrium N
        (kineticCouplingMagnitude depth r0 energyDensity) omega (q : Real))
    (hcontinuous : forall omega, Continuous
      (distanceAtCoupling micro equilibrium N
        (kineticCouplingMagnitude depth r0 energyDensity) omega)) :
    MeasurableSet (rationalStrictWindowBadEventAtCoupling micro equilibrium
        startReal duration threshold N
        (kineticCouplingMagnitude depth r0 energyDensity)) /\
      (start ∈ measurableWindowThermalizationCandidatesAtCoupling P micro
          equilibrium threshold duration failureTolerance N
          (kineticCouplingMagnitude depth r0 energyDensity) <->
        0 < start /\ start < (⊤ : ENNReal) /\
          P.real (realStrictWindowBadEvent
            (distanceAtCoupling micro equilibrium N
              (kineticCouplingMagnitude depth r0 energyDensity))
            start.toReal duration threshold) <= failureTolerance) := by
  exact ⟨
    measurableSet_rationalStrictWindowBadEventAtCoupling micro equilibrium
      startReal duration threshold N
      (kineticCouplingMagnitude depth r0 energyDensity) heval,
    mem_measurableWindowThermalizationCandidatesAtCoupling_iff_real P micro
      equilibrium threshold duration failureTolerance N
      (kineticCouplingMagnitude depth r0 energyDensity)
      hduration hcontinuous start⟩

/-- The three requested order laws for the energy-dependent measurable Tc. -/
theorem problem_lennardJones_measurableWindow_parameter_order
    (P : Measure Omega) [IsProbabilityMeasure P]
    (micro : Nat -> Real -> Omega -> Real -> E) (equilibrium : E)
    (thresholdSmall thresholdLarge durationSmall durationLarge
      failureToleranceSmall failureToleranceLarge depth r0 energyDensity : Real)
    (N : Nat) (hthreshold : thresholdSmall <= thresholdLarge)
    (hduration : durationSmall <= durationLarge)
    (hfailure : failureToleranceSmall <= failureToleranceLarge) :
    lennardJonesMeasurableWindowThermalizationTime P micro equilibrium
        thresholdLarge durationSmall failureToleranceSmall depth r0 N
        energyDensity <=
      lennardJonesMeasurableWindowThermalizationTime P micro equilibrium
        thresholdSmall durationSmall failureToleranceSmall depth r0 N
        energyDensity /\
    lennardJonesMeasurableWindowThermalizationTime P micro equilibrium
        thresholdSmall durationSmall failureToleranceSmall depth r0 N
        energyDensity <=
      lennardJonesMeasurableWindowThermalizationTime P micro equilibrium
        thresholdSmall durationLarge failureToleranceSmall depth r0 N
        energyDensity /\
    lennardJonesMeasurableWindowThermalizationTime P micro equilibrium
        thresholdSmall durationSmall failureToleranceLarge depth r0 N
        energyDensity <=
      lennardJonesMeasurableWindowThermalizationTime P micro equilibrium
        thresholdSmall durationSmall failureToleranceSmall depth r0 N
        energyDensity := by
  exact ⟨
    lennardJonesMeasurableWindowThermalizationTime_antitone_threshold P micro
      equilibrium thresholdSmall thresholdLarge durationSmall
      failureToleranceSmall depth r0 N energyDensity hthreshold,
    lennardJonesMeasurableWindowThermalizationTime_monotone_duration P micro
      equilibrium thresholdSmall durationSmall durationLarge
      failureToleranceSmall depth r0 N energyDensity hduration,
    lennardJonesMeasurableWindowThermalizationTime_antitone_failureTolerance
      P micro equilibrium thresholdSmall durationSmall failureToleranceSmall
      failureToleranceLarge depth r0 N energyDensity hfailure⟩

/-- Strict measurable failure is no stronger than the old closed-failure
convention; no equality is asserted at the threshold boundary. -/
theorem problem_lennardJones_measurableWindow_le_closedFailureTime
    (P : Measure Omega) [IsProbabilityMeasure P]
    (micro : Nat -> Real -> Omega -> Real -> E) (equilibrium : E)
    (threshold kineticDuration failureTolerance depth r0 : Real)
    (N : Nat) (energyDensity : Real) :
    lennardJonesMeasurableKineticScaledWindowThermalizationTime P micro
        equilibrium threshold kineticDuration failureTolerance depth r0 N
        energyDensity <=
      lennardJonesKineticScaledWindowThermalizationTime P micro equilibrium
        threshold kineticDuration failureTolerance depth r0 N energyDensity :=
  lennardJonesMeasurableKineticScaledWindowThermalizationTime_le_closedFailureTime
    P micro equilibrium threshold kineticDuration failureTolerance depth r0 N
    energyDensity

/-- The adapter is constant in its dummy sample and is automatically
measurable; the nontrivial certificate fields remain external obligations. -/
theorem problem_lennardJones_measurableWindow_adapter_is_dummy_measurable
    (P : Measure Omega)
    (micro : Nat -> Real -> Omega -> Real -> E) (equilibrium : E)
    (threshold kineticDuration failureTolerance : Real)
    (N : Nat) (g : Real) (omega1 omega2 : Omega) :
    measurableKineticScaledWindowCertificateAdapter P micro equilibrium
        threshold kineticDuration failureTolerance N g omega1 =
      measurableKineticScaledWindowCertificateAdapter P micro equilibrium
        threshold kineticDuration failureTolerance N g omega2 /\
    Measurable (measurableKineticScaledWindowCertificateAdapter P micro
      equilibrium threshold kineticDuration failureTolerance N g) := by
  exact ⟨rfl,
    measurable_measurableKineticScaledWindowCertificateAdapter P micro
      equilibrium threshold kineticDuration failureTolerance N g⟩

/-- The `32 / 49` law follows only from the explicit transparent certificate. -/
theorem problem_lennardJones_measurableWindow_energyDensityTime_law
    (P : Measure Omega) [IsProbabilityMeasure P]
    (micro : Nat -> Real -> Omega -> Real -> E) (equilibrium : E)
    (threshold kineticDuration failureTolerance : Real)
    (sizeCutoff : Real -> Nat) (kineticDistance : Real -> Real)
    (delta tauStar depth r0 : Real)
    (certificate : LennardJonesMeasurableKineticScaledWindowScalingCertificate
      P micro equilibrium threshold kineticDuration failureTolerance
      sizeCutoff kineticDistance delta tauStar depth r0)
    (s : AdmissibleLennardJonesJointLimit sizeCutoff depth r0) :
    ConvergesInProbabilityTo P
      (fun j _omega =>
        ENNReal.ofReal (s.energyDensity j / depth) *
          lennardJonesMeasurableKineticScaledWindowThermalizationTime P micro
            equilibrium threshold kineticDuration failureTolerance depth r0
            (s.systemSize j) (s.energyDensity j))
      (ENNReal.ofReal ((32 / 49 : Real) * tauStar)) :=
  lennardJonesMeasurableKineticScaledWindow_energyDensityTime_law P micro
    equilibrium threshold kineticDuration failureTolerance sizeCutoff
    kineticDistance delta tauStar depth r0 certificate s

#print axioms problem_lennardJones_measurableWindow_event_and_literal_candidate
#print axioms problem_lennardJones_measurableWindow_parameter_order
#print axioms problem_lennardJones_measurableWindow_le_closedFailureTime
#print axioms problem_lennardJones_measurableWindow_adapter_is_dummy_measurable
#print axioms problem_lennardJones_measurableWindow_energyDensityTime_law

end

end ArchonPhysicsConsumers.Thermalization
