import ArchonPhysics.LennardJonesStrictWindowThermalizationTime
import ArchonPhysics.MeasurableMicroscopicWindowThermalizationTime

/-!
# Measurable strict-window thermalization time for Lennard--Jones chains

This is a thin model-specific wrapper around the countable rational-window
construction in `MeasurableMicroscopicWindowThermalizationTime`.  At fixed
coupling, size, and rational time, measurability of the displayed distance is
enough to make the strict bad event measurable.  Positive duration and
pathwise continuity then identify it with the literal real-time strict event.

The final `32 / 49` law is deliberately conditional.  The time below is an
ensemble probability infimum, so its adapter to the existing thermodynamic
hitting API ignores a dummy sample argument.  The transparent certificate is
not constructed here: in particular, no microscopic--kinetic approximation
or identification with a kinetic first crossing is inferred from
measurability, the LJ Taylor coefficients, or the ensemble aggregation.
-/

namespace ArchonPhysics.LennardJonesMeasurableWindowThermalizationTime

open Filter MeasureTheory
open ArchonPhysics.LennardJonesStrictWindowThermalizationTime
open ArchonPhysics.LennardJonesThermodynamicHittingTransfer
open ArchonPhysics.MeasurableMicroscopicWindowThermalizationTime
open ArchonPhysics.ArbitrarilyLongMicroscopicKineticPersistence
open ArchonPhysics.ThermalizationTransfer

noncomputable section

variable {Omega E : Type*} [MeasurableSpace Omega] [PseudoMetricSpace E]

/-! ## Coupling, energy, and duration wrappers -/

/-- The equilibrium-distance diagnostic at fixed chain size and coupling. -/
def distanceAtCoupling
    (micro : Nat -> Real -> Omega -> Real -> E) (equilibrium : E)
    (N : Nat) (g : Real) (omega : Omega) (time : Real) : Real :=
  dist (micro N g omega time) equilibrium

/-- Strict rational bad event at one coupling and system size. -/
def rationalStrictWindowBadEventAtCoupling
    (micro : Nat -> Real -> Omega -> Real -> E) (equilibrium : E)
    (start duration threshold : Real) (N : Nat) (g : Real) : Set Omega :=
  rationalStrictWindowBadEvent (distanceAtCoupling micro equilibrium N g)
    start duration threshold

/-- Measurable strict-window candidates at one coupling. -/
def measurableWindowThermalizationCandidatesAtCoupling
    (P : Measure Omega)
    (micro : Nat -> Real -> Omega -> Real -> E) (equilibrium : E)
    (threshold duration failureTolerance : Real) (N : Nat) (g : Real) :
    Set ENNReal :=
  rationalStrictWindowThermalizationCandidates P
    (distanceAtCoupling micro equilibrium N g)
    threshold duration failureTolerance

/-- Measurable rational-strict ensemble Tc at one coupling. -/
def measurableWindowThermalizationTimeAtCoupling
    (P : Measure Omega)
    (micro : Nat -> Real -> Omega -> Real -> E) (equilibrium : E)
    (threshold duration failureTolerance : Real) (N : Nat) (g : Real) :
    ENNReal :=
  rationalStrictWindowThermalizationTime P
    (distanceAtCoupling micro equilibrium N g)
    threshold duration failureTolerance

/-- Energy-dependent LJ specialization via the exact positive cubic coupling
magnitude. -/
def lennardJonesMeasurableWindowThermalizationTime
    (P : Measure Omega)
    (micro : Nat -> Real -> Omega -> Real -> E) (equilibrium : E)
    (threshold duration failureTolerance depth r0 : Real)
    (N : Nat) (energyDensity : Real) : ENNReal :=
  measurableWindowThermalizationTimeAtCoupling P micro equilibrium
    threshold duration failureTolerance N
    (kineticCouplingMagnitude depth r0 energyDensity)

/-- Physical window length representing a fixed kinetic duration at coupling
`g`: `L_phys = L_kin / g^2`. -/
def kineticScaledPhysicalDuration (kineticDuration g : Real) : Real :=
  kineticDuration / g ^ 2

theorem kineticScaledPhysicalDuration_eq
    (kineticDuration g : Real) :
    kineticScaledPhysicalDuration kineticDuration g =
      physicalDurationFromKinetic kineticDuration g := rfl

/-- Coupling-level measurable Tc with a fixed kinetic-time window. -/
def measurableKineticScaledWindowThermalizationTimeAtCoupling
    (P : Measure Omega)
    (micro : Nat -> Real -> Omega -> Real -> E) (equilibrium : E)
    (threshold kineticDuration failureTolerance : Real)
    (N : Nat) (g : Real) : ENNReal :=
  measurableWindowThermalizationTimeAtCoupling P micro equilibrium
    threshold (kineticScaledPhysicalDuration kineticDuration g)
    failureTolerance N g

/-- LJ energy specialization of the measurable kinetic-scaled-window Tc. -/
def lennardJonesMeasurableKineticScaledWindowThermalizationTime
    (P : Measure Omega)
    (micro : Nat -> Real -> Omega -> Real -> E) (equilibrium : E)
    (threshold kineticDuration failureTolerance depth r0 : Real)
    (N : Nat) (energyDensity : Real) : ENNReal :=
  measurableKineticScaledWindowThermalizationTimeAtCoupling P micro equilibrium
    threshold kineticDuration failureTolerance N
    (kineticCouplingMagnitude depth r0 energyDensity)

/-! ## Measurable event and literal continuous-time semantics -/

/-- Fixed-rational-time measurability of the distance makes the complete
strict rational-window bad event measurable. -/
theorem measurableSet_rationalStrictWindowBadEventAtCoupling
    (micro : Nat -> Real -> Omega -> Real -> E) (equilibrium : E)
    (start duration threshold : Real) (N : Nat) (g : Real)
    (heval : forall q : Rat, Measurable fun omega =>
      distanceAtCoupling micro equilibrium N g omega (q : Real)) :
    MeasurableSet (rationalStrictWindowBadEventAtCoupling micro equilibrium
      start duration threshold N g) := by
  exact measurableSet_rationalStrictWindowBadEvent
    (distanceAtCoupling micro equilibrium N g)
    start duration threshold heval

/-- At positive duration and for continuous sample diagnostics, candidate
membership is exactly the literal all-real-times strict-window probability
condition. -/
theorem mem_measurableWindowThermalizationCandidatesAtCoupling_iff_real
    (P : Measure Omega)
    (micro : Nat -> Real -> Omega -> Real -> E) (equilibrium : E)
    (threshold duration failureTolerance : Real) (N : Nat) (g : Real)
    (hduration : 0 < duration)
    (hcontinuous : forall omega,
      Continuous (distanceAtCoupling micro equilibrium N g omega))
    (start : ENNReal) :
    start ∈ measurableWindowThermalizationCandidatesAtCoupling P micro
        equilibrium threshold duration failureTolerance N g <->
      0 < start /\ start < (⊤ : ENNReal) /\
        P.real (realStrictWindowBadEvent
          (distanceAtCoupling micro equilibrium N g)
          start.toReal duration threshold) <= failureTolerance := by
  exact mem_rationalStrictWindowThermalizationCandidates_iff_real
    P (distanceAtCoupling micro equilibrium N g)
    threshold duration failureTolerance hduration hcontinuous start

/-- A positive kinetic duration gives a positive physical duration whenever
the coupling is nonzero. -/
theorem kineticScaledPhysicalDuration_pos
    {kineticDuration g : Real} (hduration : 0 < kineticDuration)
    (hg : g ≠ 0) :
    0 < kineticScaledPhysicalDuration kineticDuration g := by
  exact div_pos hduration (sq_pos_of_ne_zero hg)

/-! ## Parameter order laws -/

theorem lennardJonesMeasurableWindowThermalizationTime_antitone_threshold
    (P : Measure Omega) [IsProbabilityMeasure P]
    (micro : Nat -> Real -> Omega -> Real -> E) (equilibrium : E)
    (thresholdSmall thresholdLarge duration failureTolerance depth r0 : Real)
    (N : Nat) (energyDensity : Real)
    (hthreshold : thresholdSmall <= thresholdLarge) :
    lennardJonesMeasurableWindowThermalizationTime P micro equilibrium
        thresholdLarge duration failureTolerance depth r0 N energyDensity <=
      lennardJonesMeasurableWindowThermalizationTime P micro equilibrium
        thresholdSmall duration failureTolerance depth r0 N energyDensity := by
  exact rationalStrictWindowThermalizationTime_antitone_threshold P
    (distanceAtCoupling micro equilibrium N
      (kineticCouplingMagnitude depth r0 energyDensity))
    thresholdSmall thresholdLarge duration failureTolerance hthreshold

theorem lennardJonesMeasurableWindowThermalizationTime_monotone_duration
    (P : Measure Omega) [IsProbabilityMeasure P]
    (micro : Nat -> Real -> Omega -> Real -> E) (equilibrium : E)
    (threshold durationSmall durationLarge failureTolerance depth r0 : Real)
    (N : Nat) (energyDensity : Real)
    (hduration : durationSmall <= durationLarge) :
    lennardJonesMeasurableWindowThermalizationTime P micro equilibrium
        threshold durationSmall failureTolerance depth r0 N energyDensity <=
      lennardJonesMeasurableWindowThermalizationTime P micro equilibrium
        threshold durationLarge failureTolerance depth r0 N energyDensity := by
  exact rationalStrictWindowThermalizationTime_monotone_duration P
    (distanceAtCoupling micro equilibrium N
      (kineticCouplingMagnitude depth r0 energyDensity))
    threshold durationSmall durationLarge failureTolerance hduration

theorem lennardJonesMeasurableWindowThermalizationTime_antitone_failureTolerance
    (P : Measure Omega)
    (micro : Nat -> Real -> Omega -> Real -> E) (equilibrium : E)
    (threshold duration failureToleranceSmall failureToleranceLarge depth r0 : Real)
    (N : Nat) (energyDensity : Real)
    (hfailure : failureToleranceSmall <= failureToleranceLarge) :
    lennardJonesMeasurableWindowThermalizationTime P micro equilibrium
        threshold duration failureToleranceLarge depth r0 N energyDensity <=
      lennardJonesMeasurableWindowThermalizationTime P micro equilibrium
        threshold duration failureToleranceSmall depth r0 N energyDensity := by
  exact rationalStrictWindowThermalizationTime_antitone_failureTolerance P
    (distanceAtCoupling micro equilibrium N
      (kineticCouplingMagnitude depth r0 energyDensity))
    threshold duration failureToleranceSmall failureToleranceLarge hfailure

/-- The kinetic-duration parameter is monotone on every genuine positive LJ
energy path. -/
theorem lennardJonesMeasurableKineticScaledWindowThermalizationTime_monotone_duration
    (P : Measure Omega) [IsProbabilityMeasure P]
    (micro : Nat -> Real -> Omega -> Real -> E) (equilibrium : E)
    (threshold durationSmall durationLarge failureTolerance depth r0 : Real)
    (N : Nat) (energyDensity : Real)
    (hdepth : 0 < depth) (hr0 : 0 < r0) (he : 0 < energyDensity)
    (hduration : durationSmall <= durationLarge) :
    lennardJonesMeasurableKineticScaledWindowThermalizationTime P micro
        equilibrium threshold durationSmall failureTolerance depth r0 N
        energyDensity <=
      lennardJonesMeasurableKineticScaledWindowThermalizationTime P micro
        equilibrium threshold durationLarge failureTolerance depth r0 N
        energyDensity := by
  have hg : 0 < kineticCouplingMagnitude depth r0 energyDensity :=
    kineticCouplingMagnitude_pos hdepth hr0 he
  have hphysical :
      kineticScaledPhysicalDuration durationSmall
          (kineticCouplingMagnitude depth r0 energyDensity) <=
        kineticScaledPhysicalDuration durationLarge
          (kineticCouplingMagnitude depth r0 energyDensity) := by
    exact (div_le_div_iff_of_pos_right
      (sq_pos_of_ne_zero (ne_of_gt hg))).2 hduration
  exact rationalStrictWindowThermalizationTime_monotone_duration P
    (distanceAtCoupling micro equilibrium N
      (kineticCouplingMagnitude depth r0 energyDensity))
    threshold
    (kineticScaledPhysicalDuration durationSmall
      (kineticCouplingMagnitude depth r0 energyDensity))
    (kineticScaledPhysicalDuration durationLarge
      (kineticCouplingMagnitude depth r0 energyDensity))
    failureTolerance hphysical

/-! ## Boundary comparison with the older closed-failure Tc -/

/-- The measurable strict event uses `threshold < distance`; the older event
uses `threshold <= distance`.  Hence the new Tc is no later.  Equality is not
claimed without a no-threshold-boundary theorem. -/
theorem lennardJonesMeasurableWindowThermalizationTime_le_closedFailureTime
    (P : Measure Omega) [IsProbabilityMeasure P]
    (micro : Nat -> Real -> Omega -> Real -> E) (equilibrium : E)
    (threshold duration failureTolerance depth r0 : Real)
    (N : Nat) (energyDensity : Real) :
    lennardJonesMeasurableWindowThermalizationTime P micro equilibrium
        threshold duration failureTolerance depth r0 N energyDensity <=
      lennardJonesStrictWindowThermalizationTime P micro equilibrium
        threshold duration failureTolerance depth r0 N energyDensity := by
  exact rationalStrictWindowThermalizationTime_le_microscopicWindowThermalizationTime
    P
    (fun M omega time => micro M
      (kineticCouplingMagnitude depth r0 energyDensity) omega time)
    equilibrium threshold duration failureTolerance N

/-- The same one-sided comparison for the kinetic-scaled physical window. -/
theorem lennardJonesMeasurableKineticScaledWindowThermalizationTime_le_closedFailureTime
    (P : Measure Omega) [IsProbabilityMeasure P]
    (micro : Nat -> Real -> Omega -> Real -> E) (equilibrium : E)
    (threshold kineticDuration failureTolerance depth r0 : Real)
    (N : Nat) (energyDensity : Real) :
    lennardJonesMeasurableKineticScaledWindowThermalizationTime P micro
        equilibrium threshold kineticDuration failureTolerance depth r0 N
        energyDensity <=
      lennardJonesKineticScaledWindowThermalizationTime P micro equilibrium
        threshold kineticDuration failureTolerance depth r0 N energyDensity := by
  exact rationalStrictWindowThermalizationTime_le_microscopicWindowThermalizationTime
    P
    (fun M omega time => micro M
      (kineticCouplingMagnitude depth r0 energyDensity) omega time)
    equilibrium threshold
    (kineticScaledPhysicalDuration kineticDuration
      (kineticCouplingMagnitude depth r0 energyDensity))
    failureTolerance N

/-! ## Transparent conditional `32 / 49` bridge -/

/-- Constant-in-sample adapter.  The sample is dummy because the measurable
Tc has already aggregated the ensemble probability `P`. -/
def measurableKineticScaledWindowCertificateAdapter
    (P : Measure Omega)
    (micro : Nat -> Real -> Omega -> Real -> E) (equilibrium : E)
    (threshold kineticDuration failureTolerance : Real) :
    Nat -> Real -> Omega -> ENNReal :=
  fun N g _omega =>
    measurableKineticScaledWindowThermalizationTimeAtCoupling P micro
      equilibrium threshold kineticDuration failureTolerance N g

@[simp]
theorem measurableKineticScaledWindowCertificateAdapter_apply
    (P : Measure Omega)
    (micro : Nat -> Real -> Omega -> Real -> E) (equilibrium : E)
    (threshold kineticDuration failureTolerance : Real)
    (N : Nat) (g : Real) (omega : Omega) :
    measurableKineticScaledWindowCertificateAdapter P micro equilibrium
        threshold kineticDuration failureTolerance N g omega =
      measurableKineticScaledWindowThermalizationTimeAtCoupling P micro
        equilibrium threshold kineticDuration failureTolerance N g := rfl

theorem measurable_measurableKineticScaledWindowCertificateAdapter
    (P : Measure Omega)
    (micro : Nat -> Real -> Omega -> Real -> E) (equilibrium : E)
    (threshold kineticDuration failureTolerance : Real)
    (N : Nat) (g : Real) :
    Measurable (measurableKineticScaledWindowCertificateAdapter P micro
      equilibrium threshold kineticDuration failureTolerance N g) :=
  measurable_const

/-- Transparent unresolved inputs for the measurable ensemble Tc.  This
abbreviation does not construct the certificate's microscopic approximation,
robust kinetic crossing, or scaled-time hitting identification. -/
abbrev LennardJonesMeasurableKineticScaledWindowScalingCertificate
    (P : Measure Omega) [IsProbabilityMeasure P]
    (micro : Nat -> Real -> Omega -> Real -> E) (equilibrium : E)
    (threshold kineticDuration failureTolerance : Real)
    (sizeCutoff : Real -> Nat) (kineticDistance : Real -> Real)
    (delta tauStar depth r0 : Real) :=
  LennardJonesThermodynamicHittingCertificate P
    (measurableKineticScaledWindowCertificateAdapter P micro equilibrium
      threshold kineticDuration failureTolerance)
    sizeCutoff kineticDistance delta tauStar depth r0

/-- Conditional simultaneous low-energy/thermodynamic law

`(e_j / depth) Tc(N_j,e_j) -> (32 / 49) tauStar`

in probability.  Its certificate is an explicit argument and is not supplied
by this module. -/
theorem lennardJonesMeasurableKineticScaledWindow_energyDensityTime_law
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
      (ENNReal.ofReal ((32 / 49 : Real) * tauStar)) := by
  simpa [scaledEnergyDensityEquilibrationTime,
    measurableKineticScaledWindowCertificateAdapter,
    lennardJonesMeasurableKineticScaledWindowThermalizationTime] using
    (certificate.energyDensityTime_law P
      (measurableKineticScaledWindowCertificateAdapter P micro equilibrium
        threshold kineticDuration failureTolerance)
      sizeCutoff kineticDistance delta tauStar depth r0 s)

end

end ArchonPhysics.LennardJonesMeasurableWindowThermalizationTime
