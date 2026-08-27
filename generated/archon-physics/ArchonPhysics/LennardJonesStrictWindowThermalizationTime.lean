import ArchonPhysics.ArbitrarilyLongMicroscopicKineticPersistence
import ArchonPhysics.LennardJonesThermodynamicHittingTransfer
import ArchonPhysics.PaperSpectralEntropyCriterion

/-!
# Strict finite-window thermalization time for one-dimensional LJ chains

This module deliberately keeps two conventions separate.

* `lennardJonesPaperFirstHitAtEnergy` is the samplewise first time at which the
  paper spectral-entropy diagnostic crosses `1 / 2`.
* `lennardJonesStrictWindowThermalizationTime` is an ensemble quantity: it is
  the infimum of starts for which the probability of an equipartition failure
  anywhere in the following complete time window is below the prescribed
  tolerance.

Thus the second definition is not silently identified with the first.  The
final scaling theorem is conditional on the existing transparent
microscopic--kinetic certificate, specialized to the strict-window time.  No
inhabitant of that certificate is constructed here.

The original `duration` parameter is a fixed *physical* duration.  Along a
weak-coupling path `g -> 0`, its kinetic duration is `g ^ 2 * duration -> 0`,
so it cannot represent a fixed, let alone growing, kinetic observation window.
The kinetic-scaled variant below instead uses the physical duration
`kineticDuration / g ^ 2`.
-/

namespace ArchonPhysics.LennardJonesStrictWindowThermalizationTime

open Filter MeasureTheory
open ArchonPhysics.ArbitrarilyLongMicroscopicKineticPersistence
open ArchonPhysics.LennardJonesThermodynamicHittingTransfer
open ArchonPhysics.PaperSpectralEntropyCriterion
open ArchonPhysics.ThermalizationTransfer

noncomputable section

variable {Omega E : Type*} [MeasurableSpace Omega] [PseudoMetricSpace E]

/-! ## The two non-equivalent time conventions -/

/-- The ordinary paper convention at LJ energy density `e`: a samplewise first
crossing of the spectral-entropy threshold `1 / 2`.  It neither controls a
later time window nor averages over the ensemble. -/
def lennardJonesPaperFirstHitAtEnergy
    {OmegaPaper : Type}
    (xi : Nat -> Real -> OmegaPaper -> Real -> Real)
    (depth r₀ e : Real) (N : Nat) (omega : OmegaPaper) : ENNReal :=
  paperXiHalfEquilibrationTime xi N
    (kineticCouplingMagnitude depth r₀ e) omega

/-- Strict ensemble finite-window time at a fixed weak coupling `g`.

The microscopic path retains its one-dimensional chain-size coordinate `N`.
Membership of the candidate set bounds the probability of a violation at
*some* time in the whole interval `[start, start + duration]`. -/
def strictWindowThermalizationTimeAtCoupling
    (P : Measure Omega)
    (micro : Nat -> Real -> Omega -> Real -> E) (equilibrium : E)
    (threshold duration failureTolerance : Real) (N : Nat) (g : Real) : ENNReal :=
  microscopicWindowThermalizationTime P
    (fun M omega time => micro M g omega time) equilibrium
    threshold duration failureTolerance N

/-- Energy-dependent strict `Tc` for the LJ chain.  The LJ energy density is
converted to the positive cubic kinetic coupling with the exact coefficient
used by `LennardJonesThermodynamicHittingTransfer`. -/
def lennardJonesStrictWindowThermalizationTime
    (P : Measure Omega)
    (micro : Nat -> Real -> Omega -> Real -> E) (equilibrium : E)
    (threshold duration failureTolerance depth r₀ : Real)
    (N : Nat) (e : Real) : ENNReal :=
  strictWindowThermalizationTimeAtCoupling P micro equilibrium
    threshold duration failureTolerance N
    (kineticCouplingMagnitude depth r₀ e)

theorem lennardJonesStrictWindowThermalizationTime_antitone_threshold
    (P : Measure Omega) [IsProbabilityMeasure P]
    (micro : Nat -> Real -> Omega -> Real -> E) (equilibrium : E)
    (thresholdSmall thresholdLarge duration failureTolerance depth r₀ : Real)
    (N : Nat) (e : Real) (hthreshold : thresholdSmall <= thresholdLarge) :
    lennardJonesStrictWindowThermalizationTime P micro equilibrium
        thresholdLarge duration failureTolerance depth r₀ N e <=
      lennardJonesStrictWindowThermalizationTime P micro equilibrium
        thresholdSmall duration failureTolerance depth r₀ N e := by
  exact microscopicWindowThermalizationTime_antitone_threshold P
    (fun M omega time =>
      micro M (kineticCouplingMagnitude depth r₀ e) omega time)
    equilibrium thresholdSmall thresholdLarge duration failureTolerance N
    hthreshold

theorem lennardJonesStrictWindowThermalizationTime_monotone_duration
    (P : Measure Omega) [IsProbabilityMeasure P]
    (micro : Nat -> Real -> Omega -> Real -> E) (equilibrium : E)
    (threshold durationSmall durationLarge failureTolerance depth r₀ : Real)
    (N : Nat) (e : Real) (hduration : durationSmall <= durationLarge) :
    lennardJonesStrictWindowThermalizationTime P micro equilibrium
        threshold durationSmall failureTolerance depth r₀ N e <=
      lennardJonesStrictWindowThermalizationTime P micro equilibrium
        threshold durationLarge failureTolerance depth r₀ N e := by
  exact microscopicWindowThermalizationTime_monotone_duration P
    (fun M omega time =>
      micro M (kineticCouplingMagnitude depth r₀ e) omega time)
    equilibrium threshold durationSmall durationLarge failureTolerance N
    hduration

theorem lennardJonesStrictWindowThermalizationTime_antitone_failureTolerance
    (P : Measure Omega)
    (micro : Nat -> Real -> Omega -> Real -> E) (equilibrium : E)
    (threshold duration failureToleranceSmall failureToleranceLarge depth r₀ : Real)
    (N : Nat) (e : Real)
    (hfailure : failureToleranceSmall <= failureToleranceLarge) :
    lennardJonesStrictWindowThermalizationTime P micro equilibrium
        threshold duration failureToleranceLarge depth r₀ N e <=
      lennardJonesStrictWindowThermalizationTime P micro equilibrium
        threshold duration failureToleranceSmall depth r₀ N e := by
  exact microscopicWindowThermalizationTime_antitone_failureTolerance P
    (fun M omega time =>
      micro M (kineticCouplingMagnitude depth r₀ e) omega time)
    equilibrium threshold duration failureToleranceSmall
    failureToleranceLarge N hfailure


/-! ## Coupling-dependent and kinetic-scaled durations -/

/-- Strict window time with a physical duration selected from the coupling.
This low-level wrapper can also express growing kinetic windows by choosing an
appropriate `durationAtCoupling`; no asymptotic property is assumed here. -/
def strictWindowThermalizationTimeWithDurationAtCoupling
    (P : Measure Omega)
    (micro : Nat -> Real -> Omega -> Real -> E) (equilibrium : E)
    (threshold : Real) (durationAtCoupling : Real -> Real)
    (failureTolerance : Real) (N : Nat) (g : Real) : ENNReal :=
  strictWindowThermalizationTimeAtCoupling P micro equilibrium threshold
    (durationAtCoupling g) failureTolerance N g

/-- Physical duration corresponding to `kineticDuration` in kinetic time
`tau = g ^ 2 * t`.  Lean keeps this definition total: at `g = 0` it evaluates
to zero, while every admitted positive-energy LJ path has `g > 0`. -/
def physicalDurationFromKinetic (kineticDuration g : Real) : Real :=
  kineticDuration / g ^ 2

theorem physicalDurationFromKinetic_pos
    {kineticDuration g : Real} (hduration : 0 < kineticDuration)
    (hg : g ≠ 0) :
    0 < physicalDurationFromKinetic kineticDuration g := by
  exact div_pos hduration (sq_pos_of_ne_zero hg)

/-- Strict `Tc` whose following physical observation window has length
`kineticDuration / g ^ 2`, hence exactly `kineticDuration` in kinetic time. -/
def kineticScaledWindowThermalizationTimeAtCoupling
    (P : Measure Omega)
    (micro : Nat -> Real -> Omega -> Real -> E) (equilibrium : E)
    (threshold kineticDuration failureTolerance : Real)
    (N : Nat) (g : Real) : ENNReal :=
  strictWindowThermalizationTimeWithDurationAtCoupling P micro equilibrium
    threshold (physicalDurationFromKinetic kineticDuration) failureTolerance N g

/-- Energy-dependent LJ specialization of the kinetic-scaled strict time. -/
def lennardJonesKineticScaledWindowThermalizationTime
    (P : Measure Omega)
    (micro : Nat -> Real -> Omega -> Real -> E) (equilibrium : E)
    (threshold kineticDuration failureTolerance depth r₀ : Real)
    (N : Nat) (e : Real) : ENNReal :=
  kineticScaledWindowThermalizationTimeAtCoupling P micro equilibrium
    threshold kineticDuration failureTolerance N
    (kineticCouplingMagnitude depth r₀ e)
/-! ## Transparent conditional LJ scaling -/

/-- Constant-in-sample adapter required by the existing hitting-transfer API.

The sample argument is intentionally ignored because the strict-window `Tc`
has already aggregated failure probability with `P`.  This adapter is only a
type bridge; it does not turn the ensemble time into a samplewise first hit. -/
def strictWindowThermalizationTimeCertificateAdapter
    (P : Measure Omega)
    (micro : Nat -> Real -> Omega -> Real -> E) (equilibrium : E)
    (threshold duration failureTolerance : Real) :
    Nat -> Real -> Omega -> ENNReal :=
  fun N g _omega => strictWindowThermalizationTimeAtCoupling P micro equilibrium
    threshold duration failureTolerance N g

@[simp]
theorem strictWindowThermalizationTimeCertificateAdapter_apply
    (P : Measure Omega)
    (micro : Nat -> Real -> Omega -> Real -> E) (equilibrium : E)
    (threshold duration failureTolerance g : Real) (N : Nat) (omega : Omega) :
    strictWindowThermalizationTimeCertificateAdapter P micro equilibrium
        threshold duration failureTolerance N g omega =
      strictWindowThermalizationTimeAtCoupling P micro equilibrium
        threshold duration failureTolerance N g := rfl

/-- The transparent hypotheses needed to apply the existing LJ
microscopic--kinetic hitting transfer to the strict-window ensemble time.

In particular, this abbreviation does not construct its
`scaledEquilibrationTime_eq_hittingTime` field.  Supplying a value requires a
genuine theorem identifying the scaled strict-window infimum with the chosen
kinetic crossing; that missing physics is not assumed elsewhere in this
module. -/
abbrev LennardJonesStrictWindowScalingCertificate
    (P : Measure Omega) [IsProbabilityMeasure P]
    (micro : Nat -> Real -> Omega -> Real -> E) (equilibrium : E)
    (threshold duration failureTolerance : Real)
    (sizeCutoff : Real -> Nat) (kineticDistance : Real -> Real)
    (delta tauStar depth r₀ : Real) :=
  LennardJonesThermodynamicHittingCertificate P
    (strictWindowThermalizationTimeCertificateAdapter P micro equilibrium
      threshold duration failureTolerance)
    sizeCutoff kineticDistance delta tauStar depth r₀

/-- Conditional joint low-energy/thermodynamic scaling of the strict-window
LJ time:

`(e_j / depth) Tc(N_j,e_j) -> (32 / 49) tauStar`

in probability along the same simultaneous path `e_j -> 0`, `N_j -> infinity`
and size cutoff used by the existing LJ transfer.  The conclusion follows
from the exact LJ cubic identity once the transparent certificate above is
provided. -/
theorem strictWindow_energyDensityTime_law
    (P : Measure Omega) [IsProbabilityMeasure P]
    (micro : Nat -> Real -> Omega -> Real -> E) (equilibrium : E)
    (threshold duration failureTolerance : Real)
    (sizeCutoff : Real -> Nat) (kineticDistance : Real -> Real)
    (delta tauStar depth r₀ : Real)
    (certificate : LennardJonesStrictWindowScalingCertificate P micro
      equilibrium threshold duration failureTolerance sizeCutoff
      kineticDistance delta tauStar depth r₀)
    (s : AdmissibleLennardJonesJointLimit sizeCutoff depth r₀) :
    ConvergesInProbabilityTo P
      (fun j _omega =>
        ENNReal.ofReal (s.energyDensity j / depth) *
          lennardJonesStrictWindowThermalizationTime P micro equilibrium
            threshold duration failureTolerance depth r₀
            (s.systemSize j) (s.energyDensity j))
      (ENNReal.ofReal ((32 / 49 : Real) * tauStar)) := by
  simpa [scaledEnergyDensityEquilibrationTime,
    strictWindowThermalizationTimeCertificateAdapter,
    lennardJonesStrictWindowThermalizationTime] using
    (certificate.energyDensityTime_law P
      (strictWindowThermalizationTimeCertificateAdapter P micro equilibrium
        threshold duration failureTolerance)
      sizeCutoff kineticDistance delta tauStar depth r₀ s)


/-! ### Kinetic-scaled-window certificate bridge -/

/-- Constant-in-sample type bridge for the kinetic-scaled strict-window time.
As above, the ignored sample is explicit: this is an ensemble probability
infimum, not the paper's samplewise first hit. -/
def kineticScaledWindowThermalizationTimeCertificateAdapter
    (P : Measure Omega)
    (micro : Nat -> Real -> Omega -> Real -> E) (equilibrium : E)
    (threshold kineticDuration failureTolerance : Real) :
    Nat -> Real -> Omega -> ENNReal :=
  fun N g _omega => kineticScaledWindowThermalizationTimeAtCoupling P micro
    equilibrium threshold kineticDuration failureTolerance N g

/-- Transparent microscopic--kinetic obligations for the kinetic-scaled
strict-window time.  This changes only the duration bookkeeping; it does not
construct the unresolved microscopic certificate. -/
abbrev LennardJonesKineticScaledWindowScalingCertificate
    (P : Measure Omega) [IsProbabilityMeasure P]
    (micro : Nat -> Real -> Omega -> Real -> E) (equilibrium : E)
    (threshold kineticDuration failureTolerance : Real)
    (sizeCutoff : Real -> Nat) (kineticDistance : Real -> Real)
    (delta tauStar depth r₀ : Real) :=
  LennardJonesThermodynamicHittingCertificate P
    (kineticScaledWindowThermalizationTimeCertificateAdapter P micro equilibrium
      threshold kineticDuration failureTolerance)
    sizeCutoff kineticDistance delta tauStar depth r₀

/-- Conditional simultaneous low-energy/thermodynamic scaling for a physical
window of length `kineticDuration / g ^ 2`:

`(e_j / depth) Tc_kinWindow(N_j,e_j) -> (32 / 49) tauStar`.

The admissible path supplies positive `g_j`, so the displayed division has its
physical meaning at every index. -/
theorem kineticScaledWindow_energyDensityTime_law
    (P : Measure Omega) [IsProbabilityMeasure P]
    (micro : Nat -> Real -> Omega -> Real -> E) (equilibrium : E)
    (threshold kineticDuration failureTolerance : Real)
    (sizeCutoff : Real -> Nat) (kineticDistance : Real -> Real)
    (delta tauStar depth r₀ : Real)
    (certificate : LennardJonesKineticScaledWindowScalingCertificate P micro
      equilibrium threshold kineticDuration failureTolerance sizeCutoff
      kineticDistance delta tauStar depth r₀)
    (s : AdmissibleLennardJonesJointLimit sizeCutoff depth r₀) :
    ConvergesInProbabilityTo P
      (fun j _omega =>
        ENNReal.ofReal (s.energyDensity j / depth) *
          lennardJonesKineticScaledWindowThermalizationTime P micro equilibrium
            threshold kineticDuration failureTolerance depth r₀
            (s.systemSize j) (s.energyDensity j))
      (ENNReal.ofReal ((32 / 49 : Real) * tauStar)) := by
  simpa [scaledEnergyDensityEquilibrationTime,
    kineticScaledWindowThermalizationTimeCertificateAdapter,
    lennardJonesKineticScaledWindowThermalizationTime] using
    (certificate.energyDensityTime_law P
      (kineticScaledWindowThermalizationTimeCertificateAdapter P micro equilibrium
        threshold kineticDuration failureTolerance)
      sizeCutoff kineticDistance delta tauStar depth r₀ s)
end

end ArchonPhysics.LennardJonesStrictWindowThermalizationTime
