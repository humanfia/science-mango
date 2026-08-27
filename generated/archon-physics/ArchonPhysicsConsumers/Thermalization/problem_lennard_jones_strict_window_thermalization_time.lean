import ArchonPhysics.LennardJonesStrictWindowThermalizationTime

namespace ArchonPhysicsConsumers.Thermalization

open Filter MeasureTheory
open ArchonPhysics
open ArchonPhysics.ArbitrarilyLongMicroscopicKineticPersistence
open ArchonPhysics.LennardJonesThermodynamicHittingTransfer
open ArchonPhysics.LennardJonesStrictWindowThermalizationTime
open ArchonPhysics.ThermalizationTransfer

noncomputable section

variable {Omega E : Type*} [MeasurableSpace Omega] [PseudoMetricSpace E]

/-- The strict LJ `Tc` unfolds to the all-times-in-one-window bad-probability
definition, not to the paper's samplewise spectral-entropy first hit. -/
theorem problem_lennardJones_strictWindowTime_is_windowProbabilityInfimum
    (P : Measure Omega)
    (micro : Nat -> Real -> Omega -> Real -> E) (equilibrium : E)
    (threshold duration failureTolerance depth r₀ : Real)
    (N : Nat) (e : Real) :
    lennardJonesStrictWindowThermalizationTime P micro equilibrium
        threshold duration failureTolerance depth r₀ N e =
      microscopicWindowThermalizationTime P
        (fun M omega time =>
          micro M (kineticCouplingMagnitude depth r₀ e) omega time)
        equilibrium threshold duration failureTolerance N := rfl

/-- The certificate adapter is constant in its sample argument because the
strict time has already aggregated the ensemble probability. -/
theorem problem_lennardJones_strictWindowAdapter_ignores_sample
    (P : Measure Omega)
    (micro : Nat -> Real -> Omega -> Real -> E) (equilibrium : E)
    (threshold duration failureTolerance g : Real) (N : Nat)
    (omega₁ omega₂ : Omega) :
    strictWindowThermalizationTimeCertificateAdapter P micro equilibrium
        threshold duration failureTolerance N g omega₁ =
      strictWindowThermalizationTimeCertificateAdapter P micro equilibrium
        threshold duration failureTolerance N g omega₂ := rfl

/-- Kernel-lock the joint low-energy/thermodynamic `32 / 49` specialization.
The certificate remains an explicit argument. -/
theorem problem_lennardJones_strictWindow_energyDensityTime_law
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
      (ENNReal.ofReal ((32 / 49 : Real) * tauStar)) :=
  strictWindow_energyDensityTime_law P micro equilibrium threshold duration
    failureTolerance sizeCutoff kineticDistance delta tauStar depth r₀
    certificate s


/-- The kinetic-scaled LJ wrapper uses exactly the physical duration
`kineticDuration / g(e) ^ 2`. -/
theorem problem_lennardJones_kineticScaledWindow_uses_physical_g2_duration
    (P : Measure Omega)
    (micro : Nat -> Real -> Omega -> Real -> E) (equilibrium : E)
    (threshold kineticDuration failureTolerance depth r₀ : Real)
    (N : Nat) (e : Real) :
    lennardJonesKineticScaledWindowThermalizationTime P micro equilibrium
        threshold kineticDuration failureTolerance depth r₀ N e =
      microscopicWindowThermalizationTime P
        (fun M omega time =>
          micro M (kineticCouplingMagnitude depth r₀ e) omega time)
        equilibrium threshold
        (kineticDuration / kineticCouplingMagnitude depth r₀ e ^ 2)
        failureTolerance N := rfl

/-- Kernel-lock the conditional `32 / 49` law for the kinetic-scaled window. -/
theorem problem_lennardJones_kineticScaledWindow_energyDensityTime_law
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
      (ENNReal.ofReal ((32 / 49 : Real) * tauStar)) :=
  kineticScaledWindow_energyDensityTime_law P micro equilibrium threshold
    kineticDuration failureTolerance sizeCutoff kineticDistance delta tauStar
    depth r₀ certificate s
#print axioms problem_lennardJones_kineticScaledWindow_uses_physical_g2_duration
#print axioms problem_lennardJones_kineticScaledWindow_energyDensityTime_law
#print axioms problem_lennardJones_strictWindowTime_is_windowProbabilityInfimum
#print axioms problem_lennardJones_strictWindowAdapter_ignores_sample
#print axioms problem_lennardJones_strictWindow_energyDensityTime_law

end

end ArchonPhysicsConsumers.Thermalization
