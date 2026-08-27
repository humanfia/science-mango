import ArchonPhysics.LennardJonesThermodynamicHittingTransfer

namespace ArchonPhysicsConsumers.Thermalization

open Filter MeasureTheory Set Topology
open ArchonPhysics
open ArchonPhysics.ThermalizationTransfer
open ArchonPhysics.LennardJonesThermodynamicHittingTransfer

noncomputable section

theorem problem_lennardJones_kineticCouplingMagnitude_sq
    {depth r₀ e : Real} (hdepth : 0 < depth) (hr₀ : 0 < r₀)
    (he : 0 ≤ e) :
    kineticCouplingMagnitude depth r₀ e ^ 2 =
      49 * e / (32 * depth) :=
  kineticCouplingMagnitude_sq hdepth hr₀ he

def problem_lennardJones_toAdmissibleJointLimit
    {sizeCutoff : Real → Nat} {depth r₀ : Real}
    (s : AdmissibleLennardJonesJointLimit sizeCutoff depth r₀)
    (hdepth : 0 < depth) (hr₀ : 0 < r₀) :
    AdmissibleJointLimit sizeCutoff :=
  s.toAdmissibleJointLimit hdepth hr₀

theorem problem_lennardJones_energyDensityTime_law
    {Omega : Type*} [MeasurableSpace Omega]
    (P : Measure Omega) [IsProbabilityMeasure P]
    (equilibrationTime : Nat → Real → Omega → ENNReal)
    (sizeCutoff : Real → Nat) (kineticDistance : Real → Real)
    (delta tauStar depth r₀ : Real)
    (certificate : LennardJonesThermodynamicHittingCertificate
      P equilibrationTime sizeCutoff kineticDistance
      delta tauStar depth r₀)
    (s : AdmissibleLennardJonesJointLimit sizeCutoff depth r₀) :
    ConvergesInProbabilityTo P
      (fun j omega => scaledEnergyDensityEquilibrationTime equilibrationTime
        depth r₀ (s.systemSize j) (s.energyDensity j) omega)
      (ENNReal.ofReal ((32 / 49 : Real) * tauStar)) :=
  certificate.energyDensityTime_law P equilibrationTime sizeCutoff
    kineticDistance delta tauStar depth r₀ s

theorem problem_lennardJones_tendsto_measure_window
    {Omega : Type*} [MeasurableSpace Omega]
    (P : Measure Omega) [IsProbabilityMeasure P]
    (equilibrationTime : Nat → Real → Omega → ENNReal)
    (sizeCutoff : Real → Nat) (kineticDistance : Real → Real)
    (delta tauStar depth r₀ lower upper : Real)
    (certificate : LennardJonesThermodynamicHittingCertificate
      P equilibrationTime sizeCutoff kineticDistance
      delta tauStar depth r₀)
    (s : AdmissibleLennardJonesJointLimit sizeCutoff depth r₀)
    (hlower : lower < (32 / 49 : Real) * tauStar)
    (hupper : (32 / 49 : Real) * tauStar < upper) :
    Tendsto
      (fun j => P ((fun omega =>
        scaledEnergyDensityEquilibrationTime equilibrationTime
          depth r₀ (s.systemSize j) (s.energyDensity j) omega) ⁻¹'
        Icc (ENNReal.ofReal lower) (ENNReal.ofReal upper)))
      atTop (nhds 1) :=
  certificate.tendsto_measure_window P equilibrationTime sizeCutoff
    kineticDistance delta tauStar depth r₀ lower upper s hlower hupper

#print axioms problem_lennardJones_kineticCouplingMagnitude_sq
#print axioms problem_lennardJones_toAdmissibleJointLimit
#print axioms problem_lennardJones_energyDensityTime_law
#print axioms problem_lennardJones_tendsto_measure_window

end

end ArchonPhysicsConsumers.Thermalization
