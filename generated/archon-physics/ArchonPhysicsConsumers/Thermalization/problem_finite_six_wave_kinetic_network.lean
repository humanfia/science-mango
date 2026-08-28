import ArchonPhysics.FiniteSixWaveKineticNetwork

/-!
# Consumer: finite resonant six-wave kinetic network

This consumer verifies the kinetic-side conservation and equilibrium target
for the equal-mass alpha-FPUT derivation.  The channel family and its rates
remain outputs to be identified by the microscopic diagram limit.
-/

namespace ArchonPhysicsConsumers.Thermalization

open ArchonPhysics.FiniteSixWaveKineticNetwork

noncomputable section

variable {Mode Channel : Type*} [Fintype Mode] [Fintype Channel]

theorem problem_finite_six_wave_weak_action_conservation
    (channels : Channel -> SixWaveChannel Mode) (rate : Channel -> Real)
    (trajectory : Real -> Mode -> Real)
    (hsolve : SolvesFiniteSixWaveKineticWeakly channels rate trajectory)
    (time : Real) :
    HasDerivAt (fun s => ∑ mode, trajectory s mode) 0 time :=
  hasDerivAt_totalAction_zero_of_solvesWeakly
    channels rate trajectory hsolve time

theorem problem_finite_six_wave_weak_energy_conservation
    (channels : Channel -> SixWaveChannel Mode) (rate : Channel -> Real)
    (trajectory : Real -> Mode -> Real) (frequency : Mode -> Real)
    (hsolve : SolvesFiniteSixWaveKineticWeakly channels rate trajectory)
    (hresonant : ∀ collision, ChannelResonant (channels collision) frequency)
    (time : Real) :
    HasDerivAt
      (fun s => ∑ mode, frequency mode * trajectory s mode) 0 time :=
  hasDerivAt_totalEnergy_zero_of_solvesWeakly
    channels rate trajectory frequency hsolve hresonant time

omit [Fintype Mode] in
theorem problem_finite_six_wave_rayleigh_jeans_network_stationary
    (channels : Channel -> SixWaveChannel Mode) (rate : Channel -> Real)
    (frequency weight : Mode -> Real) (chemical inverseTemperature : Real)
    (hresonant : ∀ collision, ChannelResonant (channels collision) frequency) :
    finiteSixWaveObservableSlope channels rate
      (fun mode =>
        ArchonPhysics.SixWaveCollisionAlgebra.rayleighJeansAction
          chemical inverseTemperature (frequency mode)) weight = 0 :=
  finiteSixWaveObservableSlope_rayleighJeans_eq_zero
    channels rate frequency weight chemical inverseTemperature hresonant

theorem problem_rayleigh_jeans_is_finite_six_wave_weak_solution
    (channels : Channel -> SixWaveChannel Mode) (rate : Channel -> Real)
    (frequency : Mode -> Real) (chemical inverseTemperature : Real)
    (hresonant : ∀ collision, ChannelResonant (channels collision) frequency) :
    SolvesFiniteSixWaveKineticWeakly channels rate
      (fun _time mode =>
        ArchonPhysics.SixWaveCollisionAlgebra.rayleighJeansAction
          chemical inverseTemperature (frequency mode)) :=
  rayleighJeans_solvesFiniteSixWaveKineticWeakly
    channels rate frequency chemical inverseTemperature hresonant

#print axioms problem_finite_six_wave_weak_action_conservation
#print axioms problem_finite_six_wave_weak_energy_conservation
#print axioms problem_finite_six_wave_rayleigh_jeans_network_stationary
#print axioms problem_rayleigh_jeans_is_finite_six_wave_weak_solution

end

end ArchonPhysicsConsumers.Thermalization
