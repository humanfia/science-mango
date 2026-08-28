import ArchonPhysics.FiniteFourWaveKineticNetwork

/-!
# Consumer: finite resonant four-wave kinetic network

This consumer fixes the kinetic-side endpoints needed by the equal-mass
alpha-FPUT Hamiltonian-to-WKE derivation.  The microscopic diagram limit must
still identify the channels and their rates.
-/

namespace ArchonPhysicsConsumers.Thermalization

open ArchonPhysics.FiniteFourWaveKineticNetwork

noncomputable section

variable {Mode Channel : Type*} [Fintype Mode] [Fintype Channel]

theorem problem_finite_four_wave_weak_action_conservation
    (channels : Channel -> FourWaveChannel Mode) (rate : Channel -> Real)
    (trajectory : Real -> Mode -> Real)
    (hsolve : SolvesFiniteFourWaveKineticWeakly channels rate trajectory)
    (time : Real) :
    HasDerivAt (fun s => ∑ mode, trajectory s mode) 0 time :=
  hasDerivAt_totalAction_zero_of_solvesWeakly
    channels rate trajectory hsolve time

theorem problem_finite_four_wave_weak_energy_conservation
    (channels : Channel -> FourWaveChannel Mode) (rate : Channel -> Real)
    (trajectory : Real -> Mode -> Real) (frequency : Mode -> Real)
    (hsolve : SolvesFiniteFourWaveKineticWeakly channels rate trajectory)
    (hresonant : ∀ collision, ChannelResonant (channels collision) frequency)
    (time : Real) :
    HasDerivAt
      (fun s => ∑ mode, frequency mode * trajectory s mode) 0 time :=
  hasDerivAt_totalEnergy_zero_of_solvesWeakly
    channels rate trajectory frequency hsolve hresonant time

omit [Fintype Mode] in
theorem problem_finite_four_wave_rayleigh_jeans_network_stationary
    (channels : Channel -> FourWaveChannel Mode) (rate : Channel -> Real)
    (frequency weight : Mode -> Real) (chemical inverseTemperature : Real)
    (hresonant : ∀ collision, ChannelResonant (channels collision) frequency) :
    finiteFourWaveObservableSlope channels rate
      (fun mode =>
        ArchonPhysics.FourWaveCollisionAlgebra.fourWaveRayleighJeansAction
          chemical inverseTemperature (frequency mode)) weight = 0 :=
  finiteFourWaveObservableSlope_rayleighJeans_eq_zero
    channels rate frequency weight chemical inverseTemperature hresonant

theorem problem_rayleigh_jeans_is_finite_four_wave_weak_solution
    (channels : Channel -> FourWaveChannel Mode) (rate : Channel -> Real)
    (frequency : Mode -> Real) (chemical inverseTemperature : Real)
    (hresonant : ∀ collision, ChannelResonant (channels collision) frequency) :
    SolvesFiniteFourWaveKineticWeakly channels rate
      (fun _time mode =>
        ArchonPhysics.FourWaveCollisionAlgebra.fourWaveRayleighJeansAction
          chemical inverseTemperature (frequency mode)) :=
  rayleighJeans_solvesFiniteFourWaveKineticWeakly
    channels rate frequency chemical inverseTemperature hresonant

#print axioms problem_finite_four_wave_weak_action_conservation
#print axioms problem_finite_four_wave_weak_energy_conservation
#print axioms problem_finite_four_wave_rayleigh_jeans_network_stationary
#print axioms problem_rayleigh_jeans_is_finite_four_wave_weak_solution

end

end ArchonPhysicsConsumers.Thermalization
