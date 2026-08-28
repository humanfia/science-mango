import ArchonPhysics.ResonantThreeWaveKineticLInfinityEquilibrium

/-!
# Consumer: quotient Rayleigh--Jeans stationary flow

The pointwise RN equilibrium is consumed here through the canonical
`L-infinity` quotient dynamics, including the global stationary trajectory
and its zero entropy production.
-/

namespace ArchonPhysicsConsumers.Thermalization.ResonantThreeWaveKineticLInfinityEquilibrium

open MeasureTheory
open ArchonPhysics
open ArchonPhysics.ResonantThreeWaveKineticEntropy
open ArchonPhysics.ResonantThreeWaveKineticEquilibrium
open ArchonPhysics.ResonantThreeWaveKineticLInfinityEquilibrium
open ArchonPhysics.ResonantThreeWaveKineticLInfinityLocalWellposedness
open scoped ENNReal MeasureTheory

noncomputable section

variable {Mode : Type*} [MeasurableSpace Mode]

/-- Under the same positive-frequency assumptions as the RN H-theorem, the
Rayleigh--Jeans class is an actual global solution of the unclipped quotient
ODE. -/
theorem problem_rayleighJeansClass_global_stationary
    (collision : ResonantThreeWaveMeasure Mode) (g temperature : Real)
    (htemperature : 0 < temperature)
    (frequencyFloor : Real) (hfrequencyFloor : 0 < frequencyFloor)
    (hfrequency : ∀ mode, frequencyFloor ≤ collision.frequency mode) :
    let equilibrium := rayleighJeansClass collision temperature frequencyFloor
      hfrequencyFloor hfrequency
    (∀ t : Real, (fun _ : Real ↦ equilibrium) t = equilibrium) ∧
      ∀ t : Real, HasDerivAt (fun _ : Real ↦ equilibrium)
        (rnCollisionVectorField collision g equilibrium) t :=
  rayleighJeansClass_global_stationary collision g temperature htemperature
    frequencyFloor hfrequencyFloor hfrequency

/-- The representative defining the same quotient stationary state has zero
continuum logarithmic-entropy production. -/
theorem problem_rayleighJeansClass_entropyProduction_eq_zero
    (collision : ResonantThreeWaveMeasure Mode) (temperature : Real)
    (htemperature : 0 < temperature)
    (frequencyFloor : Real) (hfrequencyFloor : 0 < frequencyFloor)
    (hfrequency : ∀ mode, frequencyFloor ≤ collision.frequency mode) :
    continuumLogEntropyProduction collision
      (rayleighJeansAction temperature collision.frequency) = 0 :=
  rayleighJeansClass_entropyProduction_eq_zero collision temperature
    htemperature frequencyFloor hfrequencyFloor hfrequency

end

end ArchonPhysicsConsumers.Thermalization.ResonantThreeWaveKineticLInfinityEquilibrium
