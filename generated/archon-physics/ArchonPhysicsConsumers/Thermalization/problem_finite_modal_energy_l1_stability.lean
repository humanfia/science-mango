import ArchonPhysics.FiniteModalEnergyL1Stability

/-!
# Consumer: finite modal-energy `L1` stability

The acceptance theorems expose the complex-amplitude inequality and its
per-mode and normalized `O(g)` consequences.  Their amplitude-distance bounds
remain explicit inputs: this consumer does not prove closeness of two flows.
-/

namespace ArchonPhysicsConsumers.Thermalization.FiniteModalEnergyL1Stability

open ArchonPhysics.EquipartitionEntropy
open ArchonPhysics.FiniteModalEnergyL1Stability

noncomputable section

variable {Mode : Type} [Fintype Mode]

/-- Complex form of
`sum ||a_k|²-|b_k|²| ≤ (‖a‖₂+‖b‖₂)‖a-b‖₂`. -/
theorem problem_complex_modalEnergyL1Distance_le
    (a b : Mode → Complex) :
    (∑ k, |Complex.normSq (a k) - Complex.normSq (b k)|) ≤
      (amplitudeL2Norm a + amplitudeL2Norm b) *
        amplitudeL2Distance a b := by
  simpa only [modalEnergyL1Distance, l1Distance, modalEnergySpectrum,
    Complex.normSq_eq_norm_sq] using modalEnergyL1Distance_le a b

/-- Per-mode RMS state error `O(g)` gives mean modal-energy error `O(g)` under
uniform square-root energy-density bounds. -/
theorem problem_perMode_modalEnergy_O_g_of_accumulated_rms
    [Nonempty Mode] (a b : Mode → Complex)
    (amplitudeCeilingA amplitudeCeilingB errorCoefficient g : Real)
    (hA : 0 ≤ amplitudeCeilingA) (hB : 0 ≤ amplitudeCeilingB)
    (hcoefficient : 0 ≤ errorCoefficient) (hg : 0 ≤ g)
    (ha : amplitudeRMSNorm a ≤ amplitudeCeilingA)
    (hb : amplitudeRMSNorm b ≤ amplitudeCeilingB)
    (hab : amplitudeRMSDistance a b ≤ errorCoefficient * g) :
    perModeModalEnergyL1Distance a b ≤
      (amplitudeCeilingA + amplitudeCeilingB) * errorCoefficient * g :=
  perModeModalEnergyL1Distance_le_of_rms_error
    a b amplitudeCeilingA amplitudeCeilingB errorCoefficient g
    hA hB hcoefficient hg ha hb hab

/-- With an extensive positive total-energy floor, the normalized modal-energy
profile inherits the same `O(g)` rate. -/
theorem problem_normalized_modalEnergy_O_g_of_accumulated_rms
    [Nonempty Mode] (a b : Mode → Complex)
    (energyDensityFloor amplitudeCeilingA amplitudeCeilingB
      errorCoefficient g : Real)
    (hfloor : 0 < energyDensityFloor)
    (hA : 0 ≤ amplitudeCeilingA) (hB : 0 ≤ amplitudeCeilingB)
    (hcoefficient : 0 ≤ errorCoefficient) (hg : 0 ≤ g)
    (haFloor : (Fintype.card Mode : Real) * energyDensityFloor ≤
      totalWeight (modalEnergySpectrum (Mode := Mode) (E := Complex) a))
    (hbTotal : 0 < totalWeight (modalEnergySpectrum (Mode := Mode) (E := Complex) b))
    (ha : amplitudeRMSNorm a ≤ amplitudeCeilingA)
    (hb : amplitudeRMSNorm b ≤ amplitudeCeilingB)
    (hab : amplitudeRMSDistance a b ≤ errorCoefficient * g) :
    normalizedModalEnergyL1Distance a b ≤
      (2 / energyDensityFloor) *
        ((amplitudeCeilingA + amplitudeCeilingB) *
          errorCoefficient * g) :=
  normalizedModalEnergyL1Distance_le_of_rms_error
    a b energyDensityFloor amplitudeCeilingA amplitudeCeilingB
    errorCoefficient g hfloor hA hB hcoefficient hg haFloor hbTotal
    ha hb hab

#print axioms problem_complex_modalEnergyL1Distance_le
#print axioms problem_perMode_modalEnergy_O_g_of_accumulated_rms
#print axioms problem_normalized_modalEnergy_O_g_of_accumulated_rms

end

end ArchonPhysicsConsumers.Thermalization.FiniteModalEnergyL1Stability
