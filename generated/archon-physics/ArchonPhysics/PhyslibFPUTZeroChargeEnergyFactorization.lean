import ArchonPhysics.FreeFPUTCrossOrbitCoefficientVolumeBound
import ArchonPhysics.PhyslibFPUTCanonicalQuadraticKernel

/-!
# Exact energy factorization of zero-charge FPUT coefficients

The exceptional coherent cross-orbit sector is supported on quadratic terms
of zero phase charge.  Such a term repeats one input mode with opposite phase
signs.  Consequently its two radial factors form a square and are exactly
linear in the energy of that repeated mode.  This file proves that identity,
including the zero-frequency branch where the physical interaction tensor
vanishes before division by frequency is used.
-/

namespace ArchonPhysics.PhyslibFPUTZeroChargeEnergyFactorization

open ArchonPhysics
open ArchonPhysics.FreeFPUTCrossOrbitCoefficientVolumeBound
open ArchonPhysics.FreeFPUTDuhamelResonanceBridge
open ArchonPhysics.FreeFPUTTensorPhaseExpansion
open ArchonPhysics.ModalPhaseMismatch
open ArchonPhysics.ModeCoupling
open ArchonPhysics.PhyslibFPUTSecondPicardHistoryBridge

noncomputable section

/-- The deterministic coefficient multiplying the energy in a zero-charge
quadratic Duhamel term. -/
def zeroChargeDuhamelEnergyCoefficient
    {N : Nat} [NeZero N]
    (coupling : Complex) (m : Lattice.PositiveMassConfig N)
    (observed : Lattice.Site N) (term : QuadraticPhaseTerm N) : Complex :=
  coupling *
    (interactionTensor m 3 (Fin.cons observed term.1) : Complex) *
    (((1 / (2 * modeFrequency m (term.1 0) ^ 2) : Real)) : Complex)

/-- Exact replacement of the paired square roots by one modal energy on the
zero-charge fiber. -/
theorem freeQuadraticDuhamelCoefficient_phaseEnergyRadius_eq_energy
    {N : Nat} [NeZero N]
    (coupling : Complex) (m : Lattice.PositiveMassConfig N)
    (observed : Lattice.Site N) (energy : Lattice.Site N → Real)
    (term : QuadraticPhaseTerm N)
    (henergy : ∀ mode, 0 ≤ energy mode)
    (hzero : quadraticPhaseCharge term = 0) :
    freeQuadraticDuhamelCoefficient coupling m observed
        (phaseEnergyRadius energy (modeFrequency m)) term =
      zeroChargeDuhamelEnergyCoefficient coupling m observed term *
        energy (term.1 0) := by
  have hstructure :=
    (quadraticPhaseCharge_eq_zero_iff_repeated_opposite term).1 hzero
  have hmodes : term.1 1 = term.1 0 := hstructure.1.symm
  by_cases hfrequency : 0 < modeFrequency m (term.1 0)
  · have hsqrt :
        (Real.sqrt (2 * energy (term.1 0))) ^ 2 =
          2 * energy (term.1 0) :=
      Real.sq_sqrt (mul_nonneg zero_le_two (henergy _))
    have hradius :
        (phaseEnergyRadius energy (modeFrequency m) (term.1 0) / 2) *
            (phaseEnergyRadius energy (modeFrequency m) (term.1 0) / 2) =
          (1 / (2 * modeFrequency m (term.1 0) ^ 2)) *
            energy (term.1 0) := by
      unfold phaseEnergyRadius
      rw [← pow_two, div_pow, div_pow, hsqrt]
      field_simp [hfrequency.ne']
    unfold freeQuadraticDuhamelCoefficient quadraticPhaseCoefficient
      zeroChargeDuhamelEnergyCoefficient
    rw [hmodes]
    let radius : Real :=
      phaseEnergyRadius energy (modeFrequency m) (term.1 0) / 2
    let coefficient : Real :=
      1 / (2 * modeFrequency m (term.1 0) ^ 2)
    let tensor : Complex :=
      interactionTensor m 3 (Fin.cons observed term.1)
    have hradiusComplex :
        (radius : Complex) * (radius : Complex) =
          ((coefficient * energy (term.1 0) : Real) : Complex) := by
      dsimp [radius, coefficient]
      exact_mod_cast hradius
    change coupling * (tensor * (radius : Complex) * (radius : Complex)) =
      coupling * tensor * (coefficient : Complex) * (energy (term.1 0) : Complex)
    calc
      coupling * (tensor * (radius : Complex) * (radius : Complex)) =
          coupling * tensor * ((radius : Complex) * (radius : Complex)) := by
        ring
      _ = coupling * tensor *
          ((coefficient * energy (term.1 0) : Real) : Complex) := by
        rw [hradiusComplex]
      _ = coupling * tensor * (coefficient : Complex) *
          (energy (term.1 0) : Complex) := by
        simp only [Complex.ofReal_mul, mul_assoc]
  · have hfrequencyZero : modeFrequency m (term.1 0) = 0 :=
      le_antisymm (not_lt.mp hfrequency) (modeFrequency_nonneg m _)
    have htensor :
        interactionTensor m 3 (Fin.cons observed term.1) = 0 := by
      simpa using
        (interactionTensor_cons_eq_zero_of_inputFrequency_eq_zero
          m observed term.1 0 hfrequencyZero)
    unfold freeQuadraticDuhamelCoefficient quadraticPhaseCoefficient
      zeroChargeDuhamelEnergyCoefficient
    rw [htensor]
    simp

end

end ArchonPhysics.PhyslibFPUTZeroChargeEnergyFactorization
