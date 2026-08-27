import ArchonPhysics.FreeFPUTCollisionMismatchBridge
import ArchonPhysics.FreeFPUTHaarResonanceReduction

/-!
# Energy normalization of one free FPUT collision term

This module identifies the squared coefficient of one signed quadratic FPUT
term with the existing positive-frequency normalized interaction weight.  The
initial real modal coordinates use `phaseEnergyRadius`, and the distinguished
output leg receives exactly the complex-amplitude normalization dictated by
`ForcedComplexModeDuhamel`.

The result is deliberately termwise.  Haar averaging retains coherent cross
terms between distinct quadratic terms with equal phase charge, notably input
permutations and the zero-charge fiber.  Nothing below replaces that coherent
fiber square by a diagonal sum of interaction weights.  No nonlinear-trajectory
approximation, kinetic limit, or thermalization statement is made.
-/

namespace ArchonPhysics.FreeFPUTEnergyCollisionWeightBridge

open ArchonPhysics
open ArchonPhysics.FreeFPUTCollisionMismatchBridge
open ArchonPhysics.FreeFPUTDuhamelResonanceBridge
open ArchonPhysics.FreeFPUTTensorPhaseExpansion
open ArchonPhysics.ModalPhaseMismatch
open ArchonPhysics.NormalizedModeCoupling

noncomputable section

/-- Harmonic action associated with a prescribed modal energy and frequency. -/
def modeAction {d : Type*}
    (energy frequency : d → Real) (mode : d) : Real :=
  energy mode / frequency mode

/-- Physical prefactor of the quadratic FPUT source in the distinguished
mode's complex-amplitude equation.  The quadratic real force is
`-(kappa * g) * tensorContraction`, while `forcedModeSource` contributes
`I / sqrt (2 * omega_observed)`. -/
def physicalQuadraticCoupling {N : Nat} [NeZero N]
    (kappa g : Real) (m : Lattice.PositiveMassConfig N)
    (observed : Lattice.Site N) : Complex :=
  -(Complex.I * ((kappa * g : Real) : Complex)) *
    (modeAmplitudeNormalization m observed : Complex)

/-- Squared modulus of one raw quadratic phase coefficient at prescribed
nonnegative input energies.  The missing distinguished-leg amplitude
normalization appears explicitly as `2 * omega_observed`. -/
theorem normSq_quadraticPhaseCoefficient_phaseEnergyRadius_eq
    {N : Nat} [NeZero N]
    (m : Lattice.PositiveMassConfig N) (observed : Lattice.Site N)
    (energy : Lattice.Site N → Real) (term : QuadraticPhaseTerm N)
    (henergy : ∀ r : Fin 2, 0 ≤ energy (term.1 r))
    (hpositive : PositiveModeTuple m
      (quadraticCollisionModes observed term)) :
    Complex.normSq
        (quadraticPhaseCoefficient m observed
          (phaseEnergyRadius energy (modeFrequency m)) term) =
      (2 * modeFrequency m observed) *
        normalizedInteractionWeight m
          (quadraticCollisionModes observed term) *
        ∏ r : Fin 2,
          modeAction energy (modeFrequency m) (term.1 r) := by
  have hFinSuccZero : Fin.succ (0 : Fin 1) = (1 : Fin 2) := rfl
  have hfrequencyObserved : 0 < modeFrequency m observed := by
    simpa [quadraticCollisionModes] using hpositive (0 : Fin 3)
  have hfrequencyZero : 0 < modeFrequency m (term.1 0) := by
    simpa only [quadraticCollisionModes, Fin.cons_succ] using
      hpositive (Fin.succ (0 : Fin 2))
  have hfrequencyOne : 0 < modeFrequency m (term.1 1) := by
    have h := hpositive (Fin.succ (Fin.succ (0 : Fin 1)))
    simp only [quadraticCollisionModes, Fin.cons_succ] at h
    simpa only [hFinSuccZero] using h
  have hsqrtZero :
      (Real.sqrt (2 * energy (term.1 0))) ^ 2 =
        2 * energy (term.1 0) :=
    Real.sq_sqrt (mul_nonneg zero_le_two (henergy 0))
  have hsqrtOne :
      (Real.sqrt (2 * energy (term.1 1))) ^ 2 =
        2 * energy (term.1 1) :=
    Real.sq_sqrt (mul_nonneg zero_le_two (henergy 1))
  have hradiusZero :
      (Real.sqrt (2 * energy (term.1 0)) /
          modeFrequency m (term.1 0) / 2) *
        (Real.sqrt (2 * energy (term.1 0)) /
          modeFrequency m (term.1 0) / 2) =
      energy (term.1 0) /
        (2 * modeFrequency m (term.1 0) ^ 2) := by
    rw [← pow_two, div_pow, div_pow, hsqrtZero]
    ring
  have hradiusOne :
      (Real.sqrt (2 * energy (term.1 1)) /
          modeFrequency m (term.1 1) / 2) *
        (Real.sqrt (2 * energy (term.1 1)) /
          modeFrequency m (term.1 1) / 2) =
      energy (term.1 1) /
        (2 * modeFrequency m (term.1 1) ^ 2) := by
    rw [← pow_two, div_pow, div_pow, hsqrtOne]
    ring
  simp only [quadraticPhaseCoefficient, Complex.normSq_mul,
    Complex.normSq_ofReal, phaseEnergyRadius,
    normalizedInteractionWeight, quadraticCollisionModes,
    Fin.prod_univ_succ, modeAction, hFinSuccZero,
    Fin.cons_zero, Fin.cons_succ]
  rw [hradiusZero, hradiusOne]
  field_simp [hfrequencyObserved.ne', hfrequencyZero.ne',
    hfrequencyOne.ne']
  ring

/-- The physical distinguished-mode prefactor supplies the remaining output
normalization.  The squared term is exactly `(kappa * g)^2` times the
normalized three-leg interaction weight and the two input actions. -/
theorem normSq_physicalQuadraticDuhamelCoefficient_eq
    {N : Nat} [NeZero N]
    (kappa g : Real) (m : Lattice.PositiveMassConfig N)
    (observed : Lattice.Site N)
    (energy : Lattice.Site N → Real) (term : QuadraticPhaseTerm N)
    (henergy : ∀ r : Fin 2, 0 ≤ energy (term.1 r))
    (hpositive : PositiveModeTuple m
      (quadraticCollisionModes observed term)) :
    Complex.normSq
        (freeQuadraticDuhamelCoefficient
          (physicalQuadraticCoupling kappa g m observed) m observed
          (phaseEnergyRadius energy (modeFrequency m)) term) =
      (kappa * g) ^ 2 *
        normalizedInteractionWeight m
          (quadraticCollisionModes observed term) *
        ∏ r : Fin 2,
          modeAction energy (modeFrequency m) (term.1 r) := by
  have hfrequencyObserved : 0 < modeFrequency m observed := by
    simpa [quadraticCollisionModes] using hpositive (0 : Fin 3)
  rw [freeQuadraticDuhamelCoefficient, Complex.normSq_mul,
    normSq_quadraticPhaseCoefficient_phaseEnergyRadius_eq
      m observed energy term henergy hpositive]
  unfold physicalQuadraticCoupling modeAmplitudeNormalization
  simp only [Complex.normSq_mul, Complex.normSq_neg,
    Complex.normSq_I, Complex.normSq_ofReal, one_mul]
  have hsqrtObserved :
      (Real.sqrt (2 * modeFrequency m observed)) ^ 2 =
        2 * modeFrequency m observed :=
    Real.sq_sqrt (mul_pos zero_lt_two hfrequencyObserved).le
  have hsqrtObservedNe :
      Real.sqrt (2 * modeFrequency m observed) ≠ 0 :=
    Real.sqrt_ne_zero'.mpr (mul_pos zero_lt_two hfrequencyObserved)
  have hinvSqrtObserved :
      (Real.sqrt (2 * modeFrequency m observed))⁻¹ *
          (Real.sqrt (2 * modeFrequency m observed))⁻¹ =
        (2 * modeFrequency m observed)⁻¹ := by
    field_simp [hsqrtObservedNe, hfrequencyObserved.ne'];
      nlinarith [hsqrtObserved]
  rw [hinvSqrtObserved]
  field_simp [hfrequencyObserved.ne']

end

end ArchonPhysics.FreeFPUTEnergyCollisionWeightBridge
