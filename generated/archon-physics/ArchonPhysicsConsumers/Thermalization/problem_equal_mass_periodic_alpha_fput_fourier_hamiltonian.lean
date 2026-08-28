import ArchonPhysics.EqualMassPeriodicFPUTFourierHamiltonian

/-!
# Equal-mass periodic alpha-FPUT Fourier/Hamiltonian interface

Named consumer endpoints for the exact finite-volume character tensor and
the exact projection of a differentiable Physlib Hamilton trajectory.  The
Fourier transform is average-normalized, while the character waves are not
normalized.  No kinetic, random-phase, or resonant-shell statement is used.
-/

namespace ArchonPhysicsConsumers.Thermalization

open scoped BigOperators

open ArchonPhysics
open ArchonPhysics.CoerciveHamiltonianPhyslib
open ArchonPhysics.EqualMassPeriodicFPUTFourierHamiltonian
open ArchonPhysics.Lattice
open Time

noncomputable section

/-- Exact bond-tensor momentum selector in the canonical `ZMod N` Fourier
basis. -/
theorem equalMassPeriodicAlphaBondTensorMomentumSelector
    (N : Nat) [NeZero N] (k₀ k₁ k₂ : Site N) :
    bondDifferenceCubicTensor N k₀ k₁ k₂ =
      if k₀ + k₁ + k₂ = 0 then
        (N : Complex) * bondFourierSymbol N k₀ *
          bondFourierSymbol N k₁ * bondFourierSymbol N k₂
      else 0 :=
  bondDifferenceCubicTensor_eq_ite N k₀ k₁ k₂

/-- A translation zero-mode leg kills the cubic bond tensor. -/
theorem equalMassPeriodicAlphaBondTensorZeroModeLeg
    (N : Nat) [NeZero N] (k₁ k₂ : Site N) :
    bondDifferenceCubicTensor N 0 k₁ k₂ = 0 :=
  bondDifferenceCubicTensor_eq_zero_of_first_zero N k₁ k₂

/-- Every differentiable trajectory satisfying the existing pure-alpha
Physlib Hamilton predicate obeys the exact complex Fourier modal system. -/
theorem equalMassPeriodicAlphaFourierHamiltonEquations
    {N : Nat} [NeZero N] (alpha : Real)
    (p q : Time → HilbertConfiguration N)
    (hHamilton :
      SatisfiesHamiltonEquations (unitMassConfig N) 1 0 alpha p q)
    (hp : Differentiable Real p) (hq : Differentiable Real q) :
    (∀ t k,
      ∂ₜ (fun s ↦ cycleFourierProjectionCLM N k (q s)) t =
        cycleFourierProjectionCLM N k (p t)) ∧
    (∀ t k,
      ∂ₜ (fun s ↦ cycleFourierProjectionCLM N k (p s)) t =
        -(ArchonPhysics.CleanCycleAcousticCountEnvelope.cleanCycleModeEnergy N k :
            Complex) * cycleFourierProjectionCLM N k (q t) +
          ∑ l : Site N,
            pureAlphaQuadraticFourierCoefficient N alpha k l *
              cycleFourierProjectionCLM N l (q t) *
              cycleFourierProjectionCLM N (k - l) (q t)) :=
  pureAlpha_fourierModalEquations alpha p q hHamilton hp hq

/-- The quadratic modal coefficient has no translation-mode output. -/
theorem equalMassPeriodicAlphaQuadraticCoefficientZeroOutput
    (N : Nat) [NeZero N] (alpha : Real) (l : Site N) :
    pureAlphaQuadraticFourierCoefficient N alpha 0 l = 0 :=
  pureAlphaQuadraticFourierCoefficient_output_zero N alpha l

/-- The quadratic modal coefficient has no translation-mode left child. -/
theorem equalMassPeriodicAlphaQuadraticCoefficientZeroLeftChild
    (N : Nat) [NeZero N] (alpha : Real) (k : Site N) :
    pureAlphaQuadraticFourierCoefficient N alpha k 0 = 0 :=
  pureAlphaQuadraticFourierCoefficient_left_zero N alpha k

/-- The quadratic modal coefficient has no translation-mode right child. -/
theorem equalMassPeriodicAlphaQuadraticCoefficientZeroRightChild
    (N : Nat) [NeZero N] (alpha : Real) (k : Site N) :
    pureAlphaQuadraticFourierCoefficient N alpha k k = 0 :=
  pureAlphaQuadraticFourierCoefficient_right_zero N alpha k

/-- The full projected pure-alpha force vanishes at the translation mode. -/
theorem equalMassPeriodicAlphaProjectedZeroModeForce
    {N : Nat} [NeZero N] (alpha : Real)
    (q : HilbertConfiguration N) :
    cycleFourierProjectionCLM N 0
        (-ArchonPhysics.ConcreteHamiltonGradients.potentialGradient
          1 0 alpha q) = 0 :=
  cycleFourierProjection_neg_potentialGradient_pureAlpha_zero alpha q

#print axioms equalMassPeriodicAlphaBondTensorMomentumSelector
#print axioms equalMassPeriodicAlphaBondTensorZeroModeLeg
#print axioms equalMassPeriodicAlphaFourierHamiltonEquations
#print axioms equalMassPeriodicAlphaQuadraticCoefficientZeroOutput
#print axioms equalMassPeriodicAlphaQuadraticCoefficientZeroLeftChild
#print axioms equalMassPeriodicAlphaQuadraticCoefficientZeroRightChild
#print axioms equalMassPeriodicAlphaProjectedZeroModeForce

end

end ArchonPhysicsConsumers.Thermalization
