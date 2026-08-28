import ArchonPhysics.EqualMassPeriodicFPUTInteractionPicture

/-!
# Exact signed interaction picture for periodic alpha-FPUT

Named endpoints for the finite-volume Hamiltonian-to-interaction-picture
bridge.  These statements retain all momentum, branch-sign, mismatch, and
vertex factors explicitly and make no kinetic or random-phase approximation.
-/

namespace ArchonPhysicsConsumers.Thermalization

open scoped BigOperators

open ArchonPhysics
open ArchonPhysics.CoerciveHamiltonianPhyslib
open ArchonPhysics.EqualMassPeriodicFPUTFourierHamiltonian
open ArchonPhysics.EqualMassPeriodicFPUTInteractionPicture
open ArchonPhysics.FinitePhaseMonomials
open ArchonPhysics.Lattice
open ArchonPhysics.PhaseRenormalization
open Time

noncomputable section

/-- The convolution label always carries the exact modular momentum relation. -/
theorem equalMassPeriodicFPUTInteractionMomentumRelation
    {N : Nat} [NeZero N] (k l : Site N) :
    k = l + (k - l) :=
  output_eq_left_add_right k l

/-- Zero-frequency inputs may be deleted without changing the full
Hamiltonian quadratic convolution. -/
theorem equalMassPeriodicFPUTInteractionSafeNonzeroInputs
    {N : Nat} [NeZero N] (alpha : Real) (k : Site N)
    (Q : Site N → Complex) :
    (∑ l : Site N,
        pureAlphaQuadraticFourierCoefficient N alpha k l *
          Q l * Q (k - l)) =
      ∑ l ∈ nonzeroInputMomenta N k,
        pureAlphaQuadraticFourierCoefficient N alpha k l *
          Q l * Q (k - l) :=
  fullQuadraticConvolution_eq_nonzeroInputs alpha k Q

/-- The three branch rotations combine into the displayed signed mismatch. -/
theorem equalMassPeriodicFPUTInteractionPhaseMismatch
    {N : Nat} [NeZero N] (k l : Site N)
    (outputSign leftSign rightSign : PhaseSign) (tau : Real) :
    phaseFactor
        (ComplexFourierBranchAmplitude.phaseSignReal outputSign *
          equalMassFourierFrequency N k * tau) *
      phaseFactor
        (-(ComplexFourierBranchAmplitude.phaseSignReal leftSign *
          equalMassFourierFrequency N l * tau)) *
      phaseFactor
        (-(ComplexFourierBranchAmplitude.phaseSignReal rightSign *
          equalMassFourierFrequency N (k - l) * tau)) =
      phaseFactor
        (equalMassQuadraticBranchMismatch k l
          outputSign leftSign rightSign * tau) :=
  phaseFactor_output_mul_inputs_eq_mismatch
    k l outputSign leftSign rightSign tau

/-- The exact signed vertex displays the output source normalization and both
input reconstruction normalizations. -/
theorem equalMassPeriodicFPUTInteractionVertexFormula
    {N : Nat} [NeZero N] (alpha : Real) (k l : Site N)
    (outputSign : PhaseSign) :
    equalMassQuadraticBranchVertex alpha k l outputSign =
      ((ComplexFourierBranchAmplitude.phaseSignReal outputSign : Complex) *
          Complex.I *
          pureAlphaQuadraticFourierCoefficient N alpha k l) /
        Real.sqrt (2 * equalMassFourierFrequency N k) /
        Real.sqrt (2 * equalMassFourierFrequency N l) /
        Real.sqrt (2 * equalMassFourierFrequency N (k - l)) := rfl

/-- Every nonzero output branch of an actual differentiable Physlib
trajectory obeys the explicit finite quadratic branch sum. -/
theorem equalMassPeriodicFPUTExactInteractionPictureDerivative
    {N : Nat} [NeZero N] (alpha : Real)
    (outputSign : PhaseSign) (k : Site N)
    (p q : Time → HilbertConfiguration N)
    (hHamilton :
      SatisfiesHamiltonEquations (unitMassConfig N) 1 0 alpha p q)
    (hp : Differentiable Real p) (hq : Differentiable Real q)
    (hk : k ≠ 0) (tau : Real) :
    HasDerivAt (equalMassInteractionBranch outputSign k p q)
      (∑ l ∈ nonzeroInputMomenta N k,
        ∑ leftSign ∈ phaseSignFinset,
          ∑ rightSign ∈ phaseSignFinset,
            equalMassQuadraticBranchTerm alpha k l
              outputSign leftSign rightSign p q tau) tau :=
  hasDerivAt_equalMassInteractionBranch_explicit
    alpha outputSign k p q hHamilton hp hq hk tau

#print axioms equalMassPeriodicFPUTInteractionMomentumRelation
#print axioms equalMassPeriodicFPUTInteractionSafeNonzeroInputs
#print axioms equalMassPeriodicFPUTInteractionPhaseMismatch
#print axioms equalMassPeriodicFPUTInteractionVertexFormula
#print axioms equalMassPeriodicFPUTExactInteractionPictureDerivative

end

end ArchonPhysicsConsumers.Thermalization
