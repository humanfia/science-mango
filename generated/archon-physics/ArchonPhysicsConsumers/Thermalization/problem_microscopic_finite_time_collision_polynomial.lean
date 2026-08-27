import ArchonPhysics.MicroscopicFiniteTimeCollisionPolynomial

/-!
# Consumer: microscopic finite-time collision polynomial

These endpoints lock the force-level FPUT convention: differentiating the
Hamiltonian bond terms `alpha / 3 * x^3` and `beta / 4 * x^4` leaves the
interaction-vertex couplings `alpha` and `beta` used by the three- and
four-wave kernels.
-/

namespace ArchonPhysicsConsumers.Thermalization

open ArchonPhysics
open ArchonPhysics.MicroscopicFiniteTimeCollisionPolynomial

noncomputable section

theorem problem_fputAlphaBetaCollisionPolynomial_forceLevelCouplings
    {N : Nat} [NeZero N]
    (m : Lattice.PositiveMassConfig N) (alpha beta : Real)
    (signThree : Fin 3 → ModalPhaseMismatch.InteractionSign)
    (signFour : Fin 4 → ModalPhaseMismatch.InteractionSign) (T : Real) :
    fputAlphaBetaCollisionPolynomial m alpha beta signThree signFour T =
      threeWaveCollisionPolynomial m alpha signThree T +
        fourWaveCollisionPolynomial m beta signFour T := by
  rfl

theorem problem_fputAlphaBetaCollisionPolynomial_reflectionSymmetric
    {N : Nat} [NeZero N]
    (m : Lattice.PositiveMassConfig N) {alpha beta : Real}
    (signThree : Fin 3 → ModalPhaseMismatch.InteractionSign)
    (signFour : Fin 4 → ModalPhaseMismatch.InteractionSign) (T : Real)
    (halpha : alpha = 0) :
    fputAlphaBetaCollisionPolynomial m alpha beta signThree signFour T =
      fourWaveCollisionPolynomial m beta signFour T :=
  fputAlphaBetaCollisionPolynomial_eq_four_of_alpha_eq_zero
    m signThree signFour T halpha

#print axioms problem_fputAlphaBetaCollisionPolynomial_forceLevelCouplings
#print axioms problem_fputAlphaBetaCollisionPolynomial_reflectionSymmetric

end

end ArchonPhysicsConsumers.Thermalization
