import ArchonPhysics.RandomMassTwoStepAnnealedTransferGrowth

/-!
# Consumer: two-step annealed transfer growth

This consumer exposes the exact independent two-mass quadratic expectation
and its direction-uniform lower bound.  It does not promote annealed second
moments to quenched Lyapunov, EFC, or localization statements.
-/

namespace ArchonPhysicsConsumers.Thermalization

open ArchonPhysics
open ArchonPhysics.RandomMassTwoStepAnnealedTransferGrowth
open ArchonPhysics.RandomMassWeakEnergyTransferGroundwork

noncomputable section

theorem frozen_iid_uniform_twoStep_annealed_Q_formula_and_growth
    {lambda : Real} (hlambda_pos : 0 < lambda) (hlambda_one : lambda ≤ 1)
    (state : Fin 2 → Real) :
    independentTwoStepQuadraticExpectation lambda state =
      meanInvariantQuadratic lambda state +
        (lambda ^ 2 / 75) *
          (state 0 ^ 2 + ((2 - lambda) * state 0 - state 1) ^ 2) +
        (lambda ^ 4 / 5625) * state 0 ^ 2 ∧
    (1 + lambda ^ 2 / 150) * meanInvariantQuadratic lambda state ≤
      independentTwoStepQuadraticExpectation lambda state := by
  exact ⟨independentTwoStepQuadraticExpectation_eq lambda state,
    independentTwoStepQuadraticExpectation_lower
      hlambda_pos hlambda_one state⟩

#print axioms independentTwoStepQuadraticExpectation_eq
#print axioms meanInvariantQuadratic_le_two_mul_stepSquares
#print axioms frozen_iid_uniform_twoStep_annealed_Q_formula_and_growth

end

end ArchonPhysicsConsumers.Thermalization
