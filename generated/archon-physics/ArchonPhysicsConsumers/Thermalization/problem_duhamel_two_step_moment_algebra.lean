import ArchonPhysics.DuhamelTwoStepMomentAlgebra

/-! Independent consumer for the exact two-correction moment polynomial. -/

namespace ArchonPhysicsConsumers.Thermalization.DuhamelTwoStepMomentAlgebra

open ArchonPhysics.DuhamelSecondMomentAlgebra
open ArchonPhysics.DuhamelTwoStepMomentAlgebra

noncomputable section

/-- Four arbitrary modes consume the pointwise exact identity. -/
theorem fourMode_twoStep_contract
    (z w u : Fin 4 → Complex) (epsilon : Real) :
    ∀ k, Complex.normSq
        (twoStepPerturbedAmplitude epsilon (z k) (w k) (u k)) =
      secondMomentZeroth (z k) +
        epsilon * secondMomentFirst (z k) (w k) +
        epsilon ^ 2 * twoStepSecondCoefficient (z k) (w k) (u k) +
        epsilon ^ 3 * twoStepThirdCoefficient (w k) (u k) +
        epsilon ^ 4 * twoStepFourthCoefficient (u k) := by
  intro k
  exact normSq_twoStepPerturbedAmplitude (z k) (w k) (u k) epsilon

end

end ArchonPhysicsConsumers.Thermalization.DuhamelTwoStepMomentAlgebra
