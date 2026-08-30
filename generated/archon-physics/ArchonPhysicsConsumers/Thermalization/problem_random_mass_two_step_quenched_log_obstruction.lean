import ArchonPhysics.RandomMassTwoStepQuenchedLogObstruction

/-!
# Consumer: obstruction to uniform two-step log drift

This consumer records the actual nonpositive logarithmic direction at
`λ = 1/2` and the resulting failure of a direction-uniform positive drift.
The imported projective-stationary interface states the next certificate to
construct; no Lyapunov, EFC, or localization conclusion is claimed.
-/

namespace ArchonPhysicsConsumers.Thermalization

open ArchonPhysics
open ArchonPhysics.RandomMassTwoStepQuenchedLogObstruction

noncomputable section

theorem frozen_iid_uniform_twoStep_log_uniformPos_obstruction :
    independentTwoStepLogDrift (1 / 2 : Real) verticalUnitState ≤ 0 ∧
    ¬(∀ lambda : Real, 0 < lambda → lambda ≤ 1 →
      ∀ state : Fin 2 → Real, state ≠ 0 →
        0 < independentTwoStepLogDrift lambda state) := by
  exact ⟨independentTwoStepLogDrift_half_vertical_nonpos,
    not_forall_independentTwoStepLogDrift_pos⟩

#print axioms halfVerticalTwoStep_log_pair_nonpos
#print axioms independentTwoStepLogDrift_half_vertical_nonpos
#print axioms frozen_iid_uniform_twoStep_log_uniformPos_obstruction

end

end ArchonPhysicsConsumers.Thermalization
