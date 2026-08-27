import ArchonPhysics.PaperXiHalfNotEquipartition

/-!
# Consumer: paper Xi half-threshold is not full equipartition

This kernel-locks a static two-mode diagnostic counterexample.  It makes no
claim about which profiles are visited by a particular microscopic orbit.
-/

namespace ArchonPhysicsConsumers.Thermalization

open ArchonPhysics.EquipartitionEntropy
open ArchonPhysics.PaperSpectralEntropyCriterion
open ArchonPhysics.PaperXiHalfNotEquipartition

noncomputable section

theorem problem_paperXi_half_not_fullMode_equipartition :
    paperXi energy monitored = 1 / 2 ∧
      l1Distance (normalizedWeights energy)
        (uniformWeights : Fin 2 -> Real) = 1 / 2 :=
  exists_paperXi_half_with_fullMode_error_half

#print axioms problem_paperXi_half_not_fullMode_equipartition

end

end ArchonPhysicsConsumers.Thermalization
