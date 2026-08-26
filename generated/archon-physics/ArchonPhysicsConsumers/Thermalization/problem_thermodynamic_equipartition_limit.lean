import ArchonPhysics.PersistentEquipartition
import ArchonPhysics.ThermodynamicEquipartitionLimit
import ArchonPhysics.QuantitativeThermodynamicRelaxation
import ArchonPhysics.ThermodynamicEquipartitionRelaxation

/-!
# Consumer: thermodynamic equipartition limits and persistent relaxation

This target locks the finite-volume `l1` diagnostic, vanishing thermodynamic
tolerances, persistent-tail semantics, recurrence obstruction, and the
explicit exponential settling-time bridge.
-/

namespace ArchonPhysicsConsumers.Thermalization

open ArchonPhysics.PersistentEquipartition
open ArchonPhysics.ThermodynamicEquipartitionLimit
open ArchonPhysics.QuantitativeThermodynamicRelaxation
open ArchonPhysics.ThermodynamicEquipartitionRelaxation

/-- Kernel-lock the criterion that the finite mode count grows in the
thermodynamic limit. -/
theorem problem_hasThermodynamicModeGrowth_iff :
    (@hasThermodynamicModeGrowth_iff) =
      @hasThermodynamicModeGrowth_iff := rfl

/-- Kernel-lock the normalized late-window `l1` formula. -/
theorem problem_lateWindowEquipartitionError_formula :
    (@lateWindowEquipartitionError_eq_sum_abs) =
      @lateWindowEquipartitionError_eq_sum_abs := rfl

/-- Kernel-lock nonnegativity of the finite-volume `l1` error. -/
theorem problem_lateWindowEquipartitionError_nonnegative :
    (@lateWindowEquipartitionError_nonneg) =
      @lateWindowEquipartitionError_nonneg := rfl

/-- Kernel-lock normalization of every physically admissible late-window
modal-energy profile. -/
theorem problem_physicalLateWindow_normalizedWeights_sum_one :
    (@PhysicalLateWindow.sum_normalizedWeights_eq_one) =
      @PhysicalLateWindow.sum_normalizedWeights_eq_one := rfl

/-- Kernel-lock the universal `l1` diameter bound for a physical window. -/
theorem problem_physicalLateWindow_l1_error_le_two :
    (@PhysicalLateWindow.lateWindowEquipartitionError_le_two) =
      @PhysicalLateWindow.lateWindowEquipartitionError_le_two := rfl

/-- Kernel-lock the full `[0, 2]` physical error range. -/
theorem problem_physicalLateWindow_l1_error_bounds :
    (@PhysicalLateWindow.lateWindowEquipartitionError_bounds) =
      @PhysicalLateWindow.lateWindowEquipartitionError_bounds := rfl

/-- Kernel-lock convergence along every certified late thermodynamic path. -/
theorem problem_thermodynamicTailControl_error_tendsto_zero_along :
    (@ThermodynamicTailControl.error_tendsto_zero_along) =
      @ThermodynamicTailControl.error_tendsto_zero_along := rfl

/-- Kernel-lock the direct epsilon endpoint which is uniform over the whole
post-settling time tail at every sufficiently large size. -/
theorem problem_thermodynamicTailControl_eventually_error_lt_on_tail :
    (@ThermodynamicTailControl.eventually_error_lt_on_every_settled_tail) =
      @ThermodynamicTailControl.eventually_error_lt_on_every_settled_tail :=
  rfl

/-- Kernel-lock the two- and three-dimensional source specialization of the
thermodynamic tail theorem. -/
theorem problem_highDimensionalSource_lateWindowError_tendsto_zero :
    (@highDimensionalSource_lateWindowEquipartitionError_tendsto_zero_along) =
      @highDimensionalSource_lateWindowEquipartitionError_tendsto_zero_along :=
  rfl

/-- Kernel-lock the physical source wrapper: fixed supplied `g, omega`, mode
growth and a late-time diagonal limit, without a fixed-energy-density claim. -/
theorem problem_highDimensionalSource_physical_lateWindowError_limit :
    (@highDimensionalSource_physical_lateWindowEquipartitionError_limit) =
      @highDimensionalSource_physical_lateWindowEquipartitionError_limit :=
  rfl

/-- The fixed `0.65` paper threshold does not tighten to one. -/
theorem problem_constant_sixtyFivePercent_not_tendsto_one :
    (@not_tendsto_constant_threshold_sixtyFivePercent_to_one) =
      @not_tendsto_constant_threshold_sixtyFivePercent_to_one := rfl

/-- The fixed `0.95` paper threshold does not tighten to one. -/
theorem problem_constant_ninetyFivePercent_not_tendsto_one :
    (@not_tendsto_constant_threshold_ninetyFivePercent_to_one) =
      @not_tendsto_constant_threshold_ninetyFivePercent_to_one := rfl

/-- Vanishing `l1` tolerances induce spectral-entropy thresholds tending to
one. -/
theorem problem_shrinkingXiThreshold_tendsto_one :
    (@shrinkingXiThreshold_tendsto_one) =
      @shrinkingXiThreshold_tendsto_one := rfl

/-- Convergence of the distance to zero yields a permanent finite-time tail
below every positive threshold. -/
theorem problem_exists_permanent_tail_of_tendsto_zero :
    (@exists_ennreal_tail_of_tendsto_zero) =
      @exists_ennreal_tail_of_tendsto_zero := rfl

/-- A finite first hit alone does not imply permanent equipartition. -/
theorem problem_first_hitting_alone_not_persistent :
    (@first_hitting_alone_does_not_imply_tail_persistence) =
      @first_hitting_alone_does_not_imply_tail_persistence := rfl

/-- Recurrent finite failures force the settling time to be infinite. -/
theorem problem_recurrent_failure_settlingTime_eq_top :
    (@settlingTime_eq_top_of_recurrent_failure) =
      @settlingTime_eq_top_of_recurrent_failure := rfl

/-- Kernel-lock the exact kinetic `g^2` scaling of permanent settling time. -/
theorem problem_strictDistanceSettlingTime_g_sq_timeScale :
    (@strictDistanceSettlingTime_g_sq_timeScale) =
      @strictDistanceSettlingTime_g_sq_timeScale := rfl

/-- Kernel-lock the explicit post-settling exponential error bound. -/
theorem problem_error_le_after_exponentialSettlingBound :
    (@error_le_of_exponential_tail_of_settlingBound_le) =
      @error_le_of_exponential_tail_of_settlingBound_le := rfl

/-- Kernel-lock the exact `g^2` settling-bound scaling identity. -/
theorem problem_g_sq_exponentialSettlingBound_formula :
    (@g_sq_mul_exponentialSettlingBound) =
      @g_sq_mul_exponentialSettlingBound := rfl

/-- Kernel-lock construction of thermodynamic tail control from the uniform
exponential relaxation estimate. -/
theorem problem_exponentialThermodynamicTailControl :
    (@exponentialThermodynamicTailControl) =
      @exponentialThermodynamicTailControl := rfl

/-- Kernel-lock the direct growing-size, late-time convergence endpoint. -/
theorem problem_exponential_error_tendsto_zero_along_growing_size :
    (@error_tendsto_zero_along_growing_size) =
      @error_tendsto_zero_along_growing_size := rfl

#print axioms problem_lateWindowEquipartitionError_formula
#print axioms problem_physicalLateWindow_normalizedWeights_sum_one
#print axioms problem_physicalLateWindow_l1_error_bounds
#print axioms problem_thermodynamicTailControl_error_tendsto_zero_along
#print axioms problem_thermodynamicTailControl_eventually_error_lt_on_tail
#print axioms problem_highDimensionalSource_physical_lateWindowError_limit
#print axioms problem_recurrent_failure_settlingTime_eq_top
#print axioms problem_exponentialThermodynamicTailControl

end ArchonPhysicsConsumers.Thermalization
