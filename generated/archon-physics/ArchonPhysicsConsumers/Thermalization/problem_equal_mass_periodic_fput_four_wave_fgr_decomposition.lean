import ArchonPhysics.EqualMassPeriodicFPUTFourWaveFGRDecomposition

/-!
# Consumer: microscopic alpha-FPUT four-wave FGR decomposition
-/

namespace ArchonPhysicsConsumers.Thermalization

open ArchonPhysics.EqualMassPeriodicFPUTEffectiveFourWaveVertex
open ArchonPhysics.EqualMassPeriodicFPUTFourWaveFGRDecomposition

noncomputable section

theorem problem_actual_alpha_fput_diagram_rate_scales_fourth_power
    (N : Nat) [NeZero N] (alpha : Real)
    (diagram : EffectiveFourWaveDiagram N) (time : Real) :
    effectiveDiagramFiniteTimeRate N alpha diagram time =
      alpha ^ 4 * effectiveDiagramFiniteTimeRate N 1 diagram time :=
  effectiveDiagramFiniteTimeRate_eq_alpha_four_mul_unit
    N alpha diagram time

theorem problem_actual_alpha_fput_fgr_closure_error_is_interference
    (N : Nat) [NeZero N] (alpha : Real) {time : Real}
    (htime : 0 < time) :
    |Complex.normSq (activeFourWaveDuhamelAmplitude N alpha time) / time -
        ∑ diagram : ActiveEffectiveFourWaveDiagram N,
          effectiveDiagramFiniteTimeRate N alpha diagram.1 time| =
      |activeFourWaveInterferencePower N alpha time| / time :=
  abs_normalized_activeFourWavePower_sub_sum_rates N alpha htime

#print axioms problem_actual_alpha_fput_diagram_rate_scales_fourth_power
#print axioms problem_actual_alpha_fput_fgr_closure_error_is_interference

end


end ArchonPhysicsConsumers.Thermalization
