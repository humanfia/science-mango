import ArchonPhysics.FourWaveDuhamelFGRBridge

/-!
# Consumer: effective four-wave Duhamel/FGR bridge
-/

namespace ArchonPhysicsConsumers.Thermalization

open ArchonPhysics.FourWaveDuhamelFGRBridge

noncomputable section

theorem problem_four_wave_normalized_duhamel_power_eq_rate
    (vertex : Complex) (mismatch : Real) {time : Real} (htime : 0 < time) :
    Complex.normSq (fourWaveDuhamelCoefficient vertex mismatch time) / time =
      finiteTimeFourWaveRate vertex mismatch time :=
  normSq_fourWaveDuhamelCoefficient_div_time vertex mismatch htime

theorem problem_alpha_fput_effective_vertex_rate_pow_four
    (epsilon : Real) (vertex : Complex) (mismatch time : Real) :
    finiteTimeFourWaveRate
        ((epsilon ^ 2 : Real) * vertex) mismatch time =
      epsilon ^ 4 * finiteTimeFourWaveRate vertex mismatch time :=
  finiteTimeFourWaveRate_epsilon_sq epsilon vertex mismatch time

theorem problem_four_wave_finite_time_entropy_nonnegative
    (vertex : Complex) (mismatch time : Real)
    {n₁ n₂ n₃ n₄ : Real}
    (hn₁ : 0 < n₁) (hn₂ : 0 < n₂)
    (hn₃ : 0 < n₃) (hn₄ : 0 < n₄) :
    0 ≤ ArchonPhysics.FourWaveCollisionAlgebra.fourWaveEntropyProduction
      (finiteTimeFourWaveRate vertex mismatch time) n₁ n₂ n₃ n₄ :=
  fourWaveEntropyProduction_finiteTime_nonneg
    vertex mismatch time hn₁ hn₂ hn₃ hn₄

#print axioms problem_four_wave_normalized_duhamel_power_eq_rate
#print axioms problem_alpha_fput_effective_vertex_rate_pow_four
#print axioms problem_four_wave_finite_time_entropy_nonnegative

end

end ArchonPhysicsConsumers.Thermalization
