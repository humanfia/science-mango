import ArchonPhysics.AlphaFPUTEffectiveKineticScaling
import ArchonPhysics.FiniteTimeResonanceWeight
import ArchonPhysics.FourWaveCollisionAlgebra

/-!
# Finite-time Fermi-golden-rule bridge for an effective four-wave vertex

The first alpha-FPUT normal form produces an effective four-wave amplitude.
For one fixed quartet, its first Duhamel coefficient is the effective vertex
times an oscillatory time integral.  This module proves that the squared
coefficient, divided by positive observation time, is exactly the vertex
norm-square times the existing finite-time squared-sinc resonance weight.

It also proves the alpha-FPUT power bookkeeping at the level of the actual
complex coefficient: an `epsilon^2` effective vertex produces an
`epsilon^4` finite-time rate.  These are exact finite-time identities.  No
large-volume limit, delta distribution, random-phase closure, or kinetic
equation is assumed.
-/

namespace ArchonPhysics.FourWaveDuhamelFGRBridge

open ArchonPhysics.FiniteTimeResonanceWeight
open ArchonPhysics.FourWaveCollisionAlgebra
open ArchonPhysics.NonresonantOscillatoryGain

noncomputable section

/-- First Duhamel coefficient of one supplied effective four-wave channel. -/
def fourWaveDuhamelCoefficient
    (vertex : Complex) (mismatch time : Real) : Complex :=
  vertex * oscillatoryIntegral mismatch time

/-- Finite-time golden-rule rate of one supplied effective channel. -/
def finiteTimeFourWaveRate
    (vertex : Complex) (mismatch time : Real) : Real :=
  Complex.normSq vertex * finiteTimeResonanceWeight mismatch time

/-- The rate is nonnegative at every real time, including the chosen zero
extension for nonpositive time. -/
theorem finiteTimeFourWaveRate_nonneg
    (vertex : Complex) (mismatch time : Real) :
    0 ≤ finiteTimeFourWaveRate vertex mismatch time := by
  unfold finiteTimeFourWaveRate
  exact mul_nonneg (Complex.normSq_nonneg vertex)
    (finiteTimeResonanceWeight_nonneg mismatch time)

/-- Exact finite-time FGR identity: normalized Duhamel power equals vertex
power times the squared-sinc resonance weight. -/
theorem normSq_fourWaveDuhamelCoefficient_div_time
    (vertex : Complex) (mismatch : Real) {time : Real} (htime : 0 < time) :
    Complex.normSq (fourWaveDuhamelCoefficient vertex mismatch time) / time =
      finiteTimeFourWaveRate vertex mismatch time := by
  unfold fourWaveDuhamelCoefficient finiteTimeFourWaveRate
    finiteTimeResonanceWeight
  rw [if_pos htime, Complex.normSq_mul]
  simp_rw [Complex.normSq_eq_norm_sq]
  ring

/-- On exact resonance, the rate grows linearly with positive observation
time. -/
theorem finiteTimeFourWaveRate_zeroMismatch
    (vertex : Complex) {time : Real} (htime : 0 < time) :
    finiteTimeFourWaveRate vertex 0 time =
      Complex.normSq vertex * time := by
  unfold finiteTimeFourWaveRate
  rw [finiteTimeResonanceWeight_zero_of_pos htime]

/-- An off-shell mismatch has the usual inverse-gap-square finite-time
bound. -/
theorem finiteTimeFourWaveRate_le_inverseGap
    (vertex : Complex) {mismatch time : Real}
    (hmismatch : mismatch ≠ 0) (htime : 0 < time) :
    finiteTimeFourWaveRate vertex mismatch time ≤
      Complex.normSq vertex * ((2 / |mismatch|) ^ 2 / time) := by
  unfold finiteTimeFourWaveRate
  exact mul_le_mul_of_nonneg_left
    (finiteTimeResonanceWeight_le_inverse_gap hmismatch htime)
    (Complex.normSq_nonneg vertex)

/-- Scaling a complex effective vertex by the real factor `epsilon^2`
scales its finite-time rate by `epsilon^4`. -/
theorem finiteTimeFourWaveRate_epsilon_sq
    (epsilon : Real) (vertex : Complex) (mismatch time : Real) :
    finiteTimeFourWaveRate
        ((epsilon ^ 2 : Real) * vertex) mismatch time =
      epsilon ^ 4 * finiteTimeFourWaveRate vertex mismatch time := by
  unfold finiteTimeFourWaveRate
  rw [Complex.normSq_mul, Complex.normSq_ofReal]
  ring

/-- The same exact `epsilon^4` factor multiplies the weak collision slope of
any linear observable. -/
theorem fourWaveLinearObservableSlope_epsilon_sq_vertex
    (epsilon : Real) (vertex : Complex) (mismatch time : Real)
    (gamma₁ gamma₂ gamma₃ gamma₄ n₁ n₂ n₃ n₄ : Real) :
    fourWaveLinearObservableSlope gamma₁ gamma₂ gamma₃ gamma₄
        (finiteTimeFourWaveRate
          ((epsilon ^ 2 : Real) * vertex) mismatch time)
        n₁ n₂ n₃ n₄ =
      epsilon ^ 4 *
        fourWaveLinearObservableSlope gamma₁ gamma₂ gamma₃ gamma₄
          (finiteTimeFourWaveRate vertex mismatch time)
          n₁ n₂ n₃ n₄ := by
  rw [finiteTimeFourWaveRate_epsilon_sq]
  unfold fourWaveLinearObservableSlope
  ring

/-- Nonnegative finite-time rate gives the channelwise four-wave entropy
production sign as soon as all four actions are positive. -/
theorem fourWaveEntropyProduction_finiteTime_nonneg
    (vertex : Complex) (mismatch time : Real)
    {n₁ n₂ n₃ n₄ : Real}
    (hn₁ : 0 < n₁) (hn₂ : 0 < n₂)
    (hn₃ : 0 < n₃) (hn₄ : 0 < n₄) :
    0 ≤ fourWaveEntropyProduction
      (finiteTimeFourWaveRate vertex mismatch time) n₁ n₂ n₃ n₄ :=
  fourWaveEntropyProduction_nonneg
    (finiteTimeFourWaveRate_nonneg vertex mismatch time)
    hn₁ hn₂ hn₃ hn₄

end

end ArchonPhysics.FourWaveDuhamelFGRBridge
