import ArchonPhysics.EqualMassPeriodicFPUTEffectiveFourWaveVertex
import ArchonPhysics.FourWaveDuhamelFGRBridge

/-!
# Equal-mass alpha-FPUT: exact four-wave FGR and interference decomposition

The two-vertex normal form supplies an explicit effective coefficient and a
literal four-wave mismatch for every active finite-volume diagram.  This
module feeds those microscopic objects into the finite-time FGR identity.

For a sum of diagrams, squared amplitudes are not silently replaced by a sum
of squared amplitudes.  Instead, the exact off-diagonal interference power is
defined and retained.  Consequently the random-phase/diagram-cancellation
input needed later is exposed as one quantitative remainder, rather than
being hidden in a kinetic-equation axiom.

No probabilistic cancellation or thermodynamic/weak-coupling limit is
asserted here.
-/

namespace ArchonPhysics.EqualMassPeriodicFPUTFourWaveFGRDecomposition

open scoped BigOperators

open ArchonPhysics.EqualMassPeriodicFPUTEffectiveFourWaveVertex
open ArchonPhysics.FourWaveDuhamelFGRBridge

noncomputable section

/-- Literal first Duhamel coefficient of one effective alpha-FPUT four-wave
diagram. -/
def effectiveDiagramDuhamelCoefficient
    (N : Nat) [NeZero N] (alpha : Real)
    (diagram : EffectiveFourWaveDiagram N) (time : Real) : Complex :=
  fourWaveDuhamelCoefficient
    (effectiveFourWaveCoefficient N alpha diagram)
    (totalFourWaveMismatch diagram) time

/-- Finite-time FGR rate associated with the same microscopic diagram. -/
def effectiveDiagramFiniteTimeRate
    (N : Nat) [NeZero N] (alpha : Real)
    (diagram : EffectiveFourWaveDiagram N) (time : Real) : Real :=
  finiteTimeFourWaveRate
    (effectiveFourWaveCoefficient N alpha diagram)
    (totalFourWaveMismatch diagram) time

/-- One effective term in the nested normal form is exactly the diagram
Duhamel coefficient used by the FGR bridge. -/
theorem effectiveDiagramDuhamelCoefficient_eq
    (N : Nat) [NeZero N] (alpha : Real)
    (diagram : EffectiveFourWaveDiagram N) (time : Real) :
    effectiveDiagramDuhamelCoefficient N alpha diagram time =
      effectiveFourWaveCoefficient N alpha diagram *
        ArchonPhysics.NonresonantOscillatoryGain.oscillatoryIntegral
          (totalFourWaveMismatch diagram) time := rfl

/-- Per diagram, normalized power is the finite-time FGR rate, with no
statistical assumption. -/
theorem normSq_effectiveDiagramDuhamelCoefficient_div_time
    (N : Nat) [NeZero N] (alpha : Real)
    (diagram : EffectiveFourWaveDiagram N) {time : Real}
    (htime : 0 < time) :
    Complex.normSq
        (effectiveDiagramDuhamelCoefficient N alpha diagram time) / time =
      effectiveDiagramFiniteTimeRate N alpha diagram time := by
  exact normSq_fourWaveDuhamelCoefficient_div_time
    (effectiveFourWaveCoefficient N alpha diagram)
    (totalFourWaveMismatch diagram) htime

/-- The actual two-vertex alpha-FPUT rate carries exactly four powers of the
microscopic cubic coupling. -/
theorem effectiveDiagramFiniteTimeRate_eq_alpha_four_mul_unit
    (N : Nat) [NeZero N] (alpha : Real)
    (diagram : EffectiveFourWaveDiagram N) (time : Real) :
    effectiveDiagramFiniteTimeRate N alpha diagram time =
      alpha ^ 4 * effectiveDiagramFiniteTimeRate N 1 diagram time := by
  unfold effectiveDiagramFiniteTimeRate
  rw [effectiveFourWaveCoefficient_eq_alpha_sq_mul_unit]
  have hscale :
      (alpha : Complex) ^ 2 * effectiveFourWaveCoefficient N 1 diagram =
        ((alpha ^ 2 : Real) : Complex) *
          effectiveFourWaveCoefficient N 1 diagram := by
    norm_cast
  rw [hscale]
  exact finiteTimeFourWaveRate_epsilon_sq alpha
    (effectiveFourWaveCoefficient N 1 diagram)
    (totalFourWaveMismatch diagram) time

/-- A zero external leg kills both the microscopic coefficient and its FGR
rate. -/
theorem effectiveDiagramFiniteTimeRate_eq_zero_of_external_zero
    (N : Nat) [NeZero N] (alpha : Real)
    (diagram : EffectiveFourWaveDiagram N) (time : Real)
    (hsupported : IsTwoVertexMomentumSupported diagram)
    (hzero : ∃ slot : Fin 4, totalFourWaveModes diagram slot = 0) :
    effectiveDiagramFiniteTimeRate N alpha diagram time = 0 := by
  unfold effectiveDiagramFiniteTimeRate
  rw [effectiveFourWaveCoefficient_eq_zero_of_external_zero
    N alpha diagram hsupported hzero]
  simp [finiteTimeFourWaveRate]

/-- Sum of all active microscopic four-wave Duhamel coefficients. -/
def activeFourWaveDuhamelAmplitude
    (N : Nat) [NeZero N] (alpha time : Real) : Complex :=
  ∑ diagram : ActiveEffectiveFourWaveDiagram N,
    effectiveDiagramDuhamelCoefficient N alpha diagram.1 time

/-- Sum of the diagonal powers, before dividing by observation time. -/
def activeFourWaveDiagonalPower
    (N : Nat) [NeZero N] (alpha time : Real) : Real :=
  ∑ diagram : ActiveEffectiveFourWaveDiagram N,
    Complex.normSq
      (effectiveDiagramDuhamelCoefficient N alpha diagram.1 time)

/-- Exact off-diagonal interference power.  This is the finite-volume object
which a quantitative RPA/diagram-cancellation theorem must control. -/
def activeFourWaveInterferencePower
    (N : Nat) [NeZero N] (alpha time : Real) : Real :=
  Complex.normSq (activeFourWaveDuhamelAmplitude N alpha time) -
    activeFourWaveDiagonalPower N alpha time

/-- The effective term already extracted from the Hamiltonian is precisely
the active Duhamel amplitude defined above. -/
theorem activeFiniteEffectiveInteractionSum_eq_activeFourWaveDuhamelAmplitude
    (N : Nat) [NeZero N] (alpha time : Real) :
    ArchonPhysics.FiniteNestedNormalFormExtraction.finiteEffectiveInteractionSum
        (activeTwoVertexNumerator N alpha)
        (activeOuterThreeWaveMismatch N)
        (activeInnerHomologicalDivisor N) time =
      activeFourWaveDuhamelAmplitude N alpha time := by
  rw [activeFiniteEffectiveInteractionSum_eq_fourWaveVertexSum]
  rfl

/-- Total power is diagonal power plus the exact interference correction. -/
theorem normSq_activeFourWaveDuhamelAmplitude_eq_diagonal_add_interference
    (N : Nat) [NeZero N] (alpha time : Real) :
    Complex.normSq (activeFourWaveDuhamelAmplitude N alpha time) =
      activeFourWaveDiagonalPower N alpha time +
        activeFourWaveInterferencePower N alpha time := by
  unfold activeFourWaveInterferencePower
  ring

/-- After division by positive time, the diagonal contribution is exactly
the sum of the microscopic finite-time FGR rates. -/
theorem activeFourWaveDiagonalPower_div_time_eq_sum_rates
    (N : Nat) [NeZero N] (alpha : Real) {time : Real}
    (htime : 0 < time) :
    activeFourWaveDiagonalPower N alpha time / time =
      ∑ diagram : ActiveEffectiveFourWaveDiagram N,
        effectiveDiagramFiniteTimeRate N alpha diagram.1 time := by
  unfold activeFourWaveDiagonalPower
  rw [Finset.sum_div]
  apply Finset.sum_congr rfl
  intro diagram _hdiagram
  exact normSq_effectiveDiagramDuhamelCoefficient_div_time
    N alpha diagram.1 htime

/-- Exact many-diagram closure identity.  The sole difference between total
normalized power and the diagonal FGR sum is the displayed interference
remainder. -/
theorem normalized_activeFourWavePower_eq_sum_rates_add_interference
    (N : Nat) [NeZero N] (alpha : Real) {time : Real}
    (htime : 0 < time) :
    Complex.normSq (activeFourWaveDuhamelAmplitude N alpha time) / time =
      (∑ diagram : ActiveEffectiveFourWaveDiagram N,
        effectiveDiagramFiniteTimeRate N alpha diagram.1 time) +
      activeFourWaveInterferencePower N alpha time / time := by
  rw [normSq_activeFourWaveDuhamelAmplitude_eq_diagonal_add_interference]
  rw [add_div, activeFourWaveDiagonalPower_div_time_eq_sum_rates
    N alpha htime]

/-- Quantitative RPA has an exact target: bounding normalized interference
is equivalent to bounding the error in the diagonal FGR closure. -/
theorem abs_normalized_activeFourWavePower_sub_sum_rates
    (N : Nat) [NeZero N] (alpha : Real) {time : Real}
    (htime : 0 < time) :
    |Complex.normSq (activeFourWaveDuhamelAmplitude N alpha time) / time -
        ∑ diagram : ActiveEffectiveFourWaveDiagram N,
          effectiveDiagramFiniteTimeRate N alpha diagram.1 time| =
      |activeFourWaveInterferencePower N alpha time| / time := by
  rw [normalized_activeFourWavePower_eq_sum_rates_add_interference
    N alpha htime]
  ring_nf
  rw [abs_mul, abs_inv, abs_of_pos htime]
  ring

end

end ArchonPhysics.EqualMassPeriodicFPUTFourWaveFGRDecomposition
