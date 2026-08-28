import ArchonPhysics.FreeFPUTChargeFiberAggregation

/-!
# Decay of the zero-charge free FPUT fiber

The exact finite-Haar first-Picard formula groups all terms carrying the same
integer phase charge into one coherent coefficient.  This module isolates the
zero-charge fiber.  Its input phase carries zero frequency, so its
interaction-picture mismatch is exactly the observed output frequency.

Consequently, at a fixed strictly positive output frequency, the normalized
finite-time resonance weight of this fiber is bounded by

`4 / (omega_observed ^ 2 * T)`.

The same bound controls the complete coherent fiber contribution, including
all cross terms inside that fiber.  These are exact finite-volume statements.
They provide no lower bound on the smallest output frequency as the volume
grows (the acoustic low-frequency sector remains a risk), and assert neither
nonlinear random-phase propagation nor a kinetic limit.
-/

namespace ArchonPhysics.FreeFPUTZeroChargeFiberDecay

open ArchonPhysics
open ArchonPhysics.FiniteTimeResonanceWeight
open ArchonPhysics.FreeFPUTChargeFiberAggregation
open ArchonPhysics.FreeFPUTMismatchPhaseExpansion

noncomputable section

/-- The coherent coefficient formed by all freely evaluated quadratic terms
whose integer phase charge is zero. -/
def zeroChargeCoherentFiberCoefficient
    {N : Nat} [NeZero N]
    (coupling : Complex) (m : Lattice.PositiveMassConfig N)
    (observed : Lattice.Site N) (radius : Lattice.Site N → Real) : Complex :=
  freeQuadraticChargeFiberCoefficient coupling m observed radius
    (0 : Lattice.Site N → Int)

/-- The real, normalized finite-time contribution of the complete coherent
zero-charge fiber. -/
def zeroChargeFiberContribution
    {N : Nat} [NeZero N]
    (coupling : Complex) (m : Lattice.PositiveMassConfig N)
    (observed : Lattice.Site N)
    (radius frequency : Lattice.Site N → Real) (T : Real) : Real :=
  Complex.normSq
      (zeroChargeCoherentFiberCoefficient coupling m observed radius) *
    finiteTimeResonanceWeight
      (outputChargeMismatch (frequency observed)
        (0 : Lattice.Site N → Int) frequency) T

/-- A zero phase charge carries zero input frequency. -/
@[simp] theorem chargeFrequency_zero
    {d : Type*} [Fintype d] (frequency : d → Real) :
    chargeFrequency (0 : d → Int) frequency = 0 := by
  simp [chargeFrequency]

/-- The interaction-picture mismatch of the zero-charge fiber is exactly the
observed output frequency. -/
@[simp] theorem outputChargeMismatch_zero
    {d : Type*} [Fintype d] (outputFrequency : Real)
    (frequency : d → Real) :
    outputChargeMismatch outputFrequency (0 : d → Int) frequency =
      outputFrequency := by
  simp [outputChargeMismatch]

/-- The zero-charge term occurring in the complex-valued charge-fiber sum is
the complex embedding of `zeroChargeFiberContribution`. -/
theorem zeroChargeFiberSummand_eq_coe_contribution
    {N : Nat} [NeZero N]
    (coupling : Complex) (m : Lattice.PositiveMassConfig N)
    (observed : Lattice.Site N)
    (radius frequency : Lattice.Site N → Real) (T : Real) :
    (Complex.normSq
        (freeQuadraticChargeFiberCoefficient coupling m observed radius
          (0 : Lattice.Site N → Int)) : Complex) *
        (finiteTimeResonanceWeight
          (outputChargeMismatch (frequency observed)
            (0 : Lattice.Site N → Int) frequency) T : Complex) =
      (zeroChargeFiberContribution
        coupling m observed radius frequency T : Complex) := by
  simp [zeroChargeFiberContribution, zeroChargeCoherentFiberCoefficient]

/-- The zero-charge resonance weight obeys the existing inverse-gap bound at
a nonzero observed output frequency. -/
theorem zeroChargeResonanceWeight_le_inverseGap
    {N : Nat} [NeZero N]
    (observed : Lattice.Site N) (frequency : Lattice.Site N → Real)
    {T : Real} (hfrequency : frequency observed ≠ 0) (hT : 0 < T) :
    finiteTimeResonanceWeight
        (outputChargeMismatch (frequency observed)
          (0 : Lattice.Site N → Int) frequency) T ≤
      (2 / |frequency observed|) ^ 2 / T := by
  rw [outputChargeMismatch_zero]
  exact finiteTimeResonanceWeight_le_inverse_gap hfrequency hT

/-- Explicit positive-frequency form of the inverse-gap estimate. -/
theorem zeroChargeResonanceWeight_le_four_div_sq_mul_time
    {N : Nat} [NeZero N]
    (observed : Lattice.Site N) (frequency : Lattice.Site N → Real)
    {T : Real} (hfrequency : 0 < frequency observed) (hT : 0 < T) :
    finiteTimeResonanceWeight
        (outputChargeMismatch (frequency observed)
          (0 : Lattice.Site N → Int) frequency) T ≤
      4 / (frequency observed ^ 2 * T) := by
  calc
    finiteTimeResonanceWeight
        (outputChargeMismatch (frequency observed)
          (0 : Lattice.Site N → Int) frequency) T ≤
        (2 / |frequency observed|) ^ 2 / T :=
      zeroChargeResonanceWeight_le_inverseGap observed frequency
        hfrequency.ne' hT
    _ = 4 / (frequency observed ^ 2 * T) := by
      rw [abs_of_pos hfrequency]
      field_simp
      ring

/-- The coherent zero-charge contribution is nonnegative. -/
theorem zeroChargeFiberContribution_nonneg
    {N : Nat} [NeZero N]
    (coupling : Complex) (m : Lattice.PositiveMassConfig N)
    (observed : Lattice.Site N)
    (radius frequency : Lattice.Site N → Real) (T : Real) :
    0 ≤ zeroChargeFiberContribution
      coupling m observed radius frequency T := by
  exact mul_nonneg (Complex.normSq_nonneg _)
    (finiteTimeResonanceWeight_nonneg _ _)

/-- The full coherent zero-charge contribution, including all cross terms in
the fiber, decays like `T⁻¹` at fixed positive output frequency. -/
theorem zeroChargeFiberContribution_le_four_div_sq_mul_time
    {N : Nat} [NeZero N]
    (coupling : Complex) (m : Lattice.PositiveMassConfig N)
    (observed : Lattice.Site N)
    (radius frequency : Lattice.Site N → Real) {T : Real}
    (hfrequency : 0 < frequency observed) (hT : 0 < T) :
    zeroChargeFiberContribution coupling m observed radius frequency T ≤
      Complex.normSq
          (zeroChargeCoherentFiberCoefficient coupling m observed radius) *
        (4 / (frequency observed ^ 2 * T)) := by
  unfold zeroChargeFiberContribution
  exact mul_le_mul_of_nonneg_left
    (zeroChargeResonanceWeight_le_four_div_sq_mul_time
      observed frequency hfrequency hT)
    (Complex.normSq_nonneg _)

/-- Absolute-value version of the coherent zero-charge fiber bound. -/
theorem abs_zeroChargeFiberContribution_le_four_div_sq_mul_time
    {N : Nat} [NeZero N]
    (coupling : Complex) (m : Lattice.PositiveMassConfig N)
    (observed : Lattice.Site N)
    (radius frequency : Lattice.Site N → Real) {T : Real}
    (hfrequency : 0 < frequency observed) (hT : 0 < T) :
    |zeroChargeFiberContribution coupling m observed radius frequency T| ≤
      Complex.normSq
          (zeroChargeCoherentFiberCoefficient coupling m observed radius) *
        (4 / (frequency observed ^ 2 * T)) := by
  rw [abs_of_nonneg (zeroChargeFiberContribution_nonneg
    coupling m observed radius frequency T)]
  exact zeroChargeFiberContribution_le_four_div_sq_mul_time
    coupling m observed radius frequency hfrequency hT

/-- Norm version of the coherent zero-charge fiber bound. -/
theorem norm_zeroChargeFiberContribution_le_four_div_sq_mul_time
    {N : Nat} [NeZero N]
    (coupling : Complex) (m : Lattice.PositiveMassConfig N)
    (observed : Lattice.Site N)
    (radius frequency : Lattice.Site N → Real) {T : Real}
    (hfrequency : 0 < frequency observed) (hT : 0 < T) :
    ‖zeroChargeFiberContribution coupling m observed radius frequency T‖ ≤
      Complex.normSq
          (zeroChargeCoherentFiberCoefficient coupling m observed radius) *
        (4 / (frequency observed ^ 2 * T)) := by
  simpa only [Real.norm_eq_abs] using
    abs_zeroChargeFiberContribution_le_four_div_sq_mul_time
      coupling m observed radius frequency hfrequency hT

end

end ArchonPhysics.FreeFPUTZeroChargeFiberDecay
