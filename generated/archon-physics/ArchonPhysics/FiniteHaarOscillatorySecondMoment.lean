import ArchonPhysics.FiniteDuhamelPhaseAverage
import ArchonPhysics.FiniteTimeResonanceWeight

/-!
# Finite Haar oscillatory second moments

This module combines the exact finite random-phase selector with the
finite-time oscillatory integral.  A term `j` has a deterministic complex
coefficient, an integer phase-charge vector, and a real frequency mismatch.
The Haar second moment of their oscillatory sum retains every ordered pair
with equal charge.

Equal charge does not imply equal frequency mismatch.  Consequently the
off-diagonal terms retain the cross product
`I(Delta_j,T) * conj (I(Delta_k,T))`; it would be incorrect to replace all of
them by a single `finiteTimeResonanceWeight`.  Only a diagonal term `j = k`
is exactly the usual finite-time resonance weight after division by a
positive observation time.

Everything below is finite-dimensional and exact.  No random-phase
propagation, kinetic limit, or collision-kernel identification is asserted.
-/

namespace ArchonPhysics.FiniteHaarOscillatorySecondMoment

open MeasureTheory
open UnitAddTorus
open ArchonPhysics
open ArchonPhysics.FiniteDuhamelPhaseAverage
open ArchonPhysics.FiniteEnsemblePhaseMoments
open ArchonPhysics.FiniteTimeResonanceWeight
open ArchonPhysics.NonresonantOscillatoryGain
open ArchonPhysics.RandomPhaseMoments

noncomputable section

variable {d J : Type*} [Fintype d] [Fintype J]

/-- The deterministic coefficient of one finite-time Duhamel term. -/
def oscillatoryCoefficient
    (coefficient : J -> Complex) (mismatch : J -> Real)
    (T : Real) (j : J) : Complex :=
  coefficient j * oscillatoryIntegral (mismatch j) T

/-- A finite sum of oscillatory Duhamel coefficients multiplied by their
phase characters. -/
def finiteHaarOscillatorySum
    (coefficient : J -> Complex) (charge : J -> d -> Int)
    (mismatch : J -> Real) (T : Real) (phase : UnitAddTorus d) : Complex :=
  finitePhaseCorrection (oscillatoryCoefficient coefficient mismatch T)
    charge phase

/-- The finite oscillatory sum is continuous in the phase variables. -/
theorem finiteHaarOscillatorySum_continuous
    (coefficient : J -> Complex) (charge : J -> d -> Int)
    (mismatch : J -> Real) (T : Real) :
    Continuous (finiteHaarOscillatorySum coefficient charge mismatch T) := by
  exact finitePhaseCorrection_continuous
    (oscillatoryCoefficient coefficient mismatch T) charge

/-- Exact Haar second moment in coefficient form.  Every ordered pair with
the same phase charge survives, including distinct terms with repeated
charge. -/
theorem integral_finiteHaarOscillatorySum_mul_star_eq_equalChargePairSum
    (coefficient : J -> Complex) (charge : J -> d -> Int)
    (mismatch : J -> Real) (T : Real) :
    (∫ phase : UnitAddTorus d,
      finiteHaarOscillatorySum coefficient charge mismatch T phase *
        starRingEnd Complex
          (finiteHaarOscillatorySum coefficient charge mismatch T phase)
      ∂finitePhaseHaarLaw d) =
      ∑ j, ∑ k,
        if charge j = charge k then
          oscillatoryCoefficient coefficient mismatch T j *
            starRingEnd Complex
              (oscillatoryCoefficient coefficient mismatch T k)
        else 0 := by
  simpa only [finiteHaarOscillatorySum] using
    integral_finitePhaseCorrection_mul_star_eq_equalChargePairSum
      (oscillatoryCoefficient coefficient mismatch T) charge

/-- The same exact identity written literally as the complex embedding of
the squared absolute value. -/
theorem integral_normSq_finiteHaarOscillatorySum_eq_equalChargePairSum
    (coefficient : J -> Complex) (charge : J -> d -> Int)
    (mismatch : J -> Real) (T : Real) :
    (∫ phase : UnitAddTorus d,
      (Complex.normSq
        (finiteHaarOscillatorySum coefficient charge mismatch T phase) :
          Complex)
      ∂finitePhaseHaarLaw d) =
      ∑ j, ∑ k,
        if charge j = charge k then
          oscillatoryCoefficient coefficient mismatch T j *
            starRingEnd Complex
              (oscillatoryCoefficient coefficient mismatch T k)
        else 0 := by
  simpa only [Complex.mul_conj] using
    integral_finiteHaarOscillatorySum_mul_star_eq_equalChargePairSum
      coefficient charge mismatch T

/-- The unnormalized cross-time factor carried by a pair of terms. -/
def oscillatoryCrossProduct (leftMismatch rightMismatch T : Real) : Complex :=
  oscillatoryIntegral leftMismatch T *
    starRingEnd Complex (oscillatoryIntegral rightMismatch T)

/-- Expanded exact pair formula.  In particular, equal-charge off-diagonal
pairs keep both of their, potentially different, mismatches. -/
theorem integral_normSq_finiteHaarOscillatorySum_eq_crossPairSum
    (coefficient : J -> Complex) (charge : J -> d -> Int)
    (mismatch : J -> Real) (T : Real) :
    (∫ phase : UnitAddTorus d,
      (Complex.normSq
        (finiteHaarOscillatorySum coefficient charge mismatch T phase) :
          Complex)
      ∂finitePhaseHaarLaw d) =
      ∑ j, ∑ k,
        if charge j = charge k then
          coefficient j * starRingEnd Complex (coefficient k) *
            oscillatoryCrossProduct (mismatch j) (mismatch k) T
        else 0 := by
  rw [integral_normSq_finiteHaarOscillatorySum_eq_equalChargePairSum]
  apply Finset.sum_congr rfl
  intro j hj
  apply Finset.sum_congr rfl
  intro k hk
  by_cases hcharge : charge j = charge k
  · rw [if_pos hcharge, if_pos hcharge]
    simp only [oscillatoryCoefficient, oscillatoryCrossProduct, map_mul]
    ring
  · rw [if_neg hcharge, if_neg hcharge]

/-- The positive-time normalized cross-resonance factor.  This is generally
complex off the diagonal. -/
def finiteTimeCrossResonanceWeight
    (leftMismatch rightMismatch T : Real) : Complex :=
  if 0 < T then
    oscillatoryCrossProduct leftMismatch rightMismatch T / (T : Complex)
  else 0

@[simp] theorem finiteTimeCrossResonanceWeight_of_nonpos
    {leftMismatch rightMismatch T : Real} (hT : T <= 0) :
    finiteTimeCrossResonanceWeight leftMismatch rightMismatch T = 0 := by
  simp [finiteTimeCrossResonanceWeight, not_lt.mpr hT]

/-- On the diagonal the unnormalized cross product is the complex embedding
of the squared norm of the oscillatory integral. -/
theorem oscillatoryCrossProduct_self (mismatch T : Real) :
    oscillatoryCrossProduct mismatch mismatch T =
      (norm (oscillatoryIntegral mismatch T) ^ 2 : Complex) := by
  rw [oscillatoryCrossProduct, Complex.mul_conj,
    Complex.normSq_eq_norm_sq]
  norm_num

/-- Only the diagonal cross-resonance factor is the existing real
`finiteTimeResonanceWeight`. -/
@[simp] theorem finiteTimeCrossResonanceWeight_self
    (mismatch T : Real) :
    finiteTimeCrossResonanceWeight mismatch mismatch T =
      (finiteTimeResonanceWeight mismatch T : Complex) := by
  by_cases hT : 0 < T
  · rw [finiteTimeCrossResonanceWeight, if_pos hT,
      finiteTimeResonanceWeight, if_pos hT,
      oscillatoryCrossProduct_self]
    norm_cast
  · rw [finiteTimeCrossResonanceWeight, if_neg hT,
      finiteTimeResonanceWeight_of_nonpos (le_of_not_gt hT)]
    norm_num

/-- Positive-time normalized Haar second moment.  The right side remains a
same-charge *pair* sum with cross-resonance weights; it is not a diagonal
sum unless an additional charge-injectivity or cancellation hypothesis is
available. -/
theorem normalized_integral_normSq_eq_equalChargeCrossWeightSum
    (coefficient : J -> Complex) (charge : J -> d -> Int)
    (mismatch : J -> Real) {T : Real} (hT : 0 < T) :
    (1 / (T : Complex)) *
        (∫ phase : UnitAddTorus d,
          (Complex.normSq
            (finiteHaarOscillatorySum coefficient charge mismatch T phase) :
              Complex)
          ∂finitePhaseHaarLaw d) =
      ∑ j, ∑ k,
        if charge j = charge k then
          coefficient j * starRingEnd Complex (coefficient k) *
            finiteTimeCrossResonanceWeight (mismatch j) (mismatch k) T
        else 0 := by
  rw [integral_normSq_finiteHaarOscillatorySum_eq_crossPairSum,
    Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j hj
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro k hk
  by_cases hcharge : charge j = charge k
  · rw [if_pos hcharge, if_pos hcharge,
      finiteTimeCrossResonanceWeight, if_pos hT]
    ring
  · rw [if_neg hcharge, if_neg hcharge]
    ring

omit [Fintype J] in
/-- A single diagonal summand in the normalized pair formula is exactly the
usual real finite-time resonance weight times the coefficient norm square. -/
theorem normalized_diagonal_pair_eq_finiteTimeResonanceWeight
    (coefficient : J -> Complex) (mismatch : J -> Real)
    (j : J) (T : Real) :
    coefficient j * starRingEnd Complex (coefficient j) *
        finiteTimeCrossResonanceWeight (mismatch j) (mismatch j) T =
      ((Complex.normSq (coefficient j) *
        finiteTimeResonanceWeight (mismatch j) T : Real) : Complex) := by
  rw [finiteTimeCrossResonanceWeight_self, Complex.mul_conj,
    Complex.normSq_eq_norm_sq]
  norm_cast

end

end ArchonPhysics.FiniteHaarOscillatorySecondMoment
