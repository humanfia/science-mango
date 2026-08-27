import ArchonPhysics.NormalizedModeCoupling

/-!
# Exact soft-mode scaling of normalized bond legs

For a normalized eigenmode of the mass-weighted harmonic Gram operator, the
sum of squares of its physical bond coefficients is exactly its squared
frequency.  After the complex-amplitude normalization, the corresponding
sum is exactly one half of the frequency.

These finite-volume identities expose the acoustic-edge issue without making
any probabilistic, resonance-density, or kinetic-limit assertion.  In
particular, they do not by themselves decide whether the density of resonant
tuples compensates the soft vertex in the thermodynamic limit.
-/

namespace ArchonPhysics.AcousticVertexScaling

open ArchonPhysics
open HarmonicModes
open ModeCoupling
open NormalizedModeCoupling
open ModalPhaseMismatch

noncomputable section

/-- The squared `l2` norm of the physical bond leg of a normalized mode is its
squared frequency. -/
theorem sum_sq_bondModeCoefficient {N : Nat} [NeZero N]
    (m : Lattice.PositiveMassConfig N) (k : Lattice.Site N) :
    ∑ j, (bondModeCoefficient m j k) ^ 2 = modeFrequencySq m k := by
  classical
  let D := massWeightedDifferenceMatrix m
  let e : Lattice.Configuration N := ⇑(normalModeBasis m k)
  have hgram : massWeightedHarmonicMatrix m = Matrix.transpose D * D := by
    rfl
  have heigen : Matrix.mulVec (massWeightedHarmonicMatrix m) e =
      modeFrequencySq m k • e := by
    exact normalMode_eigenvector m k
  calc
    ∑ j, (bondModeCoefficient m j k) ^ 2 =
        (Matrix.mulVec D e) ⬝ᵥ (Matrix.mulVec D e) := by
      simp only [dotProduct, bondModeCoefficient, D, e, pow_two]
    _ = e ⬝ᵥ Matrix.mulVec (Matrix.transpose D)
          (Matrix.mulVec D e) := by
      exact (Matrix.dotProduct_transpose_mulVec D e
        (Matrix.mulVec D e)).symm
    _ = e ⬝ᵥ Matrix.mulVec (massWeightedHarmonicMatrix m) e := by
      rw [Matrix.mulVec_mulVec, ← hgram]
    _ = e ⬝ᵥ (modeFrequencySq m k • e) := by rw [heigen]
    _ = modeFrequencySq m k * ∑ i, (e i) ^ 2 := by
      simp only [dotProduct, Pi.smul_apply, smul_eq_mul, pow_two]
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i hi
      ring
    _ = modeFrequencySq m k * ‖normalModeBasis m k‖ ^ 2 := by
      rw [EuclideanSpace.real_norm_sq_eq]
    _ = modeFrequencySq m k := by simp

/-- The exact squared `l2` norm after one positive-frequency phonon-amplitude
normalization is `omega / 2`. -/
theorem sum_sq_normalizedBondLeg {N : Nat} [NeZero N]
    (m : Lattice.PositiveMassConfig N) (k : Lattice.Site N)
    (hfrequency : 0 < modeFrequency m k) :
    ∑ j, (bondModeCoefficient m j k * modeAmplitudeNormalization m k) ^ 2 =
      modeFrequency m k / 2 := by
  classical
  have hsqrt_ne : Real.sqrt (2 * modeFrequency m k) ≠ 0 :=
    ne_of_gt (Real.sqrt_pos.2 (mul_pos zero_lt_two hfrequency))
  have hfrequency_ne : modeFrequency m k ≠ 0 := ne_of_gt hfrequency
  calc
    ∑ j, (bondModeCoefficient m j k * modeAmplitudeNormalization m k) ^ 2 =
        modeAmplitudeNormalization m k ^ 2 *
          ∑ j, (bondModeCoefficient m j k) ^ 2 := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro j hj
      ring
    _ = modeAmplitudeNormalization m k ^ 2 * modeFrequencySq m k := by
      rw [sum_sq_bondModeCoefficient]
    _ = (Real.sqrt (2 * modeFrequency m k))⁻¹ ^ 2 *
          (modeFrequency m k) ^ 2 := by
      rw [modeFrequency_sq]
      rfl
    _ = modeFrequency m k / 2 := by
      rw [inv_pow, Real.sq_sqrt (mul_nonneg zero_le_two hfrequency.le)]
      field_simp [hfrequency_ne]

end

end ArchonPhysics.AcousticVertexScaling
