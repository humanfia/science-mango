import ArchonPhysics.ModalPhaseMismatch

/-!
# Complex amplitudes for positive-frequency normal modes

Wave-kinetic Duhamel expansions are written in complex normal-mode
amplitudes.  This module supplies the exact algebraic bridge from a real modal
coordinate `Q` and momentum `P` at positive frequency `omega`:

`a = (omega * Q + i * P) / sqrt (2 * omega)`.

It proves reconstruction of the real and imaginary components, the harmonic
energy identity, and the exact derivative formula.  The zero-frequency
translation mode is deliberately excluded by an explicit `0 < omega`
hypothesis.  No random measurable ordering or kinetic approximation is used.
-/

namespace ArchonPhysics.ComplexModeAmplitude

open ArchonPhysics
open HarmonicModes
open ModalPhaseMismatch

noncomputable section

/-- Complex wave amplitude associated with one positive-frequency real mode. -/
def complexModeAmplitude (omega Q P : Real) : Complex :=
  ((omega * Q : Real) + (P : Complex) * Complex.I) /
    Real.sqrt (2 * omega)

@[simp] theorem complexModeAmplitude_re (omega Q P : Real) :
    (complexModeAmplitude omega Q P).re =
      omega * Q / Real.sqrt (2 * omega) := by
  unfold complexModeAmplitude
  rw [Complex.div_ofReal_re]
  simp

@[simp] theorem complexModeAmplitude_im (omega Q P : Real) :
    (complexModeAmplitude omega Q P).im =
      P / Real.sqrt (2 * omega) := by
  unfold complexModeAmplitude
  rw [Complex.div_ofReal_im]
  simp

/-- The momentum is recovered from the imaginary component. -/
theorem sqrt_two_mul_frequency_mul_im_eq_momentum {omega Q P : Real}
    (homega : 0 < omega) :
    Real.sqrt (2 * omega) * (complexModeAmplitude omega Q P).im = P := by
  rw [complexModeAmplitude_im]
  exact mul_div_cancel₀ P (Real.sqrt_ne_zero'.mpr (mul_pos zero_lt_two homega))

/-- The coordinate is recovered from the real component. -/
theorem sqrt_two_mul_frequency_mul_re_eq_frequency_mul_coordinate
    {omega Q P : Real} (homega : 0 < omega) :
    Real.sqrt (2 * omega) * (complexModeAmplitude omega Q P).re = omega * Q := by
  rw [complexModeAmplitude_re]
  exact mul_div_cancel₀ (omega * Q)
    (Real.sqrt_ne_zero'.mpr (mul_pos zero_lt_two homega))

/-- Wave action times frequency equals the real harmonic modal energy. -/
theorem frequency_mul_normSq_eq_modalEnergy {omega Q P : Real}
    (homega : 0 < omega) :
    omega * Complex.normSq (complexModeAmplitude omega Q P) =
      HarmonicModes.modalEnergy (omega ^ 2) Q P := by
  have hsqrt : (Real.sqrt (2 * omega)) ^ 2 = 2 * omega :=
    Real.sq_sqrt (mul_pos zero_lt_two homega).le
  unfold complexModeAmplitude HarmonicModes.modalEnergy
  rw [Complex.normSq_div, Complex.normSq_add_mul_I,
    Complex.normSq_ofReal]
  rw [show Real.sqrt (2 * omega) * Real.sqrt (2 * omega) = 2 * omega by
    simpa [pow_two] using hsqrt]
  field_simp [homega.ne']
  ring

/-- Exact derivative of the complex-amplitude transform. -/
theorem hasDerivAt_complexModeAmplitude {omega : Real}
    {Q P : Real → Real} {Qdot Pdot t : Real}
    (hQ : HasDerivAt Q Qdot t) (hP : HasDerivAt P Pdot t) :
    HasDerivAt (fun s ↦ complexModeAmplitude omega (Q s) (P s))
      (((omega * Qdot : Real) + (Pdot : Complex) * Complex.I) /
        Real.sqrt (2 * omega)) t := by
  simpa [complexModeAmplitude] using
    (((hQ.const_mul omega).ofReal_comp.add
      ((hP.ofReal_comp).mul_const Complex.I)).div_const
        (Real.sqrt (2 * omega) : Complex))

/-- For the free harmonic oscillator, the complex amplitude rotates at frequency `omega`. -/
theorem hasDerivAt_complexModeAmplitude_harmonic {omega : Real}
    {Q P : Real → Real} {t : Real}
    (hQ : HasDerivAt Q (P t) t)
    (hP : HasDerivAt P (-(omega ^ 2) * Q t) t) :
    HasDerivAt (fun s ↦ complexModeAmplitude omega (Q s) (P s))
      ((-Complex.I * omega) * complexModeAmplitude omega (Q t) (P t)) t := by
  convert hasDerivAt_complexModeAmplitude (omega := omega) hQ hP using 1
  have hnum :
      ((omega * P t : Real) +
          ((-(omega ^ 2) * Q t : Real) : Complex) * Complex.I) =
        (-Complex.I * omega) *
          ((omega * Q t : Real) + (P t : Complex) * Complex.I) := by
    push_cast
    ring_nf
    simp
  unfold complexModeAmplitude
  rw [hnum]
  ring

/-- Complex amplitude of one selected random-mass normal mode. -/
def latticeModeAmplitude {N : Nat} [NeZero N]
    (m : Lattice.PositiveMassConfig N) (k : Lattice.Site N) (Q P : Real) : Complex :=
  complexModeAmplitude (modeFrequency m k) Q P

/-- The selected positive mode has exactly the existing real modal energy. -/
theorem latticeModeAmplitude_energy {N : Nat} [NeZero N]
    (m : Lattice.PositiveMassConfig N) (k : Lattice.Site N) (Q P : Real)
    (hfrequency : 0 < modeFrequency m k) :
    modeFrequency m k * Complex.normSq (latticeModeAmplitude m k Q P) =
      HarmonicModes.modalEnergy (modeFrequencySq m k) Q P := by
  unfold latticeModeAmplitude
  rw [← modeFrequency_sq m k]
  exact frequency_mul_normSq_eq_modalEnergy hfrequency

end

end ArchonPhysics.ComplexModeAmplitude
