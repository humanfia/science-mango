import ArchonPhysics.FinitePhaseMonomials
import ArchonPhysics.InteractionPictureDuhamel

/-!
# Complex Fourier oscillator branches

Fourier coefficients of a real lattice trajectory are complex even before
the positive/negative frequency splitting.  This module performs that split
directly for a complex forced oscillator

`Q' = P`, `P' = -omega^2 Q + R`.

For a branch sign `sigma` equal to `+1` or `-1`, the amplitude

`a_sigma = (omega Q + sigma i P) / sqrt(2 omega)`

has free drift `-sigma i omega a_sigma` and forcing
`sigma i R / sqrt(2 omega)`.  Rotating by `exp(sigma i omega t)` removes the
free drift exactly.  These identities are the model-independent algebra used
to turn the equal-mass alpha-FPUT Fourier Hamilton equations into the
quadratic interaction-picture equation.
-/

namespace ArchonPhysics.ComplexFourierBranchAmplitude

open ArchonPhysics.FinitePhaseMonomials
open ArchonPhysics.InteractionPictureDuhamel
open ArchonPhysics.PhaseRenormalization

noncomputable section

/-- Real value `+1` on the positive-frequency branch and `-1` on the
negative-frequency branch. -/
def phaseSignReal (sign : PhaseSign) : Real := sign.exponent

@[simp] theorem phaseSignReal_phase : phaseSignReal .phase = 1 := by
  simp [phaseSignReal]

@[simp] theorem phaseSignReal_conjugate : phaseSignReal .conjugate = -1 := by
  simp [phaseSignReal]

/-- One signed complex Fourier oscillator amplitude. -/
def complexFourierBranchAmplitude
    (omega : Real) (sign : PhaseSign) (Q P : Complex) : Complex :=
  ((omega : Complex) * Q +
      (phaseSignReal sign : Complex) * Complex.I * P) /
    Real.sqrt (2 * omega)

/-- Complex forcing in the signed branch equation. -/
def complexFourierBranchSource
    (omega : Real) (sign : PhaseSign) (R : Complex) : Complex :=
  (phaseSignReal sign : Complex) * Complex.I * R /
    Real.sqrt (2 * omega)

/-- The two signed amplitudes reconstruct the complex Fourier coordinate. -/
theorem coordinate_eq_branch_sum_div_sqrt
    {omega : Real} (homega : 0 < omega) (Q P : Complex) :
    Q =
      (complexFourierBranchAmplitude omega .phase Q P +
        complexFourierBranchAmplitude omega .conjugate Q P) /
          Real.sqrt (2 * omega) := by
  have hsqrt : Real.sqrt (2 * omega) ≠ 0 :=
    Real.sqrt_ne_zero'.mpr (mul_pos zero_lt_two homega)
  have hsqrtSq : (Real.sqrt (2 * omega) : Complex) ^ 2 =
      (2 * omega : Real) := by
    norm_cast
    exact Real.sq_sqrt (mul_pos zero_lt_two homega).le
  simp only [complexFourierBranchAmplitude, phaseSignReal_phase,
    phaseSignReal_conjugate]
  push_cast
  field_simp [hsqrt]
  rw [hsqrtSq]
  field_simp [homega.ne']
  push_cast
  ring

/-- Exact derivative of a signed complex Fourier amplitude. -/
theorem hasDerivAt_complexFourierBranchAmplitude
    {omega : Real} (sign : PhaseSign)
    {Q P : Real -> Complex} {Qdot Pdot : Complex} {time : Real}
    (hQ : HasDerivAt Q Qdot time) (hP : HasDerivAt P Pdot time) :
    HasDerivAt
      (fun s => complexFourierBranchAmplitude omega sign (Q s) (P s))
      (((omega : Complex) * Qdot +
          (phaseSignReal sign : Complex) * Complex.I * Pdot) /
        Real.sqrt (2 * omega)) time := by
  have hnumerator :=
    (hQ.const_smul (omega : Complex)).add
      (hP.const_smul
        ((phaseSignReal sign : Complex) * Complex.I))
  have hscaled := hnumerator.const_smul
    ((Real.sqrt (2 * omega) : Complex)⁻¹)
  refine (hscaled.congr_of_eventuallyEq ?_).congr_deriv ?_
  · filter_upwards with s
    simp only [Pi.add_apply, Pi.smul_apply, complexFourierBranchAmplitude,
      smul_eq_mul, div_eq_mul_inv]
    ring
  · simp only [smul_eq_mul, div_eq_mul_inv]
    ring

/-- The complex forced oscillator becomes the signed free rotation plus the
displayed signed source. -/
theorem hasDerivAt_complexFourierBranchAmplitude_forced
    {omega : Real} (homega : 0 < omega) (sign : PhaseSign)
    {Q P R : Real -> Complex} {time : Real}
    (hQ : HasDerivAt Q (P time) time)
    (hP : HasDerivAt P
      (-(omega ^ 2 : Real) * Q time + R time) time) :
    HasDerivAt
      (fun s => complexFourierBranchAmplitude omega sign (Q s) (P s))
      (complexFourierBranchSource omega sign (R time) -
        (Complex.I * (phaseSignReal sign * omega : Real)) *
          complexFourierBranchAmplitude omega sign (Q time) (P time)) time := by
  have hsqrt : Real.sqrt (2 * omega) ≠ 0 :=
    Real.sqrt_ne_zero'.mpr (mul_pos zero_lt_two homega)
  convert hasDerivAt_complexFourierBranchAmplitude
    (omega := omega) sign hQ hP using 1
  cases sign <;>
    simp only [complexFourierBranchSource, complexFourierBranchAmplitude,
      phaseSignReal_phase, phaseSignReal_conjugate] <;>
    push_cast <;>
    field_simp [hsqrt] <;>
    ring_nf <;>
    simp

/-- Signed interaction-picture amplitude. -/
def complexFourierInteractionBranch
    (omega : Real) (sign : PhaseSign)
    (Q P : Real -> Complex) (time : Real) : Complex :=
  phaseRenormalize (phaseSignReal sign * omega * time)
    (complexFourierBranchAmplitude omega sign (Q time) (P time))

/-- The signed interaction picture removes the complete free drift. -/
theorem hasDerivAt_complexFourierInteractionBranch
    {omega : Real} (homega : 0 < omega) (sign : PhaseSign)
    {Q P R : Real -> Complex} {time : Real}
    (hQ : HasDerivAt Q (P time) time)
    (hP : HasDerivAt P
      (-(omega ^ 2 : Real) * Q time + R time) time) :
    HasDerivAt
      (fun s => complexFourierInteractionBranch omega sign Q P s)
      (phaseFactor (phaseSignReal sign * omega * time) *
        complexFourierBranchSource omega sign (R time)) time := by
  unfold complexFourierInteractionBranch
  apply hasDerivAt_phaseRenormalize_of_sub_phaseDrift
    (theta' := phaseSignReal sign * omega)
  · simpa only [id_eq, mul_one] using
      (hasDerivAt_id time).const_mul (phaseSignReal sign * omega)
  · exact hasDerivAt_complexFourierBranchAmplitude_forced
      homega sign hQ hP

/-- Undoing the signed interaction rotation recovers the corresponding
Schrodinger-picture branch amplitude. -/
theorem inversePhase_interactionBranch
    (omega time : Real) (sign : PhaseSign)
    (Q P : Real -> Complex) :
    phaseRenormalize (-(phaseSignReal sign * omega * time))
        (complexFourierInteractionBranch omega sign Q P time) =
      complexFourierBranchAmplitude omega sign (Q time) (P time) := by
  unfold complexFourierInteractionBranch
  rw [phaseRenormalize_neg_phaseRenormalize]

/-- Exact reconstruction of the Fourier coordinate from the two
interaction-picture branches. -/
theorem coordinate_eq_interactionBranch_sum_div_sqrt
    {omega : Real} (homega : 0 < omega)
    (Q P : Real -> Complex) (time : Real) :
    Q time =
      (phaseRenormalize (-(omega * time))
          (complexFourierInteractionBranch omega .phase Q P time) +
        phaseRenormalize (omega * time)
          (complexFourierInteractionBranch omega .conjugate Q P time)) /
        Real.sqrt (2 * omega) := by
  rw [show -(omega * time) =
      -(phaseSignReal PhaseSign.phase * omega * time) by simp,
    show omega * time =
      -(phaseSignReal PhaseSign.conjugate * omega * time) by simp,
    inversePhase_interactionBranch,
    inversePhase_interactionBranch]
  exact coordinate_eq_branch_sum_div_sqrt homega (Q time) (P time)

end

end ArchonPhysics.ComplexFourierBranchAmplitude
