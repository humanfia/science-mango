import ArchonPhysics.CanonicalRandomPhaseMoments
import ArchonPhysics.ComplexModeAmplitude

/-!
# Haar phases as real modal coordinates with prescribed energy

This module turns one circle-valued phase and one nonnegative target energy
into a real harmonic coordinate--momentum pair at positive frequency:

`Q = sqrt (2 E) Re(z) / omega`, `P = sqrt (2 E) Im(z)`.

Here `z` is the first Fourier character of the phase.  The resulting pair is
globally measurable in all inputs and has harmonic energy exactly `E` whenever
`E >= 0` and `omega > 0`.  This is the deterministic, basis-independent scalar
adapter needed before a measurable eigenframe can assemble a random lattice
initial condition.  It makes no kinetic-limit or thermalization assertion.
-/

namespace ArchonPhysics.PhaseEnergyModeCoordinates

open ArchonPhysics
open HarmonicModes

noncomputable section

/-- The unit complex number represented by the first Fourier character. -/
def unitPhase (theta : UnitAddCircle) : Complex :=
  fourier 1 theta

/-- The first Fourier character depends continuously on the circle phase. -/
theorem continuous_unitPhase : Continuous unitPhase := by
  exact (fourier 1).continuous

/-- The phase character has complex norm one. -/
@[simp] theorem norm_unitPhase (theta : UnitAddCircle) :
    ‖unitPhase theta‖ = 1 := by
  rw [unitPhase, fourier_apply]
  exact Circle.norm_coe _

/-- The real and imaginary parts of the phase character lie on the unit circle. -/
theorem re_sq_add_im_sq_unitPhase (theta : UnitAddCircle) :
    (unitPhase theta).re ^ 2 + (unitPhase theta).im ^ 2 = 1 := by
  calc
    (unitPhase theta).re ^ 2 + (unitPhase theta).im ^ 2 =
        Complex.normSq (unitPhase theta) := by
          simp [Complex.normSq_apply, pow_two]
    _ = ‖unitPhase theta‖ ^ 2 := (Complex.sq_norm _).symm
    _ = 1 := by simp

/-- Real modal coordinate carrying target energy `E` at frequency `omega`. -/
def phaseCoordinate (E omega : Real) (theta : UnitAddCircle) : Real :=
  Real.sqrt (2 * E) * (unitPhase theta).re / omega

/-- Real modal momentum carrying target energy `E`. -/
def phaseMomentum (E : Real) (theta : UnitAddCircle) : Real :=
  Real.sqrt (2 * E) * (unitPhase theta).im

/-- The coordinate and momentum adapter is globally Borel measurable.  The
value at zero frequency is harmlessly totalized by real division; physical
use is restricted to positive frequencies. -/
theorem measurable_phaseModeCoordinates :
    Measurable (fun x : Real × Real × UnitAddCircle =>
      (phaseCoordinate x.1 x.2.1 x.2.2,
        phaseMomentum x.1 x.2.2)) := by
  unfold phaseCoordinate phaseMomentum unitPhase
  fun_prop

/-- Away from zero frequency the coordinate and momentum adapter is continuous. -/
theorem continuousAt_phaseModeCoordinates
    {x : Real × Real × UnitAddCircle} (homega : x.2.1 ≠ 0) :
    ContinuousAt (fun y : Real × Real × UnitAddCircle =>
      (phaseCoordinate y.1 y.2.1 y.2.2,
        phaseMomentum y.1 y.2.2)) x := by
  unfold phaseCoordinate phaseMomentum unitPhase
  fun_prop

/-- One Haar phase realizes the prescribed nonnegative harmonic energy exactly. -/
theorem modalEnergy_phaseCoordinates {E omega : Real}
    (theta : UnitAddCircle) (hE : 0 ≤ E) (homega : 0 < omega) :
    modalEnergy (omega ^ 2)
        (phaseCoordinate E omega theta) (phaseMomentum E theta) = E := by
  have hsqrt : (Real.sqrt (2 * E)) ^ 2 = 2 * E :=
    Real.sq_sqrt (mul_nonneg (by norm_num) hE)
  have hcircle := re_sq_add_im_sq_unitPhase theta
  unfold modalEnergy phaseCoordinate phaseMomentum
  field_simp [homega.ne']
  nlinarith

/-- The associated complex normal-mode amplitude is the radial square root
times the same unit phase, with the normalization used by
`ComplexModeAmplitude`. -/
theorem complexModeAmplitude_phaseCoordinates {E omega : Real}
    (theta : UnitAddCircle) (hE : 0 ≤ E) (homega : 0 < omega) :
    ComplexModeAmplitude.complexModeAmplitude omega
        (phaseCoordinate E omega theta) (phaseMomentum E theta) =
      (Real.sqrt (E / omega) : Complex) * unitPhase theta := by
  apply Complex.ext <;> simp only [ComplexModeAmplitude.complexModeAmplitude_re,
    ComplexModeAmplitude.complexModeAmplitude_im, phaseCoordinate,
    phaseMomentum, Complex.mul_re, Complex.mul_im, Complex.ofReal_re,
    Complex.ofReal_im, zero_mul, sub_zero]
  · have htwoomega : 0 < 2 * omega := mul_pos zero_lt_two homega
    have hsqrt_twoomega : Real.sqrt (2 * omega) ≠ 0 :=
      Real.sqrt_ne_zero'.mpr htwoomega
    have hsqrt_ratio : Real.sqrt (E / omega) =
        Real.sqrt (2 * E) / Real.sqrt (2 * omega) := by
      rw [← Real.sqrt_div (mul_nonneg (by norm_num) hE)]
      congr 1
      field_simp [homega.ne']
    rw [hsqrt_ratio]
    field_simp
  · have hsqrt_ratio : Real.sqrt (E / omega) =
        Real.sqrt (2 * E) / Real.sqrt (2 * omega) := by
      rw [← Real.sqrt_div (mul_nonneg (by norm_num) hE)]
      congr 1
      field_simp [homega.ne']
    rw [hsqrt_ratio]
    ring

end

end ArchonPhysics.PhaseEnergyModeCoordinates
