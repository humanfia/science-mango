import ArchonPhysics.FiniteSecondOrderCharacterFamilyExpansion
import ArchonPhysics.FreeFPUTA0DirectCubicBridge

/-!
# Cancellation of the direct cubic A0/A2 Haar interference

The free initial complex amplitude has one positive phase charge at the
observed mode.  A direct cubic character which has that same charge has zero
output mismatch.  Its finite-time oscillatory factor is therefore real,
whereas the physical cubic forced-mode coupling is purely imaginary.  Since
the free initial radial coefficient and the cubic tensor coefficient are
real, their second-order real interference vanishes term by term.

This is an exact finite-volume cancellation.  Repeated input modes and the
resonant endpoint are retained, and no kinetic or long-time limit is used.
The algebraic statements are totalized for arbitrary real frequencies;
their complex-mode physical interpretation is restricted to a strictly
positive observed frequency by the downstream modal-energy theorem.
-/

namespace ArchonPhysics.FreeFPUTDirectCubicA0InterferenceCancellation

open ArchonPhysics
open ArchonPhysics.FiniteHaarOscillatorySecondMoment
open ArchonPhysics.FiniteSecondOrderCharacterFamilyExpansion
open ArchonPhysics.FinitePhaseMonomials
open ArchonPhysics.ForcedComplexModeDuhamel
open ArchonPhysics.FreeFPUTA0DirectCubicBridge
open ArchonPhysics.FreeFPUTCubicPhaseExpansion
open ArchonPhysics.FreeFPUTMismatchPhaseExpansion
open ArchonPhysics.FreeFPUTTensorPhaseExpansion

noncomputable section

/-- The singleton free initial charge carries exactly the observed
frequency under the charge/frequency pairing. -/
@[simp] theorem chargeFrequency_freeInitialPhaseCharge
    {N : Nat} [NeZero N]
    (observed : Lattice.Site N) (frequency : Lattice.Site N → Real) :
    chargeFrequency (freeInitialPhaseCharge observed 0) frequency =
      frequency observed := by
  classical
  unfold chargeFrequency freeInitialPhaseCharge binarySignedMode
    binaryPhaseSign SignedMode.charge
  simp only [if_pos, PhaseSign.exponent_phase]
  rw [Fintype.sum_eq_single observed]
  · simp
  · intro other hne
    simp [hne]

/-- Equality with the free initial charge forces a direct cubic monomial
exactly on shell. -/
theorem cubicPhaseMismatch_eq_zero_of_charge_eq_freeInitial
    {N : Nat} [NeZero N]
    (frequency : Lattice.Site N → Real) (observed : Lattice.Site N)
    (term : CubicPhaseTerm N)
    (hcharge : cubicPhaseCharge term = freeInitialPhaseCharge observed 0) :
    cubicPhaseMismatch frequency observed term = 0 := by
  rw [cubicPhaseMismatch, hcharge]
  simp [outputChargeMismatch]

@[simp] theorem freeInitialPhaseCoefficient_im
    {N : Nat} [NeZero N]
    (radius frequency : Lattice.Site N → Real)
    (observed : Lattice.Site N) (term : FreeInitialPhaseTerm) :
    (freeInitialPhaseCoefficient radius frequency observed term).im = 0 := by
  rfl

@[simp] theorem cubicPhaseCoefficient_im
    {N : Nat} [NeZero N]
    (m : Lattice.PositiveMassConfig N) (observed : Lattice.Site N)
    (radius : Lattice.Site N → Real) (term : CubicPhaseTerm N) :
    (cubicPhaseCoefficient m observed radius term).im = 0 := by
  simp [cubicPhaseCoefficient]

@[simp] theorem physicalCubicUnitCoupling_re
    (outputFrequency beta : Real) :
    (physicalCubicUnitCoupling outputFrequency beta).re = 0 := by
  unfold physicalCubicUnitCoupling forcedModeSource
  rw [Complex.div_re]
  simp

/-- Every charge-matched direct cubic coefficient has zero real interference
with the real radial coefficient of the free initial amplitude. -/
theorem re_freeInitial_mul_star_directCubicCoefficient_eq_zero_of_charge
    {N : Nat} [NeZero N]
    (m : Lattice.PositiveMassConfig N) (beta time : Real)
    (radius frequency : Lattice.Site N → Real)
    (observed : Lattice.Site N) (term : CubicPhaseTerm N)
    (hcharge : freeInitialPhaseCharge observed 0 = cubicPhaseCharge term) :
    (freeInitialPhaseCoefficient radius frequency observed 0 *
        starRingEnd Complex
          (oscillatoryCoefficient
            (cubicDuhamelCoefficient
              (physicalCubicUnitCoupling (frequency observed) beta)
              m observed radius)
            (cubicPhaseMismatch frequency observed) time term)).re = 0 := by
  have hmismatch : cubicPhaseMismatch frequency observed term = 0 :=
    cubicPhaseMismatch_eq_zero_of_charge_eq_freeInitial
      frequency observed term hcharge.symm
  have hdirectRe :
      (oscillatoryCoefficient
        (cubicDuhamelCoefficient
          (physicalCubicUnitCoupling (frequency observed) beta)
          m observed radius)
        (cubicPhaseMismatch frequency observed) time term).re = 0 := by
    unfold oscillatoryCoefficient
    rw [hmismatch, NonresonantOscillatoryGain.oscillatoryIntegral_zero]
    unfold cubicDuhamelCoefficient
    rw [Complex.mul_re]
    simp only [Complex.ofReal_re, Complex.ofReal_im, mul_zero, sub_zero]
    rw [Complex.mul_re, physicalCubicUnitCoupling_re,
      cubicPhaseCoefficient_im]
    ring
  have hstarRe :
      (starRingEnd Complex
        (oscillatoryCoefficient
          (cubicDuhamelCoefficient
            (physicalCubicUnitCoupling (frequency observed) beta)
            m observed radius)
          (cubicPhaseMismatch frequency observed) time term)).re = 0 := by
    simpa using hdirectRe
  rw [Complex.mul_re, freeInitialPhaseCoefficient_im, hstarRe]
  ring

/-- Consequently the full singleton-A0/direct-cubic equal-charge Haar
interference vanishes, including every repeated-mode cubic term. -/
theorem equalChargeFamilyInterference_freeInitial_directCubic_eq_zero
    {N : Nat} [NeZero N]
    (m : Lattice.PositiveMassConfig N) (beta time : Real)
    (radius frequency : Lattice.Site N → Real)
    (observed : Lattice.Site N) :
    equalChargeFamilyInterference
        (freeInitialPhaseCoefficient radius frequency observed)
        (freeInitialPhaseCharge observed)
        (oscillatoryCoefficient
          (cubicDuhamelCoefficient
            (physicalCubicUnitCoupling (frequency observed) beta)
            m observed radius)
          (cubicPhaseMismatch frequency observed) time)
        cubicPhaseCharge = 0 := by
  classical
  unfold equalChargeFamilyInterference equalChargeCrossPairSum
  rw [Fin.sum_univ_one]
  rw [show (∑ term : CubicPhaseTerm N,
      (if freeInitialPhaseCharge observed 0 = cubicPhaseCharge term then
        freeInitialPhaseCoefficient radius frequency observed 0 *
          starRingEnd Complex
            (oscillatoryCoefficient
              (cubicDuhamelCoefficient
                (physicalCubicUnitCoupling (frequency observed) beta)
                m observed radius)
              (cubicPhaseMismatch frequency observed) time term)
      else 0)).re = 0 by
    change Complex.reCLM (∑ term : CubicPhaseTerm N,
      if freeInitialPhaseCharge observed 0 = cubicPhaseCharge term then
        freeInitialPhaseCoefficient radius frequency observed 0 *
          starRingEnd Complex
            (oscillatoryCoefficient
              (cubicDuhamelCoefficient
                (physicalCubicUnitCoupling (frequency observed) beta)
                m observed radius)
              (cubicPhaseMismatch frequency observed) time term)
      else 0) = 0
    rw [map_sum]
    apply Finset.sum_eq_zero
    intro term hterm
    by_cases hcharge :
        freeInitialPhaseCharge observed 0 = cubicPhaseCharge term
    · rw [if_pos hcharge]
      exact re_freeInitial_mul_star_directCubicCoefficient_eq_zero_of_charge
        m beta time radius frequency observed term hcharge
    · rw [if_neg hcharge]
      rfl]
  norm_num

end

end ArchonPhysics.FreeFPUTDirectCubicA0InterferenceCancellation
