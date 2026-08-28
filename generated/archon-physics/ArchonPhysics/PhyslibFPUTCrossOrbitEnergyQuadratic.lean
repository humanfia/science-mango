import ArchonPhysics.FreeFPUTCrossOrbitZeroChargeBridge
import ArchonPhysics.PhyslibFPUTCanonicalQuadraticClosure
import ArchonPhysics.PhyslibFPUTZeroChargeEnergyFactorization

/-!
# The exceptional cross-orbit Haar term is quadratic on physical energies

The raw phase-radius formula contains square roots and therefore is not a
quadratic polynomial on arbitrary signed energy profiles.  On the physical
nonnegative cone, however, every cross-swap-orbit coherent pair lies in the
zero-charge fiber.  The zero-charge factorization replaces each pair of
square roots by one energy coordinate.  What remains is an explicitly finite
sum of degree-two monomials.
-/

namespace ArchonPhysics.PhyslibFPUTCrossOrbitEnergyQuadratic

open ArchonPhysics
open ArchonPhysics.FiniteTimeResonanceWeight
open ArchonPhysics.FreeFPUTCrossOrbitZeroChargeBridge
open ArchonPhysics.FreeFPUTEnergyCollisionWeightBridge
open ArchonPhysics.FreeFPUTMismatchPhaseExpansion
open ArchonPhysics.FreeFPUTQuadraticTermSwapSymmetry
open ArchonPhysics.FreeFPUTDuhamelResonanceBridge
open ArchonPhysics.FreeFPUTSwapOrbitCollisionCorrection
open ArchonPhysics.FreeFPUTTensorPhaseExpansion
open ArchonPhysics.ModalPhaseMismatch
open ArchonPhysics.PhyslibFPUTCanonicalQuadraticClosure
open ArchonPhysics.PhyslibFPUTEnergyProfileKineticShadowing
open ArchonPhysics.PhyslibFPUTZeroChargeEnergyFactorization

open scoped ComplexConjugate

noncomputable section

/-- The full-site energy extension is frequency times modal action, including
the zero-frequency translation sector where both sides vanish. -/
theorem extendPositiveEnergyProfile_eq_frequency_mul_modeAction
    {N : Nat} [NeZero N]
    (m : Lattice.PositiveMassConfig N)
    (energy : PositiveEnergyProfile m) (site : Lattice.Site N) :
    extendPositiveEnergyProfile m energy site =
      modeFrequency m site *
        modeAction (extendPositiveEnergyProfile m energy) (modeFrequency m) site := by
  by_cases hsite : 0 < modeFrequency m site
  · simp only [extendPositiveEnergyProfile, dif_pos hsite, modeAction]
    field_simp [hsite.ne']
  · have hzero : modeFrequency m site = 0 :=
      le_antisymm (not_lt.mp hsite) (modeFrequency_nonneg m site)
    simp [extendPositiveEnergyProfile, modeAction, hzero]

/-- A product of two arbitrary full-site energies is a quadratic polynomial
in the complete positive-frequency energy profile. -/
theorem isPositiveEnergyQuadratic_extendedEnergyProduct
    {N : Nat} [NeZero N]
    (m : Lattice.PositiveMassConfig N)
    (first second : Lattice.Site N) :
    IsPositiveEnergyQuadratic m (fun energy ↦
      extendPositiveEnergyProfile m energy first *
        extendPositiveEnergyProfile m energy second) := by
  rcases
      (isPositiveEnergyQuadratic_modeActionProduct m first second).const_mul
        (modeFrequency m first * modeFrequency m second) with
    ⟨kernel, hkernel⟩
  refine ⟨kernel, ?_⟩
  intro energy
  change
    extendPositiveEnergyProfile m energy first *
        extendPositiveEnergyProfile m energy second = _
  rw [extendPositiveEnergyProfile_eq_frequency_mul_modeAction,
    extendPositiveEnergyProfile_eq_frequency_mul_modeAction]
  calc
    (modeFrequency m first *
          modeAction (extendPositiveEnergyProfile m energy) (modeFrequency m) first) *
        (modeFrequency m second *
          modeAction (extendPositiveEnergyProfile m energy) (modeFrequency m) second) =
      (modeFrequency m first * modeFrequency m second) *
        (modeAction (extendPositiveEnergyProfile m energy) (modeFrequency m) first *
          modeAction (extendPositiveEnergyProfile m energy) (modeFrequency m) second) := by
        ring
    _ = _ := hkernel energy

/-- Deterministic real coefficient multiplying the two energy coordinates in
one ordered zero-charge cross-orbit pair. -/
def zeroChargeCrossPairEnergyCoefficient
    {N : Nat} [NeZero N]
    (coupling : Complex) (m : Lattice.PositiveMassConfig N)
    (observed : Lattice.Site N) (time : Real)
    (left right : QuadraticPhaseTerm N) : Real :=
  (zeroChargeDuhamelEnergyCoefficient coupling m observed left *
      starRingEnd Complex
        (zeroChargeDuhamelEnergyCoefficient coupling m observed right) *
      (finiteTimeResonanceWeight
        (quadraticPhaseMismatch (modeFrequency m) observed left) time : Complex)).re

/-- On nonnegative energies, one zero-charge coherent ordered pair is exactly
its deterministic coefficient times two modal energies. -/
theorem freeQuadraticSameChargePairValue_phaseEnergyRadius_re_eq_energyProduct
    {N : Nat} [NeZero N]
    (coupling : Complex) (m : Lattice.PositiveMassConfig N)
    (observed : Lattice.Site N) (energy : Lattice.Site N → Real)
    (time : Real) (left right : QuadraticPhaseTerm N)
    (henergy : ∀ site, 0 ≤ energy site)
    (hleft : quadraticPhaseCharge left = 0)
    (hright : quadraticPhaseCharge right = 0) :
    (freeQuadraticSameChargePairValue coupling m observed
        (phaseEnergyRadius energy (modeFrequency m)) (modeFrequency m)
        time left right).re =
      zeroChargeCrossPairEnergyCoefficient coupling m observed time left right *
        energy (left.1 0) * energy (right.1 0) := by
  unfold freeQuadraticSameChargePairValue zeroChargeCrossPairEnergyCoefficient
  rw [freeQuadraticDuhamelCoefficient_phaseEnergyRadius_eq_energy
      coupling m observed energy left henergy hleft,
    freeQuadraticDuhamelCoefficient_phaseEnergyRadius_eq_energy
      coupling m observed energy right henergy hright]
  simp only [map_mul, Complex.conj_ofReal, Complex.mul_re, Complex.mul_im,
    Complex.ofReal_re, Complex.ofReal_im, Complex.conj_re, Complex.conj_im,
    Complex.conj_re, Complex.conj_im]
  ring

/-- Polynomial proxy for the exceptional cross-orbit coherent remainder.
Unlike the raw square-root expression, this definition is a genuine quadratic
polynomial on every signed positive-mode profile. -/
def zeroChargeCrossOrbitEnergyPolynomial
    {N : Nat} [NeZero N]
    (coupling : Complex) (m : Lattice.PositiveMassConfig N)
    (observed : Lattice.Site N) (time : Real)
    (energy : PositiveEnergyProfile m) : Real :=
  ∑ left : QuadraticPhaseTerm N, ∑ right : QuadraticPhaseTerm N,
    if quadraticPhaseCharge left = 0 ∧
        quadraticPhaseCharge right = 0 ∧
        right ∉ quadraticSwapOrbit left then
      zeroChargeCrossPairEnergyCoefficient coupling m observed time left right *
        extendPositiveEnergyProfile m energy (left.1 0) *
        extendPositiveEnergyProfile m energy (right.1 0)
    else 0

/-- The polynomial proxy has a constructed finite quadratic kernel. -/
theorem isPositiveEnergyQuadratic_zeroChargeCrossOrbitEnergyPolynomial
    {N : Nat} [NeZero N]
    (coupling : Complex) (m : Lattice.PositiveMassConfig N)
    (observed : Lattice.Site N) (time : Real) :
    IsPositiveEnergyQuadratic m
      (zeroChargeCrossOrbitEnergyPolynomial coupling m observed time) := by
  unfold zeroChargeCrossOrbitEnergyPolynomial
  apply isPositiveEnergyQuadratic_sum
  intro left
  apply isPositiveEnergyQuadratic_sum
  intro right
  by_cases hkeep : quadraticPhaseCharge left = 0 ∧
      quadraticPhaseCharge right = 0 ∧
      right ∉ quadraticSwapOrbit left
  · simp only [if_pos hkeep]
    simpa only [mul_assoc] using (isPositiveEnergyQuadratic_extendedEnergyProduct
      m (left.1 0) (right.1 0)).const_mul
        (zeroChargeCrossPairEnergyCoefficient
          coupling m observed time left right)
  · simpa only [if_neg hkeep] using isPositiveEnergyQuadratic_zero m

/-- On the physical nonnegative cone, the exact coherent cross-orbit term is
equal to its quadratic polynomial proxy. -/
theorem freeQuadraticCrossSwapOrbitCoherentRemainder_re_eq_energyPolynomial
    {N : Nat} [NeZero N]
    (coupling : Complex) (m : Lattice.PositiveMassConfig N)
    (observed : Lattice.Site N) (energy : PositiveEnergyProfile m)
    (time : Real) (henergy : ∀ mode, 0 ≤ energy mode) :
    (freeQuadraticCrossSwapOrbitCoherentRemainder coupling m observed
        (phaseEnergyRadius (extendPositiveEnergyProfile m energy)
          (modeFrequency m))
        (modeFrequency m) time).re =
      zeroChargeCrossOrbitEnergyPolynomial coupling m observed time energy := by
  rw [freeQuadraticCrossSwapOrbitCoherentRemainder_eq_zeroChargePairSum]
  unfold freeQuadraticZeroChargeCrossOrbitPairSum
    zeroChargeCrossOrbitEnergyPolynomial
  simp_rw [Complex.re_sum]
  apply Finset.sum_congr rfl
  intro left hleftMem
  apply Finset.sum_congr rfl
  intro right hrightMem
  by_cases hkeep : quadraticPhaseCharge left = 0 ∧
      quadraticPhaseCharge right = 0 ∧
      right ∉ quadraticSwapOrbit left
  · rw [if_pos hkeep, if_pos hkeep]
    apply freeQuadraticSameChargePairValue_phaseEnergyRadius_re_eq_energyProduct
    · intro site
      by_cases hsite : 0 < modeFrequency m site
      · simpa [extendPositiveEnergyProfile, hsite] using henergy ⟨site, hsite⟩
      · simp [extendPositiveEnergyProfile, hsite]
    · exact hkeep.1
    · exact hkeep.2.1
  · simp [hkeep]

end

end ArchonPhysics.PhyslibFPUTCrossOrbitEnergyQuadratic
