import ArchonPhysics.PhyslibFPUTIteratedA2FullCouplingSquareScaling

/-!
# Coupling scaling of the iterated-A2 Haar energy

The full iterated quadratic A2 amplitude is quadratic in the Hamiltonian
coupling.  Its Haar square is therefore exactly quartic.  This module derives
that fourth power algebraically; it is not an asymptotic or kinetic
assumption.
-/

namespace ArchonPhysics.PhyslibFPUTIteratedA2HaarEnergyCouplingScaling

open ArchonPhysics
open ArchonPhysics.CanonicalIIDCoerciveCorrectedStructuralRankRPAAdapter
open ArchonPhysics.CanonicalIIDCoerciveIteratedA2TwistRenormalizedRemainder
open ArchonPhysics.FiniteSecondOrderCharacterFamilyExpansion
open ArchonPhysics.PhyslibFPUTIteratedA2FullCouplingSquareScaling
open ArchonPhysics.PhyslibFPUTIteratedQuadraticSecondPicardCharacterFamily

noncomputable section

/-- A common complex scalar contributes its norm square to a finite Haar
square. -/
theorem sameChargeFamilySquare_const_mul
    {J d : Type*} [Fintype J] [Fintype d]
    (coefficient : J -> Complex) (charge : J -> d -> Int)
    (scalar : Complex) :
    sameChargeFamilySquare (fun term => scalar * coefficient term) charge =
      Complex.normSq scalar * sameChargeFamilySquare coefficient charge := by
  classical
  unfold sameChargeFamilySquare
  have hsum :
      equalChargeCrossPairSum
          (fun term => scalar * coefficient term) charge
          (fun term => scalar * coefficient term) charge =
        (scalar * starRingEnd Complex scalar) *
          equalChargeCrossPairSum coefficient charge coefficient charge := by
    unfold equalChargeCrossPairSum
    simp_rw [map_mul]
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro left _hleft
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro right _hright
    by_cases hcharge : charge left = charge right
    · rw [if_pos hcharge, if_pos hcharge]
      ring
    · rw [if_neg hcharge, if_neg hcharge]
      ring
  have hscalar : scalar * starRingEnd Complex scalar =
      (Complex.normSq scalar : Complex) := by
    exact Complex.mul_conj scalar
  rw [hsum, hscalar]
  simp

/-- The Haar square of the physical nested iterated-A2 family is exactly
quartic in the quadratic coupling. -/
theorem sameChargeFamilySquare_physicalIteratedA2_eq_coupling_four_mul_unit
    {N : Nat} [NeZero N]
    (m : Lattice.PositiveMassConfig N) (kappa : Real)
    (radius : Lattice.Site N -> Real) (observed : Lattice.Site N)
    (time : Real) :
    sameChargeFamilySquare
        (iteratedQuadraticSecondPicardNestedCoefficient
          m kappa radius observed time)
        iteratedQuadraticSecondPicardCharge =
      kappa ^ 4 *
        sameChargeFamilySquare
          (iteratedQuadraticSecondPicardNestedCoefficient
            m 1 radius observed time)
          iteratedQuadraticSecondPicardCharge := by
  rw [show
    (iteratedQuadraticSecondPicardNestedCoefficient
      m kappa radius observed time) =
        fun term => ((kappa : Complex) ^ 2) *
          iteratedQuadraticSecondPicardNestedCoefficient
            m 1 radius observed time term by
    funext term
    exact
      iteratedQuadraticSecondPicardNestedCoefficient_eq_coupling_sq_mul_unit
        m kappa radius observed time term]
  rw [sameChargeFamilySquare_const_mul]
  have hnorm : Complex.normSq ((kappa : Complex) ^ 2) = kappa ^ 4 := by
    rw [pow_two, Complex.normSq_mul, Complex.normSq_ofReal]
    ring
  rw [hnorm]

/-- Hence the isolated iterated/iterated structural-rank remainder has the
same exact fourth-power scaling. -/
theorem completeA2IteratedIteratedRemainder_eq_coupling_four_mul_unit
    {N : Nat} [NeZero N]
    (m : Lattice.PositiveMassConfig N) (kappa : Real)
    (radius : Lattice.Site N -> Real) (observed : Lattice.Site N)
    (time : Real) :
    completeA2IteratedIteratedRemainder
        m kappa radius observed time =
      kappa ^ 4 *
        completeA2IteratedIteratedRemainder
          m 1 radius observed time := by
  unfold completeA2IteratedIteratedRemainder
  exact
    sameChargeFamilySquare_physicalIteratedA2_eq_coupling_four_mul_unit
      m kappa radius observed time

/-- The twist-renormalized Haar square is also exactly quartic. -/
theorem
    sameChargeFamilySquare_phaseRenormalizedPhysical_eq_coupling_four_mul_unit
    {N : Nat} [NeZero N]
    (m : Lattice.PositiveMassConfig N) (kappa : Real)
    (radius : Lattice.Site N -> Real) (observed : Lattice.Site N)
    (time : Real) :
    sameChargeFamilySquare
        (phaseRenormalizedPhysicalIteratedA2Coefficient
          m kappa radius observed time)
        iteratedQuadraticSecondPicardCharge =
      kappa ^ 4 *
        sameChargeFamilySquare
          (phaseRenormalizedPhysicalIteratedA2Coefficient
            m 1 radius observed time)
          iteratedQuadraticSecondPicardCharge := by
  rw [
    sameChargeFamilySquare_phaseRenormalizedPhysical_eq_four_mul_remainder,
    sameChargeFamilySquare_phaseRenormalizedPhysical_eq_four_mul_remainder,
    completeA2IteratedIteratedRemainder_eq_coupling_four_mul_unit]
  ring

end

end ArchonPhysics.PhyslibFPUTIteratedA2HaarEnergyCouplingScaling
