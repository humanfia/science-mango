import ArchonPhysics.FiniteSecondOrderCharacterFamilyExpansion
import ArchonPhysics.FreeFPUTChargeFiberAggregation

/-!
# Charge-fiber form of the finite second-order Haar coefficient

The exact second-order Haar coefficient of three finite character families
contains the complete coherent square of the first Picard family and the
complete zeroth/second Picard interference.  This module rewrites both terms
directly in charge-fiber form when the zeroth family has one term.

Every coefficient in a realized first-order charge fiber is summed before
taking its norm square.  Likewise, the interference selects the complete
second-order fiber whose charge equals the unique zeroth-order charge.  No
diagonalization, collision interpretation, long-time limit, or probabilistic
closure is used.
-/

namespace ArchonPhysics.FiniteSecondOrderChargeFiberExpansion

open MeasureTheory
open UnitAddTorus
open ArchonPhysics
open ArchonPhysics.DuhamelTwoStepMomentAlgebra
open ArchonPhysics.FiniteDuhamelPhaseAverage
open ArchonPhysics.FiniteSecondOrderCharacterFamilyExpansion
open ArchonPhysics.FreeFPUTChargeFiberAggregation
open ArchonPhysics.RandomPhaseMoments

noncomputable section

/-- Sum of the squared norms of the complete coherent coefficient in every
realized charge fiber.  Distinct indices carrying the same charge are summed
before the norm square is taken. -/
def sameChargeFiberNormSqSum
    {Q J : Type*} [Fintype J] [DecidableEq Q]
    (coefficient : J → Complex) (charge : J → Q) : Real := by
  exact ∑ q ∈ realizedCharges charge,
    Complex.normSq (coherentFiberCoefficient charge coefficient q)

/-- The full same-charge ordered-pair square is exactly the sum of coherent
fiber norm squares. -/
theorem sameChargeFamilySquare_eq_chargeFiberNormSqSum
    {d J : Type*} [Fintype d] [Fintype J]
    (coefficient : J → Complex) (charge : J → d → Int) :
    sameChargeFamilySquare coefficient charge =
      sameChargeFiberNormSqSum coefficient charge := by
  have h := sameChargePairSum_eq_realizedChargeFiberNormSqSum
    (charge := charge) (coefficient := coefficient)
    (kernel := fun _ : d → Int ↦ (1 : Complex))
  have hre := congrArg Complex.re h
  simpa [sameChargeFamilySquare, equalChargeCrossPairSum,
    sameChargeFiberNormSqSum] using hre

/-- With one zeroth-order character, the equal-charge cross sum is its
coefficient times the conjugate of the complete matching second-order fiber.
-/
theorem equalChargeCrossPairSum_finOne_left
    {d J : Type*} [Fintype d] [Fintype J]
    (zCoefficient : Fin 1 → Complex) (zCharge : Fin 1 → d → Int)
    (uCoefficient : J → Complex) (uCharge : J → d → Int) :
    equalChargeCrossPairSum zCoefficient zCharge uCoefficient uCharge =
      zCoefficient 0 * starRingEnd Complex
        (coherentFiberCoefficient uCharge uCoefficient (zCharge 0)) := by
  classical
  unfold equalChargeCrossPairSum coherentFiberCoefficient
  rw [Fin.sum_univ_one, map_sum, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro term hterm
  by_cases hcharge : zCharge 0 = uCharge term
  · rw [if_pos hcharge, if_pos hcharge.symm]
  · rw [if_neg hcharge, if_neg (Ne.symm hcharge)]
    simp only [map_zero, mul_zero]

/-- Charge-fiber form of the complete finite-family second-order coefficient
when the zeroth family is a singleton. -/
theorem finiteCharacterFamilySecondOrderCoefficient_finOne_eq_chargeFiber
    {d J1 J2 : Type*} [Fintype d] [Fintype J1] [Fintype J2]
    (zCoefficient : Fin 1 → Complex) (zCharge : Fin 1 → d → Int)
    (wCoefficient : J1 → Complex) (wCharge : J1 → d → Int)
    (uCoefficient : J2 → Complex) (uCharge : J2 → d → Int) :
    finiteCharacterFamilySecondOrderCoefficient
        zCoefficient zCharge wCoefficient wCharge uCoefficient uCharge =
      sameChargeFiberNormSqSum wCoefficient wCharge +
        2 * (zCoefficient 0 * starRingEnd Complex
          (coherentFiberCoefficient uCharge uCoefficient (zCharge 0))).re := by
  unfold finiteCharacterFamilySecondOrderCoefficient
    equalChargeFamilyInterference
  rw [sameChargeFamilySquare_eq_chargeFiberNormSqSum,
    equalChargeCrossPairSum_finOne_left]

/-- Exact Haar average of the supplied two-step coefficient in coherent
charge-fiber form.  This is fixed finite-volume algebra; it does not identify
the displayed fibers with a kinetic collision operator. -/
theorem integral_twoStepSecondCoefficient_finOne_eq_chargeFiber
    {d J1 J2 : Type*} [Fintype d] [Fintype J1] [Fintype J2]
    (zCoefficient : Fin 1 → Complex) (zCharge : Fin 1 → d → Int)
    (wCoefficient : J1 → Complex) (wCharge : J1 → d → Int)
    (uCoefficient : J2 → Complex) (uCharge : J2 → d → Int) :
    (∫ phase : UnitAddTorus d,
      twoStepSecondCoefficient
        (finitePhaseCorrection zCoefficient zCharge phase)
        (finitePhaseCorrection wCoefficient wCharge phase)
        (finitePhaseCorrection uCoefficient uCharge phase)
      ∂finitePhaseHaarLaw d) =
      sameChargeFiberNormSqSum wCoefficient wCharge +
        2 * (zCoefficient 0 * starRingEnd Complex
          (coherentFiberCoefficient uCharge uCoefficient (zCharge 0))).re := by
  rw [integral_twoStepSecondCoefficient_finitePhaseCorrections,
    finiteCharacterFamilySecondOrderCoefficient_finOne_eq_chargeFiber]

end

end ArchonPhysics.FiniteSecondOrderChargeFiberExpansion
