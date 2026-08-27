import ArchonPhysics.FiniteSecondOrderChargeFiberExpansion

/-!
# Consumer: coherent charge-fiber form of a second-order Haar coefficient

This consumer exposes the exact finite-volume identity with a singleton
zeroth family.  It retains every same-charge cross term and makes no kinetic
or collision-limit claim.
-/

namespace ArchonPhysicsConsumers.Thermalization

open MeasureTheory
open UnitAddTorus
open ArchonPhysics
open ArchonPhysics.DuhamelTwoStepMomentAlgebra
open ArchonPhysics.FiniteDuhamelPhaseAverage
open ArchonPhysics.FiniteSecondOrderChargeFiberExpansion
open ArchonPhysics.FreeFPUTChargeFiberAggregation
open ArchonPhysics.RandomPhaseMoments

noncomputable section

/-- Consumer endpoint for the coherent square of all first-order charge
fibers. -/
theorem problem_sameChargeFamilySquare_eq_chargeFiberNormSqSum
    {d J : Type*} [Fintype d] [Fintype J]
    (coefficient : J → Complex) (charge : J → d → Int) :
    FiniteSecondOrderCharacterFamilyExpansion.sameChargeFamilySquare
        coefficient charge =
      sameChargeFiberNormSqSum coefficient charge :=
  sameChargeFamilySquare_eq_chargeFiberNormSqSum coefficient charge

/-- Consumer endpoint for the full second-order Haar coefficient: coherent
first-order fiber squares plus the matching zeroth/second-order fiber
interference. -/
theorem problem_integral_twoStepSecondCoefficient_finOne_eq_chargeFiber
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
          (coherentFiberCoefficient uCharge uCoefficient (zCharge 0))).re :=
  integral_twoStepSecondCoefficient_finOne_eq_chargeFiber
    zCoefficient zCharge wCoefficient wCharge uCoefficient uCharge

#print axioms problem_sameChargeFamilySquare_eq_chargeFiberNormSqSum
#print axioms problem_integral_twoStepSecondCoefficient_finOne_eq_chargeFiber

end

end ArchonPhysicsConsumers.Thermalization
