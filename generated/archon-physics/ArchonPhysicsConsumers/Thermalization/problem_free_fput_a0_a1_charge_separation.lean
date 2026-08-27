import ArchonPhysics.FreeFPUTA0A1ChargeSeparation

/-!
# Consumer: exact A0/A1 phase-charge separation

This consumer exposes the deterministic separation between the singleton free
`A0` charge and every quadratic `A1` charge, together with the resulting exact
vanishing of the equal-charge selectors and first-order Haar interference.
Repeated modes and opposite-sign cancellations remain included; no kinetic or
probabilistic claim is made.
-/

namespace ArchonPhysicsConsumers.Thermalization

open MeasureTheory
open UnitAddTorus
open ArchonPhysics
open ArchonPhysics.DuhamelSecondMomentAlgebra
open ArchonPhysics.FiniteDuhamelPhaseAverage
open ArchonPhysics.FiniteSecondOrderCharacterFamilyExpansion
open ArchonPhysics.FreeFPUTA0A1ChargeSeparation
open ArchonPhysics.FreeFPUTA0DirectCubicBridge
open ArchonPhysics.FreeFPUTTensorPhaseExpansion
open ArchonPhysics.RandomPhaseMoments

noncomputable section

/-- Consumer endpoint for the pointwise separation of the free `A0` charge
from every quadratic `A1` charge. -/
theorem problem_freeInitialPhaseCharge_ne_quadraticPhaseCharge
    {N : Nat} [NeZero N] (observed : Lattice.Site N)
    (term : QuadraticPhaseTerm N) :
    freeInitialPhaseCharge observed 0 ≠ quadraticPhaseCharge term :=
  freeInitialPhaseCharge_ne_quadraticPhaseCharge observed term

/-- Consumer endpoint for vanishing of the complete complex equal-charge cross
sum, for arbitrary deterministic coefficients. -/
theorem problem_equalChargeCrossPairSum_freeInitial_quadratic_eq_zero
    {N : Nat} [NeZero N] (observed : Lattice.Site N)
    (zCoefficient : FreeInitialPhaseTerm → Complex)
    (wCoefficient : QuadraticPhaseTerm N → Complex) :
    equalChargeCrossPairSum zCoefficient (freeInitialPhaseCharge observed)
        wCoefficient quadraticPhaseCharge = 0 :=
  equalChargeCrossPairSum_freeInitial_quadratic_eq_zero
    observed zCoefficient wCoefficient

/-- Consumer endpoint for vanishing of the real equal-charge interference. -/
theorem problem_equalChargeFamilyInterference_freeInitial_quadratic_eq_zero
    {N : Nat} [NeZero N] (observed : Lattice.Site N)
    (zCoefficient : FreeInitialPhaseTerm → Complex)
    (wCoefficient : QuadraticPhaseTerm N → Complex) :
    equalChargeFamilyInterference zCoefficient (freeInitialPhaseCharge observed)
        wCoefficient quadraticPhaseCharge = 0 :=
  equalChargeFamilyInterference_freeInitial_quadratic_eq_zero
    observed zCoefficient wCoefficient

/-- Consumer endpoint for exact vanishing of the first-order Haar coefficient.
-/
theorem problem_integral_secondMomentFirst_freeInitial_quadratic_eq_zero
    {N : Nat} [NeZero N] (observed : Lattice.Site N)
    (zCoefficient : FreeInitialPhaseTerm → Complex)
    (wCoefficient : QuadraticPhaseTerm N → Complex) :
    (∫ phase : UnitAddTorus (Lattice.Site N),
      secondMomentFirst
        (finitePhaseCorrection zCoefficient
          (freeInitialPhaseCharge observed) phase)
        (finitePhaseCorrection wCoefficient quadraticPhaseCharge phase)
      ∂finitePhaseHaarLaw (Lattice.Site N)) = 0 :=
  integral_secondMomentFirst_freeInitial_quadratic_eq_zero
    observed zCoefficient wCoefficient

#print axioms problem_freeInitialPhaseCharge_ne_quadraticPhaseCharge
#print axioms problem_equalChargeCrossPairSum_freeInitial_quadratic_eq_zero
#print axioms problem_equalChargeFamilyInterference_freeInitial_quadratic_eq_zero
#print axioms problem_integral_secondMomentFirst_freeInitial_quadratic_eq_zero

end

end ArchonPhysicsConsumers.Thermalization
