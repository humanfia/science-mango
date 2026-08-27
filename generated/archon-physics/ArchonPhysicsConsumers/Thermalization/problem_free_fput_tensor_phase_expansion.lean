import ArchonPhysics.FreeFPUTTensorPhaseExpansion

/-!
# Consumer checks for the free FPUT tensor phase expansion

These contracts expose the exact finite-character representation and its Haar
charge selector for the quadratic first-Picard integrand. They concern only
the freely evolved Picard main-term algebra; they do not assert nonlinear RPA
propagation, kinetic convergence, or a Duhamel-remainder estimate.
-/

namespace ArchonPhysicsConsumers.Thermalization.FreeFPUTTensorPhaseExpansion

open MeasureTheory
open UnitAddTorus
open ArchonPhysics
open ArchonPhysics.FreeFPUTTensorPhaseExpansion
open ArchonPhysics.FiniteDuhamelPhaseAverage

noncomputable section

theorem quadratic_source_character_contract
    {N : Nat} [NeZero N]
    (m : Lattice.PositiveMassConfig N) (observed : Lattice.Site N)
    (radius frequency : Lattice.Site N → Real) (time : Real)
    (phase : UnitAddTorus (Lattice.Site N)) :
    freeQuadraticTensorSource m observed radius frequency time phase =
      quadraticTensorPhasePolynomial m observed radius
        (physicalFreePhaseEvolution frequency time phase) :=
  freeQuadraticTensorSource_eq_phasePolynomial
    m observed radius frequency time phase

theorem picard_haar_charge_selector_contract
    {N : Nat} [NeZero N]
    (timeCoefficient : Complex)
    (m : Lattice.PositiveMassConfig N) (observed : Lattice.Site N)
    (radius frequency : Lattice.Site N → Real) (time : Real) :
    (∫ phase : UnitAddTorus (Lattice.Site N),
      freeQuadraticPicardIntegrand timeCoefficient m observed radius frequency
        time phase
      ∂(RandomPhaseMoments.finitePhaseHaarLaw (Lattice.Site N))) =
      ∑ term : QuadraticPhaseTerm N,
        if quadraticPhaseCharge term = 0 then
          quadraticPicardCoefficient timeCoefficient m observed radius term
        else 0 :=
  integral_freeQuadraticPicardIntegrand_eq_zeroChargeSum
    timeCoefficient m observed radius frequency time

theorem unbalanced_picard_mean_zero_contract
    {N : Nat} [NeZero N]
    (timeCoefficient : Complex)
    (m : Lattice.PositiveMassConfig N) (observed : Lattice.Site N)
    (radius frequency : Lattice.Site N → Real) (time : Real)
    (hunbalanced : ∀ term : QuadraticPhaseTerm N,
      quadraticPhaseCharge term ≠ 0) :
    (∫ phase : UnitAddTorus (Lattice.Site N),
      freeQuadraticPicardIntegrand timeCoefficient m observed radius frequency
        time phase
      ∂(RandomPhaseMoments.finitePhaseHaarLaw (Lattice.Site N))) = 0 :=
  integral_freeQuadraticPicardIntegrand_eq_zero
    timeCoefficient m observed radius frequency time hunbalanced

#check freeRealModeCoordinate_phaseEnergyRadius
#check measurePreserving_physicalFreePhaseEvolution
#check freeQuadraticTensorSource_eq_complex_tensorContraction
#check freeQuadraticPicardIntegrand_eq_finitePhaseCorrection

#print axioms quadratic_source_character_contract
#print axioms picard_haar_charge_selector_contract
#print axioms unbalanced_picard_mean_zero_contract

end

end ArchonPhysicsConsumers.Thermalization.FreeFPUTTensorPhaseExpansion
