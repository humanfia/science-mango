import ArchonPhysics.FreeFPUTCubicPhaseExpansion

/-!
# Consumer checks for the free cubic FPUT phase expansion

These contracts expose the exact finite-volume character family carried by
the cubic modal force on a free reference orbit, its output-rotated physical
forcing, and its finite-interval oscillatory coefficients.
-/

namespace ArchonPhysicsConsumers.Thermalization.FreeFPUTCubicPhaseExpansion

open UnitAddTorus
open ArchonPhysics
open ArchonPhysics.FiniteHaarOscillatorySecondMoment
open ArchonPhysics.FreeFPUTCubicPhaseExpansion
open ArchonPhysics.FreeFPUTTensorPhaseExpansion
open ArchonPhysics.ModalNonlinearForce
open ArchonPhysics.PhaseRenormalization

open scoped Interval

noncomputable section

/-- The existing order-three distinguished tensor contraction on the free
configuration is exactly the finite three-sign character polynomial. -/
theorem cubic_tensor_contraction_phase_family_contract
    {N : Nat} [NeZero N]
    (m : Lattice.PositiveMassConfig N) (observed : Lattice.Site N)
    (radius frequency : Lattice.Site N → Real) (time : Real)
    (phase : UnitAddTorus (Lattice.Site N)) :
    ((distinguishedTensorContraction m
        (freeWeightedConfiguration radius frequency time phase)
        observed 3 : Real) : Complex) =
      cubicTensorPhasePolynomial m observed radius
        (physicalFreePhaseEvolution frequency time phase) := by
  rw [← freeCubicTensorSource_eq_complex_tensorContraction]
  exact freeCubicTensorSource_eq_phasePolynomial
    m observed radius frequency time phase

/-- With the forced-mode coefficient `-beta` and the output phase inserted,
every cubic term has its exact output-minus-input frequency mismatch. -/
theorem physical_cubic_mismatch_family_contract
    {N : Nat} [NeZero N]
    (beta : Real) (m : Lattice.PositiveMassConfig N)
    (observed : Lattice.Site N)
    (radius frequency : Lattice.Site N → Real) (time : Real)
    (phase : UnitAddTorus (Lattice.Site N)) :
    physicalFreeCubicPicardIntegrand beta m observed radius frequency time phase =
      ∑ term : CubicPhaseTerm N,
        (cubicDuhamelCoefficient
            (physicalCubicUnitCoupling (frequency observed) beta)
            m observed radius term *
          mFourier (cubicPhaseCharge term) phase) *
          Complex.exp
            ((Complex.I *
              (cubicPhaseMismatch frequency observed term : Real)) * time) :=
  physicalFreeCubicPicardIntegrand_eq_mismatchSum
    beta m observed radius frequency time phase

/-- The finite-time physical cubic correction is the canonical finite
character sum whose coefficients are `oscillatoryCoefficient`s. -/
theorem physical_cubic_interval_oscillatory_family_contract
    {N : Nat} [NeZero N]
    (beta : Real) (m : Lattice.PositiveMassConfig N)
    (observed : Lattice.Site N)
    (radius frequency : Lattice.Site N → Real) (time : Real)
    (phase : UnitAddTorus (Lattice.Site N)) :
    (∫ s in (0 : Real)..time,
      physicalFreeCubicPicardIntegrand
        beta m observed radius frequency s phase) =
      finiteHaarOscillatorySum
        (cubicDuhamelCoefficient
          (physicalCubicUnitCoupling (frequency observed) beta)
          m observed radius)
        cubicPhaseCharge (cubicPhaseMismatch frequency observed)
        time phase :=
  intervalIntegral_physicalFreeCubicPicardIntegrand_eq_oscillatoryFamily
    beta m observed radius frequency time phase

#check CubicPhaseTerm
#check cubicPhaseCharge
#check cubicPhaseCoefficient
#check oscillatoryCoefficient

#print axioms cubic_tensor_contraction_phase_family_contract
#print axioms physical_cubic_mismatch_family_contract
#print axioms physical_cubic_interval_oscillatory_family_contract

end

end ArchonPhysicsConsumers.Thermalization.FreeFPUTCubicPhaseExpansion
