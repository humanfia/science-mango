import ArchonPhysics.FreeFPUTMismatchPhaseExpansion

/-!
# Consumer checks for the exact free FPUT mismatch expansion

These contracts expose the finite-volume interaction-picture formulas used by
a quadratic FPUT Duhamel term.  The character phase contains the angular
frequency pairing directly: the conversion to phase turns cancels the
`2 * pi` built into `mFourier`, so no residual `2 * pi` occurs in either the
pointwise mismatch or its time integral.
-/

namespace ArchonPhysicsConsumers.Thermalization.FreeFPUTMismatchPhaseExpansion

open UnitAddTorus
open ArchonPhysics
open ArchonPhysics.FreeFPUTMismatchPhaseExpansion
open ArchonPhysics.FreeFPUTTensorPhaseExpansion
open ArchonPhysics.NonresonantOscillatoryGain
open ArchonPhysics.PhaseRenormalization

open scoped Interval

noncomputable section

/-- Finite-lattice specialization of the exact free-character evolution.  Its
exponent is `-I * t * sum_j q_j * omega_j`, with no residual `2 * pi`. -/
theorem free_character_no_two_pi_contract
    {N : Nat} [NeZero N]
    (charge : Lattice.Site N → Int)
    (frequency : Lattice.Site N → Real) (time : Real)
    (phase : UnitAddTorus (Lattice.Site N)) :
    mFourier charge (physicalFreePhaseEvolution frequency time phase) =
      Complex.exp
          ((Complex.I * (-(chargeFrequency charge frequency) : Real)) * time) *
        mFourier charge phase :=
  mFourier_physicalFreePhaseEvolution charge frequency time phase

/-- Exact pointwise interaction-picture expansion of the quadratic source.
Every summand carries `quadraticPhaseMismatch = omega_k - sum_j q_j omega_j`.
-/
theorem quadratic_picard_mismatch_sum_contract
    {N : Nat} [NeZero N]
    (coupling : Complex) (m : Lattice.PositiveMassConfig N)
    (observed : Lattice.Site N)
    (radius frequency : Lattice.Site N → Real) (time : Real)
    (phase : UnitAddTorus (Lattice.Site N)) :
    freeQuadraticPicardIntegrand
        (coupling * phaseFactor (frequency observed * time))
        m observed radius frequency time phase =
      ∑ term : QuadraticPhaseTerm N,
        (coupling * quadraticPhaseCoefficient m observed radius term *
          mFourier (quadraticPhaseCharge term) phase) *
          Complex.exp
            ((Complex.I *
              (quadraticPhaseMismatch frequency observed term : Real)) * time) :=
  freeQuadraticPicardIntegrand_eq_mismatchSum
    coupling m observed radius frequency time phase

/-- Exact finite-time Duhamel formula.  Each time phase is integrated into the
existing `oscillatoryIntegral` at the same `quadraticPhaseMismatch`. -/
theorem quadratic_picard_interval_mismatch_sum_contract
    {N : Nat} [NeZero N]
    (coupling : Complex) (m : Lattice.PositiveMassConfig N)
    (observed : Lattice.Site N)
    (radius frequency : Lattice.Site N → Real) (time : Real)
    (phase : UnitAddTorus (Lattice.Site N)) :
    (∫ s in (0 : Real)..time,
      freeQuadraticPicardIntegrand
        (coupling * phaseFactor (frequency observed * s))
        m observed radius frequency s phase) =
      ∑ term : QuadraticPhaseTerm N,
        (coupling * quadraticPhaseCoefficient m observed radius term *
          mFourier (quadraticPhaseCharge term) phase) *
          oscillatoryIntegral
            (quadraticPhaseMismatch frequency observed term) time :=
  intervalIntegral_freeQuadraticPicardIntegrand_eq_mismatchSum
    coupling m observed radius frequency time phase

#check quadraticPhaseMismatch_eq_output_sub_chargeFrequency
#check intervalIntegral_const_mul_mismatchExp

#print axioms free_character_no_two_pi_contract
#print axioms quadratic_picard_mismatch_sum_contract
#print axioms quadratic_picard_interval_mismatch_sum_contract

end

end ArchonPhysicsConsumers.Thermalization.FreeFPUTMismatchPhaseExpansion
