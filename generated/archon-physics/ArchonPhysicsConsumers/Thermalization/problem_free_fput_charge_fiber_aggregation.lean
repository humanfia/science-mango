import ArchonPhysics.FreeFPUTChargeFiberAggregation

/-!
# Consumer checks for free-FPUT charge-fiber aggregation

These contracts expose the exact finite-volume reorganization of every
same-charge ordered pair into coherent charge fibers, followed by its
application to the normalized Haar second moment of the free quadratic FPUT
first-Picard correction.  The fiber norm squares retain all off-diagonal cross
terms.  They are not a reduction to termwise collision diagonals and do not
assert nonlinear random-phase propagation or a kinetic limit.
-/

namespace ArchonPhysicsConsumers.Thermalization.FreeFPUTChargeFiberAggregation

open MeasureTheory
open UnitAddTorus
open ArchonPhysics
open ArchonPhysics.FiniteTimeResonanceWeight
open ArchonPhysics.FreeFPUTChargeFiberAggregation
open ArchonPhysics.FreeFPUTDuhamelResonanceBridge
open ArchonPhysics.FreeFPUTMismatchPhaseExpansion
open ArchonPhysics.FreeFPUTTensorPhaseExpansion
open ArchonPhysics.RandomPhaseMoments

noncomputable section

/-- The complete same-charge ordered-pair sum is the sum of coherent-fiber
norm squares over realized charges.  Distinct terms in one fiber contribute
their cross terms to the norm square. -/
theorem same_charge_pairs_coherent_fibers_contract
    {J Q : Type*} [Fintype J] [DecidableEq Q]
    (charge : J → Q) (coefficient : J → Complex)
    (kernel : Q → Complex) :
    (∑ j, ∑ k,
      if charge j = charge k then
        coefficient j * starRingEnd Complex (coefficient k) * kernel (charge j)
      else 0) =
      ∑ q ∈ realizedCharges charge,
        (Complex.normSq
          (coherentFiberCoefficient charge coefficient q) : Complex) *
          kernel q :=
  sameChargePairSum_eq_realizedChargeFiberNormSqSum
    charge coefficient kernel

/-- The normalized free-FPUT first-Picard Haar second moment is the exact
finite-time resonance sum of coherent realized charge fibers.  This remains
a charge-fiber formula, not a termwise collision-diagonal formula. -/
theorem normalized_firstPicard_charge_fiber_resonance_contract
    {N : Nat} [NeZero N]
    (coupling : Complex) (m : Lattice.PositiveMassConfig N)
    (observed : Lattice.Site N)
    (radius frequency : Lattice.Site N → Real) {time : Real}
    (htime : 0 < time) :
    (1 / (time : Complex)) *
        (∫ phase : UnitAddTorus (Lattice.Site N),
          (Complex.normSq
            (freeQuadraticInteractionPictureCorrection
              coupling m observed radius frequency time phase) : Complex)
          ∂finitePhaseHaarLaw (Lattice.Site N)) =
      ∑ charge ∈ realizedCharges
          (quadraticPhaseCharge :
            QuadraticPhaseTerm N → Lattice.Site N → Int),
        (Complex.normSq
          (freeQuadraticChargeFiberCoefficient
            coupling m observed radius charge) : Complex) *
          (finiteTimeResonanceWeight
            (outputChargeMismatch (frequency observed) charge frequency) time :
              Complex) :=
  normalized_integral_normSq_freeQuadraticCorrection_eq_chargeFiberSum
    coupling m observed radius frequency htime

#check realizedCharges
#check coherentFiberCoefficient
#check freeQuadraticChargeFiberCoefficient

#print axioms same_charge_pairs_coherent_fibers_contract
#print axioms normalized_firstPicard_charge_fiber_resonance_contract

end

end ArchonPhysicsConsumers.Thermalization.FreeFPUTChargeFiberAggregation
