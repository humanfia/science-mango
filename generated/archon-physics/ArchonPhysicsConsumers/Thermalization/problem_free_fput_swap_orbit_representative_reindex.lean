import ArchonPhysics.FreeFPUTSwapOrbitRepresentativeReindex

/-!
# Consumer: canonical swap-orbit reindexing of the free FPUT coherent gain

These contracts expose the exact multiplicities before and after the ordered
outer quadratic terms are deduplicated.  An ordered outer term carries one
factor of its swap-orbit cardinality.  One canonical representative per orbit
carries the square of that cardinality, hence multiplicity one for a fixed
repeated-input term and four for a genuine two-element orbit.
-/

namespace ArchonPhysicsConsumers.Thermalization.FreeFPUTSwapOrbitRepresentativeReindex

open ArchonPhysics
open ArchonPhysics.FiniteTimeResonanceWeight
open ArchonPhysics.FreeFPUTDuhamelResonanceBridge
open ArchonPhysics.FreeFPUTMismatchPhaseExpansion
open ArchonPhysics.FreeFPUTQuadraticTermSwapSymmetry
open ArchonPhysics.FreeFPUTSwapOrbitCollisionCorrection
open ArchonPhysics.FreeFPUTSwapOrbitRepresentativeReindex
open ArchonPhysics.FreeFPUTTensorPhaseExpansion

noncomputable section

/-- Before deduplicating the ordered outer term, its right swap fiber supplies
one factor of `swapOrbit.card`. -/
theorem ordered_left_card_multiplicity_contract
    {N : Nat} [NeZero N]
    (coupling : Complex) (m : Lattice.PositiveMassConfig N)
    (observed : Lattice.Site N)
    (radius frequency : Lattice.Site N → Real) (time : Real) :
    freeQuadraticSwapIntraOrbitCollisionSum
        coupling m observed radius frequency time =
      freeQuadraticOrderedLeftSwapWeightSum
        coupling m observed radius frequency time :=
  freeQuadraticSwapIntraOrbitCollisionSum_eq_orderedLeftCardSum
    coupling m observed radius frequency time

/-- After choosing exactly one canonical outer representative per orbit, the
complete coherent ordered-pair contribution supplies `swapOrbit.card ^ 2`. -/
theorem representative_card_sq_multiplicity_contract
    {N : Nat} [NeZero N]
    (coupling : Complex) (m : Lattice.PositiveMassConfig N)
    (observed : Lattice.Site N)
    (radius frequency : Lattice.Site N → Real) (time : Real) :
    freeQuadraticSwapIntraOrbitCollisionSum
        coupling m observed radius frequency time =
      ∑ representative ∈ quadraticSwapOrbitRepresentatives N,
        ((quadraticSwapOrbit representative).card : Complex) ^ 2 *
          (Complex.normSq
            (freeQuadraticDuhamelCoefficient
              coupling m observed radius representative) : Complex) *
          (finiteTimeResonanceWeight
            (quadraticPhaseMismatch frequency observed representative) time :
              Complex) := by
  rw [freeQuadraticSwapIntraOrbitCollisionSum_eq_representativeSum,
    freeQuadraticSwapRepresentativeCollisionSum_eq_cardSqSum]

/-- The full same-charge coherent gain is the canonical card-squared orbit
sum plus the unchanged cross-orbit remainder. -/
theorem full_gain_representative_card_sq_add_cross_contract
    {N : Nat} [NeZero N]
    (coupling : Complex) (m : Lattice.PositiveMassConfig N)
    (observed : Lattice.Site N)
    (radius frequency : Lattice.Site N → Real) (time : Real) :
    freeQuadraticFullSameChargePairSum
        coupling m observed radius frequency time =
      (∑ representative ∈ quadraticSwapOrbitRepresentatives N,
        ((quadraticSwapOrbit representative).card : Complex) ^ 2 *
          (Complex.normSq
            (freeQuadraticDuhamelCoefficient
              coupling m observed radius representative) : Complex) *
          (finiteTimeResonanceWeight
            (quadraticPhaseMismatch frequency observed representative) time :
              Complex)) +
        freeQuadraticCrossSwapOrbitCoherentRemainder
          coupling m observed radius frequency time :=
  freeQuadraticFullSameChargePairSum_eq_representativeCardSq_add_cross
    coupling m observed radius frequency time

#print axioms ordered_left_card_multiplicity_contract
#print axioms representative_card_sq_multiplicity_contract
#print axioms full_gain_representative_card_sq_add_cross_contract

end

end ArchonPhysicsConsumers.Thermalization.FreeFPUTSwapOrbitRepresentativeReindex
