import ArchonPhysics.CanonicalIIDCoerciveCorrectedStructuralRankRPAAdapter

namespace ArchonPhysicsConsumers.Thermalization

open ArchonPhysics
open ArchonPhysics.CanonicalIIDCoerciveCorrectedStructuralRankRPAAdapter
open ArchonPhysics.CanonicalIIDCoerciveMatchedDenominatorForestRank
open ArchonPhysics.CanonicalIIDCoerciveRegularGoodCutoffExponentBalance
open ArchonPhysics.FiniteSecondOrderCharacterFamilyExpansion
open ArchonPhysics.FreeFPUTCubicPhaseExpansion
open ArchonPhysics.PhyslibFPUTCompleteSecondPicardCharacterFamily
open ArchonPhysics.PhyslibFPUTIteratedQuadraticSecondPicardCharacterFamily

noncomputable section

example {N : Nat} [NeZero N] (m : Lattice.PositiveMassConfig N)
    (observed : Lattice.Site N)
    (left : IteratedQuadraticSecondPicardCharacterTerm N)
    (right : CubicPhaseTerm N) :
    CutoffExponentAdmissible 4
      (physicalCompleteA2MatchedForestRank m observed
        (Sum.inl left) (Sum.inr right) : Real)
      quadraticKineticDeficit correctedSecondPicardG4CutoffExponent := by
  exact correctedSecondPicardG4CutoffExponent_admissible_inl_inr
    m observed left right

example {N : Nat} [NeZero N] (m : Lattice.PositiveMassConfig N)
    (observed : Lattice.Site N) (left right : CubicPhaseTerm N) :
    CutoffExponentAdmissible 4
      (physicalCompleteA2MatchedForestRank m observed
        (Sum.inr left) (Sum.inr right) : Real)
      quadraticKineticDeficit correctedSecondPicardG4CutoffExponent := by
  exact correctedSecondPicardG4CutoffExponent_admissible_inr_inr
    m observed left right

example {N : Nat} [NeZero N] (m : Lattice.PositiveMassConfig N)
    (observed : Lattice.Site N)
    (left right : IteratedQuadraticSecondPicardCharacterTerm N) :
    ¬ ∃ alpha, CutoffExponentAdmissible 4
      (physicalCompleteA2MatchedForestRank m observed
        (Sum.inl left) (Sum.inl right) : Real)
      quadraticKineticDeficit alpha := by
  exact iteratedIterated_requires_cancellation_or_renormalization
    m observed left right

example {N : Nat} [NeZero N]
    (m : Lattice.PositiveMassConfig N) (kappa beta g : Real)
    (radius : Lattice.Site N → Real) (observed : Lattice.Site N)
    (time : Real) :
    g ^ 4 * sameChargeFamilySquare
        (completeSecondPicardCoefficient
          m kappa beta radius observed time)
        completeSecondPicardCharge =
      g ^ 4 * completeA2IteratedIteratedRemainder
          m kappa radius observed time +
        g ^ 4 * completeA2CorrectedRegularGoodCoefficient
          m kappa beta radius observed time := by
  exact
    g4_completeSecondPicard_sameChargeFamilySquare_eq_remainder_add_regularGood
      m kappa beta g radius observed time

end

end ArchonPhysicsConsumers.Thermalization
