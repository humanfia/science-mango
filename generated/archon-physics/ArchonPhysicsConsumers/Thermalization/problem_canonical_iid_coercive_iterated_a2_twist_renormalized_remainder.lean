import ArchonPhysics.CanonicalIIDCoerciveIteratedA2TwistRenormalizedRemainder

namespace ArchonPhysicsConsumers.Thermalization

open ArchonPhysics
open ArchonPhysics.CanonicalIIDCoerciveCorrectedStructuralRankRPAAdapter
open ArchonPhysics.CanonicalIIDCoerciveIteratedA2TwistRenormalizedRemainder
open ArchonPhysics.FiniteSecondOrderCharacterFamilyExpansion
open ArchonPhysics.FreeFPUTTadpoleFeedbackCancellation
open ArchonPhysics.NestedOscillatoryIntegral
open ArchonPhysics.PhyslibFPUTIteratedQuadraticSecondPicardCharacterFamily

noncomputable section

example {N : Nat} [NeZero N]
    (m : Lattice.PositiveMassConfig N) (kappa : Real)
    (radius : Lattice.Site N → Real) (observed : Lattice.Site N)
    (time : Real) (term : IteratedQuadraticSecondPicardCharacterTerm N)
    (hcoefficient : physicalIteratedA2Coefficient
      m kappa radius observed time term ≠ 0) :
    0 <
      (iteratedA2MatchedPairKernel
          (physicalIteratedA2Coefficient m kappa radius observed time)
          (term, term) +
        iteratedA2MatchedPairKernel
          (physicalIteratedA2Coefficient m kappa radius observed time)
          (flipIteratedQuadraticInnerBranch term,
            flipIteratedQuadraticInnerBranch term)).re := by
  exact re_physicalDiagonalKernel_add_simultaneousFlip_pos
    m kappa radius observed time term hcoefficient

example {N : Nat} [NeZero N]
    (m : Lattice.PositiveMassConfig N) (kappa : Real)
    (radius : Lattice.Site N → Real) (observed : Lattice.Site N)
    (time : Real) (term : IteratedQuadraticSecondPicardCharacterTerm N) :
    phaseRenormalizedPhysicalIteratedA2Coefficient
        m kappa radius observed time term =
      iteratedQuadraticSecondPicardStaticCoefficient
          m kappa radius observed term *
        (nestedOscillatoryIntegral
            (iteratedQuadraticOuterMismatch m observed term)
            (iteratedQuadraticInnerMismatch m term) time -
          nestedOscillatoryIntegral
            (iteratedQuadraticOuterMismatch m observed
              (flipIteratedQuadraticInnerBranch term))
            (iteratedQuadraticInnerMismatch m
              (flipIteratedQuadraticInnerBranch term)) time) := by
  exact phaseRenormalizedPhysicalIteratedA2Coefficient_eq_nestedDifference
    m kappa radius observed time term

example {N : Nat} [NeZero N]
    (m : Lattice.PositiveMassConfig N) (kappa : Real)
    (radius : Lattice.Site N → Real) (observed : Lattice.Site N)
    (time : Real) :
    completeA2IteratedIteratedRemainder m kappa radius observed time =
      (1 / 4 : Real) *
        sameChargeFamilySquare
          (phaseRenormalizedPhysicalIteratedA2Coefficient
            m kappa radius observed time)
          iteratedQuadraticSecondPicardCharge := by
  exact
    completeA2IteratedIteratedRemainder_eq_quarter_phaseRenormalizedSquare
      m kappa radius observed time

end

end ArchonPhysicsConsumers.Thermalization
