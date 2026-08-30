import ArchonPhysics.CanonicalIIDCoerciveMatchedDenominatorForestRank

/-!
Consumer checks for the corrected matched-denominator forest rank.

The examples exercise the actual decorated-tree and garden generator
theorems, the exact physical A0/A1/A2 ranks, the minimal order-two
counterexample to the interaction-pair bound, and the resulting closed
g4 cutoff classification.
-/

namespace ArchonPhysicsConsumers.Thermalization

open ArchonPhysics
open ArchonPhysics.CanonicalIIDCoerciveHaarMatchedCouplingPower
open ArchonPhysics.CanonicalIIDCoerciveMatchedDenominatorForestRank
open ArchonPhysics.CanonicalIIDCoerciveRegularGoodCutoffExponentBalance
open ArchonPhysics.FinitePhaseMonomials
open ArchonPhysics.FreeFPUTA0DirectCubicBridge
open ArchonPhysics.FreeFPUTBranchingHistoryDenominatorEnumeration
open ArchonPhysics.FreeFPUTCubicPhaseExpansion
open ArchonPhysics.FreeFPUTMismatchPhaseExpansion
open ArchonPhysics.FreeFPUTOrderedHistoryDenominatorEnumeration
open ArchonPhysics.FreeFPUTTensorPhaseExpansion
open ArchonPhysics.ModalPhaseMismatch
open ArchonPhysics.PhyslibFPUTBinaryInteractionTreeCouples
open ArchonPhysics.PhyslibFPUTCompleteSecondPicardCharacterFamily
open ArchonPhysics.PhyslibFPUTIteratedQuadraticSecondPicardCharacterFamily

noncomputable section

variable {Mode : Type*} [Fintype Mode] [DecidableEq Mode]

example (frequency : Mode → Real)
    (couple : BinaryInteractionTreeCouple Mode)
    (hright : 0 < couple.2.shape.order)
    (hroot : couple.1.rootMode = couple.2.rootMode)
    (hbalanced : leafPhaseBalanced couple)
    (delta : Real)
    (hdelta : delta ∈ actualMatchedCoupleDenominators frequency couple) :
    AdditivelyGeneratedBy
      (actualMatchedCouplePhaseBasis frequency couple) delta := by
  exact actualMatchedCoupleDenominators_additivelyGenerated
    frequency couple hright hroot hbalanced delta hdelta

example (frequency : Mode → Real)
    (couple : BinaryInteractionTreeCouple Mode)
    (hright : 0 < couple.2.shape.order) :
    actualMatchedCoupleForestRank frequency couple =
      coupleInteractionPower couple - 1 := by
  exact actualMatchedCoupleForestRank_eq_power_sub_one
    frequency couple hright

example (frequency : Mode → Real)
    (garden : List (BinaryInteractionTreeCouple Mode))
    (hright : ∀ couple ∈ garden, 0 < couple.2.shape.order) :
    actualMatchedCoupleGardenForestRank frequency garden + garden.length =
      actualMatchedCoupleGardenInteractionPower garden := by
  exact actualMatchedCoupleGardenForestRank_add_card_eq_power
    frequency garden hright

example {N : Nat} [NeZero N] (frequency : Lattice.Site N → Real)
    (observed : Lattice.Site N) (left right : QuadraticPhaseTerm N)
    (hcharge : quadraticPhaseCharge left = quadraticPhaseCharge right)
    (delta : Real)
    (hdelta : delta ∈
      orderedHistoryDenominators
          (physicalA1PhaseHistory frequency observed left) ++
        orderedHistoryDenominators
          (physicalA1PhaseHistory frequency observed right)) :
    AdditivelyGeneratedBy
      [quadraticPhaseMismatch frequency observed left] delta := by
  exact physicalA1MatchedDenominators_one_generator
    frequency observed left right hcharge delta hdelta

example {N : Nat} [NeZero N] (m : Lattice.PositiveMassConfig N)
    (observed : Lattice.Site N)
    (term : IteratedQuadraticSecondPicardCharacterTerm N)
    (hcharge : freeInitialPhaseCharge observed 0 =
      iteratedQuadraticSecondPicardCharge term)
    (delta : Real)
    (hdelta : delta ∈ orderedHistoryDenominators
      (physicalIteratedA2PhaseHistory m observed term)) :
    AdditivelyGeneratedBy [iteratedQuadraticInnerMismatch m term] delta := by
  exact physicalA0IteratedA2Denominators_one_generator
    m observed term hcharge delta hdelta

example {N : Nat} [NeZero N] (m : Lattice.PositiveMassConfig N)
    (observed : Lattice.Site N)
    (left right : IteratedQuadraticSecondPicardCharacterTerm N) :
    physicalCompleteA2MatchedForestRank m observed
      (Sum.inl left) (Sum.inl right) = 3 := by
  exact physicalCompleteA2MatchedForestRank_inl_inl
    m observed left right

example (parameter : Fin 3 → Real) :
    actualMatchedCoupleForestRank
        (orderTwoRankCounterFrequency parameter)
        orderTwoRankCounterCouple = 3 ∧
      matchedInteractionPairCount orderTwoRankCounterCouple = 2 := by
  simp

example :
    PhaseTripleLinearlyIndependent
      orderTwoRankCounterLeftOuter
      orderTwoRankCounterLeftInner
      orderTwoRankCounterRightInner := by
  exact orderTwoRankCounter_phaseTriple_linearlyIndependent

example {N : Nat} [NeZero N] (m : Lattice.PositiveMassConfig N)
    (observed : Lattice.Site N)
    (left : IteratedQuadraticSecondPicardCharacterTerm N)
    (right : CubicPhaseTerm N) :
    ∃ alpha, CutoffExponentAdmissible 4
      (physicalCompleteA2MatchedForestRank m observed
        (Sum.inl left) (Sum.inr right) : Real)
      quadraticKineticDeficit alpha := by
  exact physicalCompleteA2_inl_inr_exists_quadraticCutoffExponent
    m observed left right

example {N : Nat} [NeZero N] (m : Lattice.PositiveMassConfig N)
    (observed : Lattice.Site N)
    (left right : IteratedQuadraticSecondPicardCharacterTerm N) :
    ¬ ∃ alpha, CutoffExponentAdmissible 4
      (physicalCompleteA2MatchedForestRank m observed
        (Sum.inl left) (Sum.inl right) : Real)
      quadraticKineticDeficit alpha := by
  exact physicalCompleteA2_inl_inl_no_quadraticCutoffExponent
    m observed left right

end

end ArchonPhysicsConsumers.Thermalization
