import ArchonPhysics.CanonicalIIDCoerciveHaarMatchedCouplingPower

/-!
Consumer checks for the Haar-matched coupling-power bridge.

The examples exercise the arbitrary even-root forest identity, the actual
fixed-order raw-history couple, the exact physical `A1`--`A2` cancellation,
and the admissible-cutoff consequence for more than one independent loss.
-/

namespace ArchonPhysicsConsumers.Thermalization

open UnitAddTorus
open ArchonPhysics
open ArchonPhysics.CanonicalIIDCoerciveHaarMatchedCouplingPower
open ArchonPhysics.CanonicalIIDCoerciveRegularGoodCutoffExponentBalance
open ArchonPhysics.FiniteSecondOrderCharacterFamilyExpansion
open ArchonPhysics.FreeFPUTArbitraryOrderInitialHaarSelection
open ArchonPhysics.FreeFPUTBinaryTreeCatalanMomentumCounting
open ArchonPhysics.FreeFPUTCubicPhaseExpansion
open ArchonPhysics.FreeFPUTTensorPhaseExpansion
open ArchonPhysics.PhyslibFPUTBinaryInteractionTreeCouples
open ArchonPhysics.PhyslibFPUTCompleteSecondPicardCharacterFamily

noncomputable section

variable {Mode : Type*} [Fintype Mode] [DecidableEq Mode]

example (forest : List (SignedInteractionTree Mode))
    (hcharge : signedInteractionForestCharge forest = 0)
    (hroots : forest.length % 2 = 0) :
    signedInteractionForestInteractionPower forest =
      2 * signedInteractionForestPairCount forest := by
  exact signedInteractionForestInteractionPower_eq_two_mul_pairCount
    forest hcharge hroots

example {N r : Nat} [NeZero N] (rootMomentum : Lattice.Site N)
    (couple : FixedRootRawCoupleIndex N r rootMomentum) :
    coupleInteractionPower
        (realizeFixedRootRawHistory rootMomentum couple.1,
          realizeFixedRootRawHistory rootMomentum couple.2) = 2 * r := by
  exact fixedRootRawHistoryCouple_interactionPower_eq rootMomentum couple

example {N : Nat} [NeZero N]
    (firstCoefficient : QuadraticPhaseTerm N → Complex)
    (secondCoefficient : CompleteSecondPicardCharacterTerm N → Complex) :
    equalChargeFamilyInterference firstCoefficient quadraticPhaseCharge
        secondCoefficient completeSecondPicardCharge = 0 := by
  exact
    equalChargeFamilyInterference_quadratic_completeSecondPicard_eq_zero
      firstCoefficient secondCoefficient

example {independentLoss : Nat} (hloss : 1 < independentLoss) :
    ∃ alpha,
      CutoffExponentAdmissible ((2 * independentLoss : Nat) : Real)
        (independentLoss : Real) quadraticKineticDeficit alpha := by
  exact exists_quadraticCutoffExponent_for_exactMatchedPower hloss


example {independentLoss : Nat} (hloss : 1 < independentLoss) :
    CutoffExponentAdmissible ((2 * independentLoss : Nat) : Real)
      (independentLoss : Real) quadraticKineticDeficit
      (exactMatchedMidpointCutoffExponent independentLoss) := by
  exact exactMatchedMidpointCutoffExponent_admissible hloss

example (forest : List (SignedInteractionTree Mode))
    (independentLoss : Nat) (hloss : 1 < independentLoss)
    (hcharge : signedInteractionForestCharge forest = 0)
    (hroots : forest.length % 2 = 0)
    (hrank : independentLoss ≤ signedInteractionForestPairCount forest) :
    ∃ alpha,
      CutoffExponentAdmissible
        (signedInteractionForestInteractionPower forest : Real)
        (independentLoss : Real) quadraticKineticDeficit alpha := by
  exact haarSurvivingEvenRootForest_exists_quadraticCutoffExponent
    forest independentLoss hloss hcharge hroots hrank


end

end ArchonPhysicsConsumers.Thermalization
