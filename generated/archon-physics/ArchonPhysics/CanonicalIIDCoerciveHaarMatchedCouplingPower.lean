import ArchonPhysics.CanonicalFixedMassHaarPicardCollisionDecomposition
import ArchonPhysics.CanonicalIIDCoerciveRegularGoodCutoffExponentBalance
import ArchonPhysics.FreeFPUTArbitraryOrderInitialHaarSelection
import ArchonPhysics.ThreeSignedChargeCancellationClassification

/-!
# Haar-matched coupling power for cubic-leading FPUT histories

For the cubic-leading (quadratic-force) channel, one Duhamel vertex carries
one power of the coupling.  This file derives the part of the often-used
"matched histories come in pairs" slogan that follows from the already
proved initial product-Haar law, without adding a Wick-pairing field.

The exact statements are:

* the total charge of a signed monomial has the parity of its number of
  leaves;
* two Haar-matched binary histories therefore have an even total number of
  interaction vertices;
* the resulting interaction-pair count is a derived arithmetic quotient,
  not extra structure or an independence hypothesis;
* an arbitrary fixed-order raw-history couple carries exactly `2 * order`
  coupling powers, and Haar averaging retains precisely its charge-balanced
  members;
* at physical two-step order the `A1`--`A2` (`g^3`) interference is in fact
  killed by the same two-leg/three-leg parity separation, strengthening the
  existing no-`g^1` decomposition;
* if the genuinely independent denominator losses are no more numerous than
  the derived interaction pairs, then `power >= 2 * loss`.  For more than one
  loss this supplies the strict cutoff margin `loss + 1 < power` and hence an
  admissible power cutoff.

The remaining arbitrary-garden problem is isolated exactly in the premise
`independentLoss <= matchedInteractionPairCount`: the current tree/charge
library does not prove that analytic denominator-rank bound.  No positive-time
RPA, Markov closure, or kinetic equation is assumed here.
-/

namespace ArchonPhysics.CanonicalIIDCoerciveHaarMatchedCouplingPower

open MeasureTheory
open UnitAddTorus
open ArchonPhysics
open ArchonPhysics.CanonicalIIDCoerciveRegularGoodCutoffExponentBalance
open ArchonPhysics.FiniteDuhamelPhaseAverage
open ArchonPhysics.FinitePhaseMonomials
open ArchonPhysics.FiniteSecondOrderCharacterFamilyExpansion
open ArchonPhysics.FreeFPUTA0DirectCubicBridge
open ArchonPhysics.FreeFPUTArbitraryOrderInitialHaarSelection
open ArchonPhysics.FreeFPUTBinaryTreeCatalanMomentumCounting
open ArchonPhysics.FreeFPUTCubicPhaseExpansion
open ArchonPhysics.FreeFPUTTensorPhaseExpansion
open ArchonPhysics.ModalPhaseMismatch
open ArchonPhysics.PhyslibFPUTActualHaarPostSecondPicardDecomposition
open ArchonPhysics.PhyslibFPUTBinaryInteractionTreeCouples
open ArchonPhysics.PhyslibFPUTCompleteSecondPicardCharacterFamily
open ArchonPhysics.PhyslibFPUTFirstShiftHaarMomentCancellation
open ArchonPhysics.PhyslibFPUTFirstPicardDecomposition
open ArchonPhysics.PhyslibFPUTIteratedQuadraticSecondPicardCharacterFamily
open ArchonPhysics.PhyslibFPUTReferenceBlockKineticResidual
open ArchonPhysics.PhyslibFPUTRenormalizedHaarMomentDefect
open ArchonPhysics.PhyslibFPUTSecondOrderHaarCharacterExpansion
open ArchonPhysics.ThreeSignedChargeCancellationClassification
open ArchonPhysics.RandomPhaseMoments

noncomputable section

/-! ## Charge parity of arbitrary signed leaves -/

variable {Mode : Type*} [Fintype Mode] [DecidableEq Mode]

/-- A single signed leaf has total charge `+1` or `-1`. -/
theorem sum_signedMode_charge (factor : SignedMode Mode) :
    (∑ mode, factor.charge mode) = factor.sign.exponent := by
  rcases factor with ⟨factorMode, sign⟩
  cases sign <;>
    simp [SignedMode.charge, PhaseSign.exponent, Pi.single_neg]

/-- The total charge minus the leaf count is even.  This formulation avoids
choosing any pairing of the leaves. -/
theorem exists_two_mul_eq_sum_monomialCharge_sub_length
    (factors : List (SignedMode Mode)) :
    ∃ k : Int,
      (∑ mode, monomialCharge factors mode) - (factors.length : Int) = 2 * k := by
  induction factors with
  | nil =>
      exact ⟨0, by simp [monomialCharge]⟩
  | cons factor rest ih =>
      rcases ih with ⟨k, hk⟩
      rcases factor with ⟨factorMode, sign⟩
      simp only [monomialCharge, List.length_cons, Nat.cast_add, Nat.cast_one]
      change ∃ k_prime : Int,
        (∑ mode, ((SignedMode.mk factorMode sign).charge mode +
          monomialCharge rest mode)) - ((rest.length : Int) + 1) =
            2 * k_prime
      rw [Finset.sum_add_distrib, sum_signedMode_charge]
      cases sign
      · refine ⟨k, ?_⟩
        norm_num [PhaseSign.exponent]
        linarith
      · refine ⟨k - 1, ?_⟩
        norm_num [PhaseSign.exponent]
        linarith

/-- Equal charge vectors force the two signed monomials to have leaf counts
of the same parity. -/
theorem exists_two_mul_eq_length_sub_length_of_monomialCharge_eq
    {left right : List (SignedMode Mode)}
    (hcharge : monomialCharge left = monomialCharge right) :
    ∃ k : Int, (left.length : Int) - (right.length : Int) = 2 * k := by
  rcases exists_two_mul_eq_sum_monomialCharge_sub_length left with ⟨k, hk⟩
  rcases exists_two_mul_eq_sum_monomialCharge_sub_length right with ⟨l, hl⟩
  refine ⟨l - k, ?_⟩
  have hsum : (∑ mode, monomialCharge left mode) =
      ∑ mode, monomialCharge right mode := by rw [hcharge]
  linarith

omit [Fintype Mode] [DecidableEq Mode] in
/-- Literal signed leaves preserve the usual binary-tree leaf count. -/
@[simp] theorem length_binaryTreeSignedLeaves
    (tree : RandomEigenmodeBinaryTree Mode) :
    (binaryTreeSignedLeaves tree).length = tree.shape.leafCount := by
  induction tree with
  | leaf mode => rfl
  | node output leftSign rightSign left right hleft hright =>
      simp [binaryTreeSignedLeaves, RandomEigenmodeBinaryTree.shape,
        BinaryInteractionTree.leafCount, hleft, hright]


/-! ## Even-root factorization and cumulant forests -/

/-- Total quadratic interaction power of an arbitrary signed forest. -/
def signedInteractionForestInteractionPower
    (forest : List (SignedInteractionTree Mode)) : Nat :=
  (forest.map fun entry => entry.2.shape.order).sum

omit [Fintype Mode] [DecidableEq Mode] in
/-- The flattened forest has one more leaf than vertex in each root. -/
theorem length_signedInteractionForestLeaves_eq_power_add_roots
    (forest : List (SignedInteractionTree Mode)) :
    (signedInteractionForestLeaves forest).length =
      signedInteractionForestInteractionPower forest + forest.length := by
  induction forest with
  | nil => rfl
  | cons entry forest ih =>
      rcases entry with ⟨outerSign, tree⟩
      have htail := ih
      simp only [signedInteractionForestLeaves,
        signedInteractionForestInteractionPower] at htail
      simp only [signedInteractionForestLeaves, List.flatMap_cons,
        List.length_append, List.length_map, length_binaryTreeSignedLeaves,
        signedInteractionForestInteractionPower, List.map_cons, List.sum_cons,
        List.length_cons]
      rw [BinaryInteractionTree.leafCount_eq_order_add_one, htail]
      omega

/-- A Haar-surviving arbitrary forest has an even total number of literal
initial leaves. -/
theorem signedInteractionForestLeaves_mod_two_eq_zero_of_charge_eq_zero
    (forest : List (SignedInteractionTree Mode))
    (hcharge : signedInteractionForestCharge forest = 0) :
    (signedInteractionForestLeaves forest).length % 2 = 0 := by
  have hparity :=
    exists_two_mul_eq_length_sub_length_of_monomialCharge_eq
      (left := signedInteractionForestLeaves forest) (right := [])
      (by simpa [signedInteractionForestCharge, monomialCharge] using hcharge)
  rcases hparity with ⟨k, hk⟩
  simp only [List.length_nil, Nat.cast_zero, sub_zero] at hk
  omega

/-- For an even number of external roots, Haar survival forces an even total
interaction power. This is the parity statement relevant to factorization
moments and even connected cumulants. -/
theorem signedInteractionForestInteractionPower_mod_two_eq_zero
    (forest : List (SignedInteractionTree Mode))
    (hcharge : signedInteractionForestCharge forest = 0)
    (hroots : forest.length % 2 = 0) :
    signedInteractionForestInteractionPower forest % 2 = 0 := by
  have hleaves :=
    signedInteractionForestLeaves_mod_two_eq_zero_of_charge_eq_zero
      forest hcharge
  rw [length_signedInteractionForestLeaves_eq_power_add_roots] at hleaves
  omega

/-- Derived interaction-pair count for an even-root Haar-surviving forest. -/
def signedInteractionForestPairCount
    (forest : List (SignedInteractionTree Mode)) : Nat :=
  signedInteractionForestInteractionPower forest / 2

/-- Exact paired-power identity for arbitrary even-root factorization or
cumulant forests. No pairing relation is stored in the forest. -/
theorem signedInteractionForestInteractionPower_eq_two_mul_pairCount
    (forest : List (SignedInteractionTree Mode))
    (hcharge : signedInteractionForestCharge forest = 0)
    (hroots : forest.length % 2 = 0) :
    signedInteractionForestInteractionPower forest =
      2 * signedInteractionForestPairCount forest := by
  have hmod := signedInteractionForestInteractionPower_mod_two_eq_zero
    forest hcharge hroots
  unfold signedInteractionForestPairCount
  omega

/-- Conditional arbitrary-forest power bound. The only additional input is
the analytic denominator-rank estimate, explicitly exposed as `hrank`. -/
theorem two_mul_independentLoss_le_signedInteractionForestInteractionPower
    (forest : List (SignedInteractionTree Mode))
    (independentLoss : Nat)
    (hcharge : signedInteractionForestCharge forest = 0)
    (hroots : forest.length % 2 = 0)
    (hrank : independentLoss ≤ signedInteractionForestPairCount forest) :
    2 * independentLoss ≤
      signedInteractionForestInteractionPower forest := by
  rw [signedInteractionForestInteractionPower_eq_two_mul_pairCount
    forest hcharge hroots]
  omega

/-! ## Haar-matched binary couples -/

/-- Total quadratic interaction power in an ordered history couple. -/
def coupleInteractionPower (couple : BinaryInteractionTreeCouple Mode) : Nat :=
  couple.1.shape.order + couple.2.shape.order

/-- Arithmetic half of the total interaction power.  It is derived from the
two existing trees and is not a Wick/Gaussian pairing datum. -/
def matchedInteractionPairCount
    (couple : BinaryInteractionTreeCouple Mode) : Nat :=
  coupleInteractionPower couple / 2

/-- Charge matching forces an even total number of interaction vertices. -/
theorem coupleInteractionPower_mod_two_eq_zero_of_leafPhaseBalanced
    (couple : BinaryInteractionTreeCouple Mode)
    (hbalanced : leafPhaseBalanced couple) :
    coupleInteractionPower couple % 2 = 0 := by
  have hcharge : binaryTreePhaseCharge couple.1 =
      binaryTreePhaseCharge couple.2 :=
    (leafPhaseBalanced_iff_charge_eq couple).mp hbalanced
  have hleaves :=
    exists_two_mul_eq_length_sub_length_of_monomialCharge_eq
      (left := binaryTreeSignedLeaves couple.1)
      (right := binaryTreeSignedLeaves couple.2)
      (by simpa [monomialCharge_binaryTreeSignedLeaves] using hcharge)
  rcases hleaves with ⟨k, hk⟩
  rw [length_binaryTreeSignedLeaves, length_binaryTreeSignedLeaves,
    BinaryInteractionTree.leafCount_eq_order_add_one,
    BinaryInteractionTree.leafCount_eq_order_add_one] at hk
  unfold coupleInteractionPower
  omega

/-- Every Haar-surviving couple has exactly twice its derived interaction
pair count. -/
theorem coupleInteractionPower_eq_two_mul_matchedInteractionPairCount
    (couple : BinaryInteractionTreeCouple Mode)
    (hbalanced : leafPhaseBalanced couple) :
    coupleInteractionPower couple =
      2 * matchedInteractionPairCount couple := by
  have hmod :=
    coupleInteractionPower_mod_two_eq_zero_of_leafPhaseBalanced
      couple hbalanced
  unfold matchedInteractionPairCount
  omega

/-- If analytic/combinatorial work bounds the number of independent
denominator losses by the charge-derived pair count, each such loss is paid
by at least two interaction powers.  This is the precise all-order frontier:
the loss-rank premise is not implied by Haar selection alone. -/
theorem two_mul_independentLoss_le_coupleInteractionPower
    (couple : BinaryInteractionTreeCouple Mode)
    (independentLoss : Nat)
    (hbalanced : leafPhaseBalanced couple)
    (hloss : independentLoss <= matchedInteractionPairCount couple) :
    2 * independentLoss <= coupleInteractionPower couple := by
  rw [coupleInteractionPower_eq_two_mul_matchedInteractionPairCount
    couple hbalanced]
  omega

/-! ## Existing arbitrary-order fixed-root raw couples -/

/-- A pair of actual raw histories at one fixed order carries exactly twice
that order in quadratic coupling power. -/
theorem fixedRootRawHistoryCouple_interactionPower_eq
    {N r : Nat} [NeZero N] (rootMomentum : Lattice.Site N)
    (couple : FixedRootRawCoupleIndex N r rootMomentum) :
    coupleInteractionPower
        (realizeFixedRootRawHistory rootMomentum couple.1,
          realizeFixedRootRawHistory rootMomentum couple.2) = 2 * r := by
  simp [coupleInteractionPower, realizeFixedRootRawHistory_shape_order]
  omega

/-- Nonzero initial Haar weight of an actual raw couple is equivalent to its
already-defined all-mode leaf-charge balance selector. -/
theorem integral_fixedRootRawHistoryCoupleCharacter_ne_zero_iff
    {N r : Nat} [NeZero N] (rootMomentum : Lattice.Site N)
    (couple : FixedRootRawCoupleIndex N r rootMomentum) :
    (∫ phase : UnitAddTorus (Lattice.Site N),
      fixedRootRawHistoryCoupleCharacter rootMomentum couple phase
      ∂finitePhaseHaarLaw (Lattice.Site N)) ≠ 0 ↔
      leafPhaseBalanced
        (realizeFixedRootRawHistory rootMomentum couple.1,
          realizeFixedRootRawHistory rootMomentum couple.2) := by
  rw [integral_fixedRootRawHistoryCoupleCharacter_eq_ite]
  by_cases hbalanced : leafPhaseBalanced
      (realizeFixedRootRawHistory rootMomentum couple.1,
        realizeFixedRootRawHistory rootMomentum couple.2) <;>
    simp [hbalanced]

/-- Thus every Haar-surviving fixed-order raw couple has exact effective
coupling power `2r`, with no added pairing structure. -/
theorem haarSurviving_fixedRootRawHistoryCouple_power_eq_two_mul_order
    {N r : Nat} [NeZero N] (rootMomentum : Lattice.Site N)
    (couple : FixedRootRawCoupleIndex N r rootMomentum)
    (_hsurvives :
      (∫ phase : UnitAddTorus (Lattice.Site N),
        fixedRootRawHistoryCoupleCharacter rootMomentum couple phase
        ∂finitePhaseHaarLaw (Lattice.Site N)) ≠ 0) :
    coupleInteractionPower
        (realizeFixedRootRawHistory rootMomentum couple.1,
          realizeFixedRootRawHistory rootMomentum couple.2) = 2 * r :=
  fixedRootRawHistoryCouple_interactionPower_eq rootMomentum couple


/-! ## Exact two-step parity strengthening -/

/-- A sum of two signed unit charges cannot equal a sum of three signed unit
charges. Repeated modes and internal cancellations are allowed. -/
theorem two_signedMode_charges_ne_three_signedMode_charges
    (left0 left1 right0 right1 right2 : SignedMode Mode) :
    left0.charge + left1.charge ≠
      right0.charge + right1.charge + right2.charge := by
  intro hcharge
  have hparity :=
    exists_two_mul_eq_length_sub_length_of_monomialCharge_eq
      (left := [left0, left1]) (right := [right0, right1, right2])
      (by simpa [monomialCharge, add_assoc] using hcharge)
  rcases hparity with ⟨k, hk⟩
  norm_num at hk
  omega

/-- Every quadratic `A1` charge differs from every direct-cubic `A2`
charge. -/
theorem quadraticPhaseCharge_ne_cubicPhaseCharge
    {N : Nat} [NeZero N] (first : QuadraticPhaseTerm N)
    (second : CubicPhaseTerm N) :
    quadraticPhaseCharge first ≠ cubicPhaseCharge second := by
  exact two_signedMode_charges_ne_three_signedMode_charges
    (binarySignedMode (first.1 0) first.2.1)
    (binarySignedMode (first.1 1) first.2.2)
    (binarySignedMode (second.1 0) (second.2 0))
    (binarySignedMode (second.1 1) (second.2 1))
    (binarySignedMode (second.1 2) (second.2 2))

/-- Every quadratic `A1` charge also differs from every iterated-quadratic
second-Picard `A2` charge: the latter has three literal initial leaves. -/
theorem quadraticPhaseCharge_ne_iteratedQuadraticSecondPicardCharge
    {N : Nat} [NeZero N] (first : QuadraticPhaseTerm N)
    (second : IteratedQuadraticSecondPicardCharacterTerm N) :
    quadraticPhaseCharge first ≠
      iteratedQuadraticSecondPicardCharge second := by
  rw [iteratedQuadraticSecondPicardCharge_eq_threeLegs]
  exact two_signedMode_charges_ne_three_signedMode_charges
    (binarySignedMode (first.1 0) first.2.1)
    (binarySignedMode (first.1 1) first.2.2)
    (iteratedQuadraticFreeSignedLeg second)
    (adjustedFirstPicardInnerLeg
      (iteratedQuadraticInnerEntry second) 0)
    (adjustedFirstPicardInnerLeg
      (iteratedQuadraticInnerEntry second) 1)

/-- Hence no `A1` index and complete `A2` index can pass the equal-charge
Haar selector. -/
theorem quadraticPhaseCharge_ne_completeSecondPicardCharge
    {N : Nat} [NeZero N] (first : QuadraticPhaseTerm N)
    (second : CompleteSecondPicardCharacterTerm N) :
    quadraticPhaseCharge first ≠ completeSecondPicardCharge second := by
  rcases second with second | second
  · exact quadraticPhaseCharge_ne_iteratedQuadraticSecondPicardCharge
      first second
  · exact quadraticPhaseCharge_ne_cubicPhaseCharge first second

/-- The complete equal-charge `A1`--`A2` cross sum is empty, independently
of all deterministic coefficients. -/
theorem equalChargeCrossPairSum_quadratic_completeSecondPicard_eq_zero
    {N : Nat} [NeZero N]
    (firstCoefficient : QuadraticPhaseTerm N → Complex)
    (secondCoefficient : CompleteSecondPicardCharacterTerm N → Complex) :
    equalChargeCrossPairSum firstCoefficient quadraticPhaseCharge
        secondCoefficient completeSecondPicardCharge = 0 := by
  classical
  unfold equalChargeCrossPairSum
  apply Finset.sum_eq_zero
  intro first hfirst
  apply Finset.sum_eq_zero
  intro second hsecond
  rw [if_neg
    (quadraticPhaseCharge_ne_completeSecondPicardCharge first second)]

/-- Consequently the physical order-`g^3` two-step interference vanishes
exactly. -/
theorem equalChargeFamilyInterference_quadratic_completeSecondPicard_eq_zero
    {N : Nat} [NeZero N]
    (firstCoefficient : QuadraticPhaseTerm N → Complex)
    (secondCoefficient : CompleteSecondPicardCharacterTerm N → Complex) :
    equalChargeFamilyInterference firstCoefficient quadraticPhaseCharge
        secondCoefficient completeSecondPicardCharge = 0 := by
  unfold equalChargeFamilyInterference
  rw [equalChargeCrossPairSum_quadratic_completeSecondPicard_eq_zero]
  norm_num

/-- The fixed-mass physical matched polynomial contains only even coupling
powers `g^0`, `g^2`, and `g^4`. Its first permitted nonconstant
Haar-surviving power is therefore `g^2`. -/
theorem physlibMatchedChargeTwoStepMoment_eq_evenCouplingPowers
    {N : Nat} [NeZero N]
    (m : Lattice.PositiveMassConfig N) (kappa beta g : Real)
    (radius : Lattice.Site N → Real) (time : Real)
    (observed : Lattice.Site N) :
    physlibMatchedChargeTwoStepMoment m kappa beta g radius time observed =
      sameChargeFamilySquare
          (freeInitialPhaseCoefficient radius (modeFrequency m) observed)
          (freeInitialPhaseCharge observed) +
        g ^ 2 * finiteCharacterFamilySecondOrderCoefficient
          (freeInitialPhaseCoefficient radius (modeFrequency m) observed)
          (freeInitialPhaseCharge observed)
          (physlibQuadraticFirstPicardCharacterCoefficient
            m kappa radius time observed)
          quadraticPhaseCharge
          (completeSecondPicardCoefficient
            m kappa beta radius observed time)
          completeSecondPicardCharge +
        g ^ 4 * sameChargeFamilySquare
          (completeSecondPicardCoefficient
            m kappa beta radius observed time)
          completeSecondPicardCharge := by
  rw [physlibMatchedChargeTwoStepMoment_eq_without_firstOrder,
    equalChargeFamilyInterference_quadratic_completeSecondPicard_eq_zero]
  ring

/-- The same strengthening at the reference-moment level: after subtracting
the initial moment, the exact two-step increment starts at `g^2` and has no
odd coupling power. -/
theorem physlibReferenceTwoStepHaarMoment_sub_initial_eq_evenCouplingPowers
    {N : Nat} [NeZero N]
    (m : Lattice.PositiveMassConfig N) (kappa beta : Real)
    (radius : Lattice.Site N → Real) (time : Real)
    (observed : Lattice.Site N) (g : Real)
    (homega : 0 < modeFrequency m observed) :
    physlibReferenceTwoStepHaarMoment
          m kappa beta g radius time observed -
        physlibReferenceInitialHaarMoment m radius observed =
      g ^ 2 * physlibHaarFiniteTimeKineticCoefficient
          m kappa beta radius time observed +
        g ^ 4 * sameChargeFamilySquare
          (completeSecondPicardCoefficient
            m kappa beta radius observed time)
          completeSecondPicardCharge := by
  rw [physlibReferenceTwoStepHaarMoment_sub_initial_eq_no_firstOrder
    m kappa beta radius time observed g homega,
    equalChargeFamilyInterference_quadratic_completeSecondPicard_eq_zero]
  ring

/-! ## From paired power to a feasible cutoff -/

/-- The derived estimate `power >= 2 * loss` gives the strict kinetic cutoff
margin as soon as there is more than one independent loss. -/
theorem independentLoss_add_one_lt_power_of_two_mul_le
    {independentLoss power : Nat} (hloss : 1 < independentLoss)
    (hpower : 2 * independentLoss ≤ power) :
    independentLoss + 1 < power := by
  omega

/-- Therefore a quadratic regular-good channel with more than one independent
loss admits a cutoff exponent whenever Haar matching plus the denominator-rank
bound supplies `power >= 2 * loss`. -/
theorem exists_quadraticCutoffExponent_of_two_mul_independentLoss_le_power
    {independentLoss power : Nat} (hloss : 1 < independentLoss)
    (hpower : 2 * independentLoss ≤ power) :
    ∃ alpha,
      CutoffExponentAdmissible (power : Real) (independentLoss : Real)
        quadraticKineticDeficit alpha := by
  have hloss0 : 0 < (independentLoss : Real) := by
    exact_mod_cast (show 0 < independentLoss by omega)
  rw [exists_cutoffExponentAdmissible_iff hloss0]
  unfold quadraticKineticDeficit
  norm_num
  exact_mod_cast
    independentLoss_add_one_lt_power_of_two_mul_le hloss hpower

/-- In particular the exact matched power `p = 2 * loss` has a nonempty
cutoff interval for every `loss > 1`. -/
theorem exists_quadraticCutoffExponent_for_exactMatchedPower
    {independentLoss : Nat} (hloss : 1 < independentLoss) :
    ∃ alpha,
      CutoffExponentAdmissible ((2 * independentLoss : Nat) : Real)
        (independentLoss : Real) quadraticKineticDeficit alpha := by
  exact exists_quadraticCutoffExponent_of_two_mul_independentLoss_le_power
    hloss le_rfl


/-- Explicit midpoint cutoff selected by the proved feasibility interval for
an exact matched power `p = 2 * loss`. -/
def exactMatchedMidpointCutoffExponent (independentLoss : Nat) : Real :=
  midpointCutoffExponent ((2 * independentLoss : Nat) : Real)
    (independentLoss : Real) quadraticKineticDeficit

/-- The displayed midpoint is admissible whenever `loss > 1`; thus the
cutoff is constructive, not merely existential. -/
theorem exactMatchedMidpointCutoffExponent_admissible
    {independentLoss : Nat} (hloss : 1 < independentLoss) :
    CutoffExponentAdmissible ((2 * independentLoss : Nat) : Real)
      (independentLoss : Real) quadraticKineticDeficit
      (exactMatchedMidpointCutoffExponent independentLoss) := by
  unfold exactMatchedMidpointCutoffExponent
  apply midpointCutoffExponent_admissible
  · exact_mod_cast (show 0 < independentLoss by omega)
  · unfold quadraticKineticDeficit
    norm_num
    exact_mod_cast (show independentLoss + 1 < 2 * independentLoss by omega)

/-- All-order conditional bridge for a Haar-balanced couple. The sole
unproved model-specific input is the displayed independent-loss rank bound;
the coupling power and cutoff conclusion are then derived. -/
theorem haarMatchedCouple_exists_quadraticCutoffExponent
    (couple : BinaryInteractionTreeCouple Mode)
    (independentLoss : Nat) (hloss : 1 < independentLoss)
    (hbalanced : leafPhaseBalanced couple)
    (hrank : independentLoss ≤ matchedInteractionPairCount couple) :
    ∃ alpha,
      CutoffExponentAdmissible (coupleInteractionPower couple : Real)
        (independentLoss : Real) quadraticKineticDeficit alpha := by
  apply exists_quadraticCutoffExponent_of_two_mul_independentLoss_le_power
    hloss
  exact two_mul_independentLoss_le_coupleInteractionPower
    couple independentLoss hbalanced hrank


/-- Even-root factorization/cumulant version of the conditional cutoff bridge.
Again, `hrank` is exactly the unproved analytic/combinatorial induction. -/
theorem haarSurvivingEvenRootForest_exists_quadraticCutoffExponent
    (forest : List (SignedInteractionTree Mode))
    (independentLoss : Nat) (hloss : 1 < independentLoss)
    (hcharge : signedInteractionForestCharge forest = 0)
    (hroots : forest.length % 2 = 0)
    (hrank : independentLoss ≤ signedInteractionForestPairCount forest) :
    ∃ alpha,
      CutoffExponentAdmissible
        (signedInteractionForestInteractionPower forest : Real)
        (independentLoss : Real) quadraticKineticDeficit alpha := by
  apply exists_quadraticCutoffExponent_of_two_mul_independentLoss_le_power
    hloss
  exact two_mul_independentLoss_le_signedInteractionForestInteractionPower
    forest independentLoss hcharge hroots hrank


end

end ArchonPhysics.CanonicalIIDCoerciveHaarMatchedCouplingPower
