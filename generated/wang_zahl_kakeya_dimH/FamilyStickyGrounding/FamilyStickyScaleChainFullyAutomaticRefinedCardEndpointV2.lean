import FamilyStickyGrounding.FamilyStickyScaleChainIdentitySeedLocalCardBudgetV2
import FamilyStickyGrounding.FamilyStickyScaleChainFullyAutomaticRefinedNonemptyBridgeV2

set_option autoImplicit false
set_option warningAsError true
set_option linter.unusedSectionVars false
set_option maxHeartbeats 3000000

open scoped BigOperators ENNReal NNReal

namespace FamilyStickyScaleChainFullyAutomaticRefinedCardEndpointV2

open LeanEval.Analysis.WangZahlKakeya
open Submission.Kakeya.ConvexFactoring
open Submission.Kakeya.Uniformity
open FamilyStickyDividingScalesFiniteStoppingV1
open FamilyStickyScaleChainCoherentIntervalProducerV1
open FamilyStickyScaleChainTwoExponentStoppingCoreV2
open FamilyStickyScaleChainTwoParameterRecoveredEndpointV2
open FamilyStickyScaleChainLocalCardBudgetInvariantV2
open FamilyStickyScaleChainFixedLocalCardCountedDriverV2
open FamilyStickyScaleChainFullyAutomaticFixedLocalCardEndpointV2
open FamilyStickyScaleChainIdentitySeedLocalCardBudgetV2
open FamilyStickyScaleChainFullyAutomaticRefinedNonemptyBridgeV2
open FamilyStickyScaleChainSelectedCanonicalCoverCoordinatesProducerV1
open FamilyStickyCapturedTubeBoxWidthV1
open FamilyStickyHierarchyRandomMotionAdapterV1
open FamilyStickyHierarchyPreMotionHullTestSupportV1
open FamilyStickyHierarchyWidenedCrossParentSourceBoundV1

noncomputable section

/-!
# Fully automatic endpoint at the exact refined cardinality

For the identity coherent cover, every adjacent active-fine cardinality is
exactly the cardinality of the original refined family.  Specializing the
fixed-local-card recursion to that exact natural number therefore removes
its final seed-budget premise without falling back to the ambient index
cardinality.

The hierarchy section records two deliberately separate interfaces.  The
exact-refined-card threshold uses the numerically smallest available card
input.  The structural threshold uses the hierarchy's level-zero
parent-count times branching-product bound.  The latter exposes the
multiscale source of the estimate, but no monotonicity comparison between
the two nonlinear thresholds is asserted, so it is not claimed to be
numerically sharper.
-/

universe u

variable {delta : NNReal} {gapEpsilon targetExponent : Real}
  {N : Nat} {eta : Nat -> Real}
  {iota : Type u} [Fintype iota] [DecidableEq iota]
  {fine : UniformTubeFamily delta iota}

/-! ## Exact refined-card cap and threshold -/

/-- The automatic theta cap with the exact refined-family cardinality as
its local-card input. -/
def fullyAutomaticRefinedCardThetaCap
    (fine : UniformTubeFamily delta iota) (eta : Nat -> Real)
    (N : Nat) : NNReal :=
  fullyAutomaticFixedLocalCardThetaCap
    fine.refinement.refined.card eta N

theorem fullyAutomaticRefinedCardThetaCap_pos
    (fine : UniformTubeFamily delta iota) (eta : Nat -> Real)
    (N : Nat) :
    0 < fullyAutomaticRefinedCardThetaCap fine eta N := by
  exact fullyAutomaticFixedLocalCardThetaCap_pos
    fine.refinement.refined.card eta N

/-- The single fixed-local-card threshold specialized to the exact
refined-family cardinality. -/
def fullyAutomaticRefinedCardDeltaThreshold
    (fine : UniformTubeFamily delta iota) (eta : Nat -> Real)
    (N : Nat) (gapEpsilon : Real) : NNReal :=
  fullyAutomaticFixedLocalCardDeltaThreshold
    fine.refinement.refined.card eta N gapEpsilon

theorem fullyAutomaticRefinedCardDeltaThreshold_pos
    (fine : UniformTubeFamily delta iota) (eta : Nat -> Real)
    (N : Nat) (gapEpsilon : Real) :
    0 < fullyAutomaticRefinedCardDeltaThreshold
      fine eta N gapEpsilon := by
  exact fullyAutomaticFixedLocalCardDeltaThreshold_pos
    fine.refinement.refined.card eta N gapEpsilon

theorem fullyAutomaticRefinedCardDeltaThreshold_le_cap
    (fine : UniformTubeFamily delta iota) (eta : Nat -> Real)
    (N : Nat) (gapEpsilon : Real) :
    fullyAutomaticRefinedCardDeltaThreshold fine eta N gapEpsilon <=
      fullyAutomaticRefinedCardThetaCap fine eta N := by
  exact fullyAutomaticFixedLocalCardDeltaThreshold_le_cap
    fine.refinement.refined.card eta N gapEpsilon

theorem fullyAutomaticRefinedCardDeltaThreshold_le_one
    (fine : UniformTubeFamily delta iota) (eta : Nat -> Real)
    (N : Nat) (gapEpsilon : Real) :
    fullyAutomaticRefinedCardDeltaThreshold fine eta N gapEpsilon <= 1 := by
  exact fullyAutomaticFixedLocalCardDeltaThreshold_le_one
    fine.refinement.refined.card eta N gapEpsilon

theorem fullyAutomaticRefinedCardDeltaThreshold_lt_one
    (fine : UniformTubeFamily delta iota) (eta : Nat -> Real)
    {N : Nat} (N_pos : 1 <= N) (gapEpsilon : Real) :
    fullyAutomaticRefinedCardDeltaThreshold fine eta N gapEpsilon < 1 := by
  exact fullyAutomaticFixedLocalCardDeltaThreshold_lt_one
    fine.refinement.refined.card eta N_pos gapEpsilon

theorem delta_lt_one_of_le_fullyAutomaticRefinedCardDeltaThreshold
    (fine : UniformTubeFamily delta iota) (eta : Nat -> Real)
    {N : Nat} (N_pos : 1 <= N) (gapEpsilon : Real)
    (delta_le : delta <=
      fullyAutomaticRefinedCardDeltaThreshold fine eta N gapEpsilon) :
    delta < 1 := by
  exact delta_lt_one_of_le_fullyAutomaticFixedLocalCardDeltaThreshold
    fine.refinement.refined.card eta N_pos gapEpsilon delta_le

/-! ## Seed, budget, initial state, and terminal state -/

/-- Readable name for the literal capped seed at the exact refined-card
threshold. -/
def fullyAutomaticRefinedCardSeed
    (fine : UniformTubeFamily delta iota) (eta : Nat -> Real)
    (N : Nat) (gap_pos : 0 < gapEpsilon)
    (delta_le : delta <=
      fullyAutomaticRefinedCardDeltaThreshold fine eta N gapEpsilon) :
    FiniteScaleSequence delta 2 :=
  fullyAutomaticFixedLocalCardSeed fine.refinement.refined.card
    eta N gap_pos delta_le

/-- The identity seed budget is automatic at the exact refined
cardinality. -/
theorem identity_fullyAutomaticRefinedCardSeedBudget
    (fine : UniformTubeFamily delta iota) (eta : Nat -> Real)
    (N : Nat) (gap_pos : 0 < gapEpsilon)
    (delta_le : delta <=
      fullyAutomaticRefinedCardDeltaThreshold fine eta N gapEpsilon) :
    NonLargeLocalCardBudget (identityRadiusCoherentCover fine)
      (fullyAutomaticRefinedCardSeed fine eta N gap_pos delta_le)
      gapEpsilon fine.refinement.refined.card := by
  simpa [fullyAutomaticRefinedCardSeed] using
    (identity_fullyAutomaticFixedLocalCardSeedBudget_of_refined_card_le
      fine fine.refinement.refined.card eta N gap_pos delta_le le_rfl)

/-- The exact-refined-card initial state; its seed budget is generated
internally from the identity-cover cardinality formula. -/
def fullyAutomaticRefinedCardInitialState
    (fine : UniformTubeFamily delta iota)
    (delta_pos : 0 < delta) (gap_pos : 0 < gapEpsilon)
    (two_lt_eta_zero : 2 < eta 0)
    (exponent_budget : 1 <
      (gapEpsilon * gapEpsilon) * (N : Real))
    (fine_refined_nonempty : fine.refinement.refined.Nonempty)
    (delta_le : delta <=
      fullyAutomaticRefinedCardDeltaThreshold fine eta N gapEpsilon) :
    RelevantFixedLocalCardCountedState
      (identityRadiusCoherentCover fine) N gapEpsilon eta
      (fullyAutomaticRefinedCardThetaCap fine eta N)
      fine.refinement.refined.card :=
  fullyAutomaticFixedLocalCardInitialState
    (identityRadiusCoherentCover fine) fine.refinement.refined.card
    delta_pos gap_pos two_lt_eta_zero exponent_budget
    fine_refined_nonempty delta_le
    (identity_fullyAutomaticFixedLocalCardSeedBudget_of_refined_card_le
      fine fine.refinement.refined.card eta N gap_pos delta_le le_rfl)

/-- The terminal state of the exact-refined-card recursion. -/
def fullyAutomaticRefinedCardTerminalState
    (fine : UniformTubeFamily delta iota)
    (delta_pos : 0 < delta) (gap_pos : 0 < gapEpsilon)
    (eta_monotone : Monotone eta) (two_lt_eta_zero : 2 < eta 0)
    (exponent_budget : 1 <
      (gapEpsilon * gapEpsilon) * (N : Real))
    (fine_refined_nonempty : fine.refinement.refined.Nonempty)
    (delta_le : delta <=
      fullyAutomaticRefinedCardDeltaThreshold fine eta N gapEpsilon) :
    RelevantFixedLocalCardCountedState
      (identityRadiusCoherentCover fine) N gapEpsilon eta
      (fullyAutomaticRefinedCardThetaCap fine eta N)
      fine.refinement.refined.card :=
  fullyAutomaticFixedLocalCardTerminalState
    (identityRadiusCoherentCover fine) fine.refinement.refined.card
    delta_pos gap_pos eta_monotone two_lt_eta_zero exponent_budget
    fine_refined_nonempty delta_le
    (identity_fullyAutomaticFixedLocalCardSeedBudget_of_refined_card_le
      fine fine.refinement.refined.card eta N gap_pos delta_le le_rfl)

/-- The computed terminal stage of the exact-refined-card recursion. -/
def fullyAutomaticRefinedCardTerminalStage
    (fine : UniformTubeFamily delta iota)
    (delta_pos : 0 < delta) (gap_pos : 0 < gapEpsilon)
    (eta_monotone : Monotone eta) (two_lt_eta_zero : 2 < eta 0)
    (exponent_budget : 1 <
      (gapEpsilon * gapEpsilon) * (N : Real))
    (fine_refined_nonempty : fine.refinement.refined.Nonempty)
    (delta_le : delta <=
      fullyAutomaticRefinedCardDeltaThreshold fine eta N gapEpsilon) : Nat :=
  fullyAutomaticFixedLocalCardTerminalStage
    (identityRadiusCoherentCover fine) fine.refinement.refined.card
    delta_pos gap_pos eta_monotone two_lt_eta_zero exponent_budget
    fine_refined_nonempty delta_le
    (identity_fullyAutomaticFixedLocalCardSeedBudget_of_refined_card_le
      fine fine.refinement.refined.card eta N gap_pos delta_le le_rfl)

/-! ## Identity endpoint with no public seed budget -/

/-- The exact refined cardinality discharges the identity seed budget, so
the public endpoint retains only geometric nonemptiness and numerical
premises. -/
theorem identityFullyAutomaticRefinedCard_sticky_or_recoveredWitness
    (fine : UniformTubeFamily delta iota)
    (delta_pos : 0 < delta) (gap_pos : 0 < gapEpsilon)
    (eta_monotone : Monotone eta) (two_lt_eta_zero : 2 < eta 0)
    (exponent_budget : 1 <
      (gapEpsilon * gapEpsilon) * (N : Real))
    (room_at_bound : eta N < targetExponent)
    (fine_refined_nonempty : fine.refinement.refined.Nonempty)
    (delta_le : delta <=
      fullyAutomaticRefinedCardDeltaThreshold fine eta N gapEpsilon) :
    (identityRadiusCoherentCover fine).base.IsStickyAtEveryScale
        ((Fintype.card iota : ENNReal) * capturedTubeBoxLoss delta 1)
        (((Fintype.card iota : ENNReal) * capturedTubeBoxLoss delta 1) *
          (Fintype.card iota : ENNReal)) \/
      Nonempty (TwoExponentKatzTaoDividingWitness delta N gapEpsilon
        targetExponent
        (recoveredProfileV2 eta
          (fullyAutomaticRefinedCardTerminalStage fine delta_pos gap_pos
            eta_monotone two_lt_eta_zero exponent_budget
            fine_refined_nonempty delta_le)
          targetExponent)) := by
  simpa [fullyAutomaticRefinedCardTerminalStage] using
    (identityFullyAutomaticFixedLocalCard_sticky_or_recoveredWitness
      fine fine.refinement.refined.card delta_pos gap_pos eta_monotone
      two_lt_eta_zero exponent_budget room_at_bound fine_refined_nonempty
      delta_le
      (identity_fullyAutomaticFixedLocalCardSeedBudget_of_refined_card_le
        fine fine.refinement.refined.card eta N gap_pos delta_le le_rfl))

/-- V1 literal-witness projection of the exact-refined-card endpoint. -/
theorem identityFullyAutomaticRefinedCard_sticky_or_recoveredLiteralWitness
    (fine : UniformTubeFamily delta iota)
    (delta_pos : 0 < delta) (gap_pos : 0 < gapEpsilon)
    (eta_monotone : Monotone eta) (two_lt_eta_zero : 2 < eta 0)
    (exponent_budget : 1 <
      (gapEpsilon * gapEpsilon) * (N : Real))
    (room_at_bound : eta N < targetExponent)
    (fine_refined_nonempty : fine.refinement.refined.Nonempty)
    (delta_le : delta <=
      fullyAutomaticRefinedCardDeltaThreshold fine eta N gapEpsilon) :
    (identityRadiusCoherentCover fine).base.IsStickyAtEveryScale
        ((Fintype.card iota : ENNReal) * capturedTubeBoxLoss delta 1)
        (((Fintype.card iota : ENNReal) * capturedTubeBoxLoss delta 1) *
          (Fintype.card iota : ENNReal)) \/
      Nonempty (KatzTaoDividingWitness delta N gapEpsilon
        (recoveredProfileV2 eta
          (fullyAutomaticRefinedCardTerminalStage fine delta_pos gap_pos
            eta_monotone two_lt_eta_zero exponent_budget
            fine_refined_nonempty delta_le)
          targetExponent)) := by
  rcases identityFullyAutomaticRefinedCard_sticky_or_recoveredWitness
      fine delta_pos gap_pos eta_monotone two_lt_eta_zero exponent_budget
      room_at_bound fine_refined_nonempty delta_le with sticky | witness
  · exact Or.inl sticky
  · rcases witness with ⟨W⟩
    exact Or.inr ⟨W.toV1⟩

/-! ## Positive-depth hierarchy adapters -/

variable {depth : Nat} {nominalRadius : Nat -> NNReal}
  {Index : Nat -> Type u}
  [forall l, Fintype (Index l)] [forall l, DecidableEq (Index l)]

/-- The hierarchy's explicit level-zero structural local-card bound. -/
def hierarchyZeroLocalCardBound
    (H : MultiscaleTubeHierarchy depth nominalRadius Index)
    (hdepth : 0 < depth) : Nat :=
  hierarchyIdentitySeedLocalCardBound H ⟨0, hdepth⟩

/-- The exact refined cardinality is bounded by the hierarchy's structural
level-zero parent-count/branching-product expression. -/
theorem hierarchyEffectiveFamilyZero_refined_card_le_zeroLocalCardBound
    (H : MultiscaleTubeHierarchy depth nominalRadius Index)
    (hdepth : 0 < depth) :
    (H.effectiveFamily 0).refinement.refined.card <=
      hierarchyZeroLocalCardBound H hdepth := by
  unfold hierarchyZeroLocalCardBound hierarchyIdentitySeedLocalCardBound
  change (H.family 0).refinement.refined.card <=
    hierarchyLayerParentCount (H := H) ⟨0, hdepth⟩ *
      H.branchingProduct 0 (0 + 1) (by omega)
  exact initialFine_card_le_parentCount_mul_branchingProduct
    (H := H) ⟨0, hdepth⟩

/-- A structural alternative to the exact refined-card threshold.  It is
useful when callers want the hierarchy branching data visible in the API;
no claim is made that it is larger than the exact threshold. -/
def hierarchyZeroLocalCardDeltaThreshold
    (H : MultiscaleTubeHierarchy depth nominalRadius Index)
    (hdepth : 0 < depth) (eta : Nat -> Real) (N : Nat)
    (gapEpsilon : Real) : NNReal :=
  fullyAutomaticFixedLocalCardDeltaThreshold
    (hierarchyZeroLocalCardBound H hdepth) eta N gapEpsilon

theorem hierarchyZeroLocalCardDeltaThreshold_pos
    (H : MultiscaleTubeHierarchy depth nominalRadius Index)
    (hdepth : 0 < depth) (eta : Nat -> Real) (N : Nat)
    (gapEpsilon : Real) :
    0 < hierarchyZeroLocalCardDeltaThreshold
      H hdepth eta N gapEpsilon := by
  exact fullyAutomaticFixedLocalCardDeltaThreshold_pos
    (hierarchyZeroLocalCardBound H hdepth) eta N gapEpsilon

theorem hierarchyZeroLocalCardDeltaThreshold_le_one
    (H : MultiscaleTubeHierarchy depth nominalRadius Index)
    (hdepth : 0 < depth) (eta : Nat -> Real) (N : Nat)
    (gapEpsilon : Real) :
    hierarchyZeroLocalCardDeltaThreshold H hdepth eta N gapEpsilon <= 1 := by
  exact fullyAutomaticFixedLocalCardDeltaThreshold_le_one
    (hierarchyZeroLocalCardBound H hdepth) eta N gapEpsilon

theorem hierarchyZeroLocalCardDeltaThreshold_lt_one
    (H : MultiscaleTubeHierarchy depth nominalRadius Index)
    (hdepth : 0 < depth) (eta : Nat -> Real) {N : Nat}
    (N_pos : 1 <= N) (gapEpsilon : Real) :
    hierarchyZeroLocalCardDeltaThreshold H hdepth eta N gapEpsilon < 1 := by
  exact fullyAutomaticFixedLocalCardDeltaThreshold_lt_one
    (hierarchyZeroLocalCardBound H hdepth) eta N_pos gapEpsilon

/-- Positive depth supplies refined nonemptiness for the numerically exact
refined-card endpoint. -/
theorem identityFullyAutomaticRefinedCard_sticky_or_recoveredWitness_of_hierarchy
    (H : MultiscaleTubeHierarchy depth nominalRadius Index)
    (hdepth : 0 < depth)
    (delta_pos : 0 < H.effectiveRadius 0)
    (gap_pos : 0 < gapEpsilon)
    (eta_monotone : Monotone eta) (two_lt_eta_zero : 2 < eta 0)
    (exponent_budget : 1 <
      (gapEpsilon * gapEpsilon) * (N : Real))
    (room_at_bound : eta N < targetExponent)
    (delta_le : H.effectiveRadius 0 <=
      fullyAutomaticRefinedCardDeltaThreshold
        (H.effectiveFamily 0) eta N gapEpsilon) :
    (identityRadiusCoherentCover
        (H.effectiveFamily 0)).base.IsStickyAtEveryScale
      ((Fintype.card (Index 0) : ENNReal) *
        capturedTubeBoxLoss (H.effectiveRadius 0) 1)
      (((Fintype.card (Index 0) : ENNReal) *
          capturedTubeBoxLoss (H.effectiveRadius 0) 1) *
        (Fintype.card (Index 0) : ENNReal)) \/
      Nonempty (TwoExponentKatzTaoDividingWitness
        (H.effectiveRadius 0) N gapEpsilon targetExponent
        (recoveredProfileV2 eta
          (fullyAutomaticRefinedCardTerminalStage
            (H.effectiveFamily 0) delta_pos gap_pos eta_monotone
            two_lt_eta_zero exponent_budget
            (hierarchyEffectiveFamilyZero_refined_nonempty H hdepth)
            delta_le)
          targetExponent)) :=
  identityFullyAutomaticRefinedCard_sticky_or_recoveredWitness
    (H.effectiveFamily 0) delta_pos gap_pos eta_monotone
    two_lt_eta_zero exponent_budget room_at_bound
    (hierarchyEffectiveFamilyZero_refined_nonempty H hdepth) delta_le

/-- V1 literal-witness form of the exact positive-depth hierarchy
endpoint. -/
theorem identityFullyAutomaticRefinedCard_sticky_or_recoveredLiteralWitness_of_hierarchy
    (H : MultiscaleTubeHierarchy depth nominalRadius Index)
    (hdepth : 0 < depth)
    (delta_pos : 0 < H.effectiveRadius 0)
    (gap_pos : 0 < gapEpsilon)
    (eta_monotone : Monotone eta) (two_lt_eta_zero : 2 < eta 0)
    (exponent_budget : 1 <
      (gapEpsilon * gapEpsilon) * (N : Real))
    (room_at_bound : eta N < targetExponent)
    (delta_le : H.effectiveRadius 0 <=
      fullyAutomaticRefinedCardDeltaThreshold
        (H.effectiveFamily 0) eta N gapEpsilon) :
    (identityRadiusCoherentCover
        (H.effectiveFamily 0)).base.IsStickyAtEveryScale
      ((Fintype.card (Index 0) : ENNReal) *
        capturedTubeBoxLoss (H.effectiveRadius 0) 1)
      (((Fintype.card (Index 0) : ENNReal) *
          capturedTubeBoxLoss (H.effectiveRadius 0) 1) *
        (Fintype.card (Index 0) : ENNReal)) \/
      Nonempty (KatzTaoDividingWitness
        (H.effectiveRadius 0) N gapEpsilon
        (recoveredProfileV2 eta
          (fullyAutomaticRefinedCardTerminalStage
            (H.effectiveFamily 0) delta_pos gap_pos eta_monotone
            two_lt_eta_zero exponent_budget
            (hierarchyEffectiveFamilyZero_refined_nonempty H hdepth)
            delta_le)
          targetExponent)) :=
  identityFullyAutomaticRefinedCard_sticky_or_recoveredLiteralWitness
    (H.effectiveFamily 0) delta_pos gap_pos eta_monotone
    two_lt_eta_zero exponent_budget room_at_bound
    (hierarchyEffectiveFamilyZero_refined_nonempty H hdepth) delta_le

/-- The hierarchy-structural local-card threshold also gives a complete
endpoint.  Its seed budget is supplied by the branching-product source
bound, rather than by an exposed caller hypothesis. -/
theorem identityFullyAutomaticHierarchyZeroLocalCard_sticky_or_recoveredWitness
    (H : MultiscaleTubeHierarchy depth nominalRadius Index)
    (hdepth : 0 < depth)
    (delta_pos : 0 < H.effectiveRadius 0)
    (gap_pos : 0 < gapEpsilon)
    (eta_monotone : Monotone eta) (two_lt_eta_zero : 2 < eta 0)
    (exponent_budget : 1 <
      (gapEpsilon * gapEpsilon) * (N : Real))
    (room_at_bound : eta N < targetExponent)
    (delta_le : H.effectiveRadius 0 <=
      hierarchyZeroLocalCardDeltaThreshold
        H hdepth eta N gapEpsilon) :
    (identityRadiusCoherentCover
        (H.effectiveFamily 0)).base.IsStickyAtEveryScale
      ((Fintype.card (Index 0) : ENNReal) *
        capturedTubeBoxLoss (H.effectiveRadius 0) 1)
      (((Fintype.card (Index 0) : ENNReal) *
          capturedTubeBoxLoss (H.effectiveRadius 0) 1) *
        (Fintype.card (Index 0) : ENNReal)) \/
      Nonempty (TwoExponentKatzTaoDividingWitness
        (H.effectiveRadius 0) N gapEpsilon targetExponent
        (recoveredProfileV2 eta
          (fullyAutomaticFixedLocalCardTerminalStage
            (identityRadiusCoherentCover (H.effectiveFamily 0))
            (hierarchyZeroLocalCardBound H hdepth) delta_pos gap_pos
            eta_monotone two_lt_eta_zero exponent_budget
            (hierarchyEffectiveFamilyZero_refined_nonempty H hdepth)
            delta_le
            (hierarchyZeroIdentity_fullyAutomaticFixedLocalCardSeedBudget
              H hdepth eta N gap_pos delta_le))
          targetExponent)) := by
  exact identityFullyAutomaticFixedLocalCard_sticky_or_recoveredWitness
    (H.effectiveFamily 0) (hierarchyZeroLocalCardBound H hdepth)
    delta_pos gap_pos eta_monotone two_lt_eta_zero exponent_budget
    room_at_bound (hierarchyEffectiveFamilyZero_refined_nonempty H hdepth)
    delta_le
    (hierarchyZeroIdentity_fullyAutomaticFixedLocalCardSeedBudget
      H hdepth eta N gap_pos delta_le)

/-! ## Final multiscale assembly adapter -/

variable
  {H : MultiscaleTubeHierarchy depth nominalRadius Index}
  {G : HierarchyRandomMotionGeometry H}
  {P : HierarchyPackingPlan.Plan H}
  {C : CoherentStickyMultiscaleCover (H.effectiveFamily 0)}
  {S : FiniteScaleSequence (H.effectiveRadius 0) depth}
  {epsilon : Real}
  {massLoss bodyLoss katzTaoLoss frostmanError katzTaoError : ENNReal}

/-- A final assembly certificate supplies positive depth, positive initial
radius, and level-zero refined nonemptiness to the exact-card terminal
construction. -/
def finalAssemblyFullyAutomaticRefinedCardTerminalState
    (A : FamilyStickyFinalMultiscaleAssemblyCertificateV1.Certificate
      H G P C S epsilon massLoss bodyLoss katzTaoLoss
        frostmanError katzTaoError)
    (gap_pos : 0 < gapEpsilon)
    (eta_monotone : Monotone eta) (two_lt_eta_zero : 2 < eta 0)
    (exponent_budget : 1 <
      (gapEpsilon * gapEpsilon) * (N : Real))
    (delta_le : H.effectiveRadius 0 <=
      fullyAutomaticRefinedCardDeltaThreshold
        (H.effectiveFamily 0) eta N gapEpsilon) :=
  fullyAutomaticRefinedCardTerminalState (H.effectiveFamily 0)
    A.initialRadius_pos gap_pos eta_monotone two_lt_eta_zero
    exponent_budget (finalAssemblyEffectiveFamilyZero_refined_nonempty A)
    delta_le

/-- Readable final-assembly projection of the computed exact-card terminal
stage. -/
def finalAssemblyFullyAutomaticRefinedCardTerminalStage
    (A : FamilyStickyFinalMultiscaleAssemblyCertificateV1.Certificate
      H G P C S epsilon massLoss bodyLoss katzTaoLoss
        frostmanError katzTaoError)
    (gap_pos : 0 < gapEpsilon)
    (eta_monotone : Monotone eta) (two_lt_eta_zero : 2 < eta 0)
    (exponent_budget : 1 <
      (gapEpsilon * gapEpsilon) * (N : Real))
    (delta_le : H.effectiveRadius 0 <=
      fullyAutomaticRefinedCardDeltaThreshold
        (H.effectiveFamily 0) eta N gapEpsilon) : Nat :=
  fullyAutomaticRefinedCardTerminalStage (H.effectiveFamily 0)
    A.initialRadius_pos gap_pos eta_monotone two_lt_eta_zero
    exponent_budget (finalAssemblyEffectiveFamilyZero_refined_nonempty A)
    delta_le

/-- A final assembly certificate removes all hierarchy-derived premises
from the exact-refined-card endpoint. -/
theorem identityFullyAutomaticRefinedCard_sticky_or_recoveredWitness_of_finalAssembly
    (A : FamilyStickyFinalMultiscaleAssemblyCertificateV1.Certificate
      H G P C S epsilon massLoss bodyLoss katzTaoLoss
        frostmanError katzTaoError)
    (gap_pos : 0 < gapEpsilon)
    (eta_monotone : Monotone eta) (two_lt_eta_zero : 2 < eta 0)
    (exponent_budget : 1 <
      (gapEpsilon * gapEpsilon) * (N : Real))
    (room_at_bound : eta N < targetExponent)
    (delta_le : H.effectiveRadius 0 <=
      fullyAutomaticRefinedCardDeltaThreshold
        (H.effectiveFamily 0) eta N gapEpsilon) :
    (identityRadiusCoherentCover
        (H.effectiveFamily 0)).base.IsStickyAtEveryScale
      ((Fintype.card (Index 0) : ENNReal) *
        capturedTubeBoxLoss (H.effectiveRadius 0) 1)
      (((Fintype.card (Index 0) : ENNReal) *
          capturedTubeBoxLoss (H.effectiveRadius 0) 1) *
        (Fintype.card (Index 0) : ENNReal)) \/
      Nonempty (TwoExponentKatzTaoDividingWitness
        (H.effectiveRadius 0) N gapEpsilon targetExponent
        (recoveredProfileV2 eta
          (finalAssemblyFullyAutomaticRefinedCardTerminalStage A gap_pos
            eta_monotone two_lt_eta_zero exponent_budget delta_le)
          targetExponent)) := by
  simpa [finalAssemblyFullyAutomaticRefinedCardTerminalStage] using
    (identityFullyAutomaticRefinedCard_sticky_or_recoveredWitness_of_hierarchy
      H A.depth_pos A.initialRadius_pos gap_pos eta_monotone
      two_lt_eta_zero exponent_budget room_at_bound delta_le)

/-- V1 literal-witness projection of the final-assembly exact-card
endpoint. -/
theorem identityFullyAutomaticRefinedCard_sticky_or_recoveredLiteralWitness_of_finalAssembly
    (A : FamilyStickyFinalMultiscaleAssemblyCertificateV1.Certificate
      H G P C S epsilon massLoss bodyLoss katzTaoLoss
        frostmanError katzTaoError)
    (gap_pos : 0 < gapEpsilon)
    (eta_monotone : Monotone eta) (two_lt_eta_zero : 2 < eta 0)
    (exponent_budget : 1 <
      (gapEpsilon * gapEpsilon) * (N : Real))
    (room_at_bound : eta N < targetExponent)
    (delta_le : H.effectiveRadius 0 <=
      fullyAutomaticRefinedCardDeltaThreshold
        (H.effectiveFamily 0) eta N gapEpsilon) :
    (identityRadiusCoherentCover
        (H.effectiveFamily 0)).base.IsStickyAtEveryScale
      ((Fintype.card (Index 0) : ENNReal) *
        capturedTubeBoxLoss (H.effectiveRadius 0) 1)
      (((Fintype.card (Index 0) : ENNReal) *
          capturedTubeBoxLoss (H.effectiveRadius 0) 1) *
        (Fintype.card (Index 0) : ENNReal)) \/
      Nonempty (KatzTaoDividingWitness
        (H.effectiveRadius 0) N gapEpsilon
        (recoveredProfileV2 eta
          (finalAssemblyFullyAutomaticRefinedCardTerminalStage A gap_pos
            eta_monotone two_lt_eta_zero exponent_budget delta_le)
          targetExponent)) := by
  rcases
      identityFullyAutomaticRefinedCard_sticky_or_recoveredWitness_of_finalAssembly
        A gap_pos eta_monotone two_lt_eta_zero exponent_budget
        room_at_bound delta_le with sticky | witness
  · exact Or.inl sticky
  · rcases witness with ⟨W⟩
    exact Or.inr ⟨W.toV1⟩

#print axioms fullyAutomaticRefinedCardDeltaThreshold_pos
#print axioms fullyAutomaticRefinedCardDeltaThreshold_le_one
#print axioms fullyAutomaticRefinedCardDeltaThreshold_lt_one
#print axioms identity_fullyAutomaticRefinedCardSeedBudget
#print axioms fullyAutomaticRefinedCardInitialState
#print axioms fullyAutomaticRefinedCardTerminalState
#print axioms identityFullyAutomaticRefinedCard_sticky_or_recoveredWitness
#print axioms identityFullyAutomaticRefinedCard_sticky_or_recoveredLiteralWitness
#print axioms hierarchyEffectiveFamilyZero_refined_card_le_zeroLocalCardBound
#print axioms hierarchyZeroLocalCardDeltaThreshold_pos
#print axioms identityFullyAutomaticRefinedCard_sticky_or_recoveredWitness_of_hierarchy
#print axioms identityFullyAutomaticHierarchyZeroLocalCard_sticky_or_recoveredWitness
#print axioms finalAssemblyFullyAutomaticRefinedCardTerminalState
#print axioms finalAssemblyFullyAutomaticRefinedCardTerminalStage
#print axioms identityFullyAutomaticRefinedCard_sticky_or_recoveredWitness_of_finalAssembly
#print axioms identityFullyAutomaticRefinedCard_sticky_or_recoveredLiteralWitness_of_finalAssembly

end
end FamilyStickyScaleChainFullyAutomaticRefinedCardEndpointV2
