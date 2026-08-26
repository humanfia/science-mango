import FamilyStickyGrounding.FamilyStickyScaleChainFixedLocalCardRecoveredEndpointV2
import FamilyStickyGrounding.FamilyStickyScaleChainCappedSeedSequenceV2
import FamilyStickyGrounding.FamilyStickyScaleChainUniformAutomaticThetaThresholdV2

set_option autoImplicit false
set_option warningAsError true
set_option linter.unusedSectionVars false
set_option maxHeartbeats 3000000

open scoped BigOperators ENNReal NNReal

namespace FamilyStickyScaleChainFullyAutomaticFixedLocalCardEndpointV2

open LeanEval.Analysis.WangZahlKakeya
open Submission.Kakeya.Uniformity
open FamilyStickyDividingScalesFiniteStoppingV1
open FamilyStickyScaleChainCoherentIntervalProducerV1
open FamilyStickyScaleChainCoherentExactHierarchyProducerV2
open FamilyStickyScaleChainCanonicalNormalizedTerminalUpperV2
open FamilyStickyScaleChainTwoExponentStoppingCoreV2
open FamilyStickyScaleChainTwoParameterRecoveredEndpointV2
open FamilyStickyScaleChainRelevantThetaCapInvariantV2
open FamilyStickyScaleChainLocalCardAutomaticBoundsV2
open FamilyStickyScaleChainLocalCardBudgetInvariantV2
open FamilyStickyScaleChainFixedLocalCardCountedDriverV2
open FamilyStickyScaleChainFixedLocalCardRecoveredEndpointV2
open FamilyStickyScaleChainCappedSeedSequenceV2
open FamilyStickyScaleChainUniformAutomaticThetaThresholdV2
open FamilyStickyScaleChainSelectedIdentityAutomaticAllLargeProducerV1
open FamilyStickyScaleChainSelectedCanonicalCoverCoordinatesProducerV1
open FamilyStickyCapturedTubeBoxWidthV1

noncomputable section

/-!
# Fully automatic endpoint with a fixed local-card budget

The automatic theta cap and every numerical delta threshold in this module
depend on one explicit natural local-card budget `n`.  A single total delta
threshold constructs the literal capped depth-two seed and supplies the
uniform adjacent bound at every possible terminal stage.

The only geometric input not generated internally is the honest packing
certificate that the generated seed has non-large local cardinalities at
most `n`.  The recursion preserves that certificate automatically.  The
ambient finite index type occurs only in the established Sticky constant,
not in the cap or either delta threshold.
-/

universe u

variable {delta : NNReal} {gapEpsilon targetExponent : Real}
  {N : Nat} {eta : Nat -> Real}
  {iota : Type u} [Fintype iota] [DecidableEq iota]
  {fine : UniformTubeFamily delta iota}

/-! ## Cap and one total delta threshold -/

/-- The uniform automatic cap formed with the fixed local-card budget. -/
def fullyAutomaticFixedLocalCardThetaCap
    (n : Nat) (eta : Nat -> Real) (N : Nat) : NNReal :=
  uniformAutomaticThetaThreshold n eta N

theorem fullyAutomaticFixedLocalCardThetaCap_pos
    (n : Nat) (eta : Nat -> Real) (N : Nat) :
    0 < fullyAutomaticFixedLocalCardThetaCap n eta N := by
  exact uniformAutomaticThetaThreshold_pos n eta N

/-- The recursive minimum is always at most one, including the harmless
zero-stage value. -/
theorem fullyAutomaticFixedLocalCardThetaCap_le_one
    (n : Nat) (eta : Nat -> Real) (N : Nat) :
    fullyAutomaticFixedLocalCardThetaCap n eta N <= 1 := by
  unfold fullyAutomaticFixedLocalCardThetaCap
  induction N with
  | zero => simp
  | succ N ih =>
      rw [uniformAutomaticThetaThreshold_succ]
      exact (min_le_left _ _).trans ih

/-- For a nonempty stage window, the cap is already at most one half. -/
theorem fullyAutomaticFixedLocalCardThetaCap_le_half
    (n : Nat) (eta : Nat -> Real) {N : Nat} (N_pos : 1 <= N) :
    fullyAutomaticFixedLocalCardThetaCap n eta N <= (2 : NNReal)⁻¹ := by
  calc
    fullyAutomaticFixedLocalCardThetaCap n eta N <=
        automaticOneStepSmallThetaThreshold n (eta 0) :=
      uniformAutomaticThetaThreshold_le_stage n eta N 0 N_pos
    _ <= (2 : NNReal)⁻¹ := min_le_left _ _

/-- One threshold for both the capped seed and the terminal adjacent
fixed-card estimate.  Its parameters contain no ambient index type. -/
def fullyAutomaticFixedLocalCardDeltaThreshold
    (n : Nat) (eta : Nat -> Real) (N : Nat)
    (gapEpsilon : Real) : NNReal :=
  min
    (cappedSeedDeltaThreshold
      (fullyAutomaticFixedLocalCardThetaCap n eta N) gapEpsilon)
    (uniformFixedLocalAdjacentCardThreshold n gapEpsilon eta N)

theorem fullyAutomaticFixedLocalCardDeltaThreshold_pos
    (n : Nat) (eta : Nat -> Real) (N : Nat)
    (gapEpsilon : Real) :
    0 < fullyAutomaticFixedLocalCardDeltaThreshold
      n eta N gapEpsilon := by
  rw [fullyAutomaticFixedLocalCardDeltaThreshold, lt_min_iff]
  exact
    ⟨cappedSeedDeltaThreshold_pos
        (fullyAutomaticFixedLocalCardThetaCap_pos n eta N) gapEpsilon,
      uniformFixedLocalAdjacentCardThreshold_pos
        n gapEpsilon eta N⟩

theorem fullyAutomaticFixedLocalCardDeltaThreshold_le_seed
    (n : Nat) (eta : Nat -> Real) (N : Nat)
    (gapEpsilon : Real) :
    fullyAutomaticFixedLocalCardDeltaThreshold n eta N gapEpsilon <=
      cappedSeedDeltaThreshold
        (fullyAutomaticFixedLocalCardThetaCap n eta N) gapEpsilon := by
  exact min_le_left _ _

theorem fullyAutomaticFixedLocalCardDeltaThreshold_le_adj
    (n : Nat) (eta : Nat -> Real) (N : Nat)
    (gapEpsilon : Real) :
    fullyAutomaticFixedLocalCardDeltaThreshold n eta N gapEpsilon <=
      uniformFixedLocalAdjacentCardThreshold n gapEpsilon eta N := by
  exact min_le_right _ _

theorem fullyAutomaticFixedLocalCardDeltaThreshold_le_cap
    (n : Nat) (eta : Nat -> Real) (N : Nat)
    (gapEpsilon : Real) :
    fullyAutomaticFixedLocalCardDeltaThreshold n eta N gapEpsilon <=
      fullyAutomaticFixedLocalCardThetaCap n eta N := by
  exact (fullyAutomaticFixedLocalCardDeltaThreshold_le_seed
    n eta N gapEpsilon).trans
      (cappedSeedDeltaThreshold_le_cap
        (fullyAutomaticFixedLocalCardThetaCap n eta N) gapEpsilon)

theorem fullyAutomaticFixedLocalCardDeltaThreshold_le_one
    (n : Nat) (eta : Nat -> Real) (N : Nat)
    (gapEpsilon : Real) :
    fullyAutomaticFixedLocalCardDeltaThreshold n eta N gapEpsilon <= 1 := by
  exact (fullyAutomaticFixedLocalCardDeltaThreshold_le_cap
    n eta N gapEpsilon).trans
      (fullyAutomaticFixedLocalCardThetaCap_le_one n eta N)

theorem fullyAutomaticFixedLocalCardDeltaThreshold_lt_one
    (n : Nat) (eta : Nat -> Real) {N : Nat} (N_pos : 1 <= N)
    (gapEpsilon : Real) :
    fullyAutomaticFixedLocalCardDeltaThreshold n eta N gapEpsilon < 1 := by
  calc
    fullyAutomaticFixedLocalCardDeltaThreshold n eta N gapEpsilon <=
        fullyAutomaticFixedLocalCardThetaCap n eta N :=
      fullyAutomaticFixedLocalCardDeltaThreshold_le_cap n eta N gapEpsilon
    _ <= (2 : NNReal)⁻¹ :=
      fullyAutomaticFixedLocalCardThetaCap_le_half n eta N_pos
    _ < 1 := by norm_num

theorem delta_lt_one_of_le_fullyAutomaticFixedLocalCardDeltaThreshold
    (n : Nat) (eta : Nat -> Real) {N : Nat} (N_pos : 1 <= N)
    (gapEpsilon : Real)
    (delta_le : delta <=
      fullyAutomaticFixedLocalCardDeltaThreshold n eta N gapEpsilon) :
    delta < 1 :=
  delta_le.trans_lt
    (fullyAutomaticFixedLocalCardDeltaThreshold_lt_one
      n eta N_pos gapEpsilon)

/-! ## Stage window and literal capped seed -/

/-- The separated-factor budget forces a positive stage bound. -/
theorem fixedLocalCardStageBound_pos_of_exponentBudget
    (exponent_budget : 1 <
      (gapEpsilon * gapEpsilon) * (N : Real)) :
    1 <= N := by
  by_contra not_pos
  have N_eq : N = 0 := by omega
  subst N
  norm_num at exponent_budget

/-- The uniform fixed-`n` cap supplies exactly the stage window consumed by
the fixed-local-card counted driver. -/
theorem fullyAutomaticFixedLocalCardStageWindow
    (n : Nat) (eta : Nat -> Real) (N : Nat)
    (eta_monotone : Monotone eta) (two_lt_eta_zero : 2 < eta 0) :
    RelevantFixedLocalCardStageWindow N eta
      (fullyAutomaticFixedLocalCardThetaCap n eta N) n := by
  intro s _stage_pos stage_lt
  exact
    ⟨two_lt_eta_of_monotone_of_two_lt_zero eta_monotone
        two_lt_eta_zero s,
      uniformAutomaticThetaThreshold_le_stage n eta N s stage_lt⟩

/-- The generated seed together with its exact non-large theta-cap
certificate. -/
structure FullyAutomaticFixedLocalCardSeedPackage
    (delta : NNReal) (n : Nat) (eta : Nat -> Real)
    (N : Nat) (gapEpsilon : Real) where
  seed : FiniteScaleSequence delta 2
  thetaCap : NonLargeThetaCap seed gapEpsilon
    (fullyAutomaticFixedLocalCardThetaCap n eta N)

/-- Construct the literal radii `1, cap, delta` from the total threshold. -/
def fullyAutomaticFixedLocalCardSeedPackage
    (n : Nat) (eta : Nat -> Real) (N : Nat)
    (gap_pos : 0 < gapEpsilon)
    (delta_le : delta <=
      fullyAutomaticFixedLocalCardDeltaThreshold
        n eta N gapEpsilon) :
    FullyAutomaticFixedLocalCardSeedPackage
      delta n eta N gapEpsilon := by
  have cap_pos : 0 < fullyAutomaticFixedLocalCardThetaCap n eta N :=
    fullyAutomaticFixedLocalCardThetaCap_pos n eta N
  have cap_le_one :
      fullyAutomaticFixedLocalCardThetaCap n eta N <= 1 :=
    fullyAutomaticFixedLocalCardThetaCap_le_one n eta N
  have delta_le_seed : delta <= cappedSeedDeltaThreshold
      (fullyAutomaticFixedLocalCardThetaCap n eta N) gapEpsilon :=
    delta_le.trans
      (fullyAutomaticFixedLocalCardDeltaThreshold_le_seed
        n eta N gapEpsilon)
  let seed := cappedSeedScaleSequenceOfThresholdPos
    cap_pos cap_le_one gap_pos delta_le_seed
  refine {
    seed := seed
    thetaCap := ?_ }
  exact cappedSeedScaleSequenceOfThresholdPos_nonLargeThetaCap
    cap_pos cap_le_one gap_pos delta_le_seed

/-- Readable name for the exact generated seed. -/
def fullyAutomaticFixedLocalCardSeed
    (n : Nat) (eta : Nat -> Real) (N : Nat)
    (gap_pos : 0 < gapEpsilon)
    (delta_le : delta <=
      fullyAutomaticFixedLocalCardDeltaThreshold
        n eta N gapEpsilon) :
    FiniteScaleSequence delta 2 :=
  (fullyAutomaticFixedLocalCardSeedPackage
    n eta N gap_pos delta_le).seed

theorem fullyAutomaticFixedLocalCardSeed_nonLargeThetaCap
    (n : Nat) (eta : Nat -> Real) (N : Nat)
    (gap_pos : 0 < gapEpsilon)
    (delta_le : delta <=
      fullyAutomaticFixedLocalCardDeltaThreshold
        n eta N gapEpsilon) :
    NonLargeThetaCap
      (fullyAutomaticFixedLocalCardSeed n eta N gap_pos delta_le)
      gapEpsilon (fullyAutomaticFixedLocalCardThetaCap n eta N) := by
  exact (fullyAutomaticFixedLocalCardSeedPackage
    n eta N gap_pos delta_le).thetaCap

/-- The sole honest packing input of the public endpoint, stated at the
exact generated seed.  As a proposition it is proof-irrelevant. -/
abbrev FullyAutomaticFixedLocalCardSeedBudget
    (C : CoherentStickyMultiscaleCover fine)
    (n : Nat) (eta : Nat -> Real) (N : Nat)
    (gap_pos : 0 < gapEpsilon)
    (delta_le : delta <=
      fullyAutomaticFixedLocalCardDeltaThreshold
        n eta N gapEpsilon) : Prop :=
  NonLargeLocalCardBudget C
    (fullyAutomaticFixedLocalCardSeed n eta N gap_pos delta_le)
    gapEpsilon n

/-! ## Automatic initial and terminal states -/

/-- The automatic fixed-local-card initial state.  The only extra input
beyond the usual endpoint data is the generated seed's local-card budget. -/
def fullyAutomaticFixedLocalCardInitialState
    (C : CoherentStickyMultiscaleCover fine) (n : Nat)
    (delta_pos : 0 < delta) (gap_pos : 0 < gapEpsilon)
    (two_lt_eta_zero : 2 < eta 0)
    (exponent_budget : 1 <
      (gapEpsilon * gapEpsilon) * (N : Real))
    (fine_refined_nonempty : fine.refinement.refined.Nonempty)
    (delta_le : delta <=
      fullyAutomaticFixedLocalCardDeltaThreshold
        n eta N gapEpsilon)
    (seed_local_card_budget :
      FullyAutomaticFixedLocalCardSeedBudget C n eta N gap_pos delta_le) :
    RelevantFixedLocalCardCountedState C N gapEpsilon eta
      (fullyAutomaticFixedLocalCardThetaCap n eta N) n := by
  have N_pos : 1 <= N :=
    fixedLocalCardStageBound_pos_of_exponentBudget exponent_budget
  let seed := fullyAutomaticFixedLocalCardSeed n eta N gap_pos delta_le
  have seed_theta_cap : NonLargeThetaCap seed gapEpsilon
      (fullyAutomaticFixedLocalCardThetaCap n eta N) := by
    exact fullyAutomaticFixedLocalCardSeed_nonLargeThetaCap
      n eta N gap_pos delta_le
  have cap_le_stage_zero :
      fullyAutomaticFixedLocalCardThetaCap n eta N <=
        automaticOneStepSmallThetaThreshold n (eta 0) :=
    uniformAutomaticThetaThreshold_le_stage n eta N 0 N_pos
  exact automaticRelevantFixedLocalCardCountedInitialState C seed
    (by omega) fine_refined_nonempty delta_pos N_pos
    (fullyAutomaticFixedLocalCardThetaCap n eta N) n seed_theta_cap
    (by simpa [seed] using seed_local_card_budget)
    two_lt_eta_zero cap_le_stage_zero

/-- The terminal state of the generated fixed-local-card recursion. -/
def fullyAutomaticFixedLocalCardTerminalState
    (C : CoherentStickyMultiscaleCover fine) (n : Nat)
    (delta_pos : 0 < delta) (gap_pos : 0 < gapEpsilon)
    (eta_monotone : Monotone eta) (two_lt_eta_zero : 2 < eta 0)
    (exponent_budget : 1 <
      (gapEpsilon * gapEpsilon) * (N : Real))
    (fine_refined_nonempty : fine.refinement.refined.Nonempty)
    (delta_le : delta <=
      fullyAutomaticFixedLocalCardDeltaThreshold
        n eta N gapEpsilon)
    (seed_local_card_budget :
      FullyAutomaticFixedLocalCardSeedBudget C n eta N gap_pos delta_le) :
    RelevantFixedLocalCardCountedState C N gapEpsilon eta
      (fullyAutomaticFixedLocalCardThetaCap n eta N) n :=
  relevantFixedLocalCardCountingTerminalState C delta_pos
    (delta_lt_one_of_le_fullyAutomaticFixedLocalCardDeltaThreshold n eta
      (fixedLocalCardStageBound_pos_of_exponentBudget exponent_budget)
      gapEpsilon delta_le)
    gap_pos eta_monotone exponent_budget
    (fullyAutomaticFixedLocalCardThetaCap n eta N) n
    (fullyAutomaticFixedLocalCardStageWindow n eta N eta_monotone
      two_lt_eta_zero)
    (fullyAutomaticFixedLocalCardInitialState C n delta_pos gap_pos
      two_lt_eta_zero exponent_budget fine_refined_nonempty
      delta_le seed_local_card_budget)

/-- The computed terminal stage used by the recovered profile. -/
def fullyAutomaticFixedLocalCardTerminalStage
    (C : CoherentStickyMultiscaleCover fine) (n : Nat)
    (delta_pos : 0 < delta) (gap_pos : 0 < gapEpsilon)
    (eta_monotone : Monotone eta) (two_lt_eta_zero : 2 < eta 0)
    (exponent_budget : 1 <
      (gapEpsilon * gapEpsilon) * (N : Real))
    (fine_refined_nonempty : fine.refinement.refined.Nonempty)
    (delta_le : delta <=
      fullyAutomaticFixedLocalCardDeltaThreshold
        n eta N gapEpsilon)
    (seed_local_card_budget :
      FullyAutomaticFixedLocalCardSeedBudget C n eta N gap_pos delta_le) :
    Nat :=
  (fullyAutomaticFixedLocalCardTerminalState C n delta_pos gap_pos
    eta_monotone two_lt_eta_zero exponent_budget fine_refined_nonempty
    delta_le seed_local_card_budget).counted.data.stage

/-! ## Identity-cover endpoints -/

/-- With only the generated seed's local-card budget left explicit, the
identity run yields Sticky at every scale or a recovered two-exponent
dividing witness. -/
theorem identityFullyAutomaticFixedLocalCard_sticky_or_recoveredWitness
    (fine : UniformTubeFamily delta iota) (n : Nat)
    (delta_pos : 0 < delta) (gap_pos : 0 < gapEpsilon)
    (eta_monotone : Monotone eta) (two_lt_eta_zero : 2 < eta 0)
    (exponent_budget : 1 <
      (gapEpsilon * gapEpsilon) * (N : Real))
    (room_at_bound : eta N < targetExponent)
    (fine_refined_nonempty : fine.refinement.refined.Nonempty)
    (delta_le : delta <=
      fullyAutomaticFixedLocalCardDeltaThreshold
        n eta N gapEpsilon)
    (seed_local_card_budget : FullyAutomaticFixedLocalCardSeedBudget
      (identityRadiusCoherentCover fine) n eta N gap_pos delta_le) :
    (identityRadiusCoherentCover fine).base.IsStickyAtEveryScale
        ((Fintype.card iota : ENNReal) * capturedTubeBoxLoss delta 1)
        (((Fintype.card iota : ENNReal) * capturedTubeBoxLoss delta 1) *
          (Fintype.card iota : ENNReal)) \/
      Nonempty (TwoExponentKatzTaoDividingWitness delta N gapEpsilon
        targetExponent
        (recoveredProfileV2 eta
          (fullyAutomaticFixedLocalCardTerminalStage
            (identityRadiusCoherentCover fine) n delta_pos gap_pos
            eta_monotone two_lt_eta_zero exponent_budget
            fine_refined_nonempty delta_le seed_local_card_budget)
          targetExponent)) := by
  have N_pos : 1 <= N :=
    fixedLocalCardStageBound_pos_of_exponentBudget exponent_budget
  have delta_lt_one : delta < 1 :=
    delta_lt_one_of_le_fullyAutomaticFixedLocalCardDeltaThreshold
      n eta N_pos gapEpsilon delta_le
  have delta_le_uniform : delta <=
      uniformFixedLocalAdjacentCardThreshold n gapEpsilon eta N :=
    delta_le.trans
      (fullyAutomaticFixedLocalCardDeltaThreshold_le_adj
        n eta N gapEpsilon)
  simpa [fullyAutomaticFixedLocalCardTerminalStage,
      fullyAutomaticFixedLocalCardTerminalState] using
    (identityRelevantFixedLocalCardCounting_sticky_or_recoveredWitness_of_uniformThreshold
      fine delta_pos delta_lt_one gap_pos eta_monotone two_lt_eta_zero.le
      exponent_budget (fullyAutomaticFixedLocalCardThetaCap n eta N) n
      (fullyAutomaticFixedLocalCardStageWindow n eta N eta_monotone
        two_lt_eta_zero)
      (fullyAutomaticFixedLocalCardInitialState
        (identityRadiusCoherentCover fine) n delta_pos gap_pos
        two_lt_eta_zero exponent_budget fine_refined_nonempty delta_le
        seed_local_card_budget)
      room_at_bound delta_le_uniform)

/-- Compatibility projection to the V1 literal-witness API. -/
theorem identityFullyAutomaticFixedLocalCard_sticky_or_recoveredLiteralWitness
    (fine : UniformTubeFamily delta iota) (n : Nat)
    (delta_pos : 0 < delta) (gap_pos : 0 < gapEpsilon)
    (eta_monotone : Monotone eta) (two_lt_eta_zero : 2 < eta 0)
    (exponent_budget : 1 <
      (gapEpsilon * gapEpsilon) * (N : Real))
    (room_at_bound : eta N < targetExponent)
    (fine_refined_nonempty : fine.refinement.refined.Nonempty)
    (delta_le : delta <=
      fullyAutomaticFixedLocalCardDeltaThreshold
        n eta N gapEpsilon)
    (seed_local_card_budget : FullyAutomaticFixedLocalCardSeedBudget
      (identityRadiusCoherentCover fine) n eta N gap_pos delta_le) :
    (identityRadiusCoherentCover fine).base.IsStickyAtEveryScale
        ((Fintype.card iota : ENNReal) * capturedTubeBoxLoss delta 1)
        (((Fintype.card iota : ENNReal) * capturedTubeBoxLoss delta 1) *
          (Fintype.card iota : ENNReal)) \/
      Nonempty (KatzTaoDividingWitness delta N gapEpsilon
        (recoveredProfileV2 eta
          (fullyAutomaticFixedLocalCardTerminalStage
            (identityRadiusCoherentCover fine) n delta_pos gap_pos
            eta_monotone two_lt_eta_zero exponent_budget
            fine_refined_nonempty delta_le seed_local_card_budget)
          targetExponent)) := by
  rcases identityFullyAutomaticFixedLocalCard_sticky_or_recoveredWitness
      fine n delta_pos gap_pos eta_monotone two_lt_eta_zero exponent_budget
      room_at_bound fine_refined_nonempty delta_le seed_local_card_budget with
    sticky | witness
  · exact Or.inl sticky
  · rcases witness with ⟨W⟩
    exact Or.inr ⟨W.toV1⟩

/-! ## Ambient-card compatibility only -/

/-- Every scale sequence admits the former ambient-card local budget.  This
shows that the new packing interface is inhabited, but no automatic endpoint
or threshold above invokes this compatibility specialization. -/
theorem nonLargeLocalCardBudget_originalCard
    (C : CoherentStickyMultiscaleCover fine)
    {depth : Nat} (S : FiniteScaleSequence delta depth)
    (fine_refined_nonempty : fine.refinement.refined.Nonempty) :
    NonLargeLocalCardBudget C S gapEpsilon (Fintype.card iota) := by
  intro m _not_large
  rw [<- ofFiniteScaleSequence_localCardBound_eq_intervalActiveFineCard
    C S fine_refined_nonempty m]
  exact canonicalOneStepLocalCardBound_le_original_card C
    (CoherentExactHierarchyFamily.ofFiniteScaleSequence
      C S fine_refined_nonempty) m

#print axioms fullyAutomaticFixedLocalCardThetaCap_pos
#print axioms fullyAutomaticFixedLocalCardThetaCap_le_half
#print axioms fullyAutomaticFixedLocalCardDeltaThreshold_pos
#print axioms fullyAutomaticFixedLocalCardDeltaThreshold_le_seed
#print axioms fullyAutomaticFixedLocalCardDeltaThreshold_le_adj
#print axioms fullyAutomaticFixedLocalCardDeltaThreshold_le_cap
#print axioms fullyAutomaticFixedLocalCardDeltaThreshold_le_one
#print axioms fullyAutomaticFixedLocalCardDeltaThreshold_lt_one
#print axioms fullyAutomaticFixedLocalCardStageWindow
#print axioms fullyAutomaticFixedLocalCardSeedPackage
#print axioms fullyAutomaticFixedLocalCardSeed_nonLargeThetaCap
#print axioms fullyAutomaticFixedLocalCardInitialState
#print axioms fullyAutomaticFixedLocalCardTerminalState
#print axioms identityFullyAutomaticFixedLocalCard_sticky_or_recoveredWitness
#print axioms identityFullyAutomaticFixedLocalCard_sticky_or_recoveredLiteralWitness
#print axioms nonLargeLocalCardBudget_originalCard

end
end FamilyStickyScaleChainFullyAutomaticFixedLocalCardEndpointV2
