import FamilyStickyGrounding.FamilyStickyScaleChainActualSmallDeltaRecoveredEndpointV1

set_option autoImplicit false
set_option warningAsError true
set_option linter.unusedSectionVars false
set_option maxHeartbeats 100000

open Set
open scoped BigOperators ENNReal NNReal

namespace FamilyStickyScaleChainActualStoppingUpstreamClosureV1

open LeanEval.Analysis.WangZahlKakeya
open Submission.Kakeya.ConvexGeometry
open Submission.Kakeya.ConvexFactoring
open Submission.Kakeya.Uniformity
open FamilyStickyAtEveryScaleCoreV1
open FamilyStickyDividingScalesFiniteStoppingV1
open FamilyStickyScaleChainActualValuesV1
open FamilyStickyScaleChainActualDividingRunV1
open FamilyStickyScaleChainBufferedTelescopeV1.MultiscaleTubeHierarchy
open FamilyStickyScaleChainCoherentIntervalProducerV1
open FamilyStickyScaleChainTerminalFiniteSearchV1
open FamilyStickyScaleChainRootedRefinementTreeV1
open FamilyStickyScaleChainTreeThresholdTransferV1
open FamilyStickyScaleChainActualStrictLossWithConstantV1
open FamilyStickyScaleChainReservedExponentProfileV1
open FamilyStickyScaleChainSmallDeltaExponentBudgetProducerV1
open FamilyStickyScaleChainActualSmallDeltaRecoveredEndpointV1

noncomputable section

/-!
# Closing automatic upstream fields of the actual stopping endpoint

Three kinds of input remained visible at the preceding recovered endpoint.

* A one-based stopping stage was represented by a natural number plus two
  range proofs.  Here it is represented by one `Fin N` slot, from which both
  proofs are generated.
* The global and adjacent exponent certificates each stored scale positivity.
  Positivity follows from `0 < delta` and the actual finite scale sequence, so
  the primitive allocation certificates below retain only local-factor,
  endpoint-ratio, and exponent-balance data.
* A lower bound of two on the reserved stage exponent follows from a natural
  target-profile normalization `2 <= eta 0` and monotonicity.

The finite tree-node inequalities do not follow from hierarchy or scale data:
they compare actual concentrations with the stopping threshold.  This file
constructs their certificate in the vacuous all-large branch and proves the
sharp obstruction caused by one failed non-large node.  Thus the direct
dividing endpoint retains exactly this finite analytic certificate, rather
than replacing it with a renamed terminal conclusion.
-/

/-! ## Typed one-based stopping stages -/

/-- Convert a zero-based slot in `Fin N` to the paper's one-based stage. -/
def oneBasedStage {N : Nat} (slot : Fin N) : Nat :=
  slot.1 + 1

theorem oneBasedStage_pos {N : Nat} (slot : Fin N) :
    1 <= oneBasedStage slot := by
  simp [oneBasedStage]

theorem oneBasedStage_le {N : Nat} (slot : Fin N) :
    oneBasedStage slot <= N := by
  change slot.1 + 1 <= N
  omega

/-! ## Scale positivity supplied by the actual sequence -/

namespace ScaleSequence

variable {delta : NNReal} {depth : Nat}

theorem tau_pos_of_delta_pos
    (S : FiniteScaleSequence delta depth) (delta_pos : 0 < delta)
    (m : Fin depth) :
    0 < S.tau m :=
  delta_pos.trans_le (S.delta_le_tau m)

theorem theta_pos_of_delta_pos
    (S : FiniteScaleSequence delta depth) (delta_pos : 0 < delta)
    (m : Fin depth) :
    0 < S.theta m :=
  (tau_pos_of_delta_pos S delta_pos m).trans_le (S.tau_le_theta m)

end ScaleSequence

/-! ## Primitive global exponent allocation -/

variable {delta : NNReal} {outerDepth chainDepth : Nat}
  {S : FiniteScaleSequence delta outerDepth}

/-- Primitive exponent assignments and literal factor estimates for the
global buffered chains.  Unlike `ExponentBudgetData`, this certificate does
not ask the caller to repeat positivity of every `theta`. -/
structure GlobalExponentAllocation
    (B : FamilyStickyScaleChainActualDividingRunV1.BufferedChainFamily
      outerDepth chainDepth)
    (S : FiniteScaleSequence delta outerDepth)
    (stage : Nat) (profile : Nat -> Real) where
  localExponent : Fin outerDepth -> Nat -> Real
  endpointExponent : Fin outerDepth -> Real
  localFactor_upper : forall m l, l < chainDepth ->
    FamilyStickyScaleChainBufferedTelescopeV1.MultiscaleTubeHierarchy.BufferedTestBodyChain.localFactor
        (B.hierarchy m) (B.datum m) l <=
      (S.theta m : ENNReal) ^ localExponent m l
  endpointRatio_upper : forall m,
    ((MeasureTheory.volume ((B.datum m).testBody chainDepth : Set Space) /
        MeasureTheory.volume ((B.datum m).testBody 0 : Set Space)) *
      ((B.datum m).tubeVolume 0 / (B.datum m).tubeVolume chainDepth)) <=
        (S.theta m : ENNReal) ^ endpointExponent m
  exponent_balance : forall m,
    (∑ l ∈ Finset.range chainDepth, localExponent m l) +
      endpointExponent m = -profile (stage - 1)

namespace GlobalExponentAllocation

variable
  {B : FamilyStickyScaleChainActualDividingRunV1.BufferedChainFamily
    outerDepth chainDepth}
  {stage : Nat} {profile : Nat -> Real}

/-- Add the automatically available `theta` positivity field. -/
def toExponentBudgetData
    (E : GlobalExponentAllocation B S stage profile)
    (delta_pos : 0 < delta) :
    FamilyStickyScaleChainExponentProductBudgetV1.BufferedChainFamily.ExponentBudgetData
      B S stage profile where
  theta_pos := ScaleSequence.theta_pos_of_delta_pos S delta_pos
  localExponent := E.localExponent
  endpointExponent := E.endpointExponent
  localFactor_upper := E.localFactor_upper
  endpointRatio_upper := E.endpointRatio_upper
  exponent_balance := E.exponent_balance

end GlobalExponentAllocation

/-! ## Primitive adjacent exponent allocation -/

variable {adjacentDepth : Nat} {A : ActualIntervalCovers S}

/-- Primitive exponent assignments for every actual adjacent test-body
chain.  The final adjacent supremum estimate is not stored, and `tau`
positivity is generated from the scale sequence. -/
structure AdjacentExponentAllocation
    (G : FamilyStickyScaleChainAdjacentUpperProducerV1.AdjacentBufferedHierarchyFamily
      S A adjacentDepth)
    (stage : Nat) (profile : Nat -> Real) where
  localExponent : Fin outerDepth -> ConvexBody Space -> Nat -> Real
  endpointExponent : Fin outerDepth -> ConvexBody Space -> Real
  localFactor_upper : forall m K hK l, l < adjacentDepth ->
    BufferedTestBodyChain.localFactor
        (G.hierarchy m) (G.datum m K hK) l <=
      (((S.theta m / S.tau m : NNReal) : ENNReal) ^
        localExponent m K l)
  endpointRatio_upper : forall m K hK,
    G.endpointRatio m K hK <=
      (((S.theta m / S.tau m : NNReal) : ENNReal) ^
        endpointExponent m K)
  exponent_balance : forall m K,
    (∑ l ∈ Finset.range adjacentDepth, localExponent m K l) +
      endpointExponent m K = profile (stage - 1)

namespace AdjacentExponentAllocation

variable
  {G : FamilyStickyScaleChainAdjacentUpperProducerV1.AdjacentBufferedHierarchyFamily
    S A adjacentDepth}
  {stage : Nat} {profile : Nat -> Real}

/-- Add the automatically available `tau` positivity field. -/
def toExponentBudgetData
    (E : AdjacentExponentAllocation G stage profile)
    (delta_pos : 0 < delta) :
    FamilyStickyScaleChainAdjacentUpperProducerV1.AdjacentBufferedHierarchyFamily.ExponentBudgetData
      G stage profile where
  tau_pos := ScaleSequence.tau_pos_of_delta_pos S delta_pos
  localExponent := E.localExponent
  endpointExponent := E.endpointExponent
  localFactor_upper := E.localFactor_upper
  endpointRatio_upper := E.endpointRatio_upper
  exponent_balance := E.exponent_balance

end AdjacentExponentAllocation

/-! ## Exact obstructions for exponent allocation -/

/-- If the literal global product exceeds its required profile power at one
interval, no global exponent allocation certificate can exist. -/
theorem no_globalExponentBudgetData_of_product_gt
    (B : FamilyStickyScaleChainActualDividingRunV1.BufferedChainFamily
      outerDepth chainDepth)
    (stage : Nat) (profile : Nat -> Real) (m : Fin outerDepth)
    (failure :
      (S.theta m : ENNReal) ^ (-profile (stage - 1)) <
        (∏ l ∈ Finset.range chainDepth,
          FamilyStickyScaleChainBufferedTelescopeV1.MultiscaleTubeHierarchy.BufferedTestBodyChain.localFactor
            (B.hierarchy m) (B.datum m) l) *
          ((MeasureTheory.volume
              ((B.datum m).testBody chainDepth : Set Space) /
            MeasureTheory.volume ((B.datum m).testBody 0 : Set Space)) *
            ((B.datum m).tubeVolume 0 /
              (B.datum m).tubeVolume chainDepth))) :
    Not (Nonempty
      (FamilyStickyScaleChainExponentProductBudgetV1.BufferedChainFamily.ExponentBudgetData
        B S stage profile)) := by
  rintro ⟨E⟩
  exact (not_le_of_gt failure) (E.actualProductBudget B m)

/-- Likewise, one failed literal adjacent upper bound rules out every
adjacent exponent allocation certificate for that profile. -/
theorem no_adjacentExponentBudgetData_of_adjacentValue_gt
    (G : FamilyStickyScaleChainAdjacentUpperProducerV1.AdjacentBufferedHierarchyFamily
      S A adjacentDepth)
    (stage : Nat) (profile : Nat -> Real) (m : Fin outerDepth)
    (failure :
      (((S.theta m / S.tau m : NNReal) : ENNReal) ^
          profile (stage - 1)) < A.adjacentCoarseValue m) :
    Not (Nonempty
      (FamilyStickyScaleChainAdjacentUpperProducerV1.AdjacentBufferedHierarchyFamily.ExponentBudgetData
        G stage profile)) := by
  rintro ⟨E⟩
  exact (not_le_of_gt failure) (E.adjacent_upper G m)

/-! ## The finite-node certificate: automatic and obstructed cases -/

variable {epsilon : Real} {profile : Nat -> Real} {stage : Nat}
  {R : IntervalRootedRefinementScaleTree S}

/-- If all terminal intervals are large, the finite-node certificate is
vacuous and follows from the scale sequence alone. -/
theorem verifiedTreeNodeLowerBounds_of_allStepsLarge
    (A : ActualIntervalCovers S) (all_large : S.AllStepsLarge epsilon) :
    VerifiedTreeNodeLowerBounds
      (epsilon := epsilon) (eta := profile) (stage := stage) A R where
  checked := by
    intro m not_large
    exact (not_large (all_large m)).elim

/-- Sharp obstruction: one strict failure at a node of a non-large interval
precludes the finite-node certificate.  Hence hierarchy and scale-order data
alone cannot synthesize it on the dividing branch. -/
theorem no_verifiedTreeNodeLowerBounds_of_failedNode
    (A : ActualIntervalCovers S)
    (m : Fin outerDepth) (not_large : ¬ S.IsLarge epsilon m)
    (i : Fin (R.tree.levelCount m))
    (failure : A.coarseValueAt m (R.tree.scale m i) <
      splitThreshold S profile stage m (R.tree.scale m i)) :
    Not (VerifiedTreeNodeLowerBounds
      (epsilon := epsilon) (eta := profile) (stage := stage) A R) := by
  intro V
  exact (not_le_of_gt failure) (V.checked m not_large i)

/-! ## Reserved-profile lower exponent -/

/-- Exact algebraic form of the quadratic producer's reserved-stage
condition. -/
theorem two_le_add_halfReservedExponentRoom_iff
    {eta : Nat -> Real} {stage : Nat} {epsilon : Real} :
    (2 : Real) <= eta stage +
        halfReservedExponentRoom eta stage epsilon <->
      4 <= eta stage + epsilon := by
  rw [halfReservedExponentRoom]
  constructor <;> intro h <;> linarith

/-- A natural target-profile normalization at stage zero, together with
monotonicity, automatically supplies the reserved quadratic lower bound at
every stage with strict room. -/
theorem two_le_add_halfReservedExponentRoom_of_two_le_zero
    {eta : Nat -> Real} {stage : Nat} {epsilon : Real}
    (eta_monotone : Monotone eta) (two_le_zero : (2 : Real) <= eta 0)
    (strict_room : eta stage < epsilon) :
    (2 : Real) <= eta stage +
      halfReservedExponentRoom eta stage epsilon := by
  have eta_zero_le : eta 0 <= eta stage := eta_monotone (Nat.zero_le stage)
  have loss_pos := halfReservedExponentRoom_pos strict_room
  linarith

/-- Monotonicity and strict room by themselves are insufficient: the zero
profile with `epsilon = 1` is a concrete counterexample. -/
theorem monotone_and_strictRoom_do_not_force_reservedTwo :
    ∃ eta : Nat -> Real, ∃ stage : Nat, ∃ epsilon : Real,
      Monotone eta ∧ eta stage < epsilon ∧
        Not ((2 : Real) <= eta stage +
          halfReservedExponentRoom eta stage epsilon) := by
  refine ⟨fun _ => 0, 1, 1, ?_, by norm_num, ?_⟩
  · intro a b hab
    exact le_rfl
  · norm_num [halfReservedExponentRoom]

/-! ## Combined endpoint with automatic upstream fields -/

variable {N : Nat} {eta : Nat -> Real}
  {iota : Type*} [Fintype iota] [DecidableEq iota]
  {fine : UniformTubeFamily delta iota}

/-- The strongest current composition from typed stage data and primitive
actual exponent allocations.  Stage range, both stored positivity fields,
and the reserved quadratic lower bound are generated automatically.  The
finite-node certificate remains explicit for the dividing branch, as forced
by `no_verifiedTreeNodeLowerBounds_of_failedNode`. -/
theorem room_and_allLarge_or_recoveredLiteralWitness_of_upstreamData
    (C : CoherentStickyMultiscaleCover fine)
    (R : IntervalRootedRefinementScaleTree S)
    (B : FamilyStickyScaleChainActualDividingRunV1.BufferedChainFamily
      outerDepth chainDepth)
    (G : FamilyStickyScaleChainAdjacentUpperProducerV1.AdjacentBufferedHierarchyFamily
      S (C.toActualIntervalCovers S) adjacentDepth)
    (slot : Fin N)
    (eta_monotone : Monotone eta) (two_le_zero : (2 : Real) <= eta 0)
    (strict_room : eta (oneBasedStage slot) < epsilon)
    (globalAllocation : GlobalExponentAllocation B S (oneBasedStage slot)
      (reserveTailLoss eta (oneBasedStage slot)
        (halfReservedExponentRoom eta (oneBasedStage slot) epsilon)))
    (adjacentAllocation : AdjacentExponentAllocation G (oneBasedStage slot)
      (reserveTailLoss eta (oneBasedStage slot)
        (halfReservedExponentRoom eta (oneBasedStage slot) epsilon)))
    (V : VerifiedTreeNodeLowerBounds
      (epsilon := epsilon)
      (eta := reserveTailLoss eta (oneBasedStage slot)
        (halfReservedExponentRoom eta (oneBasedStage slot) epsilon))
      (stage := oneBasedStage slot) (C.toActualIntervalCovers S) R)
    (delta_pos : 0 < delta)
    (delta_le : delta <=
      actualStrictLossRecoveredSmallDeltaThreshold eta
        (oneBasedStage slot) epsilon iota) :
    eta (oneBasedStage slot) +
          halfReservedExponentRoom eta (oneBasedStage slot) epsilon <=
        epsilon ∧
      (S.AllStepsLarge epsilon ∨
        Nonempty (KatzTaoDividingWitness delta N epsilon
          (recoveredReservedProfile eta (oneBasedStage slot)
            (halfReservedExponentRoom eta (oneBasedStage slot) epsilon)))) := by
  exact
    room_and_allLarge_or_recoveredLiteralWitness_of_actualStrictLoss
      C R B G (oneBasedStage slot) (oneBasedStage_pos slot)
        (oneBasedStage_le slot) eta_monotone strict_room
        (globalAllocation.toExponentBudgetData delta_pos)
        (adjacentAllocation.toExponentBudgetData delta_pos) V
        (two_le_add_halfReservedExponentRoom_of_two_le_zero eta_monotone
          two_le_zero strict_room)
        delta_pos delta_le

/-- Direct dividing-branch endpoint with the same automatically generated
upstream fields. -/
theorem exists_recoveredLiteralWitness_of_upstreamData
    (C : CoherentStickyMultiscaleCover fine)
    (R : IntervalRootedRefinementScaleTree S)
    (B : FamilyStickyScaleChainActualDividingRunV1.BufferedChainFamily
      outerDepth chainDepth)
    (G : FamilyStickyScaleChainAdjacentUpperProducerV1.AdjacentBufferedHierarchyFamily
      S (C.toActualIntervalCovers S) adjacentDepth)
    (slot : Fin N)
    (eta_monotone : Monotone eta) (two_le_zero : (2 : Real) <= eta 0)
    (strict_room : eta (oneBasedStage slot) < epsilon)
    (globalAllocation : GlobalExponentAllocation B S (oneBasedStage slot)
      (reserveTailLoss eta (oneBasedStage slot)
        (halfReservedExponentRoom eta (oneBasedStage slot) epsilon)))
    (adjacentAllocation : AdjacentExponentAllocation G (oneBasedStage slot)
      (reserveTailLoss eta (oneBasedStage slot)
        (halfReservedExponentRoom eta (oneBasedStage slot) epsilon)))
    (V : VerifiedTreeNodeLowerBounds
      (epsilon := epsilon)
      (eta := reserveTailLoss eta (oneBasedStage slot)
        (halfReservedExponentRoom eta (oneBasedStage slot) epsilon))
      (stage := oneBasedStage slot) (C.toActualIntervalCovers S) R)
    (delta_pos : 0 < delta)
    (delta_le : delta <=
      actualStrictLossRecoveredSmallDeltaThreshold eta
        (oneBasedStage slot) epsilon iota)
    (not_all_large : ¬ S.AllStepsLarge epsilon) :
    Nonempty (KatzTaoDividingWitness delta N epsilon
      (recoveredReservedProfile eta (oneBasedStage slot)
        (halfReservedExponentRoom eta (oneBasedStage slot) epsilon))) := by
  have result :=
    room_and_allLarge_or_recoveredLiteralWitness_of_upstreamData
      C R B G slot eta_monotone two_le_zero strict_room globalAllocation
        adjacentAllocation V delta_pos delta_le
  exact result.2.resolve_left not_all_large

#print axioms oneBasedStage_pos
#print axioms oneBasedStage_le
#print axioms ScaleSequence.tau_pos_of_delta_pos
#print axioms GlobalExponentAllocation.toExponentBudgetData
#print axioms AdjacentExponentAllocation.toExponentBudgetData
#print axioms no_globalExponentBudgetData_of_product_gt
#print axioms no_adjacentExponentBudgetData_of_adjacentValue_gt
#print axioms verifiedTreeNodeLowerBounds_of_allStepsLarge
#print axioms no_verifiedTreeNodeLowerBounds_of_failedNode
#print axioms two_le_add_halfReservedExponentRoom_iff
#print axioms two_le_add_halfReservedExponentRoom_of_two_le_zero
#print axioms monotone_and_strictRoom_do_not_force_reservedTwo
#print axioms room_and_allLarge_or_recoveredLiteralWitness_of_upstreamData
#print axioms exists_recoveredLiteralWitness_of_upstreamData

end
end FamilyStickyScaleChainActualStoppingUpstreamClosureV1
