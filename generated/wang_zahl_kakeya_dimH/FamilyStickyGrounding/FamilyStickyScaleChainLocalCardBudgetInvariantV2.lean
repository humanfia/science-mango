import FamilyStickyGrounding.FamilyStickyScaleChainLocalCardAutomaticBoundsV2
import FamilyStickyGrounding.FamilyStickyScaleChainRelevantThetaCapInvariantV2

set_option autoImplicit false
set_option warningAsError true
set_option linter.unusedSectionVars false
set_option maxHeartbeats 1000000

open Set MeasureTheory
open scoped BigOperators ENNReal NNReal InnerProductSpace

namespace FamilyStickyScaleChainLocalCardBudgetInvariantV2

open LeanEval.Analysis.WangZahlKakeya
open Submission.Kakeya.ConvexGeometry
open Submission.Kakeya.Uniformity
open FamilyStickyAtEveryScaleCoreV1
open FamilyStickyDeltaMaxFiniteChainV2
open FamilyStickyDividingScalesFiniteStoppingV1
open FamilyStickyScaleChainCoherentIntervalProducerV1
open FamilyStickyScaleChainCoherentExactHierarchyProducerV2
open FamilyStickyScaleChainCoherentExactHierarchyProducerV2.CoherentExactHierarchyFamily
open FamilyStickyScaleChainCanonicalBufferedTestBodyChainV2.MultiscaleTubeHierarchy
open FamilyStickyScaleChainCanonicalCoherentBufferedFamilyV2
open FamilyStickyScaleChainCanonicalOneStepEnvelopeCancellationV2
open FamilyStickyScaleChainCanonicalTerminalUnitBodyProducerV2
open FamilyStickyScaleChainCanonicalTerminalUnitBodyProducerV2.MultiscaleTubeHierarchy
open FamilyStickyScaleChainCanonicalNormalizedTerminalUpperV2
open FamilyStickyScaleChainNormalizedTerminalObstructionV2
open FamilyStickyScaleChainActualStrictLossWithConstantV1
open FamilyStickyScaleChainLocalCardAutomaticBoundsV2
open FamilyStickyScaleChainRelevantIntervalEnvelopeInvariantV2
open FamilyStickyScaleChainRelevantThetaCapInvariantV2
open FamilyStickyScaleChainLocalSuccessorAssemblerV2
open FamilyStickyScaleSequenceRefinesAtV2.FiniteScaleSequence
open FamilyStickyScaleSequenceInsertionTransportV2.FiniteScaleSequence

noncomputable section

/-!
# A refinement-stable local-card budget

The two cardinalities in the automatic one-step upper bound are not
independent for a coherent interval.  Parent surjectivity bounds the terminal
active count by the active fine count at the lower endpoint.  Consequently
the local maximum from `LocalCardAutomaticBoundsV2` is exactly that lower
count.

This file also packages the automatic analytic producer with an arbitrary
fixed natural upper bound `n`.  Literal buffered insertion preserves the
non-large lower-end cardinality budget: the lower child has the same lower
endpoint, while the upper child's new lower-end active set is a quotient of
the parent's lower-end active set.  Thus a future cap-bearing driver needs an
initial local-card budget, not a certificate for each reachable bad split.

No packing estimate or numerical upper bound for the initial active set is
proved here.
-/

universe u

variable {delta : NNReal} {gapEpsilon : Real}
  {N : Nat} {eta : Nat -> Real}
  {iota : Type u} [Fintype iota] [DecidableEq iota]
  {fine : UniformTubeFamily delta iota}

/-! ## The local maximum is the lower active count -/

theorem canonicalTerminalActiveCardAt_le_intervalActiveFineCard
    (C : CoherentStickyMultiscaleCover fine)
    {outerDepth : Nat}
    (F : CoherentExactHierarchyFamily C outerDepth 1)
    (m : Fin outerDepth) :
    canonicalTerminalActiveCardAt C F m <=
      ((F.chain m).intervalCover C 0 (by omega)).activeFine.card := by
  let I := (F.chain m).intervalCover C 0 (by omega)
  let B := (F.chain m).selectedCover C 1
  change Fintype.card {i // i ∈ B.coarse.refinement.refined} <=
    I.activeFine.card
  rw [<- B.activeCoarse_eq_refined, Fintype.card_coe]
  exact StickyScaleCover.activeCoarse_card_le_activeFine_card I

theorem canonicalOneStepLocalCardBound_eq_intervalActiveFineCard
    (C : CoherentStickyMultiscaleCover fine)
    {outerDepth : Nat}
    (F : CoherentExactHierarchyFamily C outerDepth 1)
    (m : Fin outerDepth) :
    canonicalOneStepLocalCardBound C F m =
      ((F.chain m).intervalCover C 0 (by omega)).activeFine.card := by
  rw [canonicalOneStepLocalCardBound, max_eq_left]
  exact canonicalTerminalActiveCardAt_le_intervalActiveFineCard C F m

theorem ofFiniteScaleSequence_localCardBound_eq_intervalActiveFineCard
    (C : CoherentStickyMultiscaleCover fine)
    {depth : Nat}
    (S : FiniteScaleSequence delta depth)
    (fine_refined_nonempty : fine.refinement.refined.Nonempty)
    (m : Fin depth) :
    let F := CoherentExactHierarchyFamily.ofFiniteScaleSequence
      C S fine_refined_nonempty
    canonicalOneStepLocalCardBound C F m =
      adjacentIntervalActiveFineCard C S m := by
  dsimp only
  rw [canonicalOneStepLocalCardBound_eq_intervalActiveFineCard C]
  rfl

/-! ## Fixed-card automatic one-step producer -/

/-- Coarse automatic normalized-terminal upper bound from any fixed natural
upper bound on the literal local maximum. -/
theorem ofFiniteScaleSequence_automatic_normalizedTerminal_le_fixedCardCoarseUpper
    (C : CoherentStickyMultiscaleCover fine)
    {depth : Nat}
    (S : FiniteScaleSequence delta depth)
    (fine_refined_nonempty : fine.refinement.refined.Nonempty)
    (delta_pos : 0 < delta) (m : Fin depth) (n : Nat)
    (local_card_le :
      let F := CoherentExactHierarchyFamily.ofFiniteScaleSequence
        C S fine_refined_nonempty
      canonicalOneStepLocalCardBound C F m <= n)
    (theta_le_half : S.theta m <= (2 : NNReal)⁻¹) :
    let F := CoherentExactHierarchyFamily.ofFiniteScaleSequence
      C S fine_refined_nonempty
    canonicalOneStepNormalizedTerminalAt C F
        (fun k => canonicalTerminalUnitBody (F.hierarchy k)) m <=
      automaticNormalizedTerminalCoarseUpper n (S.theta m) := by
  dsimp only at local_card_le ⊢
  let F := CoherentExactHierarchyFamily.ofFiniteScaleSequence
    C S fine_refined_nonempty
  have heffective : (F.hierarchy m).effectiveRadius 1 = S.theta m :=
    CoherentExactHierarchyFamily.ofFiniteScaleSequence_effectiveRadius_one
      C S fine_refined_nonempty m
  have heffective_half :
      (F.hierarchy m).effectiveRadius 1 <= (2 : NNReal)⁻¹ := by
    simpa only [heffective] using theta_le_half
  have initial_card_le :
      ((F.chain m).intervalCover C 0 (by omega)).activeFine.card <= n :=
    (interval_activeFine_card_le_localCardBound C F m).trans local_card_le
  have terminal_card_le : canonicalTerminalActiveCardAt C F m <= n :=
    (terminal_activeCard_le_localCardBound C F m).trans local_card_le
  calc
    canonicalOneStepNormalizedTerminalAt C F
          (fun k => canonicalTerminalUnitBody (F.hierarchy k)) m <=
        automaticNormalizedTerminalUpper n
          ((F.hierarchy m).effectiveRadius 1) :=
      automatic_normalizedTerminal_le_cardUpper C F delta_pos m n
        initial_card_le terminal_card_le heffective_half
    _ <= automaticNormalizedTerminalCoarseUpper n
          ((F.hierarchy m).effectiveRadius 1) :=
      automaticNormalizedTerminalUpper_le_coarseUpper n
        ((F.hierarchy m).effectiveRadius 1) heffective_half
    _ = automaticNormalizedTerminalCoarseUpper n (S.theta m) := by
      rw [heffective]

/-- Fixed-`n` analytic atom.  This direct proof deliberately avoids any
monotonicity theorem for the explicit threshold: the same `n` bounds the
normalized terminal and appears in the small-theta threshold. -/
def ofFiniteScaleSequence_automatic_oneStepExponentBound_of_fixedCardSmallTheta
    (C : CoherentStickyMultiscaleCover fine)
    {depth : Nat}
    (S : FiniteScaleSequence delta depth)
    (fine_refined_nonempty : fine.refinement.refined.Nonempty)
    (delta_pos : 0 < delta)
    (profile : Nat -> Real) (stage : Nat) (m : Fin depth) (n : Nat)
    (local_card_le :
      let F := CoherentExactHierarchyFamily.ofFiniteScaleSequence
        C S fine_refined_nonempty
      canonicalOneStepLocalCardBound C F m <= n)
    (profile_gt_two : 2 < profile (stage - 1))
    (theta_le_threshold : S.theta m <=
      automaticOneStepSmallThetaThreshold n (profile (stage - 1))) :
    let F := CoherentExactHierarchyFamily.ofFiniteScaleSequence
      C S fine_refined_nonempty
    OneStepNormalizedTerminalExponentBound C F
      (fun k => canonicalTerminalUnitBody (F.hierarchy k))
      S profile stage m := by
  dsimp only at local_card_le ⊢
  have theta_pos : 0 < S.theta m :=
    delta_pos.trans_le ((S.delta_le_tau m).trans (S.tau_le_theta m))
  have theta_le_half : S.theta m <= (2 : NNReal)⁻¹ :=
    theta_le_threshold.trans (min_le_left _ _)
  refine {
    exponent := -profile (stage - 1)
    normalizedTerminal_upper := ?_
    exponent_balance := le_rfl }
  exact
    (ofFiniteScaleSequence_automatic_normalizedTerminal_le_fixedCardCoarseUpper
      C S fine_refined_nonempty delta_pos m n local_card_le
        theta_le_half).trans
      (automaticNormalizedTerminalCoarseUpper_le_rpow_of_smallTheta
        n theta_pos profile_gt_two theta_le_threshold)

/-! ## A proof-irrelevant active-card-at helper -/

/-- Active coarse cardinality selected by the coherent cover at one radius.
The two order proofs are explicit only because they are inputs to `cover`. -/
def coherentActiveCoarseCardAt
    (C : CoherentStickyMultiscaleCover fine)
    (rho : NNReal) (hdelta : delta <= rho) (hone : rho <= 1) : Nat :=
  (C.base.cover rho hdelta hone).activeCoarse.card

theorem coherentActiveCoarseCardAt_congr
    (C : CoherentStickyMultiscaleCover fine)
    {rho sigma : NNReal}
    (hdeltaRho : delta <= rho) (hrhoOne : rho <= 1)
    (hdeltaSigma : delta <= sigma) (hsigmaOne : sigma <= 1)
    (h : rho = sigma) :
    coherentActiveCoarseCardAt C rho hdeltaRho hrhoOne =
      coherentActiveCoarseCardAt C sigma hdeltaSigma hsigmaOne := by
  subst sigma
  rfl

theorem adjacentIntervalActiveFineCard_congr_of_tau_eq
    (C : CoherentStickyMultiscaleCover fine)
    {depth depth' : Nat}
    (S : FiniteScaleSequence delta depth)
    (T : FiniteScaleSequence delta depth')
    (m : Fin depth) (k : Fin depth')
    (h : T.tau k = S.tau m) :
    adjacentIntervalActiveFineCard C T k =
      adjacentIntervalActiveFineCard C S m := by
  change coherentActiveCoarseCardAt C (T.tau k) _ _ =
    coherentActiveCoarseCardAt C (S.tau m) _ _
  exact coherentActiveCoarseCardAt_congr C _ _ _ _ h

/-! ## The reachable non-large local-card invariant -/

/-- Exactly the local cardinalities queried by the automatic relevant
producer are bounded by `n`.  Large intervals have no obligation. -/
def NonLargeLocalCardBudget
    (C : CoherentStickyMultiscaleCover fine)
    {depth : Nat}
    (S : FiniteScaleSequence delta depth)
    (gapEpsilon : Real) (n : Nat) : Prop :=
  forall m : Fin depth, Not (S.IsLarge gapEpsilon m) ->
    adjacentIntervalActiveFineCard C S m <= n

namespace NonLargeLocalCardBudget

variable {depth : Nat} {S : FiniteScaleSequence delta depth} {n : Nat}

/-- Convert the invariant at one non-large interval into the fixed-card
premise of the analytic producer. -/
theorem canonicalLocalCard_le
    (C : CoherentStickyMultiscaleCover fine)
    (fine_refined_nonempty : fine.refinement.refined.Nonempty)
    (hbudget : NonLargeLocalCardBudget C S gapEpsilon n)
    (m : Fin depth) (not_large : Not (S.IsLarge gapEpsilon m)) :
    let F := CoherentExactHierarchyFamily.ofFiniteScaleSequence
      C S fine_refined_nonempty
    canonicalOneStepLocalCardBound C F m <= n := by
  dsimp only
  rw [ofFiniteScaleSequence_localCardBound_eq_intervalActiveFineCard C]
  exact hbudget m not_large

variable (C : CoherentStickyMultiscaleCover fine)
  (gap_nonneg : 0 <= gapEpsilon) (delta_pos : 0 < delta)
  (X : RelevantEnvelopeStoppingState delta N gapEpsilon eta)
  (bad : RelevantSelectedActualBadSplit C X)

/-- The lower inserted child has exactly the parent's lower active count. -/
theorem lowerChild_card_eq :
    adjacentIntervalActiveFineCard C
        (bad.refinedScales C X gap_nonneg delta_pos)
        (lowerChildIndex bad.selectedStep) =
      adjacentIntervalActiveFineCard C X.scales bad.selectedStep := by
  exact adjacentIntervalActiveFineCard_congr_of_tau_eq C X.scales
    (bad.refinedScales C X gap_nonneg delta_pos) bad.selectedStep
    (lowerChildIndex bad.selectedStep)
    (tau_lowerChild_eq
      (bad.refinedScales_refinesAt C X gap_nonneg delta_pos))

/-- Parent surjectivity from the old lower endpoint to the inserted radius
bounds the upper child's new lower active count by the parent's count. -/
theorem upperChild_card_le :
    adjacentIntervalActiveFineCard C
        (bad.refinedScales C X gap_nonneg delta_pos)
        (upperChildIndex bad.selectedStep) <=
      adjacentIntervalActiveFineCard C X.scales bad.selectedStep := by
  have htauRho : X.scales.tau bad.selectedStep <= bad.rho :=
    tau_le_of_isBuffered X.scales bad.selectedStep bad.rho
      delta_pos gap_nonneg bad.rho_buffered
  have hrhoOne : bad.rho <= 1 :=
    (le_theta_of_isBuffered X.scales bad.selectedStep bad.rho
      gap_nonneg bad.rho_buffered).trans
      (X.scales.theta_le_one bad.selectedStep)
  let I := C.intervalScaleCover (X.scales.tau bad.selectedStep) bad.rho
    (X.scales.delta_le_tau bad.selectedStep) htauRho hrhoOne
  have hcard := StickyScaleCover.activeCoarse_card_le_activeFine_card I
  change coherentActiveCoarseCardAt C bad.rho _ _ <=
    coherentActiveCoarseCardAt C (X.scales.tau bad.selectedStep) _ _ at hcard
  have hupper : adjacentIntervalActiveFineCard C
        (bad.refinedScales C X gap_nonneg delta_pos)
        (upperChildIndex bad.selectedStep) =
      coherentActiveCoarseCardAt C bad.rho
        ((X.scales.delta_le_tau bad.selectedStep).trans htauRho)
        hrhoOne := by
    change coherentActiveCoarseCardAt C _ _ _ =
      coherentActiveCoarseCardAt C _ _ _
    exact coherentActiveCoarseCardAt_congr C _ _ _ _
      (tau_upperChild_eq
        (bad.refinedScales_refinesAt C X gap_nonneg delta_pos))
  rw [hupper]
  exact hcard

/-- Literal buffered insertion preserves the local-card budget on every
non-large child and every transported interval. -/
theorem refinedScales
    (hbudget : NonLargeLocalCardBudget C X.scales gapEpsilon n) :
    NonLargeLocalCardBudget C
      (bad.refinedScales C X gap_nonneg delta_pos) gapEpsilon n := by
  let href := bad.refinedScales_refinesAt C X gap_nonneg delta_pos
  intro k child_not_large
  refine Fin.succAboveCases
    (α := fun k : Fin (X.depth + 1) =>
      Not ((bad.refinedScales C X gap_nonneg delta_pos).IsLarge
        gapEpsilon k) ->
      adjacentIntervalActiveFineCard C
        (bad.refinedScales C X gap_nonneg delta_pos) k <= n)
    (lowerChildIndex bad.selectedStep)
    (fun _ => (lowerChild_card_eq C gap_nonneg delta_pos X bad).le.trans
      (hbudget bad.selectedStep (bad.selectedStep_not_large C X)))
    ?_ k child_not_large
  intro j child_not_large
  rcases lt_trichotomy j bad.selectedStep with hjm | hjm | hmj
  · rw [lowerChild_succAbove_eq_before bad.selectedStep j hjm] at child_not_large ⊢
    have old_not_large : Not (X.scales.IsLarge gapEpsilon j) := by
      exact fun old_large => child_not_large
        ((isLarge_before_iff gapEpsilon href hjm).2 old_large)
    calc
      adjacentIntervalActiveFineCard C
          (bad.refinedScales C X gap_nonneg delta_pos)
          (beforeIntervalEmbedding X.depth j) =
        adjacentIntervalActiveFineCard C X.scales j :=
          adjacentIntervalActiveFineCard_congr_of_tau_eq C X.scales
            (bad.refinedScales C X gap_nonneg delta_pos) j
            (beforeIntervalEmbedding X.depth j) (tau_before_eq href hjm)
      _ <= n := hbudget j old_not_large
  · subst j
    rw [lowerChild_succAbove_eq_upper]
    exact (upperChild_card_le C gap_nonneg delta_pos X bad).trans
      (hbudget bad.selectedStep (bad.selectedStep_not_large C X))
  · rw [lowerChild_succAbove_eq_after bad.selectedStep j hmj] at child_not_large ⊢
    have old_not_large : Not (X.scales.IsLarge gapEpsilon j) := by
      exact fun old_large => child_not_large
        ((isLarge_after_iff gapEpsilon href hmj).2 old_large)
    calc
      adjacentIntervalActiveFineCard C
          (bad.refinedScales C X gap_nonneg delta_pos)
          (afterIntervalEmbedding X.depth j) =
        adjacentIntervalActiveFineCard C X.scales j :=
          adjacentIntervalActiveFineCard_congr_of_tau_eq C X.scales
            (bad.refinedScales C X gap_nonneg delta_pos) j
            (afterIntervalEmbedding X.depth j) (tau_after_eq href hmj)
      _ <= n := hbudget j old_not_large

end NonLargeLocalCardBudget

#print axioms canonicalTerminalActiveCardAt_le_intervalActiveFineCard
#print axioms canonicalOneStepLocalCardBound_eq_intervalActiveFineCard
#print axioms ofFiniteScaleSequence_localCardBound_eq_intervalActiveFineCard
#print axioms ofFiniteScaleSequence_automatic_normalizedTerminal_le_fixedCardCoarseUpper
#print axioms ofFiniteScaleSequence_automatic_oneStepExponentBound_of_fixedCardSmallTheta
#print axioms coherentActiveCoarseCardAt_congr
#print axioms NonLargeLocalCardBudget.canonicalLocalCard_le
#print axioms NonLargeLocalCardBudget.lowerChild_card_eq
#print axioms NonLargeLocalCardBudget.upperChild_card_le
#print axioms NonLargeLocalCardBudget.refinedScales

end
end FamilyStickyScaleChainLocalCardBudgetInvariantV2
