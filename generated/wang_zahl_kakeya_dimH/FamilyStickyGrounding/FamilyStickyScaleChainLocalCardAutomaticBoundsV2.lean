import FamilyStickyGrounding.FamilyStickyScaleChainCanonicalNormalizedTerminalUpperV2
import FamilyStickyGrounding.FamilyStickyScaleChainFirstNonLargeAdjacentCardBudgetProducerV1

set_option autoImplicit false
set_option warningAsError true
set_option linter.unusedSectionVars false
set_option maxHeartbeats 1000000

open Set MeasureTheory
open scoped BigOperators ENNReal NNReal InnerProductSpace

namespace FamilyStickyScaleChainLocalCardAutomaticBoundsV2

open LeanEval.Analysis.WangZahlKakeya
open Submission.Kakeya.ConvexGeometry
open Submission.Kakeya.ConvexFactoring
open Submission.Kakeya.Uniformity
open FamilyStickyAtEveryScaleCoreV1
open FamilyStickyDeltaMaxFiniteChainV2
open FamilyStickyDeltaMaxFiniteChainV2.StickyScaleCover
open FamilyStickyDividingScalesFiniteStoppingV1
open FamilyStickyScaleChainCoherentIntervalProducerV1
open FamilyStickyScaleChainCoherentExactHierarchyProducerV2
open FamilyStickyScaleChainCoherentExactHierarchyProducerV2.CoherentExactHierarchyFamily
open FamilyStickyScaleChainBufferedHierarchyProducerV1.MultiscaleTubeHierarchy
open FamilyStickyScaleChainCanonicalBufferedTestBodyChainV2.MultiscaleTubeHierarchy
open FamilyStickyScaleChainCanonicalCoherentBufferedFamilyV2
open FamilyStickyScaleChainCanonicalTerminalUnitBodyProducerV2
open FamilyStickyScaleChainCanonicalTerminalUnitBodyProducerV2.MultiscaleTubeHierarchy
open FamilyStickyScaleChainCanonicalOneStepEnvelopeCancellationV2
open FamilyStickyScaleChainCanonicalNormalizedTerminalUpperV2
open FamilyStickyScaleChainNormalizedTerminalObstructionV2
open FamilyStickyScaleChainSmallDeltaExponentBudgetProducerV1
open FamilyStickyScaleChainActualValuesV1
open FamilyStickyScaleChainActualStrictLossWithConstantV1
open FamilyStickyScaleChainFirstNonLargeAdjacentCardBudgetProducerV1
open FamilyStickyScaleChainSelectedNumericalAllocationProducerV1

noncomputable section

/-!
# Local-card upper bounds for the automatic one-step terminal package

The global cardinality in the existing automatic upper bound is used twice:
it bounds the active fine family at the lower endpoint and the literal active
terminal subtype at the upper endpoint.  These are generally different local
finite sets.  This file first parameterizes the proof by any common upper
bound, and then takes their maximum.  It does not provide a packing estimate
for either local cardinality.

The adjacent-card argument is parameterized separately by a bound for the
literal adjacent coarse value.  Its local specialization uses the active
coarse (or active fine) cardinality of that same interval cover.
-/

universe u

variable {delta : NNReal} {iota : Type u}
  [Fintype iota] [DecidableEq iota]
  {fine : UniformTubeFamily delta iota}
  (C : CoherentStickyMultiscaleCover fine)
  {outerDepth : Nat}

/-! ## The two local terminal counts -/

/-- A common local cardinality bound for one exact one-step hierarchy: the
maximum of the lower-end active fine count and the terminal active subtype
count. -/
def canonicalOneStepLocalCardBound
    (F : CoherentExactHierarchyFamily C outerDepth 1)
    (m : Fin outerDepth) : Nat :=
  max ((F.chain m).intervalCover C 0 (by omega)).activeFine.card
    (canonicalTerminalActiveCardAt C F m)

theorem interval_activeFine_card_le_localCardBound
    (F : CoherentExactHierarchyFamily C outerDepth 1)
    (m : Fin outerDepth) :
    ((F.chain m).intervalCover C 0 (by omega)).activeFine.card <=
      canonicalOneStepLocalCardBound C F m := by
  exact Nat.le_max_left _ _

theorem terminal_activeCard_le_localCardBound
    (F : CoherentExactHierarchyFamily C outerDepth 1)
    (m : Fin outerDepth) :
    canonicalTerminalActiveCardAt C F m <=
      canonicalOneStepLocalCardBound C F m := by
  exact Nat.le_max_right _ _

/-- The local maximum is never worse than the former global fine-index
cardinality bound. -/
theorem canonicalOneStepLocalCardBound_le_original_card
    (F : CoherentExactHierarchyFamily C outerDepth 1)
    (m : Fin outerDepth) :
    canonicalOneStepLocalCardBound C F m <= Fintype.card iota := by
  rw [canonicalOneStepLocalCardBound, max_le_iff]
  exact ⟨interval_activeFine_card_le_original_card C F m,
    terminal_activeCard_le_original_card C F m⟩

/-- The normalized automatic terminal proof only needs a common upper bound
for its two literal local cardinalities.  No reference to the original fine
index cardinality is required. -/
theorem automatic_normalizedTerminal_le_cardUpper
    (F : CoherentExactHierarchyFamily C outerDepth 1)
    (delta_pos : 0 < delta)
    (m : Fin outerDepth)
    (n : Nat)
    (initial_card_le :
      ((F.chain m).intervalCover C 0 (by omega)).activeFine.card <= n)
    (terminal_card_le : canonicalTerminalActiveCardAt C F m <= n)
    (hradius : (F.hierarchy m).effectiveRadius 1 <= (2 : NNReal)⁻¹) :
    canonicalOneStepNormalizedTerminalAt C F
        (fun k => canonicalTerminalUnitBody (F.hierarchy k)) m <=
      automaticNormalizedTerminalUpper n
        ((F.hierarchy m).effectiveRadius 1) := by
  let H := F.hierarchy m
  have hvol :=
    MultiscaleTubeHierarchy.volume_automaticTerminalTestBody_le_activeCardUpper
      H hradius
  have hcardTerminal :
      (Fintype.card {i // i ∈
        (H.effectiveFamily 1).refinement.refined} : ENNReal) <=
        (n : ENNReal) := by
    exact_mod_cast terminal_card_le
  have hbody :
      volume (canonicalTestBody H (canonicalTerminalUnitBody H) 1 : Set Space) <=
        automaticTerminalBodyVolumeUpper n (H.effectiveRadius 1) := by
    exact hvol.trans (by
      unfold automaticTerminalBodyVolumeUpper
      gcongr)
  have hfloor :=
    MultiscaleTubeHierarchy.half_sq_le_terminal_canonicalTubeVolume H hradius
  have hinitialCard :
      (((F.chain m).intervalCover C 0 (by omega)).activeFine.card : ENNReal) <=
        (n : ENNReal) := by
    exact_mod_cast initial_card_le
  unfold canonicalOneStepNormalizedTerminalAt automaticNormalizedTerminalUpper
  rw [<- mul_div_assoc]
  apply ENNReal.div_le_of_le_mul
  calc
    (((F.chain m).intervalCover C 0 (by omega)).activeFine.card : ENNReal) *
        volume
          (canonicalTestBody (F.hierarchy m)
            (canonicalTerminalUnitBody (F.hierarchy m)) 1 : Set Space) <=
      (n : ENNReal) *
        automaticTerminalBodyVolumeUpper n
          ((F.hierarchy m).effectiveRadius 1) :=
      mul_le_mul' hinitialCard hbody
    _ = automaticNormalizedTerminalUpper n
          ((F.hierarchy m).effectiveRadius 1) *
        (((F.hierarchy m).effectiveRadius 1 : ENNReal) ^ 2 / 2) := by
      unfold automaticNormalizedTerminalUpper
      have hrho : 0 < ((F.hierarchy m).effectiveRadius 1 : ENNReal) :=
        ENNReal.coe_pos.mpr
          (coherentHierarchy_effectiveRadius_pos F delta_pos m 1)
      have hpos :
          0 < ((F.hierarchy m).effectiveRadius 1 : ENNReal) ^ 2 / 2 := by
        exact ENNReal.div_pos (ENNReal.pow_pos hrho 2).ne' (by norm_num)
      have htop :
          ((F.hierarchy m).effectiveRadius 1 : ENNReal) ^ 2 / 2 ≠ ∞ := by
        finiteness
      rw [ENNReal.div_mul_cancel hpos.ne' htop]
    _ <= automaticNormalizedTerminalUpper n
          ((F.hierarchy m).effectiveRadius 1) *
        canonicalTubeVolume (F.hierarchy m) (by omega) 1 := by
      gcongr

/-- Local specialization of `automatic_normalizedTerminal_le_cardUpper`.
The maximum is interval-dependent and can be strictly smaller than the
original fine index cardinality. -/
theorem automatic_normalizedTerminal_le_localCardUpper
    (F : CoherentExactHierarchyFamily C outerDepth 1)
    (delta_pos : 0 < delta)
    (m : Fin outerDepth)
    (hradius : (F.hierarchy m).effectiveRadius 1 <= (2 : NNReal)⁻¹) :
    canonicalOneStepNormalizedTerminalAt C F
        (fun k => canonicalTerminalUnitBody (F.hierarchy k)) m <=
      automaticNormalizedTerminalUpper
        (canonicalOneStepLocalCardBound C F m)
        ((F.hierarchy m).effectiveRadius 1) := by
  exact automatic_normalizedTerminal_le_cardUpper C F delta_pos m
    (canonicalOneStepLocalCardBound C F m)
    (interval_activeFine_card_le_localCardBound C F m)
    (terminal_activeCard_le_localCardBound C F m) hradius

/-! ## Local-card endpoint producer for a canonical scale sequence -/

theorem ofFiniteScaleSequence_automatic_normalizedTerminal_le_localCardCoarseUpper
    (S : FiniteScaleSequence delta outerDepth)
    (fine_refined_nonempty : fine.refinement.refined.Nonempty)
    (delta_pos : 0 < delta) (m : Fin outerDepth)
    (theta_le_half : S.theta m <= (2 : NNReal)⁻¹) :
    let F := CoherentExactHierarchyFamily.ofFiniteScaleSequence
      C S fine_refined_nonempty
    canonicalOneStepNormalizedTerminalAt C F
        (fun k => canonicalTerminalUnitBody (F.hierarchy k)) m <=
      automaticNormalizedTerminalCoarseUpper
        (canonicalOneStepLocalCardBound C F m) (S.theta m) := by
  dsimp only
  let F := CoherentExactHierarchyFamily.ofFiniteScaleSequence
    C S fine_refined_nonempty
  have heffective : (F.hierarchy m).effectiveRadius 1 = S.theta m :=
    CoherentExactHierarchyFamily.ofFiniteScaleSequence_effectiveRadius_one
      C S fine_refined_nonempty m
  have heffective_half :
      (F.hierarchy m).effectiveRadius 1 <= (2 : NNReal)⁻¹ := by
    simpa only [heffective] using theta_le_half
  calc
    canonicalOneStepNormalizedTerminalAt C F
          (fun k => canonicalTerminalUnitBody (F.hierarchy k)) m <=
        automaticNormalizedTerminalUpper
          (canonicalOneStepLocalCardBound C F m)
          ((F.hierarchy m).effectiveRadius 1) :=
      automatic_normalizedTerminal_le_localCardUpper C F delta_pos m
        heffective_half
    _ <= automaticNormalizedTerminalCoarseUpper
          (canonicalOneStepLocalCardBound C F m)
          ((F.hierarchy m).effectiveRadius 1) :=
      automaticNormalizedTerminalUpper_le_coarseUpper
        (canonicalOneStepLocalCardBound C F m)
        ((F.hierarchy m).effectiveRadius 1) heffective_half
    _ = automaticNormalizedTerminalCoarseUpper
          (canonicalOneStepLocalCardBound C F m) (S.theta m) := by
      rw [heffective]

/-- The automatic exponent package with a genuinely interval-local
cardinality threshold. -/
def ofFiniteScaleSequence_automatic_oneStepExponentBound_of_localCardSmallTheta
    (S : FiniteScaleSequence delta outerDepth)
    (fine_refined_nonempty : fine.refinement.refined.Nonempty)
    (delta_pos : 0 < delta)
    (profile : Nat -> Real) (stage : Nat) (m : Fin outerDepth)
    (profile_gt_two : 2 < profile (stage - 1))
    (theta_le_threshold : S.theta m <=
      let F := CoherentExactHierarchyFamily.ofFiniteScaleSequence
        C S fine_refined_nonempty
      automaticOneStepSmallThetaThreshold
        (canonicalOneStepLocalCardBound C F m)
        (profile (stage - 1))) :
    let F := CoherentExactHierarchyFamily.ofFiniteScaleSequence
      C S fine_refined_nonempty
    OneStepNormalizedTerminalExponentBound C F
      (fun k => canonicalTerminalUnitBody (F.hierarchy k))
      S profile stage m := by
  dsimp only at theta_le_threshold ⊢
  let F := CoherentExactHierarchyFamily.ofFiniteScaleSequence
    C S fine_refined_nonempty
  have theta_pos : 0 < S.theta m :=
    delta_pos.trans_le ((S.delta_le_tau m).trans (S.tau_le_theta m))
  have theta_le_half : S.theta m <= (2 : NNReal)⁻¹ :=
    theta_le_threshold.trans (min_le_left _ _)
  refine {
    exponent := -profile (stage - 1)
    normalizedTerminal_upper := ?_
    exponent_balance := le_rfl }
  exact
    (ofFiniteScaleSequence_automatic_normalizedTerminal_le_localCardCoarseUpper
      C S fine_refined_nonempty delta_pos m theta_le_half).trans
      (automaticNormalizedTerminalCoarseUpper_le_rpow_of_smallTheta
        (canonicalOneStepLocalCardBound C F m) theta_pos profile_gt_two
          theta_le_threshold)

/-! ## A local cardinality threshold for the adjacent value -/

/-- Small-delta threshold for any supplied finite bound on the literal
adjacent coarse value. -/
def adjacentCardBoundThreshold
    (n : Nat) (epsilon exponent : Real) : NNReal :=
  finiteConstantSmallDeltaThreshold (n : ENNReal) (epsilon * exponent)

theorem adjacentCardBoundThreshold_pos
    (n : Nat) (epsilon exponent : Real) :
    0 < adjacentCardBoundThreshold n epsilon exponent :=
  finiteConstantSmallDeltaThreshold_pos (n : ENNReal) (epsilon * exponent)

/-- The adjacent argument only needs a finite numerical upper bound for the
actual adjacent coarse value. -/
theorem adjacentBudget_of_cardBound_long_and_smallDelta
    {epsilon : Real}
    (S : FiniteScaleSequence delta outerDepth)
    (m : Fin outerDepth)
    (profile : Nat -> Real) (stage n : Nat)
    (adjacent_le :
      (C.toActualIntervalCovers S).adjacentCoarseValue m <= (n : ENNReal))
    (epsilon_pos : 0 < epsilon)
    (profile_pred_pos : 0 < profile (stage - 1))
    (delta_pos : 0 < delta)
    (long : S.IsLong epsilon m)
    (delta_le : delta <= adjacentCardBoundThreshold
      n epsilon (profile (stage - 1))) :
    (C.toActualIntervalCovers S).adjacentCoarseValue m <=
      requiredAdjacentPowerAt S profile stage m := by
  have card_ne_top : (n : ENNReal) ≠ ∞ :=
    ENNReal.natCast_ne_top n
  have card_le_power :
      (n : ENNReal) <=
        (delta : ENNReal) ^ (-(epsilon * profile (stage - 1))) := by
    exact finiteConstant_le_delta_negativePower card_ne_top
      (mul_pos epsilon_pos profile_pred_pos) delta_pos delta_le
  calc
    (C.toActualIntervalCovers S).adjacentCoarseValue m <=
        (n : ENNReal) := adjacent_le
    _ <= (delta : ENNReal) ^
        (-(epsilon * profile (stage - 1))) := card_le_power
    _ <= (((S.theta m / S.tau m : NNReal) : ENNReal) ^
        profile (stage - 1)) :=
      delta_negative_mul_exponent_le_endpointRatio_power S m
        delta_pos long profile_pred_pos.le
    _ = requiredAdjacentPowerAt S profile stage m := by
      rfl

/-- Active coarse cardinality of the literal adjacent interval cover. -/
def adjacentIntervalActiveCoarseCard
    (S : FiniteScaleSequence delta outerDepth)
    (m : Fin outerDepth) : Nat :=
  (C.intervalScaleCover (S.tau m) (S.theta m)
    (S.delta_le_tau m) (S.tau_le_theta m) (S.theta_le_one m)).activeCoarse.card

/-- Active fine cardinality of the same literal adjacent interval cover. -/
def adjacentIntervalActiveFineCard
    (S : FiniteScaleSequence delta outerDepth)
    (m : Fin outerDepth) : Nat :=
  (C.intervalScaleCover (S.tau m) (S.theta m)
    (S.delta_le_tau m) (S.tau_le_theta m) (S.theta_le_one m)).activeFine.card

theorem actualAdjacentCoarseValue_le_intervalActiveCoarseCard
    (S : FiniteScaleSequence delta outerDepth)
    (m : Fin outerDepth) :
    (C.toActualIntervalCovers S).adjacentCoarseValue m <=
      (adjacentIntervalActiveCoarseCard C S m : ENNReal) := by
  rw [C.toActualIntervalCovers_adjacentCoarseValue_eq S m]
  exact StickyScaleCover.coarseDeltaMax_le_activeCoarse_card _

theorem actualAdjacentCoarseValue_le_intervalActiveFineCard
    (S : FiniteScaleSequence delta outerDepth)
    (m : Fin outerDepth) :
    (C.toActualIntervalCovers S).adjacentCoarseValue m <=
      (adjacentIntervalActiveFineCard C S m : ENNReal) := by
  calc
    (C.toActualIntervalCovers S).adjacentCoarseValue m <=
        (adjacentIntervalActiveCoarseCard C S m : ENNReal) :=
      actualAdjacentCoarseValue_le_intervalActiveCoarseCard C S m
    _ <= (adjacentIntervalActiveFineCard C S m : ENNReal) := by
      exact_mod_cast StickyScaleCover.activeCoarse_card_le_activeFine_card
        (C.intervalScaleCover (S.tau m) (S.theta m)
          (S.delta_le_tau m) (S.tau_le_theta m) (S.theta_le_one m))

/-- Adjacent budget using the sharp literal interval active-coarse count. -/
theorem adjacentBudget_of_intervalActiveCoarseCard_long_and_smallDelta
    {epsilon : Real}
    (S : FiniteScaleSequence delta outerDepth)
    (m : Fin outerDepth)
    (profile : Nat -> Real) (stage : Nat)
    (epsilon_pos : 0 < epsilon)
    (profile_pred_pos : 0 < profile (stage - 1))
    (delta_pos : 0 < delta)
    (long : S.IsLong epsilon m)
    (delta_le : delta <= adjacentCardBoundThreshold
      (adjacentIntervalActiveCoarseCard C S m)
      epsilon (profile (stage - 1))) :
    (C.toActualIntervalCovers S).adjacentCoarseValue m <=
      requiredAdjacentPowerAt S profile stage m := by
  exact adjacentBudget_of_cardBound_long_and_smallDelta C S m profile stage
    (adjacentIntervalActiveCoarseCard C S m)
    (actualAdjacentCoarseValue_le_intervalActiveCoarseCard C S m)
    epsilon_pos profile_pred_pos delta_pos long delta_le

/-- Adjacent budget using the (possibly coarser) active-fine count of the
same interval. -/
theorem adjacentBudget_of_intervalActiveFineCard_long_and_smallDelta
    {epsilon : Real}
    (S : FiniteScaleSequence delta outerDepth)
    (m : Fin outerDepth)
    (profile : Nat -> Real) (stage : Nat)
    (epsilon_pos : 0 < epsilon)
    (profile_pred_pos : 0 < profile (stage - 1))
    (delta_pos : 0 < delta)
    (long : S.IsLong epsilon m)
    (delta_le : delta <= adjacentCardBoundThreshold
      (adjacentIntervalActiveFineCard C S m)
      epsilon (profile (stage - 1))) :
    (C.toActualIntervalCovers S).adjacentCoarseValue m <=
      requiredAdjacentPowerAt S profile stage m := by
  exact adjacentBudget_of_cardBound_long_and_smallDelta C S m profile stage
    (adjacentIntervalActiveFineCard C S m)
    (actualAdjacentCoarseValue_le_intervalActiveFineCard C S m)
    epsilon_pos profile_pred_pos delta_pos long delta_le

#print axioms canonicalOneStepLocalCardBound
#print axioms automatic_normalizedTerminal_le_cardUpper
#print axioms automatic_normalizedTerminal_le_localCardUpper
#print axioms ofFiniteScaleSequence_automatic_normalizedTerminal_le_localCardCoarseUpper
#print axioms ofFiniteScaleSequence_automatic_oneStepExponentBound_of_localCardSmallTheta
#print axioms adjacentBudget_of_cardBound_long_and_smallDelta
#print axioms actualAdjacentCoarseValue_le_intervalActiveCoarseCard
#print axioms actualAdjacentCoarseValue_le_intervalActiveFineCard
#print axioms adjacentBudget_of_intervalActiveCoarseCard_long_and_smallDelta
#print axioms adjacentBudget_of_intervalActiveFineCard_long_and_smallDelta

end
end FamilyStickyScaleChainLocalCardAutomaticBoundsV2
