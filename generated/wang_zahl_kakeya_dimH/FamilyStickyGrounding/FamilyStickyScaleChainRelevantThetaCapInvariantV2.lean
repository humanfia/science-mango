import FamilyStickyGrounding.FamilyStickyScaleChainAutomaticRelevantSuccessorV2

set_option autoImplicit false
set_option warningAsError true
set_option linter.unusedSectionVars false
set_option maxHeartbeats 3000000

open Set MeasureTheory
open scoped BigOperators ENNReal NNReal

namespace FamilyStickyScaleChainRelevantThetaCapInvariantV2

open LeanEval.Analysis.WangZahlKakeya
open Submission.Kakeya.ConvexGeometry
open Submission.Kakeya.Uniformity
open FamilyStickyDividingScalesFiniteStoppingV1
open FamilyStickyScaleChainCoherentIntervalProducerV1
open FamilyStickyScaleChainCoherentExactHierarchyProducerV2
open FamilyStickyScaleChainCoherentExactHierarchyProducerV2.CoherentExactHierarchyFamily
open FamilyStickyScaleChainCanonicalInsertionEnvelopeTransportV2
open FamilyStickyScaleChainCanonicalCoherentBufferedFamilyV2
open FamilyStickyScaleChainCanonicalOneStepEnvelopeCancellationV2
open FamilyStickyScaleChainCanonicalTerminalUnitBodyProducerV2
open FamilyStickyScaleChainCanonicalTerminalUnitBodyProducerV2.MultiscaleTubeHierarchy
open FamilyStickyScaleChainCanonicalNormalizedTerminalUpperV2
open FamilyStickyScaleChainRelevantIntervalEnvelopeInvariantV2
open FamilyStickyScaleChainRelevantCountedStoppingDriverV2
open FamilyStickyScaleChainAutomaticRelevantSuccessorV2
open FamilyStickyScaleChainSelectedNumericalAllocationProducerV1
open FamilyStickyScaleChainLocalSuccessorAssemblerV2
open FamilyStickyScaleSequenceRefinesAtV2.FiniteScaleSequence
open FamilyStickyScaleSequenceInsertionTransportV2.FiniteScaleSequence

noncomputable section

/-!
# A non-large endpoint cap for the relevant Family 7 recursion

The automatic terminal-body estimate needs a small upper endpoint only when
an interval is non-large.  We therefore record the exact invariant

`not IsLarge gapEpsilon m -> theta m <= cap`.

A canonical buffered-radius insertion preserves this invariant.  On the
upper child, `theta` is the selected parent's endpoint; on the lower child,
`theta` is the inserted radius and is at most the parent's endpoint.  The
same parent is non-large by construction.

Combining this invariant with the explicit automatic small-theta producer
removes every per-bad-split child certificate.  Since the existing
`RelevantCanonicalChildSuccessor` quantifies over all counted states, its
global adapter takes a statewise proof of the cap invariant.  No stronger
all-interval cap is introduced.
-/

universe u

variable {delta : NNReal} {gapEpsilon : Real}
  {N : Nat} {eta : Nat -> Real}
  {iota : Type u} [Fintype iota] [DecidableEq iota]
  {fine : UniformTubeFamily delta iota}

/-! ## The scale-sequence invariant -/

/-- Only endpoints which can be selected by the relevant stopping argument
must lie below `cap`. -/
def NonLargeThetaCap {depth : Nat}
    (S : FiniteScaleSequence delta depth)
    (gapEpsilon : Real) (cap : NNReal) : Prop :=
  forall m : Fin depth, Not (S.IsLarge gapEpsilon m) -> S.theta m <= cap

namespace NonLargeThetaCap

variable {depth : Nat} {S : FiniteScaleSequence delta depth} {cap : NNReal}

/-- The upper inserted child inherits the selected parent's upper endpoint,
and that parent is the first non-large interval. -/
theorem upperChild_theta_le
    (C : CoherentStickyMultiscaleCover fine)
    (gap_nonneg : 0 <= gapEpsilon) (delta_pos : 0 < delta)
    (X : RelevantEnvelopeStoppingState delta N gapEpsilon eta)
    (bad : RelevantSelectedActualBadSplit C X)
    (hcap : NonLargeThetaCap X.scales gapEpsilon cap) :
    (bad.refinedScales C X gap_nonneg delta_pos).theta
        (upperChildIndex bad.selectedStep) <= cap := by
  let href := bad.refinedScales_refinesAt C X gap_nonneg delta_pos
  calc
    (bad.refinedScales C X gap_nonneg delta_pos).theta
          (upperChildIndex bad.selectedStep) =
        X.scales.theta bad.selectedStep := theta_upperChild_eq href
    _ <= cap := hcap bad.selectedStep (bad.selectedStep_not_large C X)

/-- The lower inserted child's upper endpoint is the buffered radius, which
is at most the selected parent's upper endpoint. -/
theorem lowerChild_theta_le
    (C : CoherentStickyMultiscaleCover fine)
    (gap_nonneg : 0 <= gapEpsilon) (delta_pos : 0 < delta)
    (X : RelevantEnvelopeStoppingState delta N gapEpsilon eta)
    (bad : RelevantSelectedActualBadSplit C X)
    (hcap : NonLargeThetaCap X.scales gapEpsilon cap) :
    (bad.refinedScales C X gap_nonneg delta_pos).theta
        (lowerChildIndex bad.selectedStep) <= cap := by
  let href := bad.refinedScales_refinesAt C X gap_nonneg delta_pos
  calc
    (bad.refinedScales C X gap_nonneg delta_pos).theta
          (lowerChildIndex bad.selectedStep) = bad.rho :=
      theta_lowerChild_eq href
    _ <= X.scales.theta bad.selectedStep :=
      le_theta_of_isBuffered X.scales bad.selectedStep bad.rho gap_nonneg
        bad.rho_buffered
    _ <= cap := hcap bad.selectedStep (bad.selectedStep_not_large C X)

/-- Literal buffered-radius insertion preserves the non-large endpoint cap.
Untouched intervals transport both their endpoints and their `IsLarge`
status; both children are controlled by the selected non-large parent. -/
theorem refinedScales
    (C : CoherentStickyMultiscaleCover fine)
    (gap_nonneg : 0 <= gapEpsilon) (delta_pos : 0 < delta)
    (X : RelevantEnvelopeStoppingState delta N gapEpsilon eta)
    (bad : RelevantSelectedActualBadSplit C X)
    (hcap : NonLargeThetaCap X.scales gapEpsilon cap) :
    NonLargeThetaCap (bad.refinedScales C X gap_nonneg delta_pos)
      gapEpsilon cap := by
  let href := bad.refinedScales_refinesAt C X gap_nonneg delta_pos
  intro k child_not_large
  refine Fin.succAboveCases
    (α := fun k : Fin (X.depth + 1) =>
      Not ((bad.refinedScales C X gap_nonneg delta_pos).IsLarge
        gapEpsilon k) ->
      (bad.refinedScales C X gap_nonneg delta_pos).theta k <= cap)
    (lowerChildIndex bad.selectedStep)
    (fun _ => lowerChild_theta_le C gap_nonneg delta_pos X bad hcap)
    ?_ k child_not_large
  intro j child_not_large
  rcases lt_trichotomy j bad.selectedStep with hjm | hjm | hmj
  · rw [lowerChild_succAbove_eq_before bad.selectedStep j hjm] at child_not_large ⊢
    have old_not_large : Not (X.scales.IsLarge gapEpsilon j) := by
      exact fun old_large => child_not_large
        ((isLarge_before_iff gapEpsilon href hjm).2 old_large)
    rw [theta_before_eq href hjm]
    exact hcap j old_not_large
  · subst j
    rw [lowerChild_succAbove_eq_upper]
    exact upperChild_theta_le C gap_nonneg delta_pos X bad hcap
  · rw [lowerChild_succAbove_eq_after bad.selectedStep j hmj] at child_not_large ⊢
    have old_not_large : Not (X.scales.IsLarge gapEpsilon j) := by
      exact fun old_large => child_not_large
        ((isLarge_after_iff gapEpsilon href hmj).2 old_large)
    rw [theta_after_eq href hmj]
    exact hcap j old_not_large

end NonLargeThetaCap

/-! ## Preservation by the canonical relevant successor -/

/-- `RelevantCanonicalChildCertificate.toCanonical` changes the scale
sequence by exactly the buffered insertion above, so it preserves the cap
independently of the bodies chosen by the certificate. -/
theorem nonLargeThetaCap_toCanonical
    (C : CoherentStickyMultiscaleCover fine)
    (gap_nonneg : 0 <= gapEpsilon) (delta_pos : 0 < delta)
    (eta_monotone : Monotone eta)
    (Q : RelevantCanonicalOneStepStoppingData C N gapEpsilon eta)
    (bad : RelevantSelectedActualBadSplit C (Q.toState C delta_pos))
    (R : RelevantCanonicalChildCertificate C gap_nonneg delta_pos Q bad)
    (stage_lt : Q.stage < N) {cap : NNReal}
    (hcap : NonLargeThetaCap Q.scales gapEpsilon cap) :
    NonLargeThetaCap
      (R.toCanonical C gap_nonneg delta_pos Q bad eta_monotone stage_lt).scales
      gapEpsilon cap := by
  exact NonLargeThetaCap.refinedScales C gap_nonneg delta_pos
    (Q.toState C delta_pos) bad hcap

/-! ## Automatic child certificate from the cap -/

/-- A current-state cap and one stage's numerical room automatically supply
both conditional small-theta child packages.  There is no per-child analytic
or certificate input. -/
def relevantCanonicalChildCertificate_of_nonLargeThetaCap
    (C : CoherentStickyMultiscaleCover fine)
    (gap_nonneg : 0 <= gapEpsilon) (delta_pos : 0 < delta)
    (Q : RelevantCanonicalOneStepStoppingData C N gapEpsilon eta)
    (bad : RelevantSelectedActualBadSplit C (Q.toState C delta_pos))
    (cap : NNReal)
    (hcap : NonLargeThetaCap Q.scales gapEpsilon cap)
    (profile_gt_two : 2 < eta Q.stage)
    (cap_le_threshold : cap <=
      automaticOneStepSmallThetaThreshold (Fintype.card iota)
        (eta Q.stage)) :
    RelevantCanonicalChildCertificate C gap_nonneg delta_pos Q bad :=
  relevantCanonicalChildCertificate_of_smallTheta C gap_nonneg delta_pos
    Q bad
    { upper := fun _child_not_large =>
        ⟨profile_gt_two,
          (NonLargeThetaCap.upperChild_theta_le C gap_nonneg delta_pos
            (Q.toState C delta_pos) bad hcap).trans cap_le_threshold⟩
      lower := fun _child_not_large =>
        ⟨profile_gt_two,
          (NonLargeThetaCap.lowerChild_theta_le C gap_nonneg delta_pos
            (Q.toState C delta_pos) bad hcap).trans cap_le_threshold⟩ }

/-- Stagewise exponent room and threshold absorption required by every
below-bound state of the counted recursion. -/
def RelevantThetaCapStageWindow
    (N : Nat) (eta : Nat -> Real) (iota : Type*) [Fintype iota]
    (cap : NNReal) : Prop :=
  forall s : Nat, 1 <= s -> s < N ->
    2 < eta s /\
      cap <= automaticOneStepSmallThetaThreshold (Fintype.card iota)
        (eta s)

/-- The cap invariant in the statewise form required by the existing
successor API, whose domain contains every counted state rather than only
states reachable from a chosen initial state. -/
def RelevantCanonicalStatewiseThetaCap
    (C : CoherentStickyMultiscaleCover fine)
    (N : Nat) (gapEpsilon : Real) (eta : Nat -> Real)
    (cap : NNReal) : Prop :=
  forall X : RelevantCanonicalCountedState C N gapEpsilon eta,
    NonLargeThetaCap X.data.scales gapEpsilon cap

/-- Construct exactly the successor consumed by the counted driver from a
statewise cap invariant and a stage window.  In particular no callback
depending on a bad split remains. -/
def relevantCanonicalChildSuccessor_of_nonLargeThetaCap
    (C : CoherentStickyMultiscaleCover fine)
    (gap_nonneg : 0 <= gapEpsilon) (delta_pos : 0 < delta)
    (cap : NNReal)
    (statewiseCap : RelevantCanonicalStatewiseThetaCap C N gapEpsilon eta cap)
    (stageWindow : RelevantThetaCapStageWindow N eta iota cap) :
    RelevantCanonicalChildSuccessor (N := N) (eta := eta)
      C gap_nonneg delta_pos :=
  fun X stage_lt bad =>
    relevantCanonicalChildCertificate_of_nonLargeThetaCap C gap_nonneg
      delta_pos X.data bad cap (statewiseCap X)
      (stageWindow X.data.stage X.data.stage_pos stage_lt).1
      (stageWindow X.data.stage X.data.stage_pos stage_lt).2

/-! ## Automatic initial relevant canonical data -/

/-- The canonical automatic terminal-unit bodies satisfy the relevant
envelope invariant on an initially capped scale sequence. -/
theorem automaticCanonicalRelevantEnvelope_upper_of_nonLargeThetaCap
    {depth stage : Nat}
    (C : CoherentStickyMultiscaleCover fine)
    (S : FiniteScaleSequence delta depth)
    (fine_refined_nonempty : fine.refinement.refined.Nonempty)
    (delta_pos : 0 < delta)
    (cap : NNReal)
    (hcap : NonLargeThetaCap S gapEpsilon cap)
    (profile_gt_two : 2 < eta (stage - 1))
    (cap_le_threshold : cap <=
      automaticOneStepSmallThetaThreshold (Fintype.card iota)
        (eta (stage - 1))) :
    forall m : Fin depth, Not (S.IsLarge gapEpsilon m) ->
      canonicalHierarchyEnvelopeAt
          (CoherentExactHierarchyFamily.ofFiniteScaleSequence C S
            fine_refined_nonempty)
          (by omega)
          (fun k => canonicalTerminalUnitBody
            ((CoherentExactHierarchyFamily.ofFiniteScaleSequence C S
              fine_refined_nonempty).hierarchy k)) m <=
        requiredGlobalPowerAt S eta stage m := by
  intro m not_large
  let F := CoherentExactHierarchyFamily.ofFiniteScaleSequence C S
    fine_refined_nonempty
  let body : Fin depth -> ConvexBody Space :=
    fun k => canonicalTerminalUnitBody (F.hierarchy k)
  let bound := ofFiniteScaleSequence_automatic_oneStepExponentBound_of_smallTheta
    C S fine_refined_nonempty delta_pos eta stage m profile_gt_two
      ((hcap m not_large).trans cap_le_threshold)
  have body_volume_pos : forall k,
      0 < volume (body k : Set Space) := by
    intro k
    exact canonicalTerminalUnitBody_volume_pos _
  have theta_le_one : (S.theta m : ENNReal) <= 1 := by
    exact_mod_cast S.theta_le_one m
  change canonicalHierarchyEnvelopeAt F (by omega) body m <=
    requiredGlobalPowerAt S eta stage m
  calc
    canonicalHierarchyEnvelopeAt F (by omega) body m =
        canonicalOneStepNormalizedTerminalAt C F body m :=
      canonicalHierarchyEnvelopeAt_one_eq_normalizedTerminal C F delta_pos
        body body_volume_pos m
    _ <= (S.theta m : ENNReal) ^ bound.exponent :=
      bound.normalizedTerminal_upper
    _ <= (S.theta m : ENNReal) ^ (-eta (stage - 1)) :=
      ENNReal.rpow_le_rpow_of_exponent_ge theta_le_one
        bound.exponent_balance
    _ = requiredGlobalPowerAt S eta stage m := rfl

/-- Automatic-body initial relevant canonical stopping data.  Its only
analytic premise is the non-large endpoint cap together with the displayed
stage exponent and finite-cardinality threshold. -/
def automaticRelevantCanonicalOneStepStoppingData_of_nonLargeThetaCap
    {depth stage : Nat}
    (C : CoherentStickyMultiscaleCover fine)
    (S : FiniteScaleSequence delta depth)
    (depth_pos : 0 < depth)
    (fine_refined_nonempty : fine.refinement.refined.Nonempty)
    (delta_pos : 0 < delta)
    (stage_pos : 1 <= stage) (stage_le : stage <= N)
    (cap : NNReal)
    (hcap : NonLargeThetaCap S gapEpsilon cap)
    (profile_gt_two : 2 < eta (stage - 1))
    (cap_le_threshold : cap <=
      automaticOneStepSmallThetaThreshold (Fintype.card iota)
        (eta (stage - 1))) :
    RelevantCanonicalOneStepStoppingData C N gapEpsilon eta where
  depth := depth
  depth_pos := depth_pos
  fine_refined_nonempty := fine_refined_nonempty
  scales := S
  stage := stage
  stage_pos := stage_pos
  stage_le := stage_le
  initialBody := fun m => canonicalTerminalUnitBody
    ((CoherentExactHierarchyFamily.ofFiniteScaleSequence C S
      fine_refined_nonempty).hierarchy m)
  initialVolume_pos := fun _m => canonicalTerminalUnitBody_volume_pos _
  terminal_top_le_one := fun _m => canonicalTerminalUnitBody_top_le_one _
  canonicalRelevantEnvelope_upper :=
    automaticCanonicalRelevantEnvelope_upper_of_nonLargeThetaCap C S
      fine_refined_nonempty delta_pos cap hcap profile_gt_two
      cap_le_threshold

#print axioms NonLargeThetaCap.upperChild_theta_le
#print axioms NonLargeThetaCap.lowerChild_theta_le
#print axioms NonLargeThetaCap.refinedScales
#print axioms nonLargeThetaCap_toCanonical
#print axioms relevantCanonicalChildCertificate_of_nonLargeThetaCap
#print axioms relevantCanonicalChildSuccessor_of_nonLargeThetaCap
#print axioms automaticCanonicalRelevantEnvelope_upper_of_nonLargeThetaCap
#print axioms automaticRelevantCanonicalOneStepStoppingData_of_nonLargeThetaCap

end
end FamilyStickyScaleChainRelevantThetaCapInvariantV2
