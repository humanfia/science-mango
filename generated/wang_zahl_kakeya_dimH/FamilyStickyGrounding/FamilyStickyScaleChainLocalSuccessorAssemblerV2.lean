import FamilyStickyGrounding.FamilyStickyScaleChainHierarchyRecursiveStoppingDriverV2
import FamilyStickyGrounding.FamilyStickyScaleSequenceInsertionTransportV2

set_option autoImplicit false
set_option warningAsError true
set_option linter.unusedSectionVars false
set_option maxHeartbeats 1000000

open scoped ENNReal NNReal

namespace FamilyStickyScaleChainLocalSuccessorAssemblerV2

open Submission.Kakeya.Uniformity
open FamilyStickyDividingScalesFiniteStoppingV1
open FamilyStickyScaleChainActualDividingRunV1
open FamilyStickyScaleChainHierarchyGlobalEnvelopeV2
open FamilyStickyScaleChainSelectedNumericalAllocationProducerV1
open FamilyStickyScaleSequenceInsertionTransportV2.FiniteScaleSequence
open FamilyStickyScaleChainHierarchyRecursiveStoppingDriverV2

noncomputable section

/-!
# Local assembly of a Family7 hierarchy successor

After inserting one bad radius, only the two child intervals are new.  This
module proves that all untouched interval budgets transport automatically,
provided their new hierarchy envelopes do not exceed their old envelopes.
Thus a successor certificate no longer needs a fresh analytic estimate on
every interval: its genuinely new envelope inputs are exactly the upper and
lower children of the split interval.

The construction remains honest about the unresolved geometric step.  It
does not manufacture the new buffered hierarchy, nor prove the two child
envelopes.  Those data are fields of `LocalEnvelopeRefinementCertificate`.
-/

universe u

variable {delta : NNReal} {gapEpsilon : Real}
  {N : Nat} {eta : Nat -> Real}
  {iota : Type u} [Fintype iota] [DecidableEq iota]
  {fine : UniformTubeFamily delta iota}

/-! ## Pure index identities for the inserted interval -/

@[simp] theorem lowerChild_succAbove_eq_upper
    {depth : Nat} (m : Fin depth) :
    (lowerChildIndex m).succAbove m = upperChildIndex m := by
  exact Fin.succAbove_succ_self m

theorem lowerChild_succAbove_eq_before
    {depth : Nat} (m j : Fin depth) (hjm : j < m) :
    (lowerChildIndex m).succAbove j = beforeIntervalEmbedding depth j := by
  exact Fin.succAbove_succ_of_le m j hjm.le

theorem lowerChild_succAbove_eq_after
    {depth : Nat} (m j : Fin depth) (hmj : m < j) :
    (lowerChildIndex m).succAbove j = afterIntervalEmbedding depth j := by
  exact Fin.succAbove_succ_of_lt m j hmj

/-! ## The global power budget becomes weaker when the stage increases -/

theorem requiredGlobalPowerAt_le_succ
    {depth stage : Nat} (S : FiniteScaleSequence delta depth)
    (eta_monotone : Monotone eta) (m : Fin depth) :
    requiredGlobalPowerAt S eta stage m <=
      requiredGlobalPowerAt S eta (stage + 1) m := by
  unfold requiredGlobalPowerAt
  apply ENNReal.rpow_le_rpow_of_exponent_ge
  · exact_mod_cast S.theta_le_one m
  · have heta : eta (stage - 1) <= eta stage :=
      eta_monotone (Nat.sub_le stage 1)
    simpa using neg_le_neg heta

/-! ## A local replacement contract -/

/-- A replacement hierarchy for one inserted scale.  On untouched intervals
its hierarchy envelope may only decrease.  The only fresh quantitative
inputs are the two displayed child-envelope bounds. -/
structure LocalEnvelopeRefinementCertificate
    (C : FamilyStickyScaleChainCoherentIntervalProducerV1.CoherentStickyMultiscaleCover fine)
    (gap_nonneg : 0 <= gapEpsilon) (delta_pos : 0 < delta)
    (X : HierarchyStoppingState delta N gapEpsilon eta)
    (bad : SelectedActualBadSplit C X) where
  newChainDepth : Nat
  newBuffered : BufferedChainFamily (X.depth + 1) newChainDepth
  beforeEnvelope_le : forall j : Fin X.depth, j < bad.selectedStep ->
    hierarchyGlobalEnvelopeAt newBuffered
        (beforeIntervalEmbedding X.depth j) <=
      hierarchyGlobalEnvelopeAt X.buffered j
  afterEnvelope_le : forall j : Fin X.depth, bad.selectedStep < j ->
    hierarchyGlobalEnvelopeAt newBuffered
        (afterIntervalEmbedding X.depth j) <=
      hierarchyGlobalEnvelopeAt X.buffered j
  upperChildEnvelope_upper :
    hierarchyGlobalEnvelopeAt newBuffered
        (upperChildIndex bad.selectedStep) <=
      requiredGlobalPowerAt
        (bad.refinedScales C X gap_nonneg delta_pos) eta (X.stage + 1)
        (upperChildIndex bad.selectedStep)
  lowerChildEnvelope_upper :
    hierarchyGlobalEnvelopeAt newBuffered
        (lowerChildIndex bad.selectedStep) <=
      requiredGlobalPowerAt
        (bad.refinedScales C X gap_nonneg delta_pos) eta (X.stage + 1)
        (lowerChildIndex bad.selectedStep)

namespace LocalEnvelopeRefinementCertificate

variable
    (C : FamilyStickyScaleChainCoherentIntervalProducerV1.CoherentStickyMultiscaleCover fine)
    (gap_nonneg : 0 <= gapEpsilon) (delta_pos : 0 < delta)
    (X : HierarchyStoppingState delta N gapEpsilon eta)
    (bad : SelectedActualBadSplit C X)
    (R : LocalEnvelopeRefinementCertificate C gap_nonneg delta_pos X bad)

/-- Every new interval has the required successor-stage envelope.  The proof
uses `Fin.succAboveCases` with the lower child as the omitted coordinate: the
remaining coordinates are precisely the before intervals, the upper child,
and the after intervals. -/
theorem globalEnvelope_upper (eta_monotone : Monotone eta) :
    forall k : Fin (X.depth + 1),
      hierarchyGlobalEnvelopeAt R.newBuffered k <=
        requiredGlobalPowerAt
          (bad.refinedScales C X gap_nonneg delta_pos) eta (X.stage + 1) k := by
  let href := bad.refinedScales_refinesAt C X gap_nonneg delta_pos
  intro k
  refine Fin.succAboveCases
    (α := fun k : Fin (X.depth + 1) =>
      hierarchyGlobalEnvelopeAt R.newBuffered k <=
        requiredGlobalPowerAt
          (bad.refinedScales C X gap_nonneg delta_pos) eta
          (X.stage + 1) k)
    (lowerChildIndex bad.selectedStep) R.lowerChildEnvelope_upper ?_ k
  intro j
  rcases lt_trichotomy j bad.selectedStep with hjm | hjm | hmj
  · rw [lowerChild_succAbove_eq_before bad.selectedStep j hjm]
    calc
      hierarchyGlobalEnvelopeAt R.newBuffered
          (beforeIntervalEmbedding X.depth j) <=
          hierarchyGlobalEnvelopeAt X.buffered j :=
        R.beforeEnvelope_le j hjm
      _ <= requiredGlobalPowerAt X.scales eta X.stage j :=
        X.globalEnvelope_upper j
      _ <= requiredGlobalPowerAt X.scales eta (X.stage + 1) j :=
        requiredGlobalPowerAt_le_succ X.scales eta_monotone j
      _ = requiredGlobalPowerAt
            (bad.refinedScales C X gap_nonneg delta_pos) eta
            (X.stage + 1) (beforeIntervalEmbedding X.depth j) :=
        (requiredGlobalPowerAt_before_eq eta (X.stage + 1) href hjm).symm
  · subst j
    simpa using R.upperChildEnvelope_upper
  · rw [lowerChild_succAbove_eq_after bad.selectedStep j hmj]
    calc
      hierarchyGlobalEnvelopeAt R.newBuffered
          (afterIntervalEmbedding X.depth j) <=
          hierarchyGlobalEnvelopeAt X.buffered j :=
        R.afterEnvelope_le j hmj
      _ <= requiredGlobalPowerAt X.scales eta X.stage j :=
        X.globalEnvelope_upper j
      _ <= requiredGlobalPowerAt X.scales eta (X.stage + 1) j :=
        requiredGlobalPowerAt_le_succ X.scales eta_monotone j
      _ = requiredGlobalPowerAt
            (bad.refinedScales C X gap_nonneg delta_pos) eta
            (X.stage + 1) (afterIntervalEmbedding X.depth j) :=
        (requiredGlobalPowerAt_after_eq eta (X.stage + 1) href hmj).symm

/-- Forget the local replacement contract to the all-interval certificate
consumed by the existing bounded recursive driver. -/
def toOneStepRefinementCertificate (eta_monotone : Monotone eta) :
    OneStepRefinementCertificate C gap_nonneg delta_pos X bad where
  newChainDepth := R.newChainDepth
  newBuffered := R.newBuffered
  globalEnvelope_upper :=
    R.globalEnvelope_upper C gap_nonneg delta_pos X bad eta_monotone

end LocalEnvelopeRefinementCertificate

/-! ## Driver-level adapter -/

/-- A local analytic successor asks only for a local replacement contract at
each literal bad split. -/
def LocalHierarchyAnalyticSuccessor
    (C : FamilyStickyScaleChainCoherentIntervalProducerV1.CoherentStickyMultiscaleCover fine)
    (gap_nonneg : 0 <= gapEpsilon) (delta_pos : 0 < delta) : Type _ :=
  forall (X : HierarchyStoppingState delta N gapEpsilon eta),
    X.stage < N -> forall (bad : SelectedActualBadSplit C X),
      LocalEnvelopeRefinementCertificate C gap_nonneg delta_pos X bad

/-- The local successor is sufficient for the existing recursive driver. -/
def LocalHierarchyAnalyticSuccessor.toHierarchyAnalyticSuccessor
    (C : FamilyStickyScaleChainCoherentIntervalProducerV1.CoherentStickyMultiscaleCover fine)
    (gap_nonneg : 0 <= gapEpsilon) (delta_pos : 0 < delta)
    (eta_monotone : Monotone eta)
    (successor : LocalHierarchyAnalyticSuccessor (N := N) (eta := eta)
      C gap_nonneg delta_pos) :
    HierarchyAnalyticSuccessor (N := N) (eta := eta)
      C gap_nonneg delta_pos := by
  intro X stage_lt bad
  exact (successor X stage_lt bad).toOneStepRefinementCertificate
    C gap_nonneg delta_pos X bad eta_monotone

#print axioms lowerChild_succAbove_eq_upper
#print axioms requiredGlobalPowerAt_le_succ
#print axioms LocalEnvelopeRefinementCertificate.globalEnvelope_upper
#print axioms LocalEnvelopeRefinementCertificate.toOneStepRefinementCertificate
#print axioms LocalHierarchyAnalyticSuccessor.toHierarchyAnalyticSuccessor

end
end FamilyStickyScaleChainLocalSuccessorAssemblerV2
