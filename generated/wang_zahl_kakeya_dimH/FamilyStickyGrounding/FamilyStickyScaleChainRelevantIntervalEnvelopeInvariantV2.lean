import FamilyStickyGrounding.FamilyStickyScaleChainCanonicalInsertionEnvelopeTransportV2
import FamilyStickyGrounding.FamilyStickyScaleChainNormalizedTerminalObstructionV2

set_option autoImplicit false
set_option warningAsError true
set_option linter.unusedSectionVars false
set_option maxHeartbeats 3000000

open Set MeasureTheory
open scoped BigOperators ENNReal NNReal

namespace FamilyStickyScaleChainRelevantIntervalEnvelopeInvariantV2

open LeanEval.Analysis.WangZahlKakeya
open Submission.Kakeya.ConvexGeometry
open Submission.Kakeya.Uniformity
open FamilyStickyDividingScalesFiniteStoppingV1
open FamilyStickyScaleChainActualDividingRunV1
open FamilyStickyScaleChainActualDividingRunV1.BufferedChainFamily
open FamilyStickyScaleChainCoherentIntervalProducerV1
open FamilyStickyScaleChainCoherentExactHierarchyProducerV2
open FamilyStickyScaleChainCoherentExactHierarchyProducerV2.CoherentExactHierarchyFamily
open FamilyStickyScaleChainBufferedHierarchyProducerV1.MultiscaleTubeHierarchy
open FamilyStickyScaleChainCanonicalBufferedTestBodyChainV2.MultiscaleTubeHierarchy
open FamilyStickyScaleChainCanonicalCoherentBufferedFamilyV2
open FamilyStickyScaleChainHierarchyGlobalEnvelopeV2
open FamilyStickyScaleChainSelectedNumericalAllocationProducerV1
open FamilyStickyScaleChainDividingFiniteNodeProducerV1
open FamilyStickyScaleChainTerminalFiniteSearchV1
open FamilyStickyScaleChainHierarchyRecursiveStoppingDriverV2
open FamilyStickyScaleChainLocalSuccessorAssemblerV2
open FamilyStickyScaleChainCanonicalInsertionEnvelopeTransportV2
open FamilyStickyScaleChainCanonicalOneStepEnvelopeCancellationV2
open FamilyStickyScaleChainCanonicalTerminalUnitBodyProducerV2
open FamilyStickyScaleChainCanonicalTerminalUnitBodyProducerV2.MultiscaleTubeHierarchy
open FamilyStickyScaleChainNormalizedTerminalObstructionV2
open FamilyStickyScaleSequenceRefinesAtV2
open FamilyStickyScaleSequenceInsertionTransportV2.FiniteScaleSequence

noncomputable section

/-!
# Envelope invariants only on stopping-relevant intervals

The stopping conclusion consumes the hierarchy envelope only at the first
interval which is not `IsLarge`.  Requiring it on every interval is strictly
stronger and can be impossible at a top endpoint `theta = 1` for the
automatic terminal body.  This module records the exact conditional
invariant and proves that canonical insertion transports it.

Every untouched non-large interval is inherited automatically.  For the two
new children the local certificate asks for an envelope estimate only if that
child is itself non-large.  Thus an already-large child creates no spurious
normalized-terminal obligation; if both children are non-large, both honest
analytic inputs remain.
-/

universe u

variable {delta : NNReal} {gapEpsilon : Real}
  {N : Nat} {eta : Nat -> Real}
  {iota : Type u} [Fintype iota] [DecidableEq iota]
  {fine : UniformTubeFamily delta iota}

/-! ## Generic relevant-envelope state -/

/-- A recursive hierarchy state which controls exactly the intervals that
can be selected by the stopping argument. -/
structure RelevantEnvelopeStoppingState
    (delta : NNReal) (N : Nat) (gapEpsilon : Real)
    (eta : Nat -> Real) where
  depth : Nat
  depth_pos : 0 < depth
  chainDepth : Nat
  scales : FiniteScaleSequence delta depth
  buffered : BufferedChainFamily depth chainDepth
  stage : Nat
  stage_pos : 1 <= stage
  stage_le : stage <= N
  relevantEnvelope_upper : forall m : Fin depth,
    Not (scales.IsLarge gapEpsilon m) ->
      hierarchyGlobalEnvelopeAt buffered m <=
        requiredGlobalPowerAt scales eta stage m

/-- The old all-interval state forgets to the stopping-relevant invariant. -/
def HierarchyStoppingState.toRelevant
    (X : HierarchyStoppingState delta N gapEpsilon eta) :
    RelevantEnvelopeStoppingState delta N gapEpsilon eta where
  depth := X.depth
  depth_pos := X.depth_pos
  chainDepth := X.chainDepth
  scales := X.scales
  buffered := X.buffered
  stage := X.stage
  stage_pos := X.stage_pos
  stage_le := X.stage_le
  relevantEnvelope_upper := fun m _ => X.globalEnvelope_upper m

namespace RelevantEnvelopeStoppingState

variable (X : RelevantEnvelopeStoppingState delta N gapEpsilon eta)

/-- The endpoint proof uses only the conditional invariant at the first
non-large interval. -/
theorem actualGlobalProductAt_firstNonLarge_le
    (not_all_large : Not (X.scales.AllStepsLarge gapEpsilon)) :
    actualGlobalProductAt X.buffered
        (firstNonLargeStep X.scales gapEpsilon not_all_large) <=
      requiredGlobalPowerAt X.scales eta X.stage
        (firstNonLargeStep X.scales gapEpsilon not_all_large) := by
  exact (actualGlobalProductAt_le_hierarchyGlobalEnvelopeAt X.buffered _).trans
    (X.relevantEnvelope_upper _
      (firstNonLargeStep_not_large X.scales gapEpsilon not_all_large))

end RelevantEnvelopeStoppingState

/-! ## Bad split and literal insertion without an all-interval premise -/

/-- The same literal bad split as in the original driver, now based on the
weaker relevant-envelope state. -/
structure RelevantSelectedActualBadSplit
    (C : CoherentStickyMultiscaleCover fine)
    (X : RelevantEnvelopeStoppingState delta N gapEpsilon eta) where
  not_all_large : Not (X.scales.AllStepsLarge gapEpsilon)
  rho : NNReal
  rho_buffered : X.scales.IsBuffered gapEpsilon
    (firstNonLargeStep X.scales gapEpsilon not_all_large) rho
  strict :
    (C.toActualIntervalCovers X.scales).coarseValueAt
        (firstNonLargeStep X.scales gapEpsilon not_all_large) rho <
      splitThreshold X.scales eta X.stage
        (firstNonLargeStep X.scales gapEpsilon not_all_large) rho

namespace RelevantSelectedActualBadSplit

variable (C : CoherentStickyMultiscaleCover fine)
  (X : RelevantEnvelopeStoppingState delta N gapEpsilon eta)
  (bad : RelevantSelectedActualBadSplit C X)

def selectedStep : Fin X.depth :=
  firstNonLargeStep X.scales gapEpsilon bad.not_all_large

theorem selectedStep_not_large :
    Not (X.scales.IsLarge gapEpsilon bad.selectedStep) := by
  exact firstNonLargeStep_not_large X.scales gapEpsilon bad.not_all_large

def refinedScales (gap_nonneg : 0 <= gapEpsilon)
    (delta_pos : 0 < delta) :
    FiniteScaleSequence delta (X.depth + 1) :=
  FiniteScaleSequence.insertBufferedRadius X.scales bad.selectedStep bad.rho
    delta_pos gap_nonneg bad.rho_buffered

theorem refinedScales_refinesAt (gap_nonneg : 0 <= gapEpsilon)
    (delta_pos : 0 < delta) :
    FiniteScaleSequence.ScaleSequenceRefinesAt X.scales bad.selectedStep
      bad.rho (bad.refinedScales C X gap_nonneg delta_pos) := by
  exact FiniteScaleSequence.insertBufferedRadius_refinesAt X.scales
    bad.selectedStep bad.rho delta_pos gap_nonneg bad.rho_buffered

end RelevantSelectedActualBadSplit

/-! ## Relevant local successor assembler -/

/-- A local hierarchy replacement with no requirements on large children.
The two child fields remain separate because either, or both, may be
non-large after insertion. -/
structure RelevantLocalEnvelopeRefinementCertificate
    (C : CoherentStickyMultiscaleCover fine)
    (gap_nonneg : 0 <= gapEpsilon) (delta_pos : 0 < delta)
    (X : RelevantEnvelopeStoppingState delta N gapEpsilon eta)
    (bad : RelevantSelectedActualBadSplit C X) where
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
    Not ((bad.refinedScales C X gap_nonneg delta_pos).IsLarge gapEpsilon
      (upperChildIndex bad.selectedStep)) ->
    hierarchyGlobalEnvelopeAt newBuffered
        (upperChildIndex bad.selectedStep) <=
      requiredGlobalPowerAt
        (bad.refinedScales C X gap_nonneg delta_pos) eta (X.stage + 1)
        (upperChildIndex bad.selectedStep)
  lowerChildEnvelope_upper :
    Not ((bad.refinedScales C X gap_nonneg delta_pos).IsLarge gapEpsilon
      (lowerChildIndex bad.selectedStep)) ->
    hierarchyGlobalEnvelopeAt newBuffered
        (lowerChildIndex bad.selectedStep) <=
      requiredGlobalPowerAt
        (bad.refinedScales C X gap_nonneg delta_pos) eta (X.stage + 1)
        (lowerChildIndex bad.selectedStep)

namespace RelevantLocalEnvelopeRefinementCertificate

variable (C : CoherentStickyMultiscaleCover fine)
  (gap_nonneg : 0 <= gapEpsilon) (delta_pos : 0 < delta)
  (X : RelevantEnvelopeStoppingState delta N gapEpsilon eta)
  (bad : RelevantSelectedActualBadSplit C X)
  (R : RelevantLocalEnvelopeRefinementCertificate C gap_nonneg delta_pos X bad)

/-- Insertion preserves the conditional invariant.  The proof converts
non-largeness back across untouched endpoints before invoking the old
conditional hypothesis. -/
theorem relevantEnvelope_upper (eta_monotone : Monotone eta) :
    forall k : Fin (X.depth + 1),
      Not ((bad.refinedScales C X gap_nonneg delta_pos).IsLarge
        gapEpsilon k) ->
      hierarchyGlobalEnvelopeAt R.newBuffered k <=
        requiredGlobalPowerAt
          (bad.refinedScales C X gap_nonneg delta_pos) eta
          (X.stage + 1) k := by
  let href := bad.refinedScales_refinesAt C X gap_nonneg delta_pos
  intro k not_large
  refine Fin.succAboveCases
    (α := fun k : Fin (X.depth + 1) =>
      Not ((bad.refinedScales C X gap_nonneg delta_pos).IsLarge
        gapEpsilon k) ->
      hierarchyGlobalEnvelopeAt R.newBuffered k <=
        requiredGlobalPowerAt
          (bad.refinedScales C X gap_nonneg delta_pos) eta
          (X.stage + 1) k)
    (lowerChildIndex bad.selectedStep) R.lowerChildEnvelope_upper ?_ k
    not_large
  intro j child_not_large
  rcases lt_trichotomy j bad.selectedStep with hjm | hjm | hmj
  · rw [lowerChild_succAbove_eq_before bad.selectedStep j hjm] at child_not_large ⊢
    have old_not_large : Not (X.scales.IsLarge gapEpsilon j) := by
      exact fun old_large => child_not_large
        ((isLarge_before_iff gapEpsilon href hjm).2 old_large)
    calc
      hierarchyGlobalEnvelopeAt R.newBuffered
          (beforeIntervalEmbedding X.depth j) <=
          hierarchyGlobalEnvelopeAt X.buffered j :=
        R.beforeEnvelope_le j hjm
      _ <= requiredGlobalPowerAt X.scales eta X.stage j :=
        X.relevantEnvelope_upper j old_not_large
      _ <= requiredGlobalPowerAt X.scales eta (X.stage + 1) j :=
        requiredGlobalPowerAt_le_succ X.scales eta_monotone j
      _ = requiredGlobalPowerAt
            (bad.refinedScales C X gap_nonneg delta_pos) eta
            (X.stage + 1) (beforeIntervalEmbedding X.depth j) :=
        (requiredGlobalPowerAt_before_eq eta (X.stage + 1) href hjm).symm
  · subst j
    rw [lowerChild_succAbove_eq_upper] at child_not_large ⊢
    exact R.upperChildEnvelope_upper child_not_large
  · rw [lowerChild_succAbove_eq_after bad.selectedStep j hmj] at child_not_large ⊢
    have old_not_large : Not (X.scales.IsLarge gapEpsilon j) := by
      exact fun old_large => child_not_large
        ((isLarge_after_iff gapEpsilon href hmj).2 old_large)
    calc
      hierarchyGlobalEnvelopeAt R.newBuffered
          (afterIntervalEmbedding X.depth j) <=
          hierarchyGlobalEnvelopeAt X.buffered j :=
        R.afterEnvelope_le j hmj
      _ <= requiredGlobalPowerAt X.scales eta X.stage j :=
        X.relevantEnvelope_upper j old_not_large
      _ <= requiredGlobalPowerAt X.scales eta (X.stage + 1) j :=
        requiredGlobalPowerAt_le_succ X.scales eta_monotone j
      _ = requiredGlobalPowerAt
            (bad.refinedScales C X gap_nonneg delta_pos) eta
            (X.stage + 1) (afterIntervalEmbedding X.depth j) :=
        (requiredGlobalPowerAt_after_eq eta (X.stage + 1) href hmj).symm

/-- Materialize a below-bound relevant successor. -/
def toState (eta_monotone : Monotone eta) (stage_lt : X.stage < N) :
    RelevantEnvelopeStoppingState delta N gapEpsilon eta where
  depth := X.depth + 1
  depth_pos := Nat.succ_pos X.depth
  chainDepth := R.newChainDepth
  scales := bad.refinedScales C X gap_nonneg delta_pos
  buffered := R.newBuffered
  stage := X.stage + 1
  stage_pos := by omega
  stage_le := by omega
  relevantEnvelope_upper :=
    R.relevantEnvelope_upper C gap_nonneg delta_pos X bad eta_monotone

end RelevantLocalEnvelopeRefinementCertificate

/-! ## Canonical relevant states and inserted children -/

/-- Canonical depth-one data with an envelope bound only on non-large
intervals.  Terminal normalization remains all-interval structural data, but
is produced independently by explicit terminal unit bodies. -/
structure RelevantCanonicalOneStepStoppingData
    (C : CoherentStickyMultiscaleCover fine)
    (N : Nat) (gapEpsilon : Real) (eta : Nat -> Real) where
  depth : Nat
  depth_pos : 0 < depth
  fine_refined_nonempty : fine.refinement.refined.Nonempty
  scales : FiniteScaleSequence delta depth
  stage : Nat
  stage_pos : 1 <= stage
  stage_le : stage <= N
  initialBody : Fin depth -> ConvexBody Space
  initialVolume_pos : forall m,
    0 < volume (initialBody m : Set Space)
  terminal_top_le_one : forall m,
    let F := CoherentExactHierarchyFamily.ofFiniteScaleSequence C scales
      fine_refined_nonempty
    concentration (effectiveActiveFamily (F.hierarchy m) 1)
        (canonicalTestBody (F.hierarchy m) (initialBody m) 1) <= 1
  canonicalRelevantEnvelope_upper : forall m,
    Not (scales.IsLarge gapEpsilon m) ->
    canonicalHierarchyEnvelopeAt
        (CoherentExactHierarchyFamily.ofFiniteScaleSequence C scales
          fine_refined_nonempty)
        (by omega) initialBody m <=
      requiredGlobalPowerAt scales eta stage m

namespace RelevantCanonicalOneStepStoppingData

variable (C : CoherentStickyMultiscaleCover fine)
  (Q : RelevantCanonicalOneStepStoppingData C N gapEpsilon eta)

def buffered (delta_pos : 0 < delta) : BufferedChainFamily Q.depth 1 :=
  canonicalOneStepBufferedChainFamily C Q.scales Q.fine_refined_nonempty
    delta_pos Q.initialBody Q.initialVolume_pos Q.terminal_top_le_one

def toState (delta_pos : 0 < delta) :
    RelevantEnvelopeStoppingState delta N gapEpsilon eta where
  depth := Q.depth
  depth_pos := Q.depth_pos
  chainDepth := 1
  scales := Q.scales
  buffered := Q.buffered C delta_pos
  stage := Q.stage
  stage_pos := Q.stage_pos
  stage_le := Q.stage_le
  relevantEnvelope_upper := by
    intro m not_large
    change hierarchyGlobalEnvelopeAt
        (canonicalBufferedChainFamily
          (CoherentExactHierarchyFamily.ofFiniteScaleSequence C Q.scales
            Q.fine_refined_nonempty)
          (by omega) delta_pos Q.initialBody Q.initialVolume_pos
          Q.terminal_top_le_one) m <=
      requiredGlobalPowerAt Q.scales eta Q.stage m
    rw [hierarchyGlobalEnvelopeAt_canonicalBufferedChainFamily_eq]
    exact Q.canonicalRelevantEnvelope_upper m not_large

end RelevantCanonicalOneStepStoppingData

/-- Existing canonical all-interval data forgets to the relevant canonical
state without changing any mathematical object. -/
def CanonicalOneStepStoppingData.toRelevantCanonical
    (C : CoherentStickyMultiscaleCover fine)
    (Q : CanonicalOneStepStoppingData C N gapEpsilon eta) :
    RelevantCanonicalOneStepStoppingData C N gapEpsilon eta where
  depth := Q.depth
  depth_pos := Q.depth_pos
  fine_refined_nonempty := Q.fine_refined_nonempty
  scales := Q.scales
  stage := Q.stage
  stage_pos := Q.stage_pos
  stage_le := Q.stage_le
  initialBody := Q.initialBody
  initialVolume_pos := Q.initialVolume_pos
  terminal_top_le_one := Q.terminal_top_le_one
  canonicalRelevantEnvelope_upper := fun m _ => Q.canonicalEnvelope_upper m

variable
    (C : CoherentStickyMultiscaleCover fine)
    (gap_nonneg : 0 <= gapEpsilon) (delta_pos : 0 < delta)
    (Q : RelevantCanonicalOneStepStoppingData C N gapEpsilon eta)
    (bad : RelevantSelectedActualBadSplit C (Q.toState C delta_pos))
/-- The selected step with its canonical depth exposed definitionally. -/
def relevantSelectedStep : Fin Q.depth := bad.selectedStep


def relevantInsertedScales : FiniteScaleSequence delta (Q.depth + 1) :=
  bad.refinedScales C (Q.toState C delta_pos) gap_nonneg delta_pos

def relevantInsertedExactFamily :
    CoherentExactHierarchyFamily C (Q.depth + 1) 1 :=
  CoherentExactHierarchyFamily.ofFiniteScaleSequence C
    (relevantInsertedScales C gap_nonneg delta_pos Q bad)
    Q.fine_refined_nonempty

def relevantInsertedBody (upperBody lowerBody : ConvexBody Space) :
    Fin (Q.depth + 1) -> ConvexBody Space :=
  insertedInitialBody (relevantSelectedStep C delta_pos Q bad) Q.initialBody upperBody lowerBody

/-- The only fresh canonical inputs.  Each child envelope field is guarded by
literal non-largeness of that same child. -/
structure RelevantCanonicalChildCertificate where
  upperBody : ConvexBody Space
  lowerBody : ConvexBody Space
  upperVolume_pos : 0 < volume (upperBody : Set Space)
  lowerVolume_pos : 0 < volume (lowerBody : Set Space)
  upperTerminal :
    concentration
        (effectiveActiveFamily
          ((relevantInsertedExactFamily C gap_nonneg delta_pos Q bad).hierarchy
            (upperChildIndex (relevantSelectedStep C delta_pos Q bad))) 1)
        (canonicalTestBody
          ((relevantInsertedExactFamily C gap_nonneg delta_pos Q bad).hierarchy
            (upperChildIndex (relevantSelectedStep C delta_pos Q bad))) upperBody 1) <= 1
  lowerTerminal :
    concentration
        (effectiveActiveFamily
          ((relevantInsertedExactFamily C gap_nonneg delta_pos Q bad).hierarchy
            (lowerChildIndex (relevantSelectedStep C delta_pos Q bad))) 1)
        (canonicalTestBody
          ((relevantInsertedExactFamily C gap_nonneg delta_pos Q bad).hierarchy
            (lowerChildIndex (relevantSelectedStep C delta_pos Q bad))) lowerBody 1) <= 1
  upperEnvelope_upper :
    Not ((relevantInsertedScales C gap_nonneg delta_pos Q bad).IsLarge
      gapEpsilon (upperChildIndex (relevantSelectedStep C delta_pos Q bad))) ->
    canonicalHierarchyEnvelopeAt
        (relevantInsertedExactFamily C gap_nonneg delta_pos Q bad) (by omega)
        (relevantInsertedBody C delta_pos Q bad upperBody lowerBody)
        (upperChildIndex (relevantSelectedStep C delta_pos Q bad)) <=
      requiredGlobalPowerAt
        (relevantInsertedScales C gap_nonneg delta_pos Q bad) eta
        (Q.stage + 1) (upperChildIndex (relevantSelectedStep C delta_pos Q bad))
  lowerEnvelope_upper :
    Not ((relevantInsertedScales C gap_nonneg delta_pos Q bad).IsLarge
      gapEpsilon (lowerChildIndex (relevantSelectedStep C delta_pos Q bad))) ->
    canonicalHierarchyEnvelopeAt
        (relevantInsertedExactFamily C gap_nonneg delta_pos Q bad) (by omega)
        (relevantInsertedBody C delta_pos Q bad upperBody lowerBody)
        (lowerChildIndex (relevantSelectedStep C delta_pos Q bad)) <=
      requiredGlobalPowerAt
        (relevantInsertedScales C gap_nonneg delta_pos Q bad) eta
        (Q.stage + 1) (lowerChildIndex (relevantSelectedStep C delta_pos Q bad))

namespace RelevantCanonicalChildCertificate

variable
    (R : RelevantCanonicalChildCertificate C gap_nonneg delta_pos Q bad)

theorem insertedVolume_pos : forall k,
    0 < volume
      (relevantInsertedBody C delta_pos Q bad R.upperBody R.lowerBody k :
        Set Space) := by
  exact insertedInitialBody_volume_pos (relevantSelectedStep C delta_pos Q bad) Q.initialBody
    R.upperBody R.lowerBody Q.initialVolume_pos R.upperVolume_pos
    R.lowerVolume_pos

theorem insertedTerminal_top_le_one : forall k,
    concentration
        (effectiveActiveFamily
          ((relevantInsertedExactFamily C gap_nonneg delta_pos Q bad).hierarchy
            k) 1)
        (canonicalTestBody
          ((relevantInsertedExactFamily C gap_nonneg delta_pos Q bad).hierarchy
            k)
          (relevantInsertedBody C delta_pos Q bad R.upperBody R.lowerBody k)
          1) <= 1 := by
  let href := bad.refinedScales_refinesAt C (Q.toState C delta_pos)
    gap_nonneg delta_pos
  exact canonicalInsertedTerminal_top_le_one C Q.scales (relevantSelectedStep C delta_pos Q bad)
    bad.rho (relevantInsertedScales C gap_nonneg delta_pos Q bad) href
    Q.fine_refined_nonempty Q.initialBody R.upperBody R.lowerBody
    Q.terminal_top_le_one R.upperTerminal R.lowerTerminal

/-- Canonical insertion closes every untouched relevant interval and leaves
exactly the conditionally non-large child estimates. -/
def toCanonical (eta_monotone : Monotone eta) (stage_lt : Q.stage < N) :
    RelevantCanonicalOneStepStoppingData C N gapEpsilon eta where
  depth := Q.depth + 1
  depth_pos := Nat.succ_pos Q.depth
  fine_refined_nonempty := Q.fine_refined_nonempty
  scales := relevantInsertedScales C gap_nonneg delta_pos Q bad
  stage := Q.stage + 1
  stage_pos := by omega
  stage_le := by omega
  initialBody := relevantInsertedBody C delta_pos Q bad R.upperBody R.lowerBody
  initialVolume_pos := R.insertedVolume_pos C gap_nonneg delta_pos Q bad
  terminal_top_le_one :=
    R.insertedTerminal_top_le_one C gap_nonneg delta_pos Q bad
  canonicalRelevantEnvelope_upper := by
    let href := bad.refinedScales_refinesAt C (Q.toState C delta_pos)
      gap_nonneg delta_pos
    intro k not_large
    refine Fin.succAboveCases
      (α := fun k : Fin (Q.depth + 1) =>
        Not ((relevantInsertedScales C gap_nonneg delta_pos Q bad).IsLarge
          gapEpsilon k) ->
        canonicalHierarchyEnvelopeAt
            (relevantInsertedExactFamily C gap_nonneg delta_pos Q bad)
            (by omega)
            (relevantInsertedBody C delta_pos Q bad R.upperBody R.lowerBody)
            k <=
          requiredGlobalPowerAt
            (relevantInsertedScales C gap_nonneg delta_pos Q bad) eta
            (Q.stage + 1) k)
      (lowerChildIndex (relevantSelectedStep C delta_pos Q bad)) R.lowerEnvelope_upper ?_ k not_large
    intro j child_not_large
    rcases lt_trichotomy j (relevantSelectedStep C delta_pos Q bad) with hjm | hjm | hmj
    · rw [lowerChild_succAbove_eq_before (relevantSelectedStep C delta_pos Q bad) j hjm] at child_not_large ⊢
      have old_not_large : Not (Q.scales.IsLarge gapEpsilon j) := by
        exact fun old_large => child_not_large
          ((isLarge_before_iff gapEpsilon href hjm).2 old_large)
      calc
        canonicalHierarchyEnvelopeAt
            (relevantInsertedExactFamily C gap_nonneg delta_pos Q bad)
            (by omega)
            (relevantInsertedBody C delta_pos Q bad R.upperBody R.lowerBody)
            (beforeIntervalEmbedding Q.depth j) =
          canonicalHierarchyEnvelopeAt
            (CoherentExactHierarchyFamily.ofFiniteScaleSequence C Q.scales
              Q.fine_refined_nonempty)
            (by omega) Q.initialBody j := by
              exact canonicalHierarchyEnvelopeAt_before_eq C Q.scales
                (relevantSelectedStep C delta_pos Q bad) j bad.rho
                (relevantInsertedScales C gap_nonneg delta_pos Q bad)
                href hjm Q.fine_refined_nonempty Q.initialBody R.upperBody
                R.lowerBody
        _ <= requiredGlobalPowerAt Q.scales eta Q.stage j :=
          Q.canonicalRelevantEnvelope_upper j old_not_large
        _ <= requiredGlobalPowerAt Q.scales eta (Q.stage + 1) j :=
          requiredGlobalPowerAt_le_succ Q.scales eta_monotone j
        _ = requiredGlobalPowerAt
            (relevantInsertedScales C gap_nonneg delta_pos Q bad) eta
            (Q.stage + 1) (beforeIntervalEmbedding Q.depth j) :=
          (requiredGlobalPowerAt_before_eq eta (Q.stage + 1) href hjm).symm
    · subst j
      rw [lowerChild_succAbove_eq_upper] at child_not_large ⊢
      exact R.upperEnvelope_upper child_not_large
    · rw [lowerChild_succAbove_eq_after (relevantSelectedStep C delta_pos Q bad) j hmj] at child_not_large ⊢
      have old_not_large : Not (Q.scales.IsLarge gapEpsilon j) := by
        exact fun old_large => child_not_large
          ((isLarge_after_iff gapEpsilon href hmj).2 old_large)
      calc
        canonicalHierarchyEnvelopeAt
            (relevantInsertedExactFamily C gap_nonneg delta_pos Q bad)
            (by omega)
            (relevantInsertedBody C delta_pos Q bad R.upperBody R.lowerBody)
            (afterIntervalEmbedding Q.depth j) =
          canonicalHierarchyEnvelopeAt
            (CoherentExactHierarchyFamily.ofFiniteScaleSequence C Q.scales
              Q.fine_refined_nonempty)
            (by omega) Q.initialBody j := by
              exact canonicalHierarchyEnvelopeAt_after_eq C Q.scales
                (relevantSelectedStep C delta_pos Q bad) j bad.rho
                (relevantInsertedScales C gap_nonneg delta_pos Q bad)
                href hmj Q.fine_refined_nonempty Q.initialBody R.upperBody
                R.lowerBody
        _ <= requiredGlobalPowerAt Q.scales eta Q.stage j :=
          Q.canonicalRelevantEnvelope_upper j old_not_large
        _ <= requiredGlobalPowerAt Q.scales eta (Q.stage + 1) j :=
          requiredGlobalPowerAt_le_succ Q.scales eta_monotone j
        _ = requiredGlobalPowerAt
            (relevantInsertedScales C gap_nonneg delta_pos Q bad) eta
            (Q.stage + 1) (afterIntervalEmbedding Q.depth j) :=
          (requiredGlobalPowerAt_after_eq eta (Q.stage + 1) href hmj).symm

end RelevantCanonicalChildCertificate

/-! ## Conditional normalized-terminal child adapter -/

/-- Automatic terminal-unit body on the inserted upper child. -/
def relevantInsertedUpperBody : ConvexBody Space :=
  canonicalTerminalUnitBody
    ((relevantInsertedExactFamily C gap_nonneg delta_pos Q bad).hierarchy
      (upperChildIndex (relevantSelectedStep C delta_pos Q bad)))

/-- Automatic terminal-unit body on the inserted lower child. -/
def relevantInsertedLowerBody : ConvexBody Space :=
  canonicalTerminalUnitBody
    ((relevantInsertedExactFamily C gap_nonneg delta_pos Q bad).hierarchy
      (lowerChildIndex (relevantSelectedStep C delta_pos Q bad)))

/-- The old bodies stay literal on untouched intervals; only the two children
receive automatic terminal-unit bodies. -/
def relevantAutomaticInsertedBody : Fin (Q.depth + 1) -> ConvexBody Space :=
  relevantInsertedBody C delta_pos Q bad
    (relevantInsertedUpperBody C gap_nonneg delta_pos Q bad)
    (relevantInsertedLowerBody C gap_nonneg delta_pos Q bad)

theorem relevantAutomaticInsertedBody_volume_pos : forall k,
    0 < volume
      (relevantAutomaticInsertedBody C gap_nonneg delta_pos Q bad k :
        Set Space) := by
  exact insertedInitialBody_volume_pos
    (relevantSelectedStep C delta_pos Q bad) Q.initialBody
    (relevantInsertedUpperBody C gap_nonneg delta_pos Q bad)
    (relevantInsertedLowerBody C gap_nonneg delta_pos Q bad)
    Q.initialVolume_pos
    (canonicalTerminalUnitBody_volume_pos _)
    (canonicalTerminalUnitBody_volume_pos _)

theorem relevantInsertedUpperBody_top_le_one :
    concentration
        (effectiveActiveFamily
          ((relevantInsertedExactFamily C gap_nonneg delta_pos Q bad).hierarchy
            (upperChildIndex (relevantSelectedStep C delta_pos Q bad))) 1)
        (canonicalTestBody
          ((relevantInsertedExactFamily C gap_nonneg delta_pos Q bad).hierarchy
            (upperChildIndex (relevantSelectedStep C delta_pos Q bad)))
          (relevantInsertedUpperBody C gap_nonneg delta_pos Q bad) 1) <= 1 := by
  exact canonicalTerminalUnitBody_top_le_one _

theorem relevantInsertedLowerBody_top_le_one :
    concentration
        (effectiveActiveFamily
          ((relevantInsertedExactFamily C gap_nonneg delta_pos Q bad).hierarchy
            (lowerChildIndex (relevantSelectedStep C delta_pos Q bad))) 1)
        (canonicalTestBody
          ((relevantInsertedExactFamily C gap_nonneg delta_pos Q bad).hierarchy
            (lowerChildIndex (relevantSelectedStep C delta_pos Q bad)))
          (relevantInsertedLowerBody C gap_nonneg delta_pos Q bad) 1) <= 1 := by
  exact canonicalTerminalUnitBody_top_le_one _

/-- Exactly the remaining child estimates, guarded by literal non-largeness.
When a child is large this structure contains no bound for that child. -/
structure RelevantConditionalNormalizedTerminalBounds where
  upper :
    Not ((relevantInsertedScales C gap_nonneg delta_pos Q bad).IsLarge
      gapEpsilon (upperChildIndex (relevantSelectedStep C delta_pos Q bad))) ->
    OneStepNormalizedTerminalExponentBound C
      (relevantInsertedExactFamily C gap_nonneg delta_pos Q bad)
      (relevantAutomaticInsertedBody C gap_nonneg delta_pos Q bad)
      (relevantInsertedScales C gap_nonneg delta_pos Q bad)
      eta (Q.stage + 1)
      (upperChildIndex (relevantSelectedStep C delta_pos Q bad))
  lower :
    Not ((relevantInsertedScales C gap_nonneg delta_pos Q bad).IsLarge
      gapEpsilon (lowerChildIndex (relevantSelectedStep C delta_pos Q bad))) ->
    OneStepNormalizedTerminalExponentBound C
      (relevantInsertedExactFamily C gap_nonneg delta_pos Q bad)
      (relevantAutomaticInsertedBody C gap_nonneg delta_pos Q bad)
      (relevantInsertedScales C gap_nonneg delta_pos Q bad)
      eta (Q.stage + 1)
      (lowerChildIndex (relevantSelectedStep C delta_pos Q bad))

/-- Exact one-step cancellation turns a conditional normalized-terminal atom
into the corresponding conditional canonical envelope estimate. -/
theorem relevantAutomaticInsertedEnvelope_le_requiredGlobalPowerAt
    (k : Fin (Q.depth + 1))
    (bound : OneStepNormalizedTerminalExponentBound C
      (relevantInsertedExactFamily C gap_nonneg delta_pos Q bad)
      (relevantAutomaticInsertedBody C gap_nonneg delta_pos Q bad)
      (relevantInsertedScales C gap_nonneg delta_pos Q bad)
      eta (Q.stage + 1) k) :
    canonicalHierarchyEnvelopeAt
        (relevantInsertedExactFamily C gap_nonneg delta_pos Q bad) (by omega)
        (relevantAutomaticInsertedBody C gap_nonneg delta_pos Q bad) k <=
      requiredGlobalPowerAt
        (relevantInsertedScales C gap_nonneg delta_pos Q bad) eta
        (Q.stage + 1) k := by
  have theta_le_one :
      ((relevantInsertedScales C gap_nonneg delta_pos Q bad).theta k :
        ENNReal) <= 1 := by
    exact_mod_cast
      (relevantInsertedScales C gap_nonneg delta_pos Q bad).theta_le_one k
  calc
    canonicalHierarchyEnvelopeAt
          (relevantInsertedExactFamily C gap_nonneg delta_pos Q bad) (by omega)
          (relevantAutomaticInsertedBody C gap_nonneg delta_pos Q bad) k =
        canonicalOneStepNormalizedTerminalAt C
          (relevantInsertedExactFamily C gap_nonneg delta_pos Q bad)
          (relevantAutomaticInsertedBody C gap_nonneg delta_pos Q bad) k :=
      canonicalHierarchyEnvelopeAt_one_eq_normalizedTerminal C
        (relevantInsertedExactFamily C gap_nonneg delta_pos Q bad) delta_pos
        (relevantAutomaticInsertedBody C gap_nonneg delta_pos Q bad)
        (relevantAutomaticInsertedBody_volume_pos C gap_nonneg delta_pos Q bad)
        k
    _ <= ((relevantInsertedScales C gap_nonneg delta_pos Q bad).theta k :
          ENNReal) ^ bound.exponent := bound.normalizedTerminal_upper
    _ <= ((relevantInsertedScales C gap_nonneg delta_pos Q bad).theta k :
          ENNReal) ^ (-eta ((Q.stage + 1) - 1)) :=
      ENNReal.rpow_le_rpow_of_exponent_ge theta_le_one
        bound.exponent_balance
    _ = requiredGlobalPowerAt
          (relevantInsertedScales C gap_nonneg delta_pos Q bad) eta
          (Q.stage + 1) k := rfl

/-- Build the honest two-child local certificate.  The normalized atom is
queried only after receiving a proof that the corresponding child is
non-large. -/
def relevantCanonicalChildCertificate_of_conditionalNormalizedBounds
    (bounds : RelevantConditionalNormalizedTerminalBounds C gap_nonneg
      delta_pos Q bad) :
    RelevantCanonicalChildCertificate C gap_nonneg delta_pos Q bad where
  upperBody := relevantInsertedUpperBody C gap_nonneg delta_pos Q bad
  lowerBody := relevantInsertedLowerBody C gap_nonneg delta_pos Q bad
  upperVolume_pos := canonicalTerminalUnitBody_volume_pos _
  lowerVolume_pos := canonicalTerminalUnitBody_volume_pos _
  upperTerminal :=
    relevantInsertedUpperBody_top_le_one C gap_nonneg delta_pos Q bad
  lowerTerminal :=
    relevantInsertedLowerBody_top_le_one C gap_nonneg delta_pos Q bad
  upperEnvelope_upper := fun not_large =>
    relevantAutomaticInsertedEnvelope_le_requiredGlobalPowerAt C gap_nonneg
      delta_pos Q bad (upperChildIndex
        (relevantSelectedStep C delta_pos Q bad)) (bounds.upper not_large)
  lowerEnvelope_upper := fun not_large =>
    relevantAutomaticInsertedEnvelope_le_requiredGlobalPowerAt C gap_nonneg
      delta_pos Q bad (lowerChildIndex
        (relevantSelectedStep C delta_pos Q bad)) (bounds.lower not_large)

/-! ## Formal obstruction to the discarded all-interval requirement -/

/-- At `theta = 1`, the required power is exactly one, independently of the
profile.  Thus any canonical envelope strictly above one cannot satisfy the
all-interval invariant. -/
theorem not_envelope_le_requiredGlobalPowerAt_of_theta_eq_one
    {depth stage : Nat} (S : FiniteScaleSequence delta depth)
    (profile : Nat -> Real) (m : Fin depth)
    (theta_eq_one : S.theta m = 1) (envelope : ENNReal)
    (one_lt_envelope : 1 < envelope) :
    Not (envelope <= requiredGlobalPowerAt S profile stage m) := by
  intro envelope_le
  have required_eq_one : requiredGlobalPowerAt S profile stage m = 1 := by
    unfold requiredGlobalPowerAt
    rw [theta_eq_one]
    simp
  exact (not_le_of_gt one_lt_envelope) (envelope_le.trans_eq required_eq_one)

/-- For the automatic terminal body this obstruction follows from an actual
active-cardinality product greater than one.  It explains why the upper
child at the top scale must be exempt when it is already large. -/
theorem automaticEnvelope_not_le_requiredPower_of_theta_eq_one
    {outerDepth stage : Nat}
    (C : CoherentStickyMultiscaleCover fine)
    (F : CoherentExactHierarchyFamily C outerDepth 1)
    (delta_pos : 0 < delta)
    (S : FiniteScaleSequence delta outerDepth)
    (profile : Nat -> Real) (m : Fin outerDepth)
    (theta_eq_one : S.theta m = 1)
    (card_product_gt_one :
      1 < (((F.chain m).intervalCover C 0 (by omega)).activeFine.card :
          ENNReal) *
        (canonicalTerminalActiveCardAt C F m : ENNReal)) :
    Not (canonicalHierarchyEnvelopeAt F (by omega)
      (automaticTerminalInitialBody C F) m <=
        requiredGlobalPowerAt S profile stage m) := by
  have card_le_envelope :
      (((F.chain m).intervalCover C 0 (by omega)).activeFine.card :
          ENNReal) *
          (canonicalTerminalActiveCardAt C F m : ENNReal) <=
        canonicalHierarchyEnvelopeAt F (by omega)
          (automaticTerminalInitialBody C F) m := by
    rw [canonicalHierarchyEnvelopeAt_one_eq_normalizedTerminal C F delta_pos
      (automaticTerminalInitialBody C F)
      (fun k => automaticTerminalInitialBody_volume_pos C F k) m]
    exact activeCardProduct_le_automatic_normalizedTerminal C F delta_pos m
  exact not_envelope_le_requiredGlobalPowerAt_of_theta_eq_one S profile m
    theta_eq_one _ (card_product_gt_one.trans_le card_le_envelope)

#print axioms RelevantEnvelopeStoppingState.actualGlobalProductAt_firstNonLarge_le
#print axioms RelevantSelectedActualBadSplit.refinedScales_refinesAt
#print axioms RelevantLocalEnvelopeRefinementCertificate.relevantEnvelope_upper
#print axioms RelevantLocalEnvelopeRefinementCertificate.toState
#print axioms RelevantCanonicalOneStepStoppingData.toState
#print axioms RelevantCanonicalChildCertificate.insertedTerminal_top_le_one
#print axioms RelevantCanonicalChildCertificate.toCanonical
#print axioms relevantAutomaticInsertedBody_volume_pos
#print axioms relevantAutomaticInsertedEnvelope_le_requiredGlobalPowerAt
#print axioms relevantCanonicalChildCertificate_of_conditionalNormalizedBounds
#print axioms not_envelope_le_requiredGlobalPowerAt_of_theta_eq_one
#print axioms automaticEnvelope_not_le_requiredPower_of_theta_eq_one

end
end FamilyStickyScaleChainRelevantIntervalEnvelopeInvariantV2
