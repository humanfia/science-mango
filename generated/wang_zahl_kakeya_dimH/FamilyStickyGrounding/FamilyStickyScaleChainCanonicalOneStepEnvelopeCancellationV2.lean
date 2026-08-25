import FamilyStickyGrounding.FamilyStickyScaleChainBadSplitChildEnvelopeReductionV2

set_option autoImplicit false
set_option warningAsError true
set_option linter.unusedSectionVars false
set_option maxHeartbeats 1000000

open Set MeasureTheory
open scoped BigOperators ENNReal NNReal

namespace FamilyStickyScaleChainCanonicalOneStepEnvelopeCancellationV2

open LeanEval.Analysis.WangZahlKakeya
open Submission.Kakeya.ConvexGeometry
open Submission.Kakeya.ConvexFactoring
open Submission.Kakeya.Uniformity
open FamilyStickyAtEveryScaleCoreV1
open FamilyStickyDeltaMaxFiniteChainV2.StickyScaleCover
open FamilyStickyDividingScalesFiniteStoppingV1
open FamilyStickyScaleChainActualDividingRunV1
open FamilyStickyScaleChainActualDividingRunV1.BufferedChainFamily
open FamilyStickyScaleChainBufferedHierarchyProducerV1.MultiscaleTubeHierarchy
open FamilyStickyScaleChainCoherentIntervalProducerV1
open FamilyStickyScaleChainCoherentExactHierarchyProducerV2
open FamilyStickyScaleChainCoherentExactHierarchyProducerV2.BoundedMonotoneRadiusChain
open FamilyStickyScaleChainCoherentExactHierarchyProducerV2.CoherentExactHierarchyFamily
open FamilyStickyScaleChainCanonicalBufferedTestBodyChainV2.MultiscaleTubeHierarchy
open FamilyStickyScaleChainCanonicalCoherentBufferedFamilyV2
open FamilyStickyScaleChainHierarchyGlobalEnvelopeV2
open FamilyStickyScaleChainSelectedNumericalAllocationProducerV1
open FamilyStickyScaleChainLocalSuccessorAssemblerV2
open FamilyStickyScaleChainHierarchyRecursiveStoppingDriverV2
open FamilyStickyScaleChainActualStoppingUpstreamClosureV1
open FamilyStickyScaleChainTerminalFiniteSearchV1
open FamilyStickyScaleSequenceInsertionTransportV2.FiniteScaleSequence
open FamilyStickyScaleChainBadSplitChildEnvelopeReductionV2

noncomputable section

/-!
# Exact cancellation in a canonical one-step hierarchy envelope

At depth one the exact dimensional loss is
`volume K₀ / tubeVolume₀`, while endpoint transport is
`(volume K₁ / volume K₀) * (tubeVolume₀ / tubeVolume₁)`.
The two intermediate volumes therefore cancel exactly.
-/

/-- The `ENNReal` cancellation used by the depth-one hierarchy proof. -/
theorem oneStep_intermediate_ratios_cancel
    (initialBodyVolume initialTubeVolume terminalBodyVolume terminalTubeVolume
      branching : ENNReal)
    (initialBodyVolume_ne_zero : initialBodyVolume ≠ 0)
    (initialBodyVolume_ne_top : initialBodyVolume ≠ ∞)
    (initialTubeVolume_ne_zero : initialTubeVolume ≠ 0)
    (initialTubeVolume_ne_top : initialTubeVolume ≠ ∞) :
    (initialBodyVolume / initialTubeVolume * branching) *
        ((terminalBodyVolume / initialBodyVolume) *
          (initialTubeVolume / terminalTubeVolume)) =
      branching * (terminalBodyVolume / terminalTubeVolume) := by
  calc
    (initialBodyVolume / initialTubeVolume * branching) *
          ((terminalBodyVolume / initialBodyVolume) *
            (initialTubeVolume / terminalTubeVolume)) =
        (initialBodyVolume / initialBodyVolume) *
          (initialTubeVolume / initialTubeVolume) *
          (branching * (terminalBodyVolume / terminalTubeVolume)) := by
      simp only [div_eq_mul_inv]
      ring
    _ = branching * (terminalBodyVolume / terminalTubeVolume) := by
      rw [ENNReal.div_self initialBodyVolume_ne_zero initialBodyVolume_ne_top,
        ENNReal.div_self initialTubeVolume_ne_zero initialTubeVolume_ne_top]
      simp

universe u

variable {delta : NNReal} {iota : Type u}
  [Fintype iota] [DecidableEq iota]
  {fine : UniformTubeFamily delta iota}
  (C : CoherentStickyMultiscaleCover fine)
  {outerDepth : Nat}

/-- The literal active-fine cardinality times normalized terminal volume. -/
def canonicalOneStepNormalizedTerminalAt
    (F : CoherentExactHierarchyFamily C outerDepth 1)
    (initialBody : Fin outerDepth -> ConvexBody Space)
    (m : Fin outerDepth) : ENNReal :=
  (((F.chain m).intervalCover C 0 (by omega)).activeFine.card : ENNReal) *
    (volume
        (canonicalTestBody (F.hierarchy m) (initialBody m) 1 : Set Space) /
      canonicalTubeVolume (F.hierarchy m) (by omega) 1)

/-- The transparent canonical depth-one envelope is exactly active-fine
cardinality times normalized terminal volume. -/
theorem canonicalHierarchyEnvelopeAt_one_eq_normalizedTerminal
    (F : CoherentExactHierarchyFamily C outerDepth 1)
    (delta_pos : 0 < delta)
    (initialBody : Fin outerDepth -> ConvexBody Space)
    (initialVolume_pos : forall m,
      0 < volume (initialBody m : Set Space))
    (m : Fin outerDepth) :
    canonicalHierarchyEnvelopeAt F (by omega) initialBody m =
      canonicalOneStepNormalizedTerminalAt C F initialBody m := by
  have effectiveRadius_pos : forall l, l <= 1 ->
      0 < (F.hierarchy m).effectiveRadius l := by
    intro l _hl
    exact coherentHierarchy_effectiveRadius_pos F delta_pos m l
  have initialBodyVolume_ne_zero :
      volume (initialBody m : Set Space) ≠ 0 :=
    (initialVolume_pos m).ne'
  have initialBodyVolume_ne_top :
      volume (initialBody m : Set Space) ≠ ∞ :=
    (initialBody m).isCompact.measure_lt_top.ne
  have initialTubeVolume_ne_zero :
      canonicalTubeVolume (F.hierarchy m) (by omega) 0 ≠ 0 :=
    (canonicalTubeVolume_pos (F.hierarchy m) (by omega)
      effectiveRadius_pos 0 (by omega)).ne'
  have initialTubeVolume_ne_top :
      canonicalTubeVolume (F.hierarchy m) (by omega) 0 ≠ ∞ :=
    canonicalTubeVolume_ne_top (F.hierarchy m) (by omega) 0 (by omega)
  unfold canonicalHierarchyEnvelopeAt canonicalOneStepNormalizedTerminalAt
  simp only [Finset.prod_range_succ, Finset.prod_range_zero, one_mul,
    exactDimensionalLoss, coherentBranchingCardAt, zero_lt_one, dif_pos,
    canonicalTestBody_zero]
  exact oneStep_intermediate_ratios_cancel
    (volume (initialBody m : Set Space))
    (canonicalTubeVolume (F.hierarchy m) (by omega) 0)
    (volume
      (canonicalTestBody (F.hierarchy m) (initialBody m) 1 : Set Space))
    (canonicalTubeVolume (F.hierarchy m) (by omega) 1)
    (((F.chain m).intervalCover C 0 (by omega)).activeFine.card : ENNReal)
    initialBodyVolume_ne_zero initialBodyVolume_ne_top
    initialTubeVolume_ne_zero initialTubeVolume_ne_top

/-- Direct consumer theorem for the actual canonical one-step buffered child. -/
theorem hierarchyGlobalEnvelopeAt_canonicalBufferedChainFamily_one_eq_normalizedTerminal
    (F : CoherentExactHierarchyFamily C outerDepth 1)
    (delta_pos : 0 < delta)
    (initialBody : Fin outerDepth -> ConvexBody Space)
    (initialVolume_pos : forall m,
      0 < volume (initialBody m : Set Space))
    (terminal_top_le_one : forall m,
      concentration (effectiveActiveFamily (F.hierarchy m) 1)
          (canonicalTestBody (F.hierarchy m) (initialBody m) 1) <= 1)
    (m : Fin outerDepth) :
    hierarchyGlobalEnvelopeAt
        (canonicalBufferedChainFamily F (by omega) delta_pos initialBody
          initialVolume_pos terminal_top_le_one) m =
      canonicalOneStepNormalizedTerminalAt C F initialBody m := by
  calc
    hierarchyGlobalEnvelopeAt
          (canonicalBufferedChainFamily F (by omega) delta_pos initialBody
            initialVolume_pos terminal_top_le_one) m =
        canonicalHierarchyEnvelopeAt F (by omega) initialBody m :=
      hierarchyGlobalEnvelopeAt_canonicalBufferedChainFamily_eq
        F (by omega) delta_pos initialBody initialVolume_pos
          terminal_top_le_one m
    _ = canonicalOneStepNormalizedTerminalAt C F initialBody m :=
      canonicalHierarchyEnvelopeAt_one_eq_normalizedTerminal
        C F delta_pos initialBody initialVolume_pos m

/-! ## A single normalized-terminal analytic atom -/

/-- One quantitative premise after exact cancellation.  Its analytic field
is imposed directly on active-fine cardinality times terminal body/tube
volume; `exponent_balance` is only the arithmetic comparison with the global
profile. -/
structure OneStepNormalizedTerminalExponentBound
    (F : CoherentExactHierarchyFamily C outerDepth 1)
    (initialBody : Fin outerDepth -> ConvexBody Space)
    (S : FiniteScaleSequence delta outerDepth)
    (profile : Nat -> Real) (stage : Nat) (m : Fin outerDepth) where
  exponent : Real
  normalizedTerminal_upper :
    canonicalOneStepNormalizedTerminalAt C F initialBody m <=
      (S.theta m : ENNReal) ^ exponent
  exponent_balance : -profile (stage - 1) <= exponent

/-- The single normalized-terminal atom implies the required global-power
bound for the actual canonical one-step buffered family. -/
theorem hierarchyGlobalEnvelopeAt_canonicalBufferedChainFamily_one_le_requiredGlobalPowerAt
    (F : CoherentExactHierarchyFamily C outerDepth 1)
    (delta_pos : 0 < delta)
    (initialBody : Fin outerDepth -> ConvexBody Space)
    (initialVolume_pos : forall m,
      0 < volume (initialBody m : Set Space))
    (terminal_top_le_one : forall m,
      concentration (effectiveActiveFamily (F.hierarchy m) 1)
          (canonicalTestBody (F.hierarchy m) (initialBody m) 1) <= 1)
    (S : FiniteScaleSequence delta outerDepth)
    (profile : Nat -> Real) (stage : Nat) (m : Fin outerDepth)
    (bound : OneStepNormalizedTerminalExponentBound C F initialBody
      S profile stage m) :
    hierarchyGlobalEnvelopeAt
        (canonicalBufferedChainFamily F (by omega) delta_pos initialBody
          initialVolume_pos terminal_top_le_one) m <=
      requiredGlobalPowerAt S profile stage m := by
  have theta_le_one : (S.theta m : ENNReal) <= 1 := by
    exact_mod_cast S.theta_le_one m
  calc
    hierarchyGlobalEnvelopeAt
          (canonicalBufferedChainFamily F (by omega) delta_pos initialBody
            initialVolume_pos terminal_top_le_one) m =
        canonicalOneStepNormalizedTerminalAt C F initialBody m :=
      hierarchyGlobalEnvelopeAt_canonicalBufferedChainFamily_one_eq_normalizedTerminal
        C F delta_pos initialBody initialVolume_pos terminal_top_le_one m
    _ <= (S.theta m : ENNReal) ^ bound.exponent :=
      bound.normalizedTerminal_upper
    _ <= (S.theta m : ENNReal) ^ (-profile (stage - 1)) :=
      ENNReal.rpow_le_rpow_of_exponent_ge theta_le_one bound.exponent_balance
    _ = requiredGlobalPowerAt S profile stage m := rfl

/-! ## Direct adapters for the literal bad-split children -/

variable {gapEpsilon : Real} {N : Nat} {eta : Nat -> Real}

/-- A single normalized-terminal bound supplies any child envelope of the
bad-aware canonical refined family. -/
theorem refinedCanonical_childEnvelope_le_requiredGlobalPowerAt_of_normalizedTerminal
    (gap_nonneg : 0 <= gapEpsilon) (delta_pos : 0 < delta)
    (X : HierarchyStoppingState delta N gapEpsilon eta)
    (bad : SelectedActualBadSplit C X)
    (hfine : fine.refinement.refined.Nonempty)
    (initialBody : Fin (X.depth + 1) -> ConvexBody Space)
    (initialVolume_pos : forall k,
      0 < volume (initialBody k : Set Space))
    (threshold_le_one :
      splitThreshold X.scales eta X.stage bad.selectedStep bad.rho <= 1)
    (top_other : forall k, k ≠ lowerChildIndex bad.selectedStep ->
      let F := refinedExactFamily C gap_nonneg delta_pos X bad hfine
      concentration (effectiveActiveFamily (F.hierarchy k) 1)
          (canonicalTestBody (F.hierarchy k) (initialBody k) 1) <= 1)
    (k : Fin (X.depth + 1))
    (bound : OneStepNormalizedTerminalExponentBound C
      (refinedExactFamily C gap_nonneg delta_pos X bad hfine) initialBody
      (bad.refinedScales C X gap_nonneg delta_pos) eta (X.stage + 1) k) :
    hierarchyGlobalEnvelopeAt
        (refinedCanonicalBufferedFamily_of_bad C gap_nonneg delta_pos X bad
          hfine initialBody initialVolume_pos threshold_le_one top_other) k <=
      requiredGlobalPowerAt
        (bad.refinedScales C X gap_nonneg delta_pos) eta (X.stage + 1) k := by
  unfold refinedCanonicalBufferedFamily_of_bad refinedCanonicalBufferedFamily
  exact
    hierarchyGlobalEnvelopeAt_canonicalBufferedChainFamily_one_le_requiredGlobalPowerAt
      C (refinedExactFamily C gap_nonneg delta_pos X bad hfine) delta_pos
      initialBody initialVolume_pos
      (refined_terminalTop_of_bad C gap_nonneg delta_pos X bad hfine
        initialBody threshold_le_one top_other)
      (bad.refinedScales C X gap_nonneg delta_pos) eta (X.stage + 1) k bound

/-- Bad-split local-certificate constructor using one normalized-terminal
atom for each new child, instead of separate dimensional-loss, branching,
and endpoint-ratio atoms. -/
def localEnvelopeRefinementCertificate_of_bad_normalizedTerminalBounds
    (gap_nonneg : 0 <= gapEpsilon) (delta_pos : 0 < delta)
    (X : HierarchyStoppingState delta N gapEpsilon eta)
    (bad : SelectedActualBadSplit C X)
    (hfine : fine.refinement.refined.Nonempty)
    (initialBody : Fin (X.depth + 1) -> ConvexBody Space)
    (initialVolume_pos : forall k,
      0 < volume (initialBody k : Set Space))
    (threshold_le_one :
      splitThreshold X.scales eta X.stage bad.selectedStep bad.rho <= 1)
    (top_other : forall k, k ≠ lowerChildIndex bad.selectedStep ->
      let F := refinedExactFamily C gap_nonneg delta_pos X bad hfine
      concentration (effectiveActiveFamily (F.hierarchy k) 1)
          (canonicalTestBody (F.hierarchy k) (initialBody k) 1) <= 1)
    (beforeEnvelope_le : forall j : Fin X.depth, j < bad.selectedStep ->
      hierarchyGlobalEnvelopeAt
          (refinedCanonicalBufferedFamily_of_bad C gap_nonneg delta_pos X bad
            hfine initialBody initialVolume_pos threshold_le_one top_other)
          (beforeIntervalEmbedding X.depth j) <=
        hierarchyGlobalEnvelopeAt X.buffered j)
    (afterEnvelope_le : forall j : Fin X.depth, bad.selectedStep < j ->
      hierarchyGlobalEnvelopeAt
          (refinedCanonicalBufferedFamily_of_bad C gap_nonneg delta_pos X bad
            hfine initialBody initialVolume_pos threshold_le_one top_other)
          (afterIntervalEmbedding X.depth j) <=
        hierarchyGlobalEnvelopeAt X.buffered j)
    (upperBound : OneStepNormalizedTerminalExponentBound C
      (refinedExactFamily C gap_nonneg delta_pos X bad hfine) initialBody
      (bad.refinedScales C X gap_nonneg delta_pos) eta (X.stage + 1)
      (upperChildIndex bad.selectedStep))
    (lowerBound : OneStepNormalizedTerminalExponentBound C
      (refinedExactFamily C gap_nonneg delta_pos X bad hfine) initialBody
      (bad.refinedScales C X gap_nonneg delta_pos) eta (X.stage + 1)
      (lowerChildIndex bad.selectedStep)) :
    LocalEnvelopeRefinementCertificate C gap_nonneg delta_pos X bad where
  newChainDepth := 1
  newBuffered := refinedCanonicalBufferedFamily_of_bad C gap_nonneg delta_pos
    X bad hfine initialBody initialVolume_pos threshold_le_one top_other
  beforeEnvelope_le := beforeEnvelope_le
  afterEnvelope_le := afterEnvelope_le
  upperChildEnvelope_upper :=
    refinedCanonical_childEnvelope_le_requiredGlobalPowerAt_of_normalizedTerminal
      C gap_nonneg delta_pos X bad hfine initialBody initialVolume_pos
      threshold_le_one top_other (upperChildIndex bad.selectedStep) upperBound
  lowerChildEnvelope_upper :=
    refinedCanonical_childEnvelope_le_requiredGlobalPowerAt_of_normalizedTerminal
      C gap_nonneg delta_pos X bad hfine initialBody initialVolume_pos
      threshold_le_one top_other (lowerChildIndex bad.selectedStep) lowerBound

#print axioms oneStep_intermediate_ratios_cancel
#print axioms canonicalHierarchyEnvelopeAt_one_eq_normalizedTerminal
#print axioms hierarchyGlobalEnvelopeAt_canonicalBufferedChainFamily_one_eq_normalizedTerminal
#print axioms hierarchyGlobalEnvelopeAt_canonicalBufferedChainFamily_one_le_requiredGlobalPowerAt
#print axioms refinedCanonical_childEnvelope_le_requiredGlobalPowerAt_of_normalizedTerminal
#print axioms localEnvelopeRefinementCertificate_of_bad_normalizedTerminalBounds

end
end FamilyStickyScaleChainCanonicalOneStepEnvelopeCancellationV2
