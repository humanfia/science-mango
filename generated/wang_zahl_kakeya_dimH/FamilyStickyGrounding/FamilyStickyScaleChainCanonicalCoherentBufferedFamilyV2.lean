import FamilyStickyGrounding.FamilyStickyScaleChainCoherentExactHierarchyProducerV2
import FamilyStickyGrounding.FamilyStickyScaleChainCanonicalBufferedTestBodyChainV2
import FamilyStickyGrounding.FamilyStickyScaleChainHierarchyGlobalEnvelopeV2

set_option autoImplicit false
set_option warningAsError true
set_option linter.unusedSectionVars false
set_option maxHeartbeats 300000

open Set MeasureTheory
open scoped BigOperators ENNReal NNReal

namespace FamilyStickyScaleChainCanonicalCoherentBufferedFamilyV2

open LeanEval.Analysis.WangZahlKakeya
open Submission.Kakeya.ConvexGeometry
open Submission.Kakeya.ConvexFactoring
open Submission.Kakeya.Uniformity
open FamilyStickyAtEveryScaleCoreV1
open FamilyStickyDeltaMaxFiniteChainV2.StickyScaleCover
open FamilyStickyDividingScalesFiniteStoppingV1
open FamilyStickyScaleChainCoherentIntervalProducerV1
open FamilyStickyScaleChainCoherentExactHierarchyProducerV2
open FamilyStickyScaleChainCoherentExactHierarchyProducerV2.BoundedMonotoneRadiusChain
open FamilyStickyScaleChainCoherentExactHierarchyProducerV2.CoherentExactHierarchyFamily
open FamilyStickyScaleChainCanonicalBufferedTestBodyChainV2.MultiscaleTubeHierarchy
open FamilyStickyScaleChainBufferedHierarchyProducerV1.MultiscaleTubeHierarchy
open FamilyStickyScaleChainBufferedTelescopeV1.MultiscaleTubeHierarchy
open FamilyStickyScaleChainActualDividingRunV1
open FamilyStickyScaleChainActualDividingRunV1.BufferedChainFamily
open FamilyStickyScaleChainSelectedNumericalAllocationProducerV1
open FamilyStickyScaleChainHierarchyGlobalEnvelopeV2

noncomputable section

/-!
# Canonical coherent buffered-chain families

The coherent exact hierarchy producer supplies every radius, family,
cardinality, parent map, and adjacent exact partition.  The canonical
test-body producer supplies every remaining `BufferedTestBodyChain` field
from one positive-volume initial body.  This module composes those two
constructions pointwise over the finite outer intervals.

The only terminal analytic input retained here is the literal
`top_le_one`.  Positive `delta` supplies every effective-radius positivity
condition because the coherent radius chain is bounded below by `delta` and
has zero accumulated buffer.

The final section unfolds the hierarchy envelope.  It shows explicitly that
the bridge branching factor is the cardinality of the actual active fine set,
while the exact body/tube quotient and endpoint normalization remain.  No
dimension-only bound for those measure terms is asserted.
-/

variable {delta : NNReal} {iota : Type*}
  [Fintype iota] [DecidableEq iota]
  {fine : UniformTubeFamily delta iota}
  {C : CoherentStickyMultiscaleCover fine}
  {outerDepth chainDepth : Nat}

/-! ## General coherent family to canonical buffered family -/

/-- Every effective hierarchy radius is positive when the base tube radius
`delta` is positive.  The proof uses the literal zero-buffer coherent
hierarchy and its supplied lower radius bound. -/
theorem coherentHierarchy_effectiveRadius_pos
    (F : CoherentExactHierarchyFamily C outerDepth chainDepth)
    (delta_pos : 0 < delta) (m : Fin outerDepth) (l : Nat) :
    0 < (F.hierarchy m).effectiveRadius l := by
  change 0 < ((F.chain m).toHierarchy C F.fine_refined_nonempty).effectiveRadius l
  rw [BoundedMonotoneRadiusChain.toHierarchy_effectiveRadius]
  exact delta_pos.trans_le ((F.chain m).delta_le_nominalRadius l)

/-- Pointwise composition of the coherent exact hierarchies with the
canonical finite-minimum tube normalization and recursive test bodies. -/
def canonicalBufferedChainFamily
    (F : CoherentExactHierarchyFamily C outerDepth chainDepth)
    (chainDepth_pos : 0 < chainDepth) (delta_pos : 0 < delta)
    (initialBody : Fin outerDepth -> ConvexBody Space)
    (initialVolume_pos : forall m,
      0 < volume (initialBody m : Set Space))
    (terminal_top_le_one : forall m,
      concentration (effectiveActiveFamily (F.hierarchy m) chainDepth)
          (canonicalTestBody (F.hierarchy m) (initialBody m) chainDepth) <=
        1) :
    BufferedChainFamily outerDepth chainDepth :=
  F.toBufferedChainFamily fun m =>
    canonicalBufferedTestBodyChain (F.hierarchy m) chainDepth_pos
      (fun l _hl => coherentHierarchy_effectiveRadius_pos F delta_pos m l)
      (initialBody m) (initialVolume_pos m) (terminal_top_le_one m)

@[simp] theorem canonicalBufferedChainFamily_nominalRadius
    (F : CoherentExactHierarchyFamily C outerDepth chainDepth)
    (chainDepth_pos : 0 < chainDepth) (delta_pos : 0 < delta)
    (initialBody : Fin outerDepth -> ConvexBody Space)
    (initialVolume_pos : forall m,
      0 < volume (initialBody m : Set Space))
    (terminal_top_le_one : forall m,
      concentration (effectiveActiveFamily (F.hierarchy m) chainDepth)
          (canonicalTestBody (F.hierarchy m) (initialBody m) chainDepth) <=
        1)
    (m : Fin outerDepth) (l : Nat) :
    (canonicalBufferedChainFamily F chainDepth_pos delta_pos initialBody
      initialVolume_pos terminal_top_le_one).nominalRadius m l =
        F.nominalRadius m l := by
  rfl

@[simp] theorem canonicalBufferedChainFamily_hierarchy
    (F : CoherentExactHierarchyFamily C outerDepth chainDepth)
    (chainDepth_pos : 0 < chainDepth) (delta_pos : 0 < delta)
    (initialBody : Fin outerDepth -> ConvexBody Space)
    (initialVolume_pos : forall m,
      0 < volume (initialBody m : Set Space))
    (terminal_top_le_one : forall m,
      concentration (effectiveActiveFamily (F.hierarchy m) chainDepth)
          (canonicalTestBody (F.hierarchy m) (initialBody m) chainDepth) <=
        1)
    (m : Fin outerDepth) :
    (canonicalBufferedChainFamily F chainDepth_pos delta_pos initialBody
      initialVolume_pos terminal_top_le_one).hierarchy m = F.hierarchy m := by
  rfl

@[simp] theorem canonicalBufferedChainFamily_testBody
    (F : CoherentExactHierarchyFamily C outerDepth chainDepth)
    (chainDepth_pos : 0 < chainDepth) (delta_pos : 0 < delta)
    (initialBody : Fin outerDepth -> ConvexBody Space)
    (initialVolume_pos : forall m,
      0 < volume (initialBody m : Set Space))
    (terminal_top_le_one : forall m,
      concentration (effectiveActiveFamily (F.hierarchy m) chainDepth)
          (canonicalTestBody (F.hierarchy m) (initialBody m) chainDepth) <=
        1)
    (m : Fin outerDepth) (l : Nat) :
    ((canonicalBufferedChainFamily F chainDepth_pos delta_pos initialBody
      initialVolume_pos terminal_top_le_one).datum m).testBody l =
        canonicalTestBody (F.hierarchy m) (initialBody m) l := by
  rfl

@[simp] theorem canonicalBufferedChainFamily_tubeVolume
    (F : CoherentExactHierarchyFamily C outerDepth chainDepth)
    (chainDepth_pos : 0 < chainDepth) (delta_pos : 0 < delta)
    (initialBody : Fin outerDepth -> ConvexBody Space)
    (initialVolume_pos : forall m,
      0 < volume (initialBody m : Set Space))
    (terminal_top_le_one : forall m,
      concentration (effectiveActiveFamily (F.hierarchy m) chainDepth)
          (canonicalTestBody (F.hierarchy m) (initialBody m) chainDepth) <=
        1)
    (m : Fin outerDepth) (l : Nat) :
    ((canonicalBufferedChainFamily F chainDepth_pos delta_pos initialBody
      initialVolume_pos terminal_top_le_one).datum m).tubeVolume l =
        canonicalTubeVolume (F.hierarchy m) chainDepth_pos l := by
  rfl

@[simp] theorem canonicalBufferedChainFamily_dimensionalLoss
    (F : CoherentExactHierarchyFamily C outerDepth chainDepth)
    (chainDepth_pos : 0 < chainDepth) (delta_pos : 0 < delta)
    (initialBody : Fin outerDepth -> ConvexBody Space)
    (initialVolume_pos : forall m,
      0 < volume (initialBody m : Set Space))
    (terminal_top_le_one : forall m,
      concentration (effectiveActiveFamily (F.hierarchy m) chainDepth)
          (canonicalTestBody (F.hierarchy m) (initialBody m) chainDepth) <=
        1)
    (m : Fin outerDepth) (l : Nat) :
    ((canonicalBufferedChainFamily F chainDepth_pos delta_pos initialBody
      initialVolume_pos terminal_top_le_one).datum m).dimensionalLoss l =
        exactDimensionalLoss (F.hierarchy m) chainDepth_pos
          (initialBody m) l := by
  rfl

/-! ## The actual coherent branching factor -/

/-- The generic bridge chooses branching one and loss equal to the literal
active-fine cardinality, so its certified branching factor is exactly that
cardinality. -/
theorem coherentHierarchy_step_branchingFactor_eq_activeFine_card
    (F : CoherentExactHierarchyFamily C outerDepth chainDepth)
    (m : Fin outerDepth) (l : Nat) (hl : l < chainDepth) :
    ((F.hierarchy m).step l hl).combinatorics.branchingFactor =
      ((F.chain m).intervalCover C l hl).activeFine.card := by
  exact (F.chain m).toHierarchy_step_branchingFactor
    C F.fine_refined_nonempty l hl

/-- Totalized literal active-fine cardinality at a coherent hierarchy step. -/
def coherentBranchingCardAt
    (F : CoherentExactHierarchyFamily C outerDepth chainDepth)
    (m : Fin outerDepth) (l : Nat) : ENNReal :=
  if hl : l < chainDepth then
    (((F.chain m).intervalCover C l hl).activeFine.card : ENNReal)
  else 1

theorem coherentHierarchy_branchingFactorAt_eq
    (F : CoherentExactHierarchyFamily C outerDepth chainDepth)
    (m : Fin outerDepth) (l : Nat) :
    (if hl : l < chainDepth then
        (((F.hierarchy m).step l hl).combinatorics.branchingFactor : ENNReal)
      else 1) = coherentBranchingCardAt F m l := by
  unfold coherentBranchingCardAt
  split_ifs with hl
  · exact_mod_cast
      coherentHierarchy_step_branchingFactor_eq_activeFine_card F m l hl
  · rfl

/-! ## Canonical one-step family on any finite scale sequence -/

/-- One canonical coherent buffered hierarchy on every current adjacent
interval `tau_m -> theta_m`. -/
def canonicalOneStepBufferedChainFamily
    (C : CoherentStickyMultiscaleCover fine)
    (S : FiniteScaleSequence delta outerDepth)
    (fine_refined_nonempty : fine.refinement.refined.Nonempty)
    (delta_pos : 0 < delta)
    (initialBody : Fin outerDepth -> ConvexBody Space)
    (initialVolume_pos : forall m,
      0 < volume (initialBody m : Set Space))
    (terminal_top_le_one : forall m,
      let F := CoherentExactHierarchyFamily.ofFiniteScaleSequence
        C S fine_refined_nonempty
      concentration (effectiveActiveFamily (F.hierarchy m) 1)
          (canonicalTestBody (F.hierarchy m) (initialBody m) 1) <= 1) :
    BufferedChainFamily outerDepth 1 :=
  canonicalBufferedChainFamily
    (CoherentExactHierarchyFamily.ofFiniteScaleSequence
      C S fine_refined_nonempty)
    (by omega) delta_pos initialBody initialVolume_pos terminal_top_le_one

@[simp] theorem canonicalOneStepBufferedChainFamily_nominalRadius_zero
    (C : CoherentStickyMultiscaleCover fine)
    (S : FiniteScaleSequence delta outerDepth)
    (fine_refined_nonempty : fine.refinement.refined.Nonempty)
    (delta_pos : 0 < delta)
    (initialBody : Fin outerDepth -> ConvexBody Space)
    (initialVolume_pos : forall m,
      0 < volume (initialBody m : Set Space))
    (terminal_top_le_one : forall m,
      let F := CoherentExactHierarchyFamily.ofFiniteScaleSequence
        C S fine_refined_nonempty
      concentration (effectiveActiveFamily (F.hierarchy m) 1)
          (canonicalTestBody (F.hierarchy m) (initialBody m) 1) <= 1)
    (m : Fin outerDepth) :
    (canonicalOneStepBufferedChainFamily C S fine_refined_nonempty delta_pos
      initialBody initialVolume_pos terminal_top_le_one).nominalRadius m 0 =
        S.tau m := by
  rfl

@[simp] theorem canonicalOneStepBufferedChainFamily_nominalRadius_one
    (C : CoherentStickyMultiscaleCover fine)
    (S : FiniteScaleSequence delta outerDepth)
    (fine_refined_nonempty : fine.refinement.refined.Nonempty)
    (delta_pos : 0 < delta)
    (initialBody : Fin outerDepth -> ConvexBody Space)
    (initialVolume_pos : forall m,
      0 < volume (initialBody m : Set Space))
    (terminal_top_le_one : forall m,
      let F := CoherentExactHierarchyFamily.ofFiniteScaleSequence
        C S fine_refined_nonempty
      concentration (effectiveActiveFamily (F.hierarchy m) 1)
          (canonicalTestBody (F.hierarchy m) (initialBody m) 1) <= 1)
    (m : Fin outerDepth) :
    (canonicalOneStepBufferedChainFamily C S fine_refined_nonempty delta_pos
      initialBody initialVolume_pos terminal_top_le_one).nominalRadius m 1 =
        S.theta m := by
  rfl

@[simp] theorem canonicalOneStepBufferedChainFamily_effectiveRadius_zero
    (C : CoherentStickyMultiscaleCover fine)
    (S : FiniteScaleSequence delta outerDepth)
    (fine_refined_nonempty : fine.refinement.refined.Nonempty)
    (delta_pos : 0 < delta)
    (initialBody : Fin outerDepth -> ConvexBody Space)
    (initialVolume_pos : forall m,
      0 < volume (initialBody m : Set Space))
    (terminal_top_le_one : forall m,
      let F := CoherentExactHierarchyFamily.ofFiniteScaleSequence
        C S fine_refined_nonempty
      concentration (effectiveActiveFamily (F.hierarchy m) 1)
          (canonicalTestBody (F.hierarchy m) (initialBody m) 1) <= 1)
    (m : Fin outerDepth) :
    ((canonicalOneStepBufferedChainFamily C S fine_refined_nonempty delta_pos
      initialBody initialVolume_pos terminal_top_le_one).hierarchy m).effectiveRadius 0 =
        S.tau m := by
  exact CoherentExactHierarchyFamily.ofFiniteScaleSequence_effectiveRadius_zero
    C S fine_refined_nonempty m

@[simp] theorem canonicalOneStepBufferedChainFamily_effectiveRadius_one
    (C : CoherentStickyMultiscaleCover fine)
    (S : FiniteScaleSequence delta outerDepth)
    (fine_refined_nonempty : fine.refinement.refined.Nonempty)
    (delta_pos : 0 < delta)
    (initialBody : Fin outerDepth -> ConvexBody Space)
    (initialVolume_pos : forall m,
      0 < volume (initialBody m : Set Space))
    (terminal_top_le_one : forall m,
      let F := CoherentExactHierarchyFamily.ofFiniteScaleSequence
        C S fine_refined_nonempty
      concentration (effectiveActiveFamily (F.hierarchy m) 1)
          (canonicalTestBody (F.hierarchy m) (initialBody m) 1) <= 1)
    (m : Fin outerDepth) :
    ((canonicalOneStepBufferedChainFamily C S fine_refined_nonempty delta_pos
      initialBody initialVolume_pos terminal_top_le_one).hierarchy m).effectiveRadius 1 =
        S.theta m := by
  exact CoherentExactHierarchyFamily.ofFiniteScaleSequence_effectiveRadius_one
    C S fine_refined_nonempty m

/-! ## Fully unfolded hierarchy envelope and the remaining quantitative seam -/

/-- The canonical hierarchy envelope written only in terms of the exact
body/tube losses, literal active-fine cardinalities, and endpoint ratios. -/
def canonicalHierarchyEnvelopeAt
    (F : CoherentExactHierarchyFamily C outerDepth chainDepth)
    (chainDepth_pos : 0 < chainDepth)
    (initialBody : Fin outerDepth -> ConvexBody Space)
    (m : Fin outerDepth) : ENNReal :=
  (∏ l ∈ Finset.range chainDepth,
    exactDimensionalLoss (F.hierarchy m) chainDepth_pos
        (initialBody m) l * coherentBranchingCardAt F m l) *
    ((volume
          (canonicalTestBody (F.hierarchy m) (initialBody m) chainDepth :
            Set Space) /
        volume (initialBody m : Set Space)) *
      (canonicalTubeVolume (F.hierarchy m) chainDepth_pos 0 /
        canonicalTubeVolume (F.hierarchy m) chainDepth_pos chainDepth))

/-- For the canonical producer, the generic hierarchy envelope is exactly
the preceding transparent formula. -/
theorem hierarchyGlobalEnvelopeAt_canonicalBufferedChainFamily_eq
    (F : CoherentExactHierarchyFamily C outerDepth chainDepth)
    (chainDepth_pos : 0 < chainDepth) (delta_pos : 0 < delta)
    (initialBody : Fin outerDepth -> ConvexBody Space)
    (initialVolume_pos : forall m,
      0 < volume (initialBody m : Set Space))
    (terminal_top_le_one : forall m,
      concentration (effectiveActiveFamily (F.hierarchy m) chainDepth)
          (canonicalTestBody (F.hierarchy m) (initialBody m) chainDepth) <=
        1)
    (m : Fin outerDepth) :
    hierarchyGlobalEnvelopeAt
        (canonicalBufferedChainFamily F chainDepth_pos delta_pos initialBody
          initialVolume_pos terminal_top_le_one) m =
      canonicalHierarchyEnvelopeAt F chainDepth_pos initialBody m := by
  unfold hierarchyGlobalEnvelopeAt canonicalHierarchyEnvelopeAt
  unfold actualGlobalEndpointRatioAt
  simp only [canonicalBufferedChainFamily_dimensionalLoss,
    canonicalBufferedChainFamily_testBody,
    canonicalBufferedChainFamily_tubeVolume,
    canonicalTestBody_zero]
  congr 1
  apply Finset.prod_congr rfl
  intro l hl
  have hlt : l < chainDepth := Finset.mem_range.mp hl
  congr 1
  simp only [coherentBranchingCardAt, dif_pos hlt]
  exact_mod_cast
    coherentHierarchy_step_branchingFactor_eq_activeFine_card F m l hlt

/-- Hence the literal actual product is bounded by the completely unfolded
canonical envelope.  Closing a target power bound now requires a genuine
estimate for the displayed exact losses and endpoint ratio. -/
theorem actualGlobalProductAt_le_canonicalHierarchyEnvelopeAt
    (F : CoherentExactHierarchyFamily C outerDepth chainDepth)
    (chainDepth_pos : 0 < chainDepth) (delta_pos : 0 < delta)
    (initialBody : Fin outerDepth -> ConvexBody Space)
    (initialVolume_pos : forall m,
      0 < volume (initialBody m : Set Space))
    (terminal_top_le_one : forall m,
      concentration (effectiveActiveFamily (F.hierarchy m) chainDepth)
          (canonicalTestBody (F.hierarchy m) (initialBody m) chainDepth) <=
        1)
    (m : Fin outerDepth) :
    actualGlobalProductAt
        (canonicalBufferedChainFamily F chainDepth_pos delta_pos initialBody
          initialVolume_pos terminal_top_le_one) m <=
      canonicalHierarchyEnvelopeAt F chainDepth_pos initialBody m := by
  rw [<- hierarchyGlobalEnvelopeAt_canonicalBufferedChainFamily_eq F
    chainDepth_pos delta_pos initialBody initialVolume_pos
    terminal_top_le_one m]
  exact actualGlobalProductAt_le_hierarchyGlobalEnvelopeAt _ m

#print axioms coherentHierarchy_effectiveRadius_pos
#print axioms canonicalBufferedChainFamily
#print axioms coherentHierarchy_step_branchingFactor_eq_activeFine_card
#print axioms canonicalOneStepBufferedChainFamily
#print axioms canonicalOneStepBufferedChainFamily_effectiveRadius_zero
#print axioms canonicalOneStepBufferedChainFamily_effectiveRadius_one
#print axioms hierarchyGlobalEnvelopeAt_canonicalBufferedChainFamily_eq
#print axioms actualGlobalProductAt_le_canonicalHierarchyEnvelopeAt

end
end FamilyStickyScaleChainCanonicalCoherentBufferedFamilyV2
