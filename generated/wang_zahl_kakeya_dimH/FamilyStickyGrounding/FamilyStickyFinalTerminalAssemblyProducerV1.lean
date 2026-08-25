import FamilyStickyGrounding.FamilyStickyFinalMultiscaleAssemblyCertificateV1
import FamilyStickyGrounding.FamilyStickyHierarchyTerminalSameScaleCoverProducerV1

set_option autoImplicit false
set_option warningAsError true
set_option linter.unusedSectionVars false

open Set
open scoped NNReal

namespace FamilyStickyFinalTerminalAssemblyProducerV1

open LeanEval.Analysis.WangZahlKakeya
open Submission.Kakeya.ConvexGeometry
open Submission.Kakeya.ConvexFactoring
open FamilyStickyAtEveryScaleCoreV1
open FamilyStickyDividingScalesFiniteStoppingV1
open FamilyStickyScaleChainActualValuesV1
open FamilyStickyScaleChainCoherentIntervalProducerV1
open FamilyStickyScaleChainArbitraryRadiusBoundsV1
open FamilyStickyHierarchyRandomMotionAdapterV1
open FamilyStickyHierarchyJointRandomMotionCertificateV1
open FamilyStickyHierarchyTerminalCarrierDedupV1
open FamilyStickyHierarchyTerminalEssentialDistinctAdapterV1
open FamilyStickyHierarchyTerminalWZ2CoefficientBridgeV1
open FamilyStickyHierarchyTerminalSameScaleCoverProducerV1
open FamilyStickyHierarchyPreMotionHullTestSupportV1
open FamilyStickyHierarchySuppliedPackingJointRandomMotionV1

noncomputable section
set_option maxHeartbeats 3000000

/-!
# Terminal outputs on the final Family7 assembly certificate

The final multiscale certificate already stores one literal supplied-plan
joint output.  The terminal same-scale producer shows that this output has a
canonical identity cover, that this cover is cardinality-minimal, and that
positive hierarchy depth gives a nonempty selected coefficient family.

Only the full coefficient cap needs additional source geometry: the
level-zero fixed chart and graph-`C` half-bucket.  This file packages exactly
that datum over the same joint output.  It introduces neither a terminal
cover callback nor a selected-family nonemptiness callback.
-/

variable {depth : Nat} {nominalRadius : Nat -> NNReal}
  {Index : Nat -> Type*}
  [forall l, Fintype (Index l)] [forall l, DecidableEq (Index l)]
  (H : MultiscaleTubeHierarchy depth nominalRadius Index)
  (G : HierarchyRandomMotionGeometry H)
  (P : HierarchyPackingPlan.Plan H)
  (C : CoherentStickyMultiscaleCover (H.effectiveFamily 0))
  (S : FiniteScaleSequence (H.effectiveRadius 0) depth)

/-- The final multiscale certificate together with the sole source-level
geometry needed by the terminal full coefficient cap. -/
structure Certificate
    (epsilon : Real)
    (massLoss bodyLoss katzTaoLoss frostmanError katzTaoError : ENNReal) where
  base : FamilyStickyFinalMultiscaleAssemblyCertificateV1.Certificate
    H G P C S epsilon massLoss bodyLoss katzTaoLoss
      frostmanError katzTaoError
  terminalSource : TerminalSourceChartBucketGeometry (H := H)

namespace Certificate

variable {H G P C S}
  {epsilon : Real}
  {massLoss bodyLoss katzTaoLoss frostmanError katzTaoError : ENNReal}
  (A : Certificate H G P C S epsilon
    massLoss bodyLoss katzTaoLoss frostmanError katzTaoError)

/-- The canonical terminal cover is built from the exact terminal family of
the joint output stored in `base`. -/
noncomputable def terminalSameScaleCover :
    TerminalStrongSameScaleCover A.base.hierarchy.joint :=
  terminalStrongIdentitySameScaleCover A.base.hierarchy.joint

@[simp]
theorem terminalSameScaleCover_count_eq_representatives_card :
    A.terminalSameScaleCover.count =
      (terminalStrongRepresentatives A.base.hierarchy.joint).card := by
  exact terminalStrongIdentitySameScaleCover_count_eq_representatives_card
    A.base.hierarchy.joint

/-- No other same-radius cover of this WZ2 terminal family uses fewer
parents than the canonical cover. -/
theorem terminalSameScaleCover_count_le
    (Q : TerminalStrongSameScaleCover A.base.hierarchy.joint) :
    A.terminalSameScaleCover.count <= Q.count := by
  exact terminalStrongIdentitySameScaleCover_count_le
    A.base.hierarchy.joint Q

/-- Positive depth, already stored in the final assembly certificate,
produces a terminal strong representative. -/
theorem terminalStrongIndex_nonempty :
    Nonempty (TerminalStrongIndex A.base.hierarchy.joint) := by
  exact terminalStrongIndex_nonempty_of_depth_pos
    A.base.hierarchy.joint A.base.depth_pos

/-- The canonical terminal cover therefore has positive count. -/
theorem terminalSameScaleCover_count_pos :
    0 < A.terminalSameScaleCover.count := by
  exact terminalStrong_sameScaleCover_count_pos_of_depth_pos
    A.base.hierarchy.joint A.terminalSameScaleCover A.base.depth_pos

/-- The selected terminal coefficient family is nonempty without any
large-cardinality premise. -/
theorem terminalSelectedTubes_nonempty (scale : Real) :
    (FamilyStickyCinematicL32ActualTubeCoefficientSelectionV1.selectedTubes
      (FamilyStickyCinematicL32Lemma57EssentiallyDistinctTubeImageV1.activeTubeImage
        (terminalStrongTubeFamily A.base.hierarchy.joint) Finset.univ)
      scale).Nonempty := by
  exact terminalStrong_selectedTubes_nonempty_of_depth_pos
    A.base.hierarchy.joint A.base.depth_pos scale

/-- The packaged source chart/bucket datum supplies the entire direction
premise used by the terminal coefficient cap. -/
theorem terminalNearCoefficient_card_le_fullCap
    (center : Tube (H.effectiveRadius 0)) :
    (FamilyStickyCinematicL32ActualTubeCoefficientFiberV1.activeNearCoefficientIndices
      (terminalStrongTubeFamily A.base.hierarchy.joint) Finset.univ center
      ((H.effectiveRadius 0 : NNReal) : Real)).card <=
        FamilyStickyCinematicL32ActualHalfScaleCoefficientCoverV1.actualHalfScaleCoefficientCoverLoss *
          A.terminalSameScaleCover.count := by
  exact A.terminalSource.terminalStrong_activeNearCoefficientIndices_card_le_fullCap
    A.base.hierarchy.joint A.terminalSameScaleCover
      A.base.initialRadius_pos center

/-- The obsolete three-full-caps large-card route is inconsistent for the
very same canonical cover. -/
theorem not_three_fullCaps_large :
    Not (0 < A.terminalSameScaleCover.count ∧
      3 *
          (FamilyStickyCinematicL32ActualHalfScaleCoefficientCoverV1.actualHalfScaleCoefficientCoverLoss *
            A.terminalSameScaleCover.count) <=
        Fintype.card (TerminalStrongIndex A.base.hierarchy.joint)) := by
  exact not_terminalStrong_three_fullCaps_large
    A.base.hierarchy.joint A.terminalSameScaleCover

end Certificate

#print axioms Certificate.terminalSameScaleCover
#print axioms Certificate.terminalSameScaleCover_count_eq_representatives_card
#print axioms Certificate.terminalSameScaleCover_count_le
#print axioms Certificate.terminalStrongIndex_nonempty
#print axioms Certificate.terminalSameScaleCover_count_pos
#print axioms Certificate.terminalSelectedTubes_nonempty
#print axioms Certificate.terminalNearCoefficient_card_le_fullCap
#print axioms Certificate.not_three_fullCaps_large

end
end FamilyStickyFinalTerminalAssemblyProducerV1
