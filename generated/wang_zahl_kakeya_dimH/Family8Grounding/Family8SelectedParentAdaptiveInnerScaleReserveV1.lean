import Family8Grounding.Family8SelectedParentAdaptiveInnerAspectReserveV1
import Family8Grounding.Family8Prop66AInnerAspectReserveAlgebraV1
import Mathlib.Tactic

/-!
# Exact remaining scale reserve for the actual adaptive Eq. (46) factor

After inserting the automatically produced quadratic aspect reserve, the
only surviving bucket-dependent quantity is the explicit normalized scale
factor below.
-/

open Set MeasureTheory
open scoped ENNReal NNReal BigOperators

namespace Family8SelectedParentAdaptiveInnerScaleReserveV1

open LeanEval.Analysis.WangZahlKakeya
open Submission.Kakeya.ConvexGeometry
open Submission.Kakeya.ConvexFactoring
open Submission.Kakeya.ConvexFactoring.FullConvexMaximalDensity
open Submission.Kakeya.ConvexFactoring.GreedyOccurrenceFactorization
open Submission.Kakeya.Uniformity
open Family8Prop66AInnerAspectReserveAlgebraV1
open Family8Prop66AOuterInnerProductAlgebraV1
open Family8SelectedParentAdaptiveInnerAspectReserveV1
open Family8SelectedParentJohnPlankSideWidthBridgeV7
open Family8SelectedParentPlankCenteredAdaptiveThinCountGlobalEq46CountV2
open Family8StickySelectedParentGreedyBlockFrostmanV3
open FamilyStickyAtEveryScaleCoreV1

noncomputable section

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 5000000

variable {delta rho : NNReal} {index : Type}
  [Fintype index] [DecidableEq index]
  {fine : UniformTubeFamily delta index}

/-- Callback-free same-object lower bound.  This theorem is the exact output
of all presently available cap and aspect definitions; any further delta
power comparison must control this displayed normalized scale reserve. -/
theorem selectedParent_scaleReserve_le_adaptiveGlobalInnerFactor
    (S : StickyScaleCover fine rho) (hrho : 0 < rho)
    (P : GreedyDensityPartition S.activeCoarseFamily
      (hullCandidates (Finset.univ : Finset (ActiveParentIndex S)))
      (hullContainer S.activeCoarseFamily) Finset.univ)
    (k : Fin (blocks S.activeCoarseFamily P).length)
    (r : NNReal) (hr : 0 < r) (label : Fin 3 -> Int)
    (hoccupied : label ∈ selectedParentOccupiedShapeLabels
      S hrho P k r hr)
    (C : ENNReal) (epsilon beta : Real) (hbetaTwo : beta <= 2) :
    (rho : ENNReal) ^ (-epsilon / 2) *
        ((bucketShortB label : ENNReal) /
          (bucketShortA label : ENNReal)) *
      (((rho : ENNReal) / (bucketShortA label : ENNReal)) ^
        (2 - 3 * beta)) <=
      proposition66AInnerFactor rho
        (bucketShortA label) (bucketShortB label)
        (centeredAdaptiveGlobalFullFiberNatCap S hrho P r hr C)
        epsilon beta := by
  have ha : 0 < bucketShortA label := bucketShortA_pos label
  have hb : 0 < bucketShortB label :=
    ha.trans_le (bucketShortA_le_bucketShortB label)
  rw [← proposition66AInner_aspectReserve_eq
    hrho ha hb hbetaTwo]
  exact selectedParent_aspectScaleReserve_le_adaptiveGlobalInnerFactor
    S hrho P k r hr label hoccupied C epsilon beta hbetaTwo

#print axioms selectedParent_scaleReserve_le_adaptiveGlobalInnerFactor

end
end Family8SelectedParentAdaptiveInnerScaleReserveV1
