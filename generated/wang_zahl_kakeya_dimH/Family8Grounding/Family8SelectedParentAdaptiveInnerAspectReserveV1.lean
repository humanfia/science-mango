import Family8Grounding.Family8SelectedParentAdaptiveGlobalCapAspectLowerV1
import Family8Grounding.Family8Prop66AOuterInnerProductAlgebraV1
import Mathlib.Tactic

/-!
# The automatic aspect reserve inside the actual adaptive Eq. (46) factor

The quadratic lower bound for the same global natural cap is inserted into
the positive power in the Proposition 6.6(A) inner factor.  This removes the
packing-cap object from the remaining numerical seam without assuming an
inner-factor conclusion.
-/

open Set MeasureTheory
open scoped ENNReal NNReal BigOperators

namespace Family8SelectedParentAdaptiveInnerAspectReserveV1

open LeanEval.Analysis.WangZahlKakeya
open Submission.Kakeya.ConvexGeometry
open Submission.Kakeya.ConvexFactoring
open Submission.Kakeya.ConvexFactoring.FullConvexMaximalDensity
open Submission.Kakeya.ConvexFactoring.GreedyOccurrenceFactorization
open Submission.Kakeya.Uniformity
open Family8Prop66AOuterInnerProductAlgebraV1
open Family8SelectedParentAdaptiveGlobalCapAspectLowerV1
open Family8SelectedParentJohnPlankSideWidthBridgeV7
open Family8SelectedParentPlankCenteredAdaptiveThinCountGlobalEq46CountV2
open Family8StickySelectedParentGreedyBlockFrostmanV3
open FamilyStickyAtEveryScaleCoreV1

noncomputable section

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 5000000

/-- A quadratic aspect reserve in a natural cap gives the corresponding
literal lower bound for the Proposition 6.6(A) inner factor. -/
theorem aspectSquaredCap_reserve_le_proposition66AInnerFactor
    {d a b : NNReal} {M : Nat} {epsilon beta : Real}
    (hbetaTwo : beta <= 2)
    (hcap : ((b : ENNReal) / (a : ENNReal)) ^ (2 : Nat) <=
      (M : ENNReal)) :
    (d : ENNReal) ^ (-epsilon / 2) *
        ((a : ENNReal) / (b : ENNReal)) ^ (1 - beta) *
      ((d : ENNReal) / (a : ENNReal)) ^ (-2 * beta) *
        (((((d : ENNReal) / (a : ENNReal)) ^ (2 : Nat)) *
          (((b : ENNReal) / (a : ENNReal)) ^ (2 : Nat))) ^
            (1 - beta / 2)) <=
      proposition66AInnerFactor d a b M epsilon beta := by
  have hp : 0 <= 1 - beta / 2 := by linarith
  unfold proposition66AInnerFactor
  gcongr

variable {delta rho : NNReal} {index : Type}
  [Fintype index] [DecidableEq index]
  {fine : UniformTubeFamily delta index}

/-- Same-object specialization to an actual occupied selected-parent bucket
and the exact global cap consumed by Equation (46). -/
theorem selectedParent_aspectScaleReserve_le_adaptiveGlobalInnerFactor
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
        ((bucketShortA label : ENNReal) /
          (bucketShortB label : ENNReal)) ^ (1 - beta) *
      ((rho : ENNReal) / (bucketShortA label : ENNReal)) ^
          (-2 * beta) *
        (((((rho : ENNReal) /
            (bucketShortA label : ENNReal)) ^ (2 : Nat)) *
          (((bucketShortB label : ENNReal) /
            (bucketShortA label : ENNReal)) ^ (2 : Nat))) ^
              (1 - beta / 2)) <=
      proposition66AInnerFactor rho
        (bucketShortA label) (bucketShortB label)
        (centeredAdaptiveGlobalFullFiberNatCap S hrho P r hr C)
        epsilon beta := by
  exact aspectSquaredCap_reserve_le_proposition66AInnerFactor hbetaTwo
    (selectedParent_bucketAspect_sq_le_centeredAdaptiveGlobalFullFiberNatCap
      S hrho P k r hr label hoccupied C)

#print axioms aspectSquaredCap_reserve_le_proposition66AInnerFactor
#print axioms
  selectedParent_aspectScaleReserve_le_adaptiveGlobalInnerFactor

end
end Family8SelectedParentAdaptiveInnerAspectReserveV1
