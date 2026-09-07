import Family8Grounding.Family8SelectedParentAdaptiveActualCapSourceAspectLowerV1
import Family8Grounding.Family8Prop66AInnerAspectReserveAlgebraV1
import Mathlib.Tactic

/-!
# The source Katz--Tao reserve inside the actual adaptive inner factor

The actual local cap retains `C * (b/a)^2`.  Raising that cap to the
Proposition 6.6(A) exponent retains exactly `C^(1-beta/2)` in addition to
the already audited aspect/scale reserve.  This records the strongest honest
callback-free lower bound furnished by the current cap definition.
-/

open Set MeasureTheory
open scoped ENNReal NNReal BigOperators

namespace Family8SelectedParentAdaptiveInnerSourceReserveV1

open LeanEval.Analysis.WangZahlKakeya
open Submission.Kakeya.ConvexGeometry
open Submission.Kakeya.ConvexFactoring
open Submission.Kakeya.ConvexFactoring.FullConvexMaximalDensity
open Submission.Kakeya.ConvexFactoring.GreedyOccurrenceFactorization
open Submission.Kakeya.Uniformity
open Family8Prop66AInnerAspectReserveAlgebraV1
open Family8Prop66AOuterInnerProductAlgebraV1
open Family8SelectedParentAdaptiveActualCapSourceAspectLowerV1
open Family8SelectedParentCertifiedPlankCordobaConnectorV3
open Family8SelectedParentJohnFrameNormalizationV9
open Family8SelectedParentJohnPlankSideWidthBridgeV5
open Family8SelectedParentJohnPlankSideWidthBridgeV7
open Family8SelectedParentPlankCenteredAdaptiveThinCountGlobalEq46CountV2
open Family8SelectedParentPlankCenteredAdaptiveThinCountGlobalMassPopularEndpointV3
open Family8SelectedParentPlankCenteredHalfPostAdaptiveScalePackingV1
open Family8StickySelectedParentGreedyBlockFrostmanV3
open FamilyStickyAtEveryScaleCoreV1
open FamilyStickyCinematicL32FiniteWeightedBucketV1

noncomputable section

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 5000000

/-- Generic algebraic insertion of a source constant and squared aspect into
the natural cap used by the Proposition 6.6(A) inner factor. -/
theorem sourceAspectCap_reserve_le_proposition66AInnerFactor
    {d a b : NNReal} {C : ENNReal} {M : Nat} {epsilon beta : Real}
    (hd : 0 < d) (ha : 0 < a) (hb : 0 < b)
    (hbetaTwo : beta <= 2)
    (hcap : C * (((b : ENNReal) / (a : ENNReal)) ^ (2 : Nat)) <=
      (M : ENNReal)) :
    ((d : ENNReal) ^ (-epsilon / 2) *
        ((b : ENNReal) / (a : ENNReal)) *
      (((d : ENNReal) / (a : ENNReal)) ^ (2 - 3 * beta))) *
        C ^ (1 - beta / 2) <=
      proposition66AInnerFactor d a b M epsilon beta := by
  have hp : 0 <= 1 - beta / 2 := by linarith
  have hraw :
      (d : ENNReal) ^ (-epsilon / 2) *
          ((a : ENNReal) / (b : ENNReal)) ^ (1 - beta) *
        ((d : ENNReal) / (a : ENNReal)) ^ (-2 * beta) *
          (((((d : ENNReal) / (a : ENNReal)) ^ (2 : Nat)) *
            (C * (((b : ENNReal) / (a : ENNReal)) ^ (2 : Nat)))) ^
              (1 - beta / 2)) <=
        proposition66AInnerFactor d a b M epsilon beta := by
    unfold proposition66AInnerFactor
    gcongr
  have hpower :
      (((((d : ENNReal) / (a : ENNReal)) ^ (2 : Nat)) *
          (C * (((b : ENNReal) / (a : ENNReal)) ^ (2 : Nat)))) ^
            (1 - beta / 2)) =
        (((((d : ENNReal) / (a : ENNReal)) ^ (2 : Nat)) *
          (((b : ENNReal) / (a : ENNReal)) ^ (2 : Nat))) ^
            (1 - beta / 2)) * C ^ (1 - beta / 2) := by
    rw [ENNReal.mul_rpow_of_nonneg _ _ hp,
      ENNReal.mul_rpow_of_nonneg _ _ hp,
      ENNReal.mul_rpow_of_nonneg _ _ hp]
    ac_rfl
  calc
    ((d : ENNReal) ^ (-epsilon / 2) *
        ((b : ENNReal) / (a : ENNReal)) *
      (((d : ENNReal) / (a : ENNReal)) ^ (2 - 3 * beta))) *
        C ^ (1 - beta / 2) =
      ((d : ENNReal) ^ (-epsilon / 2) *
          ((a : ENNReal) / (b : ENNReal)) ^ (1 - beta) *
        ((d : ENNReal) / (a : ENNReal)) ^ (-2 * beta) *
          (((((d : ENNReal) / (a : ENNReal)) ^ (2 : Nat)) *
            (C * (((b : ENNReal) / (a : ENNReal)) ^ (2 : Nat)))) ^
              (1 - beta / 2))) := by
      rw [hpower, ← mul_assoc, proposition66AInner_aspectReserve_eq
        hd ha hb hbetaTwo]
    _ <= proposition66AInnerFactor d a b M epsilon beta := hraw

variable {delta rho : NNReal} {index : Type}
  [Fintype index] [DecidableEq index]
  {fine : UniformTubeFamily delta index}

/-- Literal occupancy predicate for one actual selected-parent side bucket. -/
def SelectedBucketOccupied
    (S : StickyScaleCover fine rho) (hrho : 0 < rho)
    (P : GreedyDensityPartition S.activeCoarseFamily
      (hullCandidates (Finset.univ : Finset (ActiveParentIndex S)))
      (hullContainer S.activeCoarseFamily) Finset.univ)
    (k : Fin (blocks S.activeCoarseFamily P).length)
    (r : NNReal) (hr : 0 < r) (label : Fin 3 -> Int) : Prop :=
  label ∈ occupiedWeightBuckets
    (Finset.univ : Finset
      {p // p ∈ (blockAt S.activeCoarseFamily P k).fiber})
    (fun p => sideShapeLabel
      (selectedParentLongRelabeledSide
        (contractedJohnAffineEquiv
          (selectedParentGreedyBlockJohnFrame S hrho P k) r hr)
        S (blockAt S.activeCoarseFamily P k).fiber hrho p))

/-- Same-object specialization to the exact local cap of an actual occupied
selected-parent bucket.  Radius and half-scale hypotheses are discharged
from the canonical adaptive construction. -/
theorem selectedParent_sourceScaleReserve_le_adaptiveActualInnerFactor
    (S : StickyScaleCover fine rho) (hrho : 0 < rho)
    (P : GreedyDensityPartition S.activeCoarseFamily
      (hullCandidates (Finset.univ : Finset (ActiveParentIndex S)))
      (hullContainer S.activeCoarseFamily) Finset.univ)
    (k : Fin (blocks S.activeCoarseFamily P).length)
    (r : NNReal) (hr : 0 < r) (label : Fin 3 -> Int)
    (hoccupied : SelectedBucketOccupied
      S hrho P k r hr label)
    (hdelta : 0 < delta) (hdeltaHalf : delta <= (2 : NNReal)⁻¹)
    (hsmallPacking : selectedParentCenteredHalfPostAdaptiveProxyScale
      delta rho r label / 8 <= (1 / 100 : NNReal))
    (C : ENNReal) (hCfinite : C ≠ ∞)
    (epsilon beta : Real) (hbetaTwo : beta <= 2) :
    ((rho : ENNReal) ^ (-epsilon / 2) *
        ((bucketShortB label : ENNReal) /
          (bucketShortA label : ENNReal)) *
      (((rho : ENNReal) / (bucketShortA label : ENNReal)) ^
        (2 - 3 * beta))) * C ^ (1 - beta / 2) <=
      proposition66AInnerFactor rho
        (bucketShortA label) (bucketShortB label)
        (centeredAdaptiveActualBucketFullFiberNatCap
          S hrho P k r hr label C) epsilon beta := by
  have hcap :=
    exists_sourceKatzTaoConstant_mul_bucketAspect_sq_le_centeredAdaptiveActualBucketFullFiberNatCap
      S hrho P k r hr label
      (by simpa only [SelectedBucketOccupied] using hoccupied)
      hdelta hdeltaHalf hsmallPacking C hCfinite
  exact sourceAspectCap_reserve_le_proposition66AInnerFactor
    hrho (bucketShortA_pos label)
      ((bucketShortA_pos label).trans_le (bucketShortA_le_bucketShortB label))
        hbetaTwo hcap

#print axioms sourceAspectCap_reserve_le_proposition66AInnerFactor
#print axioms selectedParent_sourceScaleReserve_le_adaptiveActualInnerFactor

end
end Family8SelectedParentAdaptiveInnerSourceReserveV1
