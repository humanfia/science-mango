import Family8Grounding.Family8SelectedParentPlankCenteredAdaptiveScaleComponentsV4
import Mathlib.Tactic

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 5000000

open Set MeasureTheory
open scoped ENNReal NNReal BigOperators

namespace Family8SelectedParentPlankCenteredAdaptiveScaleFlatnessTransportV3

open LeanEval.Analysis.WangZahlKakeya
open Submission.Kakeya.ConvexGeometry
open Submission.Kakeya.ConvexFactoring
open Submission.Kakeya.ConvexFactoring.FullConvexMaximalDensity
open Submission.Kakeya.ConvexFactoring.GreedyOccurrenceFactorization
open Submission.Kakeya.Uniformity
open Family8SelectedParentCertifiedPlankCordobaConnectorV3
open Family8SelectedParentJohnFrameNormalizationV9
open Family8SelectedParentJohnPlankSideWidthBridgeV5
open Family8SelectedParentJohnPlankSideWidthBridgeV7
open Family8SelectedParentJohnPlankSideWidthBridgeV8
open Family8SelectedParentPlankCenteredAdaptiveScaleComponentsV4
open Family8StickySelectedParentGreedyBlockFrostmanV3
open FamilyStickyAtEveryScaleCoreV1

noncomputable section

/-!
# Transport of a genuine thin-member estimate to `bucketShortA`

The ceil-log bucket costs a factor strictly smaller than two.  The theorem
below records the exact transport needed at the upstream thick/thin split:
flatness of the shortest transverse side of any retained member, relative to
the common long dyadic endpoint, implies flatness of `bucketShortA`.
-/

/-- The selected dyadic short parameter is at most twice the member's actual
short transverse side, divided by the common long endpoint. -/
theorem bucketShortA_le_two_mul_transverseShort_div_longUpper
    {source : Fin 3 -> NNReal} (hsource : forall i, 0 < source i)
    (label : Fin 3 -> Int) (hlabel : sideShapeLabel source = label) :
    bucketShortA label <=
      2 * min (source 0) (source 1) / sideShapeUpper label 2 := by
  have hband0 := sideShapeUpper_half_lt_and_le hsource 0
  have hband1 := sideShapeUpper_half_lt_and_le hsource 1
  rw [hlabel] at hband0 hband1
  have hu0 : sideShapeUpper label 0 <= 2 * source 0 := by
    nlinarith [hband0.1]
  have hu1 : sideShapeUpper label 1 <= 2 * source 1 := by
    nlinarith [hband1.1]
  by_cases h01 : source 0 <= source 1
  · have hupper01 := sideShapeUpper_le_of_side_le hsource h01
    rw [hlabel] at hupper01
    rw [min_eq_left h01]
    simp only [bucketShortA, if_pos hupper01, div_eq_mul_inv]
    exact mul_le_mul_of_nonneg_right hu0 bot_le
  · have h10 : source 1 <= source 0 := le_of_not_ge h01
    have hupper10 := sideShapeUpper_le_of_side_le hsource h10
    rw [hlabel] at hupper10
    have hbucket : bucketShortA label =
        sideShapeUpper label 1 / sideShapeUpper label 2 := by
      by_cases hupper01 : sideShapeUpper label 0 <= sideShapeUpper label 1
      · have heq : sideShapeUpper label 0 = sideShapeUpper label 1 :=
          le_antisymm hupper01 hupper10
        simp only [bucketShortA, if_pos hupper01]
        rw [heq]
      · simp only [bucketShortA, if_neg hupper01]
    rw [hbucket, min_eq_right h10]
    simp only [div_eq_mul_inv]
    exact mul_le_mul_of_nonneg_right hu1 bot_le

/-- Exact scalar form of the missing upstream transfer.  This is not a
conclusion callback: its premise is the memberwise normalized thin-branch
geometry at the point where the dyadic label is produced. -/
theorem bucketShortA_le_of_member_transverse_flatness
    {source : Fin 3 -> NNReal} (hsource : forall i, 0 < source i)
    (label : Fin 3 -> Int) (hlabel : sideShapeLabel source = label)
    (target : NNReal)
    (hflat : 2 * min (source 0) (source 1) <=
      target * sideShapeUpper label 2) :
    bucketShortA label <= target := by
  calc
    bucketShortA label <=
        2 * min (source 0) (source 1) / sideShapeUpper label 2 :=
      bucketShortA_le_two_mul_transverseShort_div_longUpper
        hsource label hlabel
    _ <= target :=
      (div_le_iff₀ (sideShapeUpper_pos label 2)).2 hflat

variable {delta rho : NNReal} {index : Type}
  [Fintype index] [DecidableEq index]
  {fine : UniformTubeFamily delta index}

/-- Specialization to an actual member of the selected-parent bucket.  It
pinpoints the minimum real upstream obligation: the thick/thin producer must
bound this member's shortest transformed transverse side relative to the
same long endpoint used by the occupied label. -/
theorem selectedParent_bucketShortA_le_of_member_transverse_flatness
    (S : StickyScaleCover fine rho) (hrho : 0 < rho)
    (P : GreedyDensityPartition S.activeCoarseFamily
      (hullCandidates (Finset.univ : Finset (ActiveParentIndex S)))
      (hullContainer S.activeCoarseFamily) Finset.univ)
    (k : Fin (blocks S.activeCoarseFamily P).length)
    (r : NNReal) (hr : 0 < r) (label : Fin 3 -> Int)
    (W : {p // p ∈ selectedParentPlankBucketIndices
      (contractedJohnAffineEquiv
        (selectedParentGreedyBlockJohnFrame S hrho P k) r hr)
      S (blockAt S.activeCoarseFamily P k).fiber hrho label})
    (target : NNReal)
    (hflat :
      let side := selectedParentLongRelabeledSide
        (contractedJohnAffineEquiv
          (selectedParentGreedyBlockJohnFrame S hrho P k) r hr)
        S (blockAt S.activeCoarseFamily P k).fiber hrho W.1
      2 * min (side 0) (side 1) <= target * sideShapeUpper label 2) :
    bucketShortA label <= target := by
  let e := contractedJohnAffineEquiv
    (selectedParentGreedyBlockJohnFrame S hrho P k) r hr
  let B := (blockAt S.activeCoarseFamily P k).fiber
  let side := selectedParentLongRelabeledSide e S B hrho W.1
  have hsource : forall i, 0 < side i := by
    intro i
    exact selectedParentLongRelabeledSide_pos e S B hrho W.1 i
  have hlabel : sideShapeLabel side = label := by
    exact (mem_sideShapeBucket_iff Finset.univ
      (fun p => selectedParentLongRelabeledSide e S B hrho p)
      label W.1).mp W.2 |>.2
  exact bucketShortA_le_of_member_transverse_flatness
    hsource label hlabel target (by simpa only [side, e, B] using hflat)

#print axioms bucketShortA_le_two_mul_transverseShort_div_longUpper
#print axioms bucketShortA_le_of_member_transverse_flatness
#print axioms selectedParent_bucketShortA_le_of_member_transverse_flatness

end
end Family8SelectedParentPlankCenteredAdaptiveScaleFlatnessTransportV3
