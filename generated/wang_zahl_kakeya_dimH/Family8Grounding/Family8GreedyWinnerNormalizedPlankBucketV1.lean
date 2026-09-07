import Family8Grounding.Family8GreedyWinnerAutomaticJohnSideBucketV1
import Family8Grounding.Family8SelectedParentJohnPlankSideWidthBridgeV8
import Mathlib.Tactic

/-!
# A common normalized plank bucket for actual greedy winners

The automatic John-side bucket for full-convex greedy winners already gives
one mass-retaining side label.  This file applies one transverse relabeling
and one scalar dilation, both determined only by that common label.  Every
selected winner image then has an actual transported box certificate and is
a `576`-plank with the same two short parameters.

The resulting family consists of winner bodies in one common normalized
coordinate system.  It is not a `StickyScaleCover` of the original fine
family: no normalized long-tube containment is pulled back through the
common scalar map here.
-/

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 5000000

open Set MeasureTheory
open scoped BigOperators ENNReal NNReal InnerProductSpace

namespace Family8GreedyWinnerNormalizedPlankBucketV1

open LeanEval.Analysis.WangZahlKakeya
open Submission.Kakeya.ConvexGeometry
open Submission.Kakeya.ConvexFactoring
open Submission.Kakeya.ConvexFactoring.FullConvexMaximalDensity
open Submission.Kakeya.ConvexFactoring.GreedyOccurrenceFactorization
open Submission.Kakeya.ConvexFactoring.GreedyDensityBucketing
open Submission.Kakeya.Uniformity
open Family6AffineConvexVolumeCoreV1
open Family8GreedyWinnerAutomaticJohnSideBucketV1
open Family8SelectedParentJohnPlankSideWidthBridgeV4
open Family8SelectedParentJohnPlankSideWidthBridgeV5
open Family8SelectedParentJohnPlankSideWidthBridgeV7
open Family8SelectedParentJohnPlankSideWidthBridgeV8
open FamilyStickyCinematicL32FiniteWeightedBucketV1

noncomputable section

universe u

variable {delta : NNReal} {iota : Type u}
  [Fintype iota] [DecidableEq iota]
  {fine : UniformTubeFamily delta iota}
  {active : Finset iota}

variable
  (P : GreedyDensityPartition fine.bodyFamily
    (hullCandidates active) (hullContainer fine.bodyFamily) active)

/-- Apply the common positive scalar attached to `label` to an actual greedy
winner body.  The scalar is independent of the occurrence. -/
def normalizedWinnerBody
    (label : Fin 3 -> Int)
    (k : Fin (blocks fine.bodyFamily P).length) : ConvexBody Space :=
  affineImageConvexBody
    (scalarDilationAffineEquiv
      (sideShapeUpper label 2)⁻¹
      (inv_pos.mpr (sideShapeUpper_pos label 2)))
    (blockAt fine.bodyFamily P k).body

/-- The normalized bodies indexed by a literal selected occurrence set. -/
def normalizedWinnerFamily
    (label : Fin 3 -> Int)
    (selected : Finset (Fin (blocks fine.bodyFamily P).length)) :
    ConvexFamily {k // k ∈ selected} :=
  fun k => normalizedWinnerBody P label k.1

/-- The longest-axis winner certificate, after the common transverse
relabeling and common scalar dilation. -/
noncomputable def normalizedWinnerCertificate
    (hdelta : 0 < delta) (label : Fin 3 -> Int)
    (k : Fin (blocks fine.bodyFamily P).length) :
    BoxDimensionsCertificate 288
      (normalizedBucketSide (winnerLongSide P hdelta k) label)
      (normalizedWinnerBody P label k) := by
  let cert0 := winnerLongCertificate P hdelta k
  let cert1 := relabelBoxDimensionsCertificate cert0
    (transverseOrderPermutation label)
  let cert2 := scalarDilationBoxDimensionsCertificate cert1
    (sideShapeUpper label 2)⁻¹
    (inv_pos.mpr (sideShapeUpper_pos label 2))
  have hside :
      (fun i => (sideShapeUpper label 2)⁻¹ *
        relabeledSide (winnerLongSide P hdelta k)
          (transverseOrderPermutation label) i) =
        normalizedBucketSide (winnerLongSide P hdelta k) label :=
    scalarNormalizedRelabeledSide_eq _ _
  exact hside ▸ cert2

/-- A member whose original long-relabeled sides lie in the common bucket
becomes a genuine plank after the common normalization. -/
theorem normalizedWinnerBody_isPlank
    (hdelta : 0 < delta) (label : Fin 3 -> Int)
    (k : Fin (blocks fine.bodyFamily P).length)
    (hb : bucketShortB label <= 1)
    (hband : forall i,
      sideShapeUpper label i / 2 < winnerLongSide P hdelta k i ∧
        winnerLongSide P hdelta k i <= sideShapeUpper label i) :
    IsPlank 576 (bucketShortA label) (bucketShortB label)
      (normalizedWinnerBody P label k) := by
  have hwidth := normalizedBucketSide_sideWidthEnvelope hband
  have hplank := isPlank_of_boxCertificate_sideWidthEnvelope
    (normalizedWinnerCertificate P hdelta label k)
    (bucketShortA_pos label) (bucketShortA_le_bucketShortB label) hb hwidth
  simpa only [show (288 : NNReal) * 2 = 576 by norm_num] using hplank

/-- One mass-retaining normalized winner bucket.  Its selected occurrences,
mass loss, common short sides, and uniform plank conclusion are all exposed
in a single output object. -/
structure GreedyWinnerNormalizedPlankBucket (hdelta : 0 < delta) where
  label : Fin 3 -> Int
  label_occupied : label ∈ occupiedWeightBuckets
    (Finset.univ : Finset (Fin (blocks fine.bodyFamily P).length))
    (fun k => sideShapeLabel (winnerLongSide P hdelta k))
  selected : Finset (Fin (blocks fine.bodyFamily P).length)
  selected_eq : selected = sideShapeBucket Finset.univ
    (winnerLongSide P hdelta) label
  selected_nonempty : selected.Nonempty
  blockMass_retention :
    (∑ i ∈ active, volume (fine.bodyFamily i : Set Space)) <=
      (winnerSideBucketLoss delta : ENNReal) *
        ∑ k ∈ selected,
          blockMass fine.bodyFamily (blockAt fine.bodyFamily P k)
  shortA_pos : 0 < bucketShortA label
  shortA_le_shortB : bucketShortA label <= bucketShortB label
  shortB_le_one : bucketShortB label <= 1
  side_band : forall k, k ∈ selected -> forall i,
    sideShapeUpper label i / 2 < winnerLongSide P hdelta k i ∧
      winnerLongSide P hdelta k i <= sideShapeUpper label i
  normalized_isPlank : forall k, k ∈ selected ->
    IsPlank 576 (bucketShortA label) (bucketShortB label)
      (normalizedWinnerBody P label k)

namespace GreedyWinnerNormalizedPlankBucket

/-- The selected normalized winner family carried by the witness. -/
def family
    {hdelta : 0 < delta}
    (W : GreedyWinnerNormalizedPlankBucket P hdelta) :
    ConvexFamily {k // k ∈ W.selected} :=
  normalizedWinnerFamily P W.label W.selected

/-- Every member of the witness's selected normalized family is the same
`576`-plank shape. -/
theorem family_isPlank
    {hdelta : 0 < delta}
    (W : GreedyWinnerNormalizedPlankBucket P hdelta)
    (k : {k // k ∈ W.selected}) :
    IsPlank 576 (bucketShortA W.label) (bucketShortB W.label)
      (family P W k) :=
  W.normalized_isPlank k.1 k.2

end GreedyWinnerNormalizedPlankBucket

/-- The mass-retaining automatic John-side bucket produces a nonempty
selected family of uniformly normalized genuine planks. -/
theorem exists_greedyWinnerNormalizedPlankBucket
    (hdelta : 0 < delta)
    (hactive : active.Nonempty)
    (hfineContained : forall i, i ∈ active ->
      (fine.tubes i).carrier ⊆ Metric.closedBall (0 : Space) 1) :
    Nonempty (GreedyWinnerNormalizedPlankBucket P hdelta) := by
  obtain ⟨label, hoccupied, hmass, hband⟩ :=
    exists_winnerSideBucket_blockMass_retention
      P hdelta hactive hfineContained
  let selected := sideShapeBucket
    (Finset.univ : Finset (Fin (blocks fine.bodyFamily P).length))
    (winnerLongSide P hdelta) label
  rcases mem_occupiedWeightBuckets_iff.mp hoccupied with
    ⟨k, hkuniv, hkLabel⟩
  have hkSelected : k ∈ selected := by
    exact (mem_sideShapeBucket_iff Finset.univ
      (winnerLongSide P hdelta) label k).2 ⟨hkuniv, hkLabel⟩
  have hsidePos : forall i, 0 < winnerLongSide P hdelta k i :=
    winnerLongSide_pos P hdelta k
  have h02 := sideShapeUpper_le_of_side_le hsidePos
    (winnerLongSide_le_two P hdelta k 0)
  have h12 := sideShapeUpper_le_of_side_le hsidePos
    (winnerLongSide_le_two P hdelta k 1)
  rw [hkLabel] at h02 h12
  have hb : bucketShortB label <= 1 :=
    bucketShortB_le_one label h02 h12
  refine ⟨{
    label := label
    label_occupied := hoccupied
    selected := selected
    selected_eq := rfl
    selected_nonempty := ⟨k, hkSelected⟩
    blockMass_retention := ?_
    shortA_pos := bucketShortA_pos label
    shortA_le_shortB := bucketShortA_le_bucketShortB label
    shortB_le_one := hb
    side_band := ?_
    normalized_isPlank := ?_ }⟩
  · simpa only [selected] using hmass
  · intro q hq i
    exact hband q (by simpa only [selected] using hq) i
  · intro q hq
    exact normalizedWinnerBody_isPlank P hdelta label q hb
      (fun i => hband q (by simpa only [selected] using hq) i)

#print axioms normalizedWinnerCertificate
#print axioms normalizedWinnerBody_isPlank
#print axioms GreedyWinnerNormalizedPlankBucket.family_isPlank
#print axioms exists_greedyWinnerNormalizedPlankBucket

end
end Family8GreedyWinnerNormalizedPlankBucketV1
