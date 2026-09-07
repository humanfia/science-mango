import Family8Grounding.Family8SelectedParentPlankCenteredAdaptiveScaleHullFlatnessGeometryV1

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 5000000

open Set MeasureTheory
open scoped ENNReal NNReal BigOperators InnerProductSpace

namespace Family8SelectedParentPlankCenteredAdaptiveScaleHullFlatnessProducerV1

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
open Family8SelectedParentPlankCenteredAdaptiveScaleComponentsV2
open Family8SelectedParentPlankCenteredAdaptiveScaleFlatnessTransportV3
open Family8SelectedParentPlankCenteredAdaptiveScaleHullFlatnessGeometryV1
open Family8StickySelectedParentGreedyBlockFrostmanV3
open FamilyStickyAtEveryScaleCoreV1

noncomputable section

variable {delta rho : NNReal} {index : Type}
  [Fintype index] [DecidableEq index]
  {fine : UniformTubeFamily delta index}

theorem selectedParent_bucketShortA_le_hullRatio
    (hfineContained : ∀ i, (fine.tubes i).carrier ⊆
      Metric.closedBall (0 : Space) 1)
    (S : StickyScaleCover fine rho) (hrho : 0 < rho) (hrhoOne : rho ≤ 1)
    (P : GreedyDensityPartition S.activeCoarseFamily
      (hullCandidates (Finset.univ : Finset (ActiveParentIndex S)))
      (hullContainer S.activeCoarseFamily) Finset.univ)
    (k : Fin (blocks S.activeCoarseFamily P).length)
    (r : NNReal) (hr : 0 < r) (label : Fin 3 → Int)
    (W : {p // p ∈ selectedParentPlankBucketIndices
      (contractedJohnAffineEquiv
        (selectedParentGreedyBlockJohnFrame S hrho P k) r hr)
      S (blockAt S.activeCoarseFamily P k).fiber hrho label}) :
    let J := selectedParentGreedyBlockJohnFrame S hrho P k
    bucketShortA label ≤ 286654464 * rho / hullShortestSide J := by
  dsimp only
  let J := selectedParentGreedyBlockJohnFrame S hrho P k
  let e := contractedJohnAffineEquiv J r hr
  let B := (blockAt S.activeCoarseFamily P k).fiber
  let side := selectedParentLongRelabeledSide e S B hrho W.1
  let m := hullShortestSide J
  have hm : 0 < m := hullShortestSide_pos J
  have hshort : min (side 0) (side 1) ≤ 3456 * r * rho / m := by
    simpa only [J, e, B, side, m] using
      (selectedParentContracted_transverseShort_le_hullRatio
        S hrho P k r hr W.1)
  have hsidePos : ∀ i, 0 < side i := by
    intro i
    exact selectedParentLongRelabeledSide_pos e S B hrho W.1 i
  have hlabel : sideShapeLabel side = label := by
    exact (mem_sideShapeBucket_iff Finset.univ
      (fun p ↦ selectedParentLongRelabeledSide e S B hrho p)
      label W.1).mp W.2 |>.2
  have hupperBand := sideShapeUpper_half_lt_and_le hsidePos 2
  rw [hlabel] at hupperBand
  have hlong : r / 41472 ≤ side 2 := by
    simpa only [J, e, B, side] using
      (selectedParentContractedLongRelabeledSide_two_lower
        hfineContained S hrho hrhoOne P k r hr W.1)
  have hlongUpper : r / 41472 ≤ sideShapeUpper label 2 :=
    hlong.trans hupperBand.2
  let target : NNReal := 286654464 * rho / m
  have hflat : 2 * min (side 0) (side 1) ≤
      target * sideShapeUpper label 2 := by
    calc
      2 * min (side 0) (side 1) ≤
          2 * (3456 * r * rho / m) := by gcongr
      _ = target * (r / 41472) := by
        dsimp only [target]
        field_simp [hm.ne']
        ring
      _ ≤ target * sideShapeUpper label 2 := by gcongr
  exact selectedParent_bucketShortA_le_of_member_transverse_flatness
    S hrho P k r hr label W target (by
      simpa only [side, e, B] using hflat)

theorem selectedParent_hullThin_or_bucketFlat
    (hfineContained : ∀ i, (fine.tubes i).carrier ⊆
      Metric.closedBall (0 : Space) 1)
    (S : StickyScaleCover fine rho) (hrho : 0 < rho) (hrhoOne : rho ≤ 1)
    (P : GreedyDensityPartition S.activeCoarseFamily
      (hullCandidates (Finset.univ : Finset (ActiveParentIndex S)))
      (hullContainer S.activeCoarseFamily) Finset.univ)
    (k : Fin (blocks S.activeCoarseFamily P).length)
    (r : NNReal) (hr : 0 < r) (label : Fin 3 → Int)
    (W : {p // p ∈ selectedParentPlankBucketIndices
      (contractedJohnAffineEquiv
        (selectedParentGreedyBlockJohnFrame S hrho P k) r hr)
      S (blockAt S.activeCoarseFamily P k).fiber hrho label})
    (threshold : NNReal) (hthreshold : 0 < threshold) :
    let J := selectedParentGreedyBlockJohnFrame S hrho P k
    hullShortestSide J ≤ threshold ∨
      bucketShortA label ≤ 286654464 * rho / threshold := by
  dsimp only
  let J := selectedParentGreedyBlockJohnFrame S hrho P k
  let m := hullShortestSide J
  rcases le_total m threshold with hthin | hthick
  · exact Or.inl hthin
  · right
    have hratio := selectedParent_bucketShortA_le_hullRatio
      hfineContained S hrho hrhoOne P k r hr label W
    calc
      bucketShortA label ≤ 286654464 * rho / m := by
        simpa only [J, m] using hratio
      _ ≤ 286654464 * rho / threshold := by
        exact div_le_div_of_nonneg_left (by positivity) hthreshold hthick

theorem rho_div_rpow_one_sub (hrho : 0 < rho) (tau : Real) :
    rho / rho ^ (1 - tau) = rho ^ tau := by
  rw [NNReal.rpow_sub hrho.ne' 1 tau, NNReal.rpow_one]
  field_simp [hrho.ne', (NNReal.rpow_pos hrho).ne']

theorem selectedParent_paperHullThin_or_bucketFlat
    (hfineContained : ∀ i, (fine.tubes i).carrier ⊆
      Metric.closedBall (0 : Space) 1)
    (S : StickyScaleCover fine rho) (hrho : 0 < rho) (hrhoOne : rho ≤ 1)
    (P : GreedyDensityPartition S.activeCoarseFamily
      (hullCandidates (Finset.univ : Finset (ActiveParentIndex S)))
      (hullContainer S.activeCoarseFamily) Finset.univ)
    (k : Fin (blocks S.activeCoarseFamily P).length)
    (r : NNReal) (hr : 0 < r) (label : Fin 3 → Int)
    (W : {p // p ∈ selectedParentPlankBucketIndices
      (contractedJohnAffineEquiv
        (selectedParentGreedyBlockJohnFrame S hrho P k) r hr)
      S (blockAt S.activeCoarseFamily P k).fiber hrho label})
    (tau : Real) :
    let J := selectedParentGreedyBlockJohnFrame S hrho P k
    hullShortestSide J ≤ rho ^ (1 - tau) ∨
      bucketShortA label ≤ 286654464 * rho ^ tau := by
  dsimp only
  have hbranch := selectedParent_hullThin_or_bucketFlat
    hfineContained S hrho hrhoOne P k r hr label W
    (rho ^ (1 - tau)) (NNReal.rpow_pos hrho)
  rcases hbranch with hthin | hflat
  · exact Or.inl hthin
  · right
    rw [mul_div_assoc, rho_div_rpow_one_sub hrho tau] at hflat
    exact hflat

#print axioms selectedParent_bucketShortA_le_hullRatio
#print axioms selectedParent_hullThin_or_bucketFlat
#print axioms rho_div_rpow_one_sub
#print axioms selectedParent_paperHullThin_or_bucketFlat

end
end Family8SelectedParentPlankCenteredAdaptiveScaleHullFlatnessProducerV1
