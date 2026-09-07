import Family8Grounding.Family8SelectedParentPlankCenteredHalfPostFiveParameterPackingV1
import Family8Grounding.Family8SelectedParentJohnPlankQuantitativeLossV9
import Mathlib.Tactic

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 5000000

open Set
open scoped NNReal

namespace Family8SelectedParentPlankCanonicalRadiusScaleV1

open LeanEval.Analysis.WangZahlKakeya
open Submission.Kakeya.ConvexGeometry
open Submission.Kakeya.ConvexFactoring
open Submission.Kakeya.ConvexFactoring.FullConvexMaximalDensity
open Submission.Kakeya.ConvexFactoring.GreedyOccurrenceFactorization
open Submission.Kakeya.Uniformity
open Family8SelectedParentCertifiedPlankCordobaConnectorV3
open Family8SelectedParentJohnFrameNormalizationV9
open Family8SelectedParentJohnPlankQuantitativeLossV9
open Family8SelectedParentJohnPlankSideWidthBridgeV5
open Family8SelectedParentJohnPlankSideWidthBridgeV7
open Family8SelectedParentJohnPlankSideWidthBridgeV8
open Family8SelectedParentPlankCanonicalThinCountV5
open Family8SelectedParentPlankCenteredHalfPostCarrierV1
open Family8SelectedParentPlankCenteredHalfPostStructuredRadiusV1
open Family8SelectedParentPlankFineAxisCoordinateV2
open Family8SelectedParentPlankFineProxyCarrierV3
open Family8StickySelectedParentGreedyBlockFrostmanV3
open FamilyStickyAtEveryScaleCoreV1

noncomputable section

/-!
# Structural scale behind the centered canonical carrier radius

The selected label is the actual dyadic label of a memberwise John box.  The
round ball transported in V9 therefore forces its shortest normalized bucket
side to dominate `2 rho q`, where `q = r/(6912 u₂)`.  This is the missing
link between the genuine parent carrier and the canonical fine-axis scale.
-/

variable {delta rho : NNReal} {index : Type}
  [Fintype index] [DecidableEq index]
  {fine : UniformTubeFamily delta index}

theorem selectedParent_two_mul_rho_mul_axisLengthFloor_le_bucketShortA
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
    2 * rho * selectedPlankFineAxisLengthFloor r label ≤
      bucketShortA label := by
  let e := contractedJohnAffineEquiv
    (selectedParentGreedyBlockJohnFrame S hrho P k) r hr
  let B := (blockAt S.activeCoarseFamily P k).fiber
  let side := selectedParentLongRelabeledSide e S B hrho W.1
  have hsidePos : ∀ i, 0 < side i := by
    intro i
    exact selectedParentLongRelabeledSide_pos e S B hrho W.1 i
  have hmem := W.2
  change W.1 ∈ sideShapeBucket Finset.univ
    (fun p => selectedParentLongRelabeledSide e S B hrho p) label at hmem
  have hlabel : sideShapeLabel side = label := by
    exact (mem_sideShapeBucket_iff Finset.univ
      (fun p => selectedParentLongRelabeledSide e S B hrho p)
      label W.1).mp hmem |>.2
  have hfloor (i : Fin 3) : selectedParentSideFloor rho r ≤ side i := by
    simpa only [side, e, B] using
      selectedParentContractedLongRelabeledSide_floor
        hfineContained S hrho hrhoOne P k r hr W.1 i
  have hupper0 : selectedParentSideFloor rho r ≤
      sideShapeUpper label 0 := by
    have hband := sideShapeUpper_half_lt_and_le hsidePos 0
    rw [hlabel] at hband
    exact (hfloor 0).trans hband.2
  have hupper1 : selectedParentSideFloor rho r ≤
      sideShapeUpper label 1 := by
    have hband := sideShapeUpper_half_lt_and_le hsidePos 1
    rw [hlabel] at hband
    exact (hfloor 1).trans hband.2
  have hfloorA : selectedParentSideFloor rho r /
      sideShapeUpper label 2 ≤ bucketShortA label := by
    by_cases h : sideShapeUpper label 0 ≤ sideShapeUpper label 1
    · simp only [bucketShortA, if_pos h, div_eq_mul_inv]
      exact mul_le_mul_of_nonneg_right hupper0 bot_le
    · simp only [bucketShortA, if_neg h, div_eq_mul_inv]
      exact mul_le_mul_of_nonneg_right hupper1 bot_le
  calc
    2 * rho * selectedPlankFineAxisLengthFloor r label =
        selectedParentSideFloor rho r / sideShapeUpper label 2 := by
      apply NNReal.eq
      have hrReal : (0 : Real) < (r : Real) := by exact_mod_cast hr
      have huReal : (0 : Real) < (sideShapeUpper label 2 : Real) := by
        exact_mod_cast sideShapeUpper_pos label 2
      norm_num [selectedPlankFineAxisLengthFloor, selectedParentSideFloor,
        NNReal.coe_div, NNReal.coe_mul]
      field_simp [hrReal.ne', huReal.ne']
      ring
    _ ≤ bucketShortA label := hfloorA

/-- The structural side floor turns one explicit fine/coarse scale comparison
into the exact centered carrier-radius scalar used by the mass/fresh chain. -/
theorem selectedParent_centeredHalfPost_canonical_radius_scalar_of_scale
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
    (hscale : 3 * r * delta ≤
      64 * rho ^ 2 * sideShapeUpper label 2) :
    ((1 / 2 : Real) *
      (3 * (r : Real) /
        ((2 * (rho : Real)) * (sideShapeUpper label 2 : Real)))) *
          (delta : Real) ≤
      (selectedPlankFineCanonicalProxyScale r label : Real) := by
  let q := selectedPlankFineAxisLengthFloor r label
  have hq : 0 < q := selectedPlankFineAxisLengthFloor_pos hr label
  have hqReal : (0 : Real) < (q : Real) := by exact_mod_cast hq
  have hrhoReal : (0 : Real) < (rho : Real) := by exact_mod_cast hrho
  have huReal : (0 : Real) < (sideShapeUpper label 2 : Real) := by
    exact_mod_cast sideShapeUpper_pos label 2
  have haLower :=
    selectedParent_two_mul_rho_mul_axisLengthFloor_le_bucketShortA
      hfineContained S hrho hrhoOne P k r hr label W
  have haLowerReal :
      (2 : Real) * (rho : Real) * (q : Real) ≤
        (bucketShortA label : Real) := by
    exact_mod_cast haLower
  have hsLower : (16 : Real) * (rho : Real) ≤
      (selectedPlankFineCanonicalProxyScale r label : Real) := by
    change (16 : Real) * (rho : Real) ≤
      8 * (bucketShortA label : Real) / (q : Real)
    apply (le_div_iff₀ hqReal).2
    nlinarith
  have hscaleReal : (3 : Real) * (r : Real) * (delta : Real) ≤
      64 * (rho : Real) ^ 2 * (sideShapeUpper label 2 : Real) := by
    exact_mod_cast hscale
  apply le_trans _ hsLower
  calc
    ((1 / 2 : Real) *
        (3 * (r : Real) /
          ((2 * (rho : Real)) * (sideShapeUpper label 2 : Real)))) *
          (delta : Real) =
        (3 * (r : Real) * (delta : Real)) /
          (4 * (rho : Real) * (sideShapeUpper label 2 : Real)) := by ring
    _ ≤ 16 * (rho : Real) := by
      apply (div_le_iff₀
        (mul_pos (mul_pos (by norm_num) hrhoReal) huReal)).2
      nlinarith

/-- A label-independent square-scale separation is sufficient for the
previous explicit comparison.  The constant `648` is the exact cost of the
already proved uniform bound `q ≤ 2`. -/
theorem selectedParent_centeredHalfPost_canonical_radius_scalar_of_quadratic_scale
    (hfineContained : ∀ i, (fine.tubes i).carrier ⊆
      Metric.closedBall (0 : Space) 1)
    (S : StickyScaleCover fine rho) (hrho : 0 < rho) (hrhoOne : rho ≤ 1)
    (P : GreedyDensityPartition S.activeCoarseFamily
      (hullCandidates (Finset.univ : Finset (ActiveParentIndex S)))
      (hullContainer S.activeCoarseFamily) Finset.univ)
    (k : Fin (blocks S.activeCoarseFamily P).length)
    (r : NNReal) (hr : 0 < r) (label : Fin 3 → Int)
    (hplank : ∀ W : {p // p ∈ selectedParentPlankBucketIndices
      (contractedJohnAffineEquiv
        (selectedParentGreedyBlockJohnFrame S hrho P k) r hr)
      S (blockAt S.activeCoarseFamily P k).fiber hrho label},
      IsPlank 576 (bucketShortA label) (bucketShortB label)
        (selectedParentPlankBucketFamily
          (contractedJohnAffineEquiv
            (selectedParentGreedyBlockJohnFrame S hrho P k) r hr)
          S (blockAt S.activeCoarseFamily P k).fiber hrho label W))
    (W : {p // p ∈ selectedParentPlankBucketIndices
      (contractedJohnAffineEquiv
        (selectedParentGreedyBlockJohnFrame S hrho P k) r hr)
      S (blockAt S.activeCoarseFamily P k).fiber hrho label})
    (hquadratic : 648 * delta ≤ rho ^ 2) :
    ((1 / 2 : Real) *
      (3 * (r : Real) /
        ((2 * (rho : Real)) * (sideShapeUpper label 2 : Real)))) *
          (delta : Real) ≤
      (selectedPlankFineCanonicalProxyScale r label : Real) := by
  let q := selectedPlankFineAxisLengthFloor r label
  let u := sideShapeUpper label 2
  have hfiberNonempty : (S.fiber W.1.1.1).Nonempty := by
    obtain ⟨i, hiActive, hiParent⟩ :=
      S.parent_surjective W.1.1.1 W.1.1.2
    exact ⟨i, (S.mem_fiber i W.1.1.1).2 ⟨hiActive, hiParent⟩⟩
  let i0 : SelectedPlankFineIndex S W :=
    ⟨hfiberNonempty.choose, hfiberNonempty.choose_spec⟩
  have hqTwo : q ≤ 2 := by
    exact selectedPlankFineAxisLengthFloor_le_two
      hfineContained S hrho hrhoOne P k r hr label hplank W i0
  have hdenom : 0 < 6912 * u :=
    mul_pos (by norm_num) (sideShapeUpper_pos label 2)
  have hru : r ≤ 13824 * u := by
    have h := (div_le_iff₀ hdenom).1 hqTwo
    calc
      r ≤ 2 * (6912 * u) := by
        simpa only [q, u, selectedPlankFineAxisLengthFloor] using h
      _ = 13824 * u := by ring
  have hscale : 3 * r * delta ≤ 64 * rho ^ 2 * u := by
    calc
      3 * r * delta ≤ 3 * (13824 * u) * delta := by gcongr
      _ = 64 * (648 * delta) * u := by ring
      _ ≤ 64 * rho ^ 2 * u := by gcongr
  exact selectedParent_centeredHalfPost_canonical_radius_scalar_of_scale
    hfineContained S hrho hrhoOne P k r hr label W hscale

#print axioms
  selectedParent_two_mul_rho_mul_axisLengthFloor_le_bucketShortA
#print axioms
  selectedParent_centeredHalfPost_canonical_radius_scalar_of_scale
#print axioms
  selectedParent_centeredHalfPost_canonical_radius_scalar_of_quadratic_scale

end
end Family8SelectedParentPlankCanonicalRadiusScaleV1
