import Family8Grounding.Family8SelectedParentPlankFineProxyDatumV1
import Family8Grounding.Family8SelectedParentJohnPlankQuantitativeLossV9
import Mathlib.Tactic

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 5000000

open Set
open scoped NNReal InnerProductSpace

namespace Family8SelectedParentPlankFineAxisLengthLowerV3

open LeanEval.Analysis.WangZahlKakeya
open Submission.Kakeya.ConvexGeometry
open Submission.Kakeya.ConvexFactoring
open Submission.Kakeya.ConvexFactoring.FullConvexMaximalDensity
open Submission.Kakeya.ConvexFactoring.GreedyOccurrenceFactorization
open Submission.Kakeya.Uniformity
open Family8ContractedJohnActualTubeProxyV1
open Family8SelectedParentCertifiedPlankCordobaConnectorV3
open Family8SelectedParentJohnFrameNormalizationV9
open Family8SelectedParentJohnPlankQuantitativeLossV9
open Family8SelectedParentJohnPlankSideWidthBridgeV5
open Family8SelectedParentJohnPlankSideWidthBridgeV7
open Family8SelectedParentJohnPlankSideWidthBridgeV8
open Family8SelectedParentPlankFineAxisCoordinateV2
open Family8StickySelectedParentGreedyBlockFrostmanV3
open FamilyStickyAtEveryScaleCoreV1

noncomputable section

/-!
# Uniform lower length for the actual selected-plank fine axes

The common winning-hull John map has an explicit inverse Lipschitz constant.
After the literal long-side bucket normalization this gives a uniform positive
lower bound for every transformed unit fine axis in the same selected plank
fibre.  This is the missing denominator needed to turn actual raw plank
coordinate bounds into normalized-direction bounds.
-/

variable {delta rho : NNReal} {index : Type}
  [Fintype index] [DecidableEq index]
  {fine : UniformTubeFamily delta index}

/-- The canonical transformed fine-axis length is at least
`r / (6912 * longBucketUpper)`. -/
theorem selectedPlankFine_bucketAffineImageAxisVector_norm_lower
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
    (i : SelectedPlankFineIndex S W) :
    ((r / (6912 * sideShapeUpper label 2) : NNReal) : Real) ≤
      ‖affineImageAxisVector
        (bucketNormalizedAffineEquiv
          (contractedJohnAffineEquiv
            (selectedParentGreedyBlockJohnFrame S hrho P k) r hr)
          label)
        (fine.tubes i.1)‖ := by
  let J := selectedParentGreedyBlockJohnFrame S hrho P k
  let e := contractedJohnAffineEquiv J r hr
  let u := sideShapeUpper label 2
  let d := bucketNormalizedAffineEquiv e label
  let T := fine.tubes i.1
  have hJside : ∀ j, J.side j ≤ (2304 : NNReal) := by
    intro j
    exact selectedParentGreedyBlockJohnSide_le_2304
      hfineContained S hrho hrhoOne P k j
  have hinv := contractedJohnAffineEquiv_symm_dist_le
    J 2304 r hr hJside (e T.axis.endpoint) (e T.axis.base)
  have hsource : dist T.axis.endpoint T.axis.base = (1 : Real) := by
    rw [dist_comm, T.axis.dist_base_endpoint]
  rw [e.symm_apply_apply, e.symm_apply_apply, hsource] at hinv
  have hcoeff : (((3 * (2304 : NNReal) / r : NNReal) : Real)) =
      (6912 : Real) / (r : Real) := by
    norm_num [NNReal.coe_div, NNReal.coe_mul]
  rw [hcoeff, dist_eq_norm] at hinv
  have hrReal : (0 : Real) < (r : Real) := by exact_mod_cast hr
  change (1 : Real) ≤ (6912 : Real) / (r : Real) *
      ‖affineImageAxisVector e T‖ at hinv
  have hinv' : (1 : Real) ≤
      ((6912 : Real) * ‖affineImageAxisVector e T‖) / (r : Real) := by
    calc
      (1 : Real) ≤ (6912 : Real) / (r : Real) *
          ‖affineImageAxisVector e T‖ := hinv
      _ = ((6912 : Real) * ‖affineImageAxisVector e T‖) /
          (r : Real) := by ring
  have hrle : (r : Real) ≤
      (6912 : Real) * ‖affineImageAxisVector e T‖ := by
    simpa only [one_mul] using (le_div_iff₀ hrReal).mp hinv'
  have hsourceLower : (r : Real) / 6912 ≤
      ‖affineImageAxisVector e T‖ := by
    apply (div_le_iff₀ (by norm_num : (0 : Real) < 6912)).2
    simpa [mul_comm] using hrle
  have huPos : (0 : Real) < (u : Real) := by
    exact_mod_cast sideShapeUpper_pos label 2
  have hvector : affineImageAxisVector d T =
      (u : Real)⁻¹ • affineImageAxisVector e T := by
    unfold d bucketNormalizedAffineEquiv affineImageAxisVector
    simp only [AffineEquiv.trans_apply, scalarDilationAffineEquiv_apply]
    module
  rw [hvector, norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr huPos)]
  change (r : Real) / (6912 * (u : Real)) ≤
    (u : Real)⁻¹ * ‖affineImageAxisVector e T‖
  calc
    (r : Real) / (6912 * (u : Real)) =
        (u : Real)⁻¹ * ((r : Real) / 6912) := by
      field_simp [huPos.ne']
    _ ≤ (u : Real)⁻¹ * ‖affineImageAxisVector e T‖ := by
      exact mul_le_mul_of_nonneg_left hsourceLower (by positivity)

#print axioms selectedPlankFine_bucketAffineImageAxisVector_norm_lower

end
end Family8SelectedParentPlankFineAxisLengthLowerV3
