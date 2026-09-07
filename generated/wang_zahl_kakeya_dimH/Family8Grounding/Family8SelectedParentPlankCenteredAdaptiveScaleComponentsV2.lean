import Family8Grounding.Family8SelectedParentPlankCenteredAdaptiveGeometricLossPowerV2
import Mathlib.Tactic

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 5000000

open Set MeasureTheory
open scoped ENNReal NNReal BigOperators

namespace Family8SelectedParentPlankCenteredAdaptiveScaleComponentsV2

open LeanEval.Analysis.WangZahlKakeya
open Submission.Kakeya.ConvexGeometry
open Submission.Kakeya.ConvexFactoring
open Submission.Kakeya.ConvexFactoring.FullConvexMaximalDensity
open Submission.Kakeya.ConvexFactoring.GreedyOccurrenceFactorization
open Submission.Kakeya.Uniformity
open Family8ContractedJohnActualTubeProxyV1
open Family8SelectedParentAffineShadingTransportV4
open Family8SelectedParentCertifiedPlankCordobaConnectorV3
open Family8SelectedParentJohnFrameNormalizationV9
open Family8SelectedParentJohnPlankQuantitativeLossV9
open Family8SelectedParentJohnPlankSideWidthBridgeV5
open Family8SelectedParentJohnPlankSideWidthBridgeV7
open Family8SelectedParentJohnPlankSideWidthBridgeV8
open Family8SelectedParentPlankCenteredAdaptiveGeometricLossPowerV2
open Family8SelectedParentPlankCenteredHalfPostAdaptiveScalePackingV1
open Family8StickySelectedParentGreedyBlockFrostmanV3
open FamilyStickyAtEveryScaleCoreV1

noncomputable section

/-!
# Callback-free component bounds for the Family 8 adaptive proxy scale

The coarse selected parent contains a unit axis.  The inverse Lipschitz
estimate for the common contracted John map therefore forces the longest
side of every actual memberwise John certificate to be at least a fixed
multiple of `r`.  This removes one spurious factor of `rho` from the radius
floor: its true bound is `31104 * delta / rho`, rather than an estimate of
order `delta / rho^2` obtained from volume alone.
-/

variable {delta rho : NNReal} {index : Type}
  [Fintype index] [DecidableEq index]
  {fine : UniformTubeFamily delta index}

/-- A selected coarse parent's longest relabeled John side cannot collapse:
the parent contains a unit axis and the common contracted John map has
inverse Lipschitz constant `6912 / r`. -/
theorem selectedParentContractedLongRelabeledSide_two_lower
    (hfineContained : ∀ i, (fine.tubes i).carrier ⊆
      Metric.closedBall (0 : Space) 1)
    (S : StickyScaleCover fine rho) (hrho : 0 < rho) (hrhoOne : rho ≤ 1)
    (P : GreedyDensityPartition S.activeCoarseFamily
      (hullCandidates (Finset.univ : Finset (ActiveParentIndex S)))
      (hullContainer S.activeCoarseFamily) Finset.univ)
    (k : Fin (blocks S.activeCoarseFamily P).length)
    (r : NNReal) (hr : 0 < r)
    (p : {p // p ∈ (blockAt S.activeCoarseFamily P k).fiber}) :
    r / 41472 ≤
      selectedParentLongRelabeledSide
        (contractedJohnAffineEquiv
          (selectedParentGreedyBlockJohnFrame S hrho P k) r hr)
        S (blockAt S.activeCoarseFamily P k).fiber hrho p 2 := by
  let J := selectedParentGreedyBlockJohnFrame S hrho P k
  let e := contractedJohnAffineEquiv J r hr
  let B := (blockAt S.activeCoarseFamily P k).fiber
  let T := S.coarse.tubes p.1.1
  let side := selectedParentLongRelabeledSide e S B hrho p
  let cert := selectedParentLongRelabeledCertificate e S B hrho p
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
  rw [hcoeff] at hinv
  have hrReal : (0 : Real) < (r : Real) := by exact_mod_cast hr
  have hinv' : (1 : Real) ≤
      ((6912 : Real) * dist (e T.axis.endpoint) (e T.axis.base)) /
        (r : Real) := by
    calc
      (1 : Real) ≤ (6912 : Real) / (r : Real) *
          dist (e T.axis.endpoint) (e T.axis.base) := hinv
      _ = ((6912 : Real) * dist (e T.axis.endpoint) (e T.axis.base)) /
          (r : Real) := by ring
  have hrle : (r : Real) ≤
      (6912 : Real) * dist (e T.axis.endpoint) (e T.axis.base) := by
    simpa only [one_mul] using (le_div_iff₀ hrReal).mp hinv'
  have hsourceLower : (r : Real) / 6912 ≤
      dist (e T.axis.endpoint) (e T.axis.base) := by
    apply (div_le_iff₀ (by norm_num : (0 : Real) < 6912)).2
    simpa [mul_comm] using hrle
  have hbaseK : e T.axis.base ∈
      (selectedParentAffineFamily e S B p : Set Space) := by
    rw [selectedParentAffineFamily_apply]
    exact ⟨T.axis.base,
      T.axis_subset_carrier T.axis.base_mem_carrier, rfl⟩
  have hendK : e T.axis.endpoint ∈
      (selectedParentAffineFamily e S B p : Set Space) := by
    rw [selectedParentAffineFamily_apply]
    exact ⟨T.axis.endpoint,
      T.axis_subset_carrier T.axis.endpoint_mem_carrier, rfl⟩
  have hbaseBox : e T.axis.base ∈ cert.box.carrier := cert.outer_le hbaseK
  have hendBox : e T.axis.endpoint ∈ cert.box.carrier := cert.outer_le hendK
  have hdist := cert.box.dist_le_diameterBound hendBox hbaseBox
  have h0 := selectedParentLongRelabeledSide_le_two e S B hrho p 0
  have h1 := selectedParentLongRelabeledSide_le_two e S B hrho p 1
  have h0Real : (side 0 : Real) ≤ (side 2 : Real) := by
    exact_mod_cast h0
  have h1Real : (side 1 : Real) ≤ (side 2 : Real) := by
    exact_mod_cast h1
  have hdiam : (cert.box.diameterBound : Real) ≤ 6 * (side 2 : Real) := by
    rw [FrameBox.diameterBound, cert.side_eq, Fin.sum_univ_three]
    norm_num only [NNReal.coe_mul, NNReal.coe_add, NNReal.coe_ofNat]
    linarith
  have hlongReal : (r : Real) / 41472 ≤ (side 2 : Real) := by
    calc
      (r : Real) / 41472 = ((r : Real) / 6912) / 6 := by ring
      _ ≤ dist (e T.axis.endpoint) (e T.axis.base) / 6 := by gcongr
      _ ≤ (cert.box.diameterBound : Real) / 6 := by gcongr
      _ ≤ side 2 := by linarith
  exact_mod_cast hlongReal

#print axioms selectedParentContractedLongRelabeledSide_two_lower

end
end Family8SelectedParentPlankCenteredAdaptiveScaleComponentsV2
