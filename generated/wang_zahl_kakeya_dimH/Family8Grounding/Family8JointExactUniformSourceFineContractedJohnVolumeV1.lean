import Family8Grounding.Family8JointExactUniformSourceFineContractedJohnV2
import Family8Grounding.Family8ActualFamilyVolumePackingV1
import Mathlib.Tactic

/-!
# Actual-volume envelope for the exact Joint contracted-John fibre

Any selected subfamily produced by the contracted-John endpoint has actual
summed volume at most its cardinality times the uniform tube-volume upper
bound.  Exact uniformity then replaces that cardinality by the same
`P.branching` used in Equation (46).  This is an ordinary volume envelope;
it deliberately introduces no aspect-ratio gain.
-/

open Set MeasureTheory
open scoped BigOperators ENNReal NNReal

namespace Family8JointExactUniformSourceFineContractedJohnVolumeV1

open LeanEval.Analysis.WangZahlKakeya
open Submission.Kakeya.ConvexGeometry
open Submission.Kakeya.ConvexFactoring
open Submission.Kakeya.Uniformity
open Family8KatzTaoFrostmanPropertiesV1
open Family8GeneralizedKatzTaoMultiplicityV1
open Family8FiniteRandomRigidMotionB2NormalizedDatumV1
open Family8ContractedJohnActualTubeProxyV1
open Family8StickyFiberContractedJohnProxyDatumV1
open Family8CoarseTubePartitionExactUniformStickyFiberV4
open Family8CoarseTubePartitionExactUniformStickyFiberV8
open Family8ActualFamilyVolumePackingV1

noncomputable section

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 3000000
set_option linter.unusedSectionVars false

variable {delta rho : NNReal} {iota : Type} {coarseCard : Nat}
  [Fintype iota] [DecidableEq iota]
  {fine : UniformTubeFamily delta iota}
  {coarse : UniformTubeFamily rho (Fin coarseCard)}

/-- The actual selected normalized-proxy volume is bounded by the exact
common Joint fibre count times the literal upper tube-volume constant. -/
theorem selectedProxy_actualFamilyVolume_le_branching_mul_eight_sq
    (P : CoarseTubePartition fine coarse)
    (hloss : P.branchingLoss = 1)
    (Y : Shading fine.bodyFamily)
    (hdeltaRho : delta ≤ rho)
    (hrho : 0 < rho) (hrhoOne : rho ≤ 1)
    (k : {k // k ∈ P.coarseIndices})
    (selected : Finset
      {i // i ∈ (exactPartitionStickyCover P).fiber k.1}) :
    (restrictActualTubeDatum
      (eighthNormalizedDatum
        (stickyFiberContractedJohnProxyDatum
          (exactPartitionStickyCover P) Y hrho hrhoOne k))
      selected).actualFamilyVolume ≤
        (P.branching : ENNReal) *
          (8 * (((contractedJohnProxyRadius delta rho / 8 : NNReal) :
            ENNReal) ^ 2)) := by
  let Dproxy := stickyFiberContractedJohnProxyDatum
    (exactPartitionStickyCover P) Y hrho hrhoOne k
  let scale : NNReal := contractedJohnProxyRadius delta rho / 8
  have hproxyHalf : contractedJohnProxyRadius delta rho ≤ (2 : NNReal)⁻¹ :=
    stickyFiberContractedJohnProxyDatum_delta_le_half hdeltaRho hrho
  have hscaleHalf : scale ≤ (2 : NNReal)⁻¹ := by
    dsimp only [scale]
    calc
      contractedJohnProxyRadius delta rho / 8 ≤
          (2 : NNReal)⁻¹ / 8 := by gcongr
      _ ≤ (2 : NNReal)⁻¹ := by
        rw [← NNReal.coe_le_coe]
        norm_num
  have hvolume := actualFamilyVolume_le_card_mul_eight_sq
    (restrictActualTubeDatum (eighthNormalizedDatum Dproxy) selected)
      hscaleHalf
  have hselectedCard : selected.card ≤ P.branching := by
    calc
      selected.card ≤
          Fintype.card
            {i // i ∈ (exactPartitionStickyCover P).fiber k.1} :=
        Finset.card_le_univ selected
      _ = P.branching :=
        exactPartitionStickyCover_fiber_fintypeCard_eq_branching
          P hloss k.1 k.2
  have hselectedCardENN : (selected.card : ENNReal) ≤ P.branching := by
    exact_mod_cast hselectedCard
  calc
    (restrictActualTubeDatum
        (eighthNormalizedDatum
          (stickyFiberContractedJohnProxyDatum
            (exactPartitionStickyCover P) Y hrho hrhoOne k))
        selected).actualFamilyVolume ≤
      (selected.card : ENNReal) * (8 * (scale : ENNReal) ^ 2) := by
        simpa only [Dproxy, scale, Fintype.card_coe] using hvolume
    _ ≤ (P.branching : ENNReal) * (8 * (scale : ENNReal) ^ 2) :=
      mul_le_mul' hselectedCardENN le_rfl
    _ = (P.branching : ENNReal) *
        (8 * (((contractedJohnProxyRadius delta rho / 8 : NNReal) :
          ENNReal) ^ 2)) := by rfl

#print axioms selectedProxy_actualFamilyVolume_le_branching_mul_eight_sq

end
end Family8JointExactUniformSourceFineContractedJohnVolumeV1
