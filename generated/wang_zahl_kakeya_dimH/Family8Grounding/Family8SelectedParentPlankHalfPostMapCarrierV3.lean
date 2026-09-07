import Family8Grounding.Family8SelectedParentPlankHalfPostMapCarrierV2
import Family8Grounding.Family8SelectedParentPlankCanonicalThinCountV5
import Mathlib.Tactic

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 5000000

open Set
open scoped NNReal InnerProductSpace BigOperators

namespace Family8SelectedParentPlankHalfPostMapCarrierV3

open LeanEval.Analysis.WangZahlKakeya
open Submission.Kakeya.ConvexGeometry
open Submission.Kakeya.ConvexFactoring
open Submission.Kakeya.Uniformity
open Family8AffineImageAxisPlankCoordinateBridgeV4
open Family8ContractedJohnActualTubeProxyV1
open Family8SelectedParentCertifiedPlankCordobaConnectorV3
open Family8SelectedParentJohnPlankSideWidthBridgeV7
open Family8SelectedParentJohnPlankSideWidthBridgeV8
open Family8SelectedParentPlankFineAxisCoordinateV2
open Family8SelectedParentPlankFineProxyCarrierV3
open Family8SelectedParentPlankFineProxyDatumV1
open Family8SelectedParentPlankHalfPostMapCarrierV2
open Family8StickySelectedParentGreedyBlockFrostmanV3
open FamilyStickyAtEveryScaleCoreV1

noncomputable section

variable {delta rho : NNReal} {index : Type}
  [Fintype index] [DecidableEq index]
  {fine : UniformTubeFamily delta index}

/-- Both mapped endpoints lie in the chosen `(a,b,1)` box, hence Parseval
gives the uniform upper length two. -/
theorem selectedPlankFine_bucketAffineImageAxisVector_norm_le_two
    (e : Space ≃ᵃ[Real] Space) (S : StickyScaleCover fine rho)
    (B : Finset (ActiveParentIndex S)) (hrho : 0 < rho)
    (label : Fin 3 → Int)
    (hplank : ∀ W :
      {p // p ∈ selectedParentPlankBucketIndices e S B hrho label},
      IsPlank 576 (bucketShortA label) (bucketShortB label)
        (selectedParentPlankBucketFamily e S B hrho label W))
    (W : {p // p ∈ selectedParentPlankBucketIndices e S B hrho label})
    (i : SelectedPlankFineIndex S W) :
    ‖affineImageAxisVector (bucketNormalizedAffineEquiv e label)
        (fine.tubes i.1)‖ ≤ 2 := by
  let d := bucketNormalizedAffineEquiv e label
  let cert := chosenPlankCertificate hplank W
  let T := fine.tubes i.1
  let v := affineImageAxisVector d T
  have h01 := selectedPlankFine_rawVector_chosenFrame_bounds
    e S B hrho label hplank W i
  have haxis := selectedPlankFine_axis_image_subset_parent
    e S B hrho label W i
  have hbaseK : d T.axis.base ∈
      (selectedParentPlankBucketFamily e S B hrho label W : Set Space) :=
    haxis ⟨T.axis.base, T.axis.base_mem_carrier, rfl⟩
  have hendK : d T.axis.endpoint ∈
      (selectedParentPlankBucketFamily e S B hrho label W : Set Space) :=
    haxis ⟨T.axis.endpoint, T.axis.endpoint_mem_carrier, rfl⟩
  have hbase : d T.axis.base ∈ cert.box.carrier := cert.outer_le hbaseK
  have hend : d T.axis.endpoint ∈ cert.box.carrier := cert.outer_le hendK
  have h2raw := abs_inner_affineImageAxisVector_le_frameBox_side
    d T cert.box hbase hend 2
  rw [cert.side_eq] at h2raw
  have h2 : |⟪cert.box.frame 2, v⟫_Real| ≤ (1 : Real) := by
    simpa only [v, plankSides, Matrix.cons_val_two,
      Matrix.tail_cons, Matrix.head_cons, NNReal.coe_one] using h2raw
  have haOne : (bucketShortA label : Real) ≤ 1 := by
    exact_mod_cast cert.a_le_b.trans cert.b_le_one
  have hbOne : (bucketShortB label : Real) ≤ 1 := by
    exact_mod_cast cert.b_le_one
  have h0 : |⟪cert.box.frame 0, v⟫_Real| ≤ (1 : Real) :=
    h01.1.trans haOne
  have h1 : |⟪cert.box.frame 1, v⟫_Real| ≤ (1 : Real) :=
    h01.2.trans hbOne
  let c0 : Real := ⟪cert.box.frame 0, v⟫_Real
  let c1 : Real := ⟪cert.box.frame 1, v⟫_Real
  let c2 : Real := ⟪cert.box.frame 2, v⟫_Real
  have hc0 : c0 ^ 2 ≤ 1 := by
    have hb := abs_le.mp h0
    have hp : 0 ≤ (1 - c0) * (1 + c0) :=
      mul_nonneg (by linarith) (by linarith)
    nlinarith
  have hc1 : c1 ^ 2 ≤ 1 := by
    have hb := abs_le.mp h1
    have hp : 0 ≤ (1 - c1) * (1 + c1) :=
      mul_nonneg (by linarith) (by linarith)
    nlinarith
  have hc2 : c2 ^ 2 ≤ 1 := by
    have hb := abs_le.mp h2
    have hp : 0 ≤ (1 - c2) * (1 + c2) :=
      mul_nonneg (by linarith) (by linarith)
    nlinarith
  have hparseval := cert.box.frame.sum_sq_inner_right v
  rw [Fin.sum_univ_three] at hparseval
  change c0 ^ 2 + c1 ^ 2 + c2 ^ 2 = ‖v‖ ^ 2 at hparseval
  have hv : ‖v‖ ≤ (2 : Real) := by
    by_contra hn
    have hn' : (2 : Real) < ‖v‖ := lt_of_not_ge hn
    nlinarith [norm_nonneg v]
  simpa only [d, T, v] using hv

/-- The post-half map automatically fits every actual same-`W` image axis
inside the unit extension, with no length callback. -/
theorem selectedPlankFine_halfPost_axisVector_norm_le_one
    (e : Space ≃ᵃ[Real] Space) (S : StickyScaleCover fine rho)
    (B : Finset (ActiveParentIndex S)) (hrho : 0 < rho)
    (label : Fin 3 → Int)
    (hplank : ∀ W :
      {p // p ∈ selectedParentPlankBucketIndices e S B hrho label},
      IsPlank 576 (bucketShortA label) (bucketShortB label)
        (selectedParentPlankBucketFamily e S B hrho label W))
    (W : {p // p ∈ selectedParentPlankBucketIndices e S B hrho label})
    (i : SelectedPlankFineIndex S W) :
    ‖affineImageAxisVector (halfPostBucketAffineEquiv e label)
        (fine.tubes i.1)‖ ≤ 1 := by
  rw [norm_affineImageAxisVector_halfPostBucketAffineEquiv]
  have h := selectedPlankFine_bucketAffineImageAxisVector_norm_le_two
    e S B hrho label hplank W i
  nlinarith

/-- Literal half-post proxy family on the original selected bucket subtype. -/
noncomputable def halfPostSelectedPlankFineProxyFamily
    (s : NNReal) (e : Space ≃ᵃ[Real] Space)
    (S : StickyScaleCover fine rho) (B : Finset (ActiveParentIndex S))
    (hrho : 0 < rho) (label : Fin 3 → Int)
    (W : {p // p ∈ selectedParentPlankBucketIndices e S B hrho label}) :
    UniformTubeFamily s (SelectedPlankFineIndex S W) where
  tubes i := affineAxisProxyTube s (halfPostBucketAffineEquiv e label)
    (fine.tubes i.1)
  refinement := UniformRefinement.ofFinset Finset.univ

@[simp] theorem halfPostSelectedPlankFineProxyFamily_tubes
    (s : NNReal) (e : Space ≃ᵃ[Real] Space)
    (S : StickyScaleCover fine rho) (B : Finset (ActiveParentIndex S))
    (hrho : 0 < rho) (label : Fin 3 → Int)
    (W : {p // p ∈ selectedParentPlankBucketIndices e S B hrho label})
    (i : SelectedPlankFineIndex S W) :
    (halfPostSelectedPlankFineProxyFamily s e S B hrho label W).tubes i =
      affineAxisProxyTube s (halfPostBucketAffineEquiv e label)
        (fine.tubes i.1) := rfl

/-- The only remaining carrier condition is the explicit transverse-radius
budget for the halved map. -/
theorem halfPost_image_tubeCarrier_subset_proxy
    (s : NNReal) (e : Space ≃ᵃ[Real] Space)
    (S : StickyScaleCover fine rho) (B : Finset (ActiveParentIndex S))
    (hrho : 0 < rho) (label : Fin 3 → Int)
    (hplank : ∀ W :
      {p // p ∈ selectedParentPlankBucketIndices e S B hrho label},
      IsPlank 576 (bucketShortA label) (bucketShortB label)
        (selectedParentPlankBucketFamily e S B hrho label W))
    (W : {p // p ∈ selectedParentPlankBucketIndices e S B hrho label})
    (hradius : affineLinearOperatorNorm
      (halfPostBucketAffineEquiv e label) * (delta : Real) ≤ (s : Real))
    (i : SelectedPlankFineIndex S W) :
    halfPostBucketAffineEquiv e label '' (fine.tubes i.1).carrier ⊆
      (halfPostSelectedPlankFineProxyFamily
        s e S B hrho label W).bodyFamily i := by
  exact image_tubeCarrier_subset_affineAxisProxyTube
    (halfPostBucketAffineEquiv e label) (fine.tubes i.1)
      (selectedPlankFine_halfPost_axisVector_norm_le_one
        e S B hrho label hplank W i) hradius

#print axioms selectedPlankFine_bucketAffineImageAxisVector_norm_le_two
#print axioms selectedPlankFine_halfPost_axisVector_norm_le_one
#print axioms halfPostSelectedPlankFineProxyFamily
#print axioms halfPost_image_tubeCarrier_subset_proxy

end
end Family8SelectedParentPlankHalfPostMapCarrierV3
