import Family8Grounding.Family8CertifiedPlankPairOverlapV2
import Family8Grounding.Family8ContractedJohnActualTubeProxyV1
import Family8Grounding.Family8ThinPlankFiveParameterFrameBoxPackingV4
import Mathlib.Tactic

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 5000000

open Set
open scoped NNReal InnerProductSpace BigOperators

namespace Family8AffineImageAxisPlankCoordinateBridgeV4

open LeanEval.Analysis.WangZahlKakeya
open Submission.Kakeya.ConvexGeometry
open Family8CertifiedPlankPairOverlapV2
open Family8ContractedJohnActualTubeProxyV1
open Family8ThinPlankFiveParameterFrameBoxPackingV4

noncomputable section

/-! Real affine-axis coordinates inside an actual certified plank. -/

theorem affineImageAxisCenter_mem_frameBox
    {delta : NNReal} (e : Space ≃ᵃ[Real] Space) (T : Tube delta)
    (B : FrameBox)
    (hbase : e T.axis.base ∈ B.carrier)
    (hend : e T.axis.endpoint ∈ B.carrier) :
    affineImageAxisCenter e T ∈ B.carrier := by
  have hmid := B.convex_carrier hbase hend
      (a := (1 / 2 : Real)) (b := (1 / 2 : Real))
      (by norm_num) (by norm_num) (by norm_num)
  simpa only [affineImageAxisCenter, smul_add] using hmid

theorem abs_inner_affineImageAxisVector_le_frameBox_side
    {delta : NNReal} (e : Space ≃ᵃ[Real] Space) (T : Tube delta)
    (B : FrameBox)
    (hbase : e T.axis.base ∈ B.carrier)
    (hend : e T.axis.endpoint ∈ B.carrier) (i : Fin 3) :
    |⟪B.frame i, affineImageAxisVector e T⟫_Real| ≤ (B.side i : Real) := by
  have hb := B.centeredCoordinate_abs_le_halfSide hbase i
  have he := B.centeredCoordinate_abs_le_halfSide hend i
  have htriangle :
      |⟪B.frame i, e T.axis.endpoint⟫_Real -
          ⟪B.frame i, e T.axis.base⟫_Real| ≤
        |⟪B.frame i, e T.axis.endpoint⟫_Real -
            ⟪B.frame i, B.center⟫_Real| +
          |⟪B.frame i, e T.axis.base⟫_Real -
            ⟪B.frame i, B.center⟫_Real| := by
    calc
      _ ≤ |⟪B.frame i, e T.axis.endpoint⟫_Real -
              ⟪B.frame i, B.center⟫_Real| +
            |⟪B.frame i, B.center⟫_Real -
              ⟪B.frame i, e T.axis.base⟫_Real| := abs_sub_le _ _ _
      _ = _ := by rw [abs_sub_comm
        (⟪B.frame i, B.center⟫_Real)
        (⟪B.frame i, e T.axis.base⟫_Real)]
  change |⟪B.frame i, e T.axis.endpoint - e T.axis.base⟫_Real| ≤ _
  rw [inner_sub_right]
  exact htriangle.trans (by nlinarith [hb, he])

/-- If the real affine image axis lies in an actual `a × b × 1` plank, its
chosen outer frame supplies exact midpoint and raw-vector coordinate bounds.
No containment of the artificial unit extension is asserted. -/
theorem exists_frameBox_affineImageAxis_bounds_of_isPlank
    {delta C a b : NNReal} {K : ConvexBody Space}
    (e : Space ≃ᵃ[Real] Space) (T : Tube delta)
    (hplank : IsPlank C a b K)
    (haxis : e '' T.axis.carrier ⊆ (K : Set Space)) :
    ∃ B : FrameBox,
      B.side = plankSides a b ∧
      affineImageAxisCenter e T ∈ B.carrier ∧
      ‖affineImageAxisCenter e T - B.center‖ ≤ 2 ∧
      |⟪B.frame 0, affineImageAxisCenter e T - B.center⟫_Real| ≤
        (a : Real) / 2 ∧
      |⟪B.frame 1, affineImageAxisCenter e T - B.center⟫_Real| ≤
        (b : Real) / 2 ∧
      |⟪B.frame 0, affineImageAxisVector e T⟫_Real| ≤ (a : Real) ∧
      |⟪B.frame 1, affineImageAxisVector e T⟫_Real| ≤ (b : Real) := by
  let cert : PlankDimensionsCertificate C a b K :=
    Classical.choice
      (Family8CertifiedPlankPairOverlapV2.IsPlank.nonempty_plankDimensionsCertificate
        hplank)
  have hbaseK : e T.axis.base ∈ (K : Set Space) :=
    haxis ⟨T.axis.base, T.axis.base_mem_carrier, rfl⟩
  have hendK : e T.axis.endpoint ∈ (K : Set Space) :=
    haxis ⟨T.axis.endpoint, T.axis.endpoint_mem_carrier, rfl⟩
  have hbase : e T.axis.base ∈ cert.box.carrier := cert.outer_le hbaseK
  have hend : e T.axis.endpoint ∈ cert.box.carrier := cert.outer_le hendK
  have hcenter : affineImageAxisCenter e T ∈ cert.box.carrier :=
    affineImageAxisCenter_mem_frameBox e T cert.box hbase hend
  have haOne : a ≤ 1 := cert.a_le_b.trans cert.b_le_one
  have haReal : (a : Real) ≤ 1 := by exact_mod_cast haOne
  have hbReal : (b : Real) ≤ 1 := by exact_mod_cast cert.b_le_one
  have hsumReal : ((∑ i, cert.box.side i : NNReal) : Real) ≤ 4 := by
    rw [cert.side_eq, Fin.sum_univ_three]
    simp only [plankSides, Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons, Fin.isValue]
    norm_num only [NNReal.coe_add, NNReal.coe_one]
    linarith
  have hnorm : ‖affineImageAxisCenter e T - cert.box.center‖ ≤ 2 := by
    have hdist := frameBox_dist_center_le_half_sum_side cert.box hcenter
    rw [dist_eq_norm] at hdist
    exact hdist.trans (by nlinarith)
  have hcenter0 := cert.box.centeredCoordinate_abs_le_halfSide hcenter 0
  have hcenter1 := cert.box.centeredCoordinate_abs_le_halfSide hcenter 1
  have hvec0 := abs_inner_affineImageAxisVector_le_frameBox_side
    e T cert.box hbase hend 0
  have hvec1 := abs_inner_affineImageAxisVector_le_frameBox_side
    e T cert.box hbase hend 1
  refine ⟨cert.box, cert.side_eq, hcenter, hnorm, ?_, ?_, ?_, ?_⟩
  · rw [cert.side_eq] at hcenter0
    simpa [inner_sub_right, plankSides] using hcenter0
  · rw [cert.side_eq] at hcenter1
    simpa [inner_sub_right, plankSides] using hcenter1
  · rw [cert.side_eq] at hvec0
    simpa [plankSides] using hvec0
  · rw [cert.side_eq] at hvec1
    simpa [plankSides] using hvec1

#print axioms affineImageAxisCenter_mem_frameBox
#print axioms abs_inner_affineImageAxisVector_le_frameBox_side
#print axioms exists_frameBox_affineImageAxis_bounds_of_isPlank

end
end Family8AffineImageAxisPlankCoordinateBridgeV4
