import Family8Grounding.Family8PolynomialJohnFrameBoxPerturbationCoreV4

set_option autoImplicit false
set_option warningAsError true
set_option linter.unusedSectionVars false
set_option maxHeartbeats 2000000

open Set
open scoped NNReal InnerProductSpace

namespace Family8PolynomialJohnFrameBoxContainmentV1

open LeanEval.Analysis.WangZahlKakeya
open Submission.Kakeya.ConvexGeometry
open TransverseCoordinateOverlap
open Family8PolynomialJohnFrameBoxTestNetV1
open Family8PolynomialJohnFrameBoxPerturbationCoreV4

noncomputable section

/-!
# Same-cell containment for the polynomial John-box catalogue

The representative retains a genuine orthonormal frame.  The three center,
nine frame, and three side coordinates are each within `delta/20` of the
source.  The two perturbation errors are respectively `< 6 mesh` and
`< 3 mesh`; the side lower bound `2 delta <= side` then leaves enough room
inside the factor-two representative box.
-/

theorem representative_inner_decomposition
    {delta : NNReal} (p r : CapturedJohnParameter delta)
    (x : Space) (i : Fin 3) :
    ⟪r.certificate.box.frame i, x⟫_Real -
        ⟪r.certificate.box.frame i, r.certificate.box.center⟫_Real =
      (⟪p.certificate.box.frame i, x⟫_Real -
        ⟪p.certificate.box.frame i, p.certificate.box.center⟫_Real) +
      ⟪r.certificate.box.frame i - p.certificate.box.frame i,
        x - p.certificate.box.center⟫_Real +
      ⟪r.certificate.box.frame i,
        p.certificate.box.center - r.certificate.box.center⟫_Real := by
  simp only [inner_sub_left, inner_sub_right]
  ring

/-- The entire clipped source body lies in the factor-two box indexed by its
own occupied floor cell. -/
theorem parameter_body_subset_representativeTestBox
    {delta : NNReal} (hdelta : 0 < delta)
    (p : CapturedJohnParameter delta) :
    (p.body : Set Space) ⊆
      (representativeTestBox delta hdelta (parameterCode hdelta p)).carrier := by
  let r := representativeParameter delta hdelta (parameterCode hdelta p)
  intro x hx
  change x ∈ (r.certificate.box.rescale 2).carrier
  apply FrameBox.centeredCoordinateWindow_subset_carrier
  rw [mem_centeredCoordinateWindow_iff]
  intro i
  have hxUnit : x ∈ Metric.closedBall (0 : Space) 1 :=
    p.body_subset_unitBall hx
  have hxBox : x ∈ p.certificate.box.carrier := by
    exact p.certificate.outer_le hx
  have hpcoord :=
    p.certificate.box.centeredCoordinate_abs_le_halfSide hxBox i
  rw [congrFun p.certificate.side_eq i] at hpcoord
  have hframe :
      |⟪r.certificate.box.frame i - p.certificate.box.frame i,
          x - p.certificate.box.center⟫_Real| <
        6 * parameterMesh delta := by
    simpa only [r] using frame_error_inner_lt_six_mesh hdelta p i hxUnit
  have hcenter :
      |⟪r.certificate.box.frame i,
          p.certificate.box.center - r.certificate.box.center⟫_Real| <
        3 * parameterMesh delta := by
    simpa only [r] using center_error_inner_lt_three_mesh hdelta p i
  have hdecomp := representative_inner_decomposition p r x i
  have hsum :
      |⟪r.certificate.box.frame i, x⟫_Real -
          ⟪r.certificate.box.frame i, r.certificate.box.center⟫_Real| <
        (p.side i : Real) / 2 + 9 * parameterMesh delta := by
    calc
      |⟪r.certificate.box.frame i, x⟫_Real -
          ⟪r.certificate.box.frame i, r.certificate.box.center⟫_Real| =
          |(⟪p.certificate.box.frame i, x⟫_Real -
              ⟪p.certificate.box.frame i,
                p.certificate.box.center⟫_Real) +
            ⟪r.certificate.box.frame i - p.certificate.box.frame i,
              x - p.certificate.box.center⟫_Real +
            ⟪r.certificate.box.frame i,
              p.certificate.box.center -
                r.certificate.box.center⟫_Real| := congrArg abs hdecomp
      _ ≤ |⟪p.certificate.box.frame i, x⟫_Real -
              ⟪p.certificate.box.frame i,
                p.certificate.box.center⟫_Real| +
            |⟪r.certificate.box.frame i - p.certificate.box.frame i,
              x - p.certificate.box.center⟫_Real| +
            |⟪r.certificate.box.frame i,
              p.certificate.box.center -
                r.certificate.box.center⟫_Real| := abs_add_three _ _ _
      _ < (p.side i : Real) / 2 + 9 * parameterMesh delta := by
        linarith
  have hsideClose := side_coordinate_close hdelta p i
  change |(p.side i : Real) - (r.side i : Real)| <
    parameterMesh delta at hsideClose
  have hdiff :
      (p.side i : Real) - (r.side i : Real) < parameterMesh delta :=
    (le_abs_self ((p.side i : Real) - (r.side i : Real))).trans_lt hsideClose
  have hlowerNN : 2 * delta ≤ r.side i := r.two_mul_delta_le_side i
  have hlower : 2 * (delta : Real) ≤ (r.side i : Real) := by
    exact_mod_cast hlowerNN
  have hdeltaReal : 0 < (delta : Real) := NNReal.coe_pos.2 hdelta
  have hnumeric :
      (p.side i : Real) / 2 + 9 * parameterMesh delta <
        (r.side i : Real) := by
    dsimp only [parameterMesh] at hdiff ⊢
    linarith
  have hfinal :
      |⟪r.certificate.box.frame i, x⟫_Real -
          ⟪r.certificate.box.frame i, r.certificate.box.center⟫_Real| ≤
        (r.certificate.box.side i : Real) := by
    rw [congrFun r.certificate.side_eq i]
    exact le_of_lt (hsum.trans hnumeric)
  simp only [FrameBox.rescale_frame, FrameBox.coordinateCenter,
    FrameBox.rescale_center, FrameBox.coordinateHalf,
    FrameBox.rescale_side, NNReal.coe_div, NNReal.coe_mul]
  convert hfinal using 1
  norm_num

theorem parameter_body_subset_representativeTestBody
    {delta : NNReal} (hdelta : 0 < delta)
    (p : CapturedJohnParameter delta) :
    (p.body : Set Space) ⊆
      (representativeTestBody delta hdelta (parameterCode hdelta p) :
        Set Space) := by
  simpa only [representativeTestBody, FrameBox.coe_body] using
    parameter_body_subset_representativeTestBox hdelta p

/-- Every tube contained in a clipped source parameter is contained in its
single polynomial-catalogue test. -/
theorem tube_subset_representativeTestBody
    {delta : NNReal} (hdelta : 0 < delta)
    (p : CapturedJohnParameter delta) (T : Tube delta)
    (hT : T.carrier ⊆ (p.body : Set Space)) :
    T.carrier ⊆
      (representativeTestBody delta hdelta (parameterCode hdelta p) :
        Set Space) :=
  hT.trans (parameter_body_subset_representativeTestBody hdelta p)

#print axioms representative_inner_decomposition
#print axioms parameter_body_subset_representativeTestBox
#print axioms parameter_body_subset_representativeTestBody
#print axioms tube_subset_representativeTestBody

end
end Family8PolynomialJohnFrameBoxContainmentV1
