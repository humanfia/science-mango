import Family8Grounding.Family8ThinPlankEssentialDistinctPackingV4
import Mathlib.Tactic

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 4000000

open Set
open scoped NNReal InnerProductSpace

namespace Family8ThinPlankFramePackingV2

open LeanEval.Analysis.WangZahlKakeya
open Submission.Kakeya.ConvexGeometry
open Family4GlobalExtremalUpstream
open Family8CommonPointTubePackingV1
open Family8PaperConflictWideAnisotropicOverlapV1
open Family8ThinPlankEssentialDistinctPackingV4
open FamilyStickyRandomFiniteFloorParameterNetV1

noncomputable section

/-!
# Frame-covariant quadratic thin-plank packing

This module removes the standard-coordinate convention from the audited
quadratic packing kernel.  Its coordinates are literal inner products with
an arbitrary orthonormal frame.  The isometric representation of that frame
transfers the coordinate estimates to the standard kernel, so no geometric
conclusion is postulated.
-/

/-- Four frame coordinates whose windows are independent of the aspect
ratio. -/
def thinPlankFrameFixedCoordinates {delta : NNReal}
    (frame : OrthonormalBasis (Fin 3) Real Space) (x : Space)
    (T : Tube delta) : Fin 4 -> Real :=
  ![tubePointLongitudinal x T,
    ⟪frame 0, tubePointTransverse x T⟫_Real / (delta : Real),
    ⟪frame 2, tubePointTransverse x T⟫_Real / (delta : Real),
    ⟪frame 0, T.axis.direction⟫_Real / (delta : Real)]

/-- The two frame coordinates whose windows grow with the aspect ratio. -/
def thinPlankFrameWideCoordinates {delta : NNReal}
    (frame : OrthonormalBasis (Fin 3) Real Space) (x : Space)
    (T : Tube delta) : Fin 2 -> Real :=
  ![⟪frame 1, tubePointTransverse x T⟫_Real / (delta : Real),
    ⟪frame 1, T.axis.direction⟫_Real / (delta : Real)]

/-- Equal split floor codes in an arbitrary orthonormal frame give physical,
not merely coordinate, anisotropic closeness. -/
theorem wide_anisotropic_close_of_thinPlankFrame_floorCodes_eq
    {delta : NNReal}
    (frame : OrthonormalBasis (Fin 3) Real Space)
    (x : Space) (T U : Tube delta)
    (hdeltaPos : 0 < delta)
    (hTForward : (1 : Real) / 2 <= ⟪frame 2, T.axis.direction⟫_Real)
    (hUForward : (1 : Real) / 2 <= ⟪frame 2, U.axis.direction⟫_Real)
    (hfixed :
      floorCode thinPlankPackingMesh
          (thinPlankFrameFixedCoordinates frame x) T =
        floorCode thinPlankPackingMesh
          (thinPlankFrameFixedCoordinates frame x) U)
    (hwide :
      floorCode thinPlankPackingMesh
          (thinPlankFrameWideCoordinates frame x) T =
        floorCode thinPlankPackingMesh
          (thinPlankFrameWideCoordinates frame x) U) :
    |tubePointLongitudinal x T - tubePointLongitudinal x U| <=
        (1 : Real) / 400 ∧
      dist (tubePointTransverse x T) (tubePointTransverse x U) <=
        (delta : Real) / 100 ∧
      dist T.axis.direction U.axis.direction <=
        (delta : Real) / 1000 := by
  have hmesh : 0 < thinPlankPackingMesh := by
    norm_num [thinPlankPackingMesh]
  have hdeltaReal : 0 < (delta : Real) := NNReal.coe_pos.mpr hdeltaPos
  have fixedClose (j : Fin 4) :=
    abs_coord_sub_lt_of_floorCode_eq hmesh
      (thinPlankFrameFixedCoordinates frame x) hfixed j
  have wideClose (j : Fin 2) :=
    abs_coord_sub_lt_of_floorCode_eq hmesh
      (thinPlankFrameWideCoordinates frame x) hwide j
  have hlong :
      |tubePointLongitudinal x T - tubePointLongitudinal x U| <
        (1 : Real) / 100000 := by
    simpa [thinPlankFrameFixedCoordinates, thinPlankPackingMesh] using
      fixedClose 0
  have normalized_to_physical {a b : Real}
      (h : |a / (delta : Real) - b / (delta : Real)| <
        (1 : Real) / 100000) :
      |a - b| < (delta : Real) / 100000 := by
    rw [<- sub_div, abs_div, abs_of_pos hdeltaReal] at h
    have hscaled := (div_lt_iff₀ hdeltaReal).mp h
    simpa only [div_eq_mul_inv, one_mul, mul_comm] using hscaled
  have he0 :
      |⟪frame 0, tubePointTransverse x T⟫_Real -
          ⟪frame 0, tubePointTransverse x U⟫_Real| <
        (delta : Real) / 100000 := by
    apply normalized_to_physical
    simpa [thinPlankFrameFixedCoordinates, thinPlankPackingMesh] using
      fixedClose 1
  have he2 :
      |⟪frame 2, tubePointTransverse x T⟫_Real -
          ⟪frame 2, tubePointTransverse x U⟫_Real| <
        (delta : Real) / 100000 := by
    apply normalized_to_physical
    simpa [thinPlankFrameFixedCoordinates, thinPlankPackingMesh] using
      fixedClose 2
  have hd0 :
      |⟪frame 0, T.axis.direction⟫_Real -
          ⟪frame 0, U.axis.direction⟫_Real| <
        (delta : Real) / 100000 := by
    apply normalized_to_physical
    simpa [thinPlankFrameFixedCoordinates, thinPlankPackingMesh] using
      fixedClose 3
  have he1 :
      |⟪frame 1, tubePointTransverse x T⟫_Real -
          ⟪frame 1, tubePointTransverse x U⟫_Real| <
        (delta : Real) / 100000 := by
    apply normalized_to_physical
    simpa [thinPlankFrameWideCoordinates, thinPlankPackingMesh] using
      wideClose 0
  have hd1 :
      |⟪frame 1, T.axis.direction⟫_Real -
          ⟪frame 1, U.axis.direction⟫_Real| <
        (delta : Real) / 100000 := by
    apply normalized_to_physical
    simpa [thinPlankFrameWideCoordinates, thinPlankPackingMesh] using
      wideClose 1
  let u : Space := frame.repr T.axis.direction
  let v : Space := frame.repr U.axis.direction
  have hu : ‖u‖ = 1 := by
    simpa only [u, frame.repr.norm_map] using T.axis.norm_direction
  have hv : ‖v‖ = 1 := by
    simpa only [v, frame.repr.norm_map] using U.axis.norm_direction
  have huForward : (1 : Real) / 2 <= u 2 := by
    simpa only [u, frame.repr_apply_apply] using hTForward
  have hvForward : (1 : Real) / 2 <= v 2 := by
    simpa only [v, frame.repr_apply_apply] using hUForward
  have hu0 : |u 0 - v 0| < (delta : Real) / 100000 := by
    simpa only [u, v, frame.repr_apply_apply] using hd0
  have hu1 : |u 1 - v 1| < (delta : Real) / 100000 := by
    simpa only [u, v, frame.repr_apply_apply] using hd1
  have hu2 : |u 2 - v 2| < (delta : Real) / 25000 := by
    have hthird := abs_third_sub_lt_four_mul_of_unit_forward
      hu hv huForward hvForward hu0 hu1
    convert hthird using 1
    all_goals ring
  refine ⟨hlong.le.trans (by norm_num), ?_, ?_⟩
  · let eT : Space := tubePointTransverse x T
    let eU : Space := tubePointTransverse x U
    have hrepr : dist (frame.repr eT) (frame.repr eU) <=
        (delta : Real) / 100 := by
      apply dist_le_delta_div_hundred_of_coordinate_close
      intro j
      fin_cases j
      · rw [frame.repr_apply_apply, frame.repr_apply_apply]
        dsimp only [eT, eU]
        exact he0.trans_le (by
          have hd : 0 <= (delta : Real) := NNReal.zero_le_coe
          nlinarith)
      · rw [frame.repr_apply_apply, frame.repr_apply_apply]
        dsimp only [eT, eU]
        exact he1.trans_le (by
          have hd : 0 <= (delta : Real) := NNReal.zero_le_coe
          nlinarith)
      · rw [frame.repr_apply_apply, frame.repr_apply_apply]
        dsimp only [eT, eU]
        exact he2.trans_le (by
          have hd : 0 <= (delta : Real) := NNReal.zero_le_coe
          nlinarith)
    simpa only [eT, eU, frame.repr.dist_map] using hrepr
  · have hrepr : dist u v <= (delta : Real) / 1000 := by
      apply dist_le_delta_div_thousand_of_coordinate_close
      intro j
      fin_cases j
      · exact hu0.trans_le (by
          have hd : 0 <= (delta : Real) := NNReal.zero_le_coe
          nlinarith)
      · exact hu1.trans_le (by
          have hd : 0 <= (delta : Real) := NNReal.zero_le_coe
          nlinarith)
      · exact hu2.trans_le (by
          have hd : 0 <= (delta : Real) := NNReal.zero_le_coe
          nlinarith)
    simpa only [u, v, frame.repr.dist_map] using hrepr

/-- Split fixed/wide frame code. -/
def thinPlankFrameCode
    {delta : NNReal} {parameter : Type}
    (frame : OrthonormalBasis (Fin 3) Real Space)
    (x : Space) (tube : parameter -> Tube delta) (R : Real)
    (hfixed : forall p j,
      |thinPlankFrameFixedCoordinates frame x (tube p) j| <=
        thinPlankPackingFixedBound)
    (hwide : forall p j,
      |thinPlankFrameWideCoordinates frame x (tube p) j| <= R)
    (p : parameter) :
    BoundedCode (Fin 4) thinPlankPackingMesh thinPlankPackingFixedBound ×
      BoundedCode (Fin 2) thinPlankPackingMesh R :=
  (boundedFloorCode thinPlankPackingMesh thinPlankPackingFixedBound
      (by norm_num [thinPlankPackingMesh])
      (thinPlankFrameFixedCoordinates frame x ∘ tube) hfixed p,
    boundedFloorCode thinPlankPackingMesh R
      (by norm_num [thinPlankPackingMesh])
      (thinPlankFrameWideCoordinates frame x ∘ tube) hwide p)

/-- Frame-covariant quadratic packing theorem. -/
theorem card_le_thinPlankFramePackingNatCap
    {delta : NNReal} {parameter : Type} [Fintype parameter]
    [DecidableEq parameter]
    (frame : OrthonormalBasis (Fin 3) Real Space)
    (x : Space) (tube : parameter -> Tube delta) (R : Real)
    (hdeltaPos : 0 < delta) (hdeltaSmall : delta <= (1 / 100 : NNReal))
    (hlong : forall p, |tubePointLongitudinal x (tube p)| <= 2)
    (hforward : forall p,
      (1 : Real) / 2 <= ⟪frame 2, (tube p).axis.direction⟫_Real)
    (hfixed : forall p j,
      |thinPlankFrameFixedCoordinates frame x (tube p) j| <=
        thinPlankPackingFixedBound)
    (hwide : forall p j,
      |thinPlankFrameWideCoordinates frame x (tube p) j| <= R)
    (hpairwise : Set.Pairwise (Set.univ : Set parameter) fun p q =>
      EssentiallyDistinct (tube p) (tube q)) :
    Fintype.card parameter <= thinPlankPackingNatCap R := by
  classical
  let Code :=
    BoundedCode (Fin 4) thinPlankPackingMesh thinPlankPackingFixedBound ×
      BoundedCode (Fin 2) thinPlankPackingMesh R
  let code : parameter -> Code :=
    thinPlankFrameCode frame x tube R hfixed hwide
  have hcodeInjective : Function.Injective code := by
    intro p q hpq
    by_contra hpqNe
    have hfixedCode := congrArg Prod.fst hpq
    have hwideCode := congrArg Prod.snd hpq
    have hfixedFloor :
        floorCode thinPlankPackingMesh
            (thinPlankFrameFixedCoordinates frame x ∘ tube) p =
          floorCode thinPlankPackingMesh
            (thinPlankFrameFixedCoordinates frame x ∘ tube) q := by
      funext j
      exact congrArg Subtype.val (congrFun hfixedCode j)
    have hwideFloor :
        floorCode thinPlankPackingMesh
            (thinPlankFrameWideCoordinates frame x ∘ tube) p =
          floorCode thinPlankPackingMesh
            (thinPlankFrameWideCoordinates frame x ∘ tube) q := by
      funext j
      exact congrArg Subtype.val (congrFun hwideCode j)
    have hclose := wide_anisotropic_close_of_thinPlankFrame_floorCodes_eq
      frame x (tube p) (tube q) hdeltaPos (hforward p) (hforward q)
      hfixedFloor hwideFloor
    obtain ⟨aligned, haligned⟩ := (tube p).exists_alignedFrame
    have hnot := not_essentiallyDistinct_of_wide_anisotropic_close
      x (tube p) (tube q) aligned haligned hdeltaPos hdeltaSmall
      (hlong p) hclose.1 hclose.2.1 hclose.2.2
    exact hnot (hpairwise (Set.mem_univ p) (Set.mem_univ q) hpqNe)
  calc
    Fintype.card parameter <= Fintype.card Code :=
      Fintype.card_le_of_injective code hcodeInjective
    _ = thinPlankPackingNatCap R := by
      simpa only [Code] using thinPlankCodeSpace_card_eq R

#print axioms thinPlankFrameFixedCoordinates
#print axioms thinPlankFrameWideCoordinates
#print axioms wide_anisotropic_close_of_thinPlankFrame_floorCodes_eq
#print axioms thinPlankFrameCode
#print axioms card_le_thinPlankFramePackingNatCap

end
end Family8ThinPlankFramePackingV2
