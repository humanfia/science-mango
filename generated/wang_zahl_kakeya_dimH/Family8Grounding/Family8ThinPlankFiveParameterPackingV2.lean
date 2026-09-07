import Family8Grounding.Family8ThinPlankFramePackingV2
import Mathlib.Tactic

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 5000000

open Set
open scoped NNReal InnerProductSpace

namespace Family8ThinPlankFiveParameterPackingV2

open LeanEval.Analysis.WangZahlKakeya
open Submission.Kakeya.ConvexGeometry
open Family4GlobalExtremalUpstream
open Family8CommonPointTubePackingV1
open Family8PaperConflictWideAnisotropicOverlapV1
open Family8ThinPlankEssentialDistinctPackingV4
open Family8ThinPlankFramePackingV2
open FamilyStickyRandomFiniteFloorParameterNetV1

noncomputable section

/-!
# The genuine five-parameter thin-plank packing code

For a tube in a `delta x (R delta) x 1` plank, the transverse residual in
the long frame coordinate need not itself be `O(delta)`.  It must therefore
not be put into a fixed-size code.  This module removes that spurious input.

Only five parameters are encoded: one longitudinal parameter, a thin
position/direction pair, and a wide position/direction pair.  Unit length
recovers the omitted direction coordinate; exact perpendicularity of the
tube transverse residual then recovers the omitted position coordinate.
Thus only the two wide parameters pay an `R`-dependent grid cost.
-/

/-- The tube midpoint residual is exactly perpendicular to its axis
direction. -/
theorem direction_inner_tubePointTransverse_eq_zero
    {delta : NNReal} (x : Space) (T : Tube delta) :
    ⟪T.axis.direction, tubePointTransverse x T⟫_Real = 0 := by
  rw [tubePointTransverse, inner_sub_right, real_inner_smul_right,
    tubePointLongitudinal, real_inner_self_eq_norm_sq,
    T.axis.norm_direction]
  norm_num

/-- Once directions are close and forward, perpendicular transverse vectors
with close first two coordinates also have close omitted third coordinate. -/
theorem abs_third_transverse_sub_lt_twentyEight_mul
    {u v e f : Space} {epsilon : Real}
    (hu : ‖u‖ = 1) (hv : ‖v‖ = 1)
    (huForward : (1 : Real) / 2 <= u 2)
    (hvForward : (1 : Real) / 2 <= v 2)
    (heOrth : ⟪u, e⟫_Real = 0) (hfOrth : ⟪v, f⟫_Real = 0)
    (hfNorm : ‖f‖ <= 2)
    (hdir0 : |u 0 - v 0| < epsilon)
    (hdir1 : |u 1 - v 1| < epsilon)
    (he0 : |e 0 - f 0| < epsilon)
    (he1 : |e 1 - f 1| < epsilon) :
    |e 2 - f 2| < 28 * epsilon := by
  have hu0 : |u 0| <= 1 := by
    simpa only [hu] using abs_apply_le_norm u (0 : Fin 3)
  have hu1 : |u 1| <= 1 := by
    simpa only [hu] using abs_apply_le_norm u (1 : Fin 3)
  have hf0 : |f 0| <= 2 :=
    (abs_apply_le_norm f (0 : Fin 3)).trans hfNorm
  have hf1 : |f 1| <= 2 :=
    (abs_apply_le_norm f (1 : Fin 3)).trans hfNorm
  have hf2 : |f 2| <= 2 :=
    (abs_apply_le_norm f (2 : Fin 3)).trans hfNorm
  have hdir2 : |u 2 - v 2| < 4 * epsilon :=
    abs_third_sub_lt_four_mul_of_unit_forward hu hv huForward hvForward
      hdir0 hdir1
  have heOrth' :
      u 0 * e 0 + u 1 * e 1 + u 2 * e 2 = 0 := by
    rw [PiLp.inner_apply, Fin.sum_univ_three] at heOrth
    norm_num at heOrth
    nlinarith [heOrth]
  have hfOrth' :
      v 0 * f 0 + v 1 * f 1 + v 2 * f 2 = 0 := by
    rw [PiLp.inner_apply, Fin.sum_univ_three] at hfOrth
    norm_num at hfOrth
    nlinarith [hfOrth]
  have hidentity :
      u 2 * (e 2 - f 2) =
        -(u 0 * (e 0 - f 0)) - u 1 * (e 1 - f 1) +
          (v 0 - u 0) * f 0 + (v 1 - u 1) * f 1 +
            (v 2 - u 2) * f 2 := by
    nlinarith [heOrth', hfOrth']
  have ht0 : |u 0 * (e 0 - f 0)| < epsilon := by
    rw [abs_mul]
    calc
      |u 0| * |e 0 - f 0| <= 1 * |e 0 - f 0| :=
        mul_le_mul_of_nonneg_right hu0 (abs_nonneg _)
      _ < epsilon := by simpa only [one_mul] using he0
  have ht1 : |u 1 * (e 1 - f 1)| < epsilon := by
    rw [abs_mul]
    calc
      |u 1| * |e 1 - f 1| <= 1 * |e 1 - f 1| :=
        mul_le_mul_of_nonneg_right hu1 (abs_nonneg _)
      _ < epsilon := by simpa only [one_mul] using he1
  have ht2 : |(v 0 - u 0) * f 0| < 2 * epsilon := by
    rw [abs_mul, abs_sub_comm (v 0) (u 0)]
    calc
      |u 0 - v 0| * |f 0| <= |u 0 - v 0| * 2 :=
        mul_le_mul_of_nonneg_left hf0 (abs_nonneg _)
      _ < epsilon * 2 :=
        mul_lt_mul_of_pos_right hdir0 (by norm_num)
      _ = 2 * epsilon := by ring
  have ht3 : |(v 1 - u 1) * f 1| < 2 * epsilon := by
    rw [abs_mul, abs_sub_comm (v 1) (u 1)]
    calc
      |u 1 - v 1| * |f 1| <= |u 1 - v 1| * 2 :=
        mul_le_mul_of_nonneg_left hf1 (abs_nonneg _)
      _ < epsilon * 2 :=
        mul_lt_mul_of_pos_right hdir1 (by norm_num)
      _ = 2 * epsilon := by ring
  have ht4 : |(v 2 - u 2) * f 2| < 8 * epsilon := by
    rw [abs_mul, abs_sub_comm (v 2) (u 2)]
    calc
      |u 2 - v 2| * |f 2| <= |u 2 - v 2| * 2 :=
        mul_le_mul_of_nonneg_left hf2 (abs_nonneg _)
      _ < (4 * epsilon) * 2 :=
        mul_lt_mul_of_pos_right hdir2 (by norm_num)
      _ = 8 * epsilon := by ring
  have hsum :
      |-(u 0 * (e 0 - f 0)) - u 1 * (e 1 - f 1) +
          (v 0 - u 0) * f 0 + (v 1 - u 1) * f 1 +
            (v 2 - u 2) * f 2| < 14 * epsilon := by
    have htri0 :
        |-(u 0 * (e 0 - f 0)) - u 1 * (e 1 - f 1)| <=
          |u 0 * (e 0 - f 0)| + |u 1 * (e 1 - f 1)| := by
      simpa only [sub_eq_add_neg, abs_neg] using
        abs_add_le (-(u 0 * (e 0 - f 0))) (-(u 1 * (e 1 - f 1)))
    have htri1 :=
      abs_add_le
        (-(u 0 * (e 0 - f 0)) - u 1 * (e 1 - f 1))
        ((v 0 - u 0) * f 0)
    have htri2 :=
      abs_add_le
        (-(u 0 * (e 0 - f 0)) - u 1 * (e 1 - f 1) +
          (v 0 - u 0) * f 0)
        ((v 1 - u 1) * f 1)
    have htri3 :=
      abs_add_le
        (-(u 0 * (e 0 - f 0)) - u 1 * (e 1 - f 1) +
          (v 0 - u 0) * f 0 + (v 1 - u 1) * f 1)
        ((v 2 - u 2) * f 2)
    have hbound :
        |-(u 0 * (e 0 - f 0)) - u 1 * (e 1 - f 1) +
            (v 0 - u 0) * f 0 + (v 1 - u 1) * f 1 +
              (v 2 - u 2) * f 2| <=
          |u 0 * (e 0 - f 0)| + |u 1 * (e 1 - f 1)| +
            |(v 0 - u 0) * f 0| + |(v 1 - u 1) * f 1| +
              |(v 2 - u 2) * f 2| := by
      linarith
    calc
      |-(u 0 * (e 0 - f 0)) - u 1 * (e 1 - f 1) +
          (v 0 - u 0) * f 0 + (v 1 - u 1) * f 1 +
            (v 2 - u 2) * f 2| <=
        |u 0 * (e 0 - f 0)| + |u 1 * (e 1 - f 1)| +
          |(v 0 - u 0) * f 0| + |(v 1 - u 1) * f 1| +
            |(v 2 - u 2) * f 2| := hbound
      _ < epsilon + epsilon + 2 * epsilon + 2 * epsilon + 8 * epsilon := by
        exact add_lt_add (add_lt_add (add_lt_add (add_lt_add ht0 ht1) ht2) ht3) ht4
      _ = 14 * epsilon := by ring
  have hproduct : |u 2 * (e 2 - f 2)| < 14 * epsilon := by
    rw [hidentity]
    exact hsum
  have hu2abs : (1 : Real) / 2 <= |u 2| :=
    huForward.trans (le_abs_self _)
  rw [abs_mul] at hproduct
  have hlower : (1 : Real) / 2 * |e 2 - f 2| <=
      |u 2| * |e 2 - f 2| :=
    mul_le_mul_of_nonneg_right hu2abs (abs_nonneg _)
  nlinarith

/-- Fixed-size longitudinal and thin position/direction coordinates. -/
def thinPlankFiveFixedCoordinates {delta : NNReal}
    (frame : OrthonormalBasis (Fin 3) Real Space) (x : Space)
    (T : Tube delta) : Fin 3 -> Real :=
  ![tubePointLongitudinal x T,
    ⟪frame 0, tubePointTransverse x T⟫_Real / (delta : Real),
    ⟪frame 0, T.axis.direction⟫_Real / (delta : Real)]

/-- The only two aspect-ratio-dependent coordinates. -/
def thinPlankFiveWideCoordinates {delta : NNReal}
    (frame : OrthonormalBasis (Fin 3) Real Space) (x : Space)
    (T : Tube delta) : Fin 2 -> Real :=
  ![⟪frame 1, tubePointTransverse x T⟫_Real / (delta : Real),
    ⟪frame 1, T.axis.direction⟫_Real / (delta : Real)]

def thinPlankFiveFixedCodeCount : Nat :=
  ((Int.floor (thinPlankPackingFixedBound / thinPlankPackingMesh) + 1 -
      Int.floor (-thinPlankPackingFixedBound / thinPlankPackingMesh)).toNat) ^ 3

def thinPlankFivePackingNatCap (R : Real) : Nat :=
  thinPlankFiveFixedCodeCount * thinPlankWideCodeCount R

/-- Equal five-parameter frame codes give the physical closeness needed by
the overlap contradiction. -/
theorem wide_anisotropic_close_of_thinPlankFive_floorCodes_eq
    {delta : NNReal}
    (frame : OrthonormalBasis (Fin 3) Real Space)
    (x : Space) (T U : Tube delta)
    (hdeltaPos : 0 < delta)
    (hTForward : (1 : Real) / 2 <= ⟪frame 2, T.axis.direction⟫_Real)
    (hUForward : (1 : Real) / 2 <= ⟪frame 2, U.axis.direction⟫_Real)
    (_hTTransverse : ‖tubePointTransverse x T‖ <= 2)
    (hUTransverse : ‖tubePointTransverse x U‖ <= 2)
    (hfixed :
      floorCode thinPlankPackingMesh
          (thinPlankFiveFixedCoordinates frame x) T =
        floorCode thinPlankPackingMesh
          (thinPlankFiveFixedCoordinates frame x) U)
    (hwide :
      floorCode thinPlankPackingMesh
          (thinPlankFiveWideCoordinates frame x) T =
        floorCode thinPlankPackingMesh
          (thinPlankFiveWideCoordinates frame x) U) :
    |tubePointLongitudinal x T - tubePointLongitudinal x U| <=
        (1 : Real) / 400 ∧
      dist (tubePointTransverse x T) (tubePointTransverse x U) <=
        (delta : Real) / 100 ∧
      dist T.axis.direction U.axis.direction <=
        (delta : Real) / 1000 := by
  have hmesh : 0 < thinPlankPackingMesh := by
    norm_num [thinPlankPackingMesh]
  have hdeltaReal : 0 < (delta : Real) := NNReal.coe_pos.mpr hdeltaPos
  have fixedClose (j : Fin 3) :=
    abs_coord_sub_lt_of_floorCode_eq hmesh
      (thinPlankFiveFixedCoordinates frame x) hfixed j
  have wideClose (j : Fin 2) :=
    abs_coord_sub_lt_of_floorCode_eq hmesh
      (thinPlankFiveWideCoordinates frame x) hwide j
  have hlong :
      |tubePointLongitudinal x T - tubePointLongitudinal x U| <
        (1 : Real) / 100000 := by
    simpa [thinPlankFiveFixedCoordinates, thinPlankPackingMesh] using
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
    simpa [thinPlankFiveFixedCoordinates, thinPlankPackingMesh] using
      fixedClose 1
  have hd0 :
      |⟪frame 0, T.axis.direction⟫_Real -
          ⟪frame 0, U.axis.direction⟫_Real| <
        (delta : Real) / 100000 := by
    apply normalized_to_physical
    simpa [thinPlankFiveFixedCoordinates, thinPlankPackingMesh] using
      fixedClose 2
  have he1 :
      |⟪frame 1, tubePointTransverse x T⟫_Real -
          ⟪frame 1, tubePointTransverse x U⟫_Real| <
        (delta : Real) / 100000 := by
    apply normalized_to_physical
    simpa [thinPlankFiveWideCoordinates, thinPlankPackingMesh] using
      wideClose 0
  have hd1 :
      |⟪frame 1, T.axis.direction⟫_Real -
          ⟪frame 1, U.axis.direction⟫_Real| <
        (delta : Real) / 100000 := by
    apply normalized_to_physical
    simpa [thinPlankFiveWideCoordinates, thinPlankPackingMesh] using
      wideClose 1
  let u : Space := frame.repr T.axis.direction
  let v : Space := frame.repr U.axis.direction
  let e : Space := frame.repr (tubePointTransverse x T)
  let f : Space := frame.repr (tubePointTransverse x U)
  have hu : ‖u‖ = 1 := by
    simpa only [u, frame.repr.norm_map] using T.axis.norm_direction
  have hv : ‖v‖ = 1 := by
    simpa only [v, frame.repr.norm_map] using U.axis.norm_direction
  have huForward : (1 : Real) / 2 <= u 2 := by
    simpa only [u, frame.repr_apply_apply] using hTForward
  have hvForward : (1 : Real) / 2 <= v 2 := by
    simpa only [v, frame.repr_apply_apply] using hUForward
  have heOrth : ⟪u, e⟫_Real = 0 := by
    simpa only [u, e, frame.repr.inner_map_map] using
      direction_inner_tubePointTransverse_eq_zero x T
  have hfOrth : ⟪v, f⟫_Real = 0 := by
    simpa only [v, f, frame.repr.inner_map_map] using
      direction_inner_tubePointTransverse_eq_zero x U
  have hfNorm : ‖f‖ <= 2 := by
    simpa only [f, frame.repr.norm_map] using hUTransverse
  have hu0 : |u 0 - v 0| < (delta : Real) / 100000 := by
    simpa only [u, v, frame.repr_apply_apply] using hd0
  have hu1 : |u 1 - v 1| < (delta : Real) / 100000 := by
    simpa only [u, v, frame.repr_apply_apply] using hd1
  have he0' : |e 0 - f 0| < (delta : Real) / 100000 := by
    simpa only [e, f, frame.repr_apply_apply] using he0
  have he1' : |e 1 - f 1| < (delta : Real) / 100000 := by
    simpa only [e, f, frame.repr_apply_apply] using he1
  have hu2 : |u 2 - v 2| < (delta : Real) / 25000 := by
    have hthird := abs_third_sub_lt_four_mul_of_unit_forward
      hu hv huForward hvForward hu0 hu1
    convert hthird using 1
    all_goals ring
  have he2 : |e 2 - f 2| < 28 * ((delta : Real) / 100000) :=
    abs_third_transverse_sub_lt_twentyEight_mul hu hv huForward hvForward
      heOrth hfOrth hfNorm hu0 hu1 he0' he1'
  refine ⟨hlong.le.trans (by norm_num), ?_, ?_⟩
  · have hrepr : dist e f <= (delta : Real) / 100 := by
      apply dist_le_delta_div_hundred_of_coordinate_close
      intro j
      fin_cases j
      · exact he0'.trans_le (by
          have hd : 0 <= (delta : Real) := NNReal.zero_le_coe
          nlinarith)
      · exact he1'.trans_le (by
          have hd : 0 <= (delta : Real) := NNReal.zero_le_coe
          nlinarith)
      · exact he2.trans_le (by
          have hd : 0 <= (delta : Real) := NNReal.zero_le_coe
          nlinarith)
    simpa only [e, f, frame.repr.dist_map] using hrepr
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

def thinPlankFiveCode
    {delta : NNReal} {parameter : Type}
    (frame : OrthonormalBasis (Fin 3) Real Space)
    (x : Space) (tube : parameter -> Tube delta) (R : Real)
    (hfixed : forall p j,
      |thinPlankFiveFixedCoordinates frame x (tube p) j| <=
        thinPlankPackingFixedBound)
    (hwide : forall p j,
      |thinPlankFiveWideCoordinates frame x (tube p) j| <= R)
    (p : parameter) :
    BoundedCode (Fin 3) thinPlankPackingMesh thinPlankPackingFixedBound ×
      BoundedCode (Fin 2) thinPlankPackingMesh R :=
  (boundedFloorCode thinPlankPackingMesh thinPlankPackingFixedBound
      (by norm_num [thinPlankPackingMesh])
      (thinPlankFiveFixedCoordinates frame x ∘ tube) hfixed p,
    boundedFloorCode thinPlankPackingMesh R
      (by norm_num [thinPlankPackingMesh])
      (thinPlankFiveWideCoordinates frame x ∘ tube) hwide p)

theorem thinPlankFiveCodeSpace_card_eq (R : Real) :
    Fintype.card
      (BoundedCode (Fin 3) thinPlankPackingMesh thinPlankPackingFixedBound ×
        BoundedCode (Fin 2) thinPlankPackingMesh R) =
      thinPlankFivePackingNatCap R := by
  rw [Fintype.card_prod]
  unfold thinPlankFivePackingNatCap thinPlankFiveFixedCodeCount
    thinPlankWideCodeCount
  congr 1
  · rw [Fintype.card_fun, Fintype.card_coe]
    unfold codeInterval
    rw [Int.card_Icc, Fintype.card_fin]
  · rw [Fintype.card_fun, Fintype.card_coe]
    unfold codeInterval
    rw [Int.card_Icc, Fintype.card_fin]

/-- Final five-parameter quadratic packing kernel. -/
theorem card_le_thinPlankFivePackingNatCap
    {delta : NNReal} {parameter : Type} [Fintype parameter]
    [DecidableEq parameter]
    (frame : OrthonormalBasis (Fin 3) Real Space)
    (x : Space) (tube : parameter -> Tube delta) (R : Real)
    (hdeltaPos : 0 < delta) (hdeltaSmall : delta <= (1 / 100 : NNReal))
    (hlong : forall p, |tubePointLongitudinal x (tube p)| <= 2)
    (hforward : forall p,
      (1 : Real) / 2 <= ⟪frame 2, (tube p).axis.direction⟫_Real)
    (htransverse : forall p, ‖tubePointTransverse x (tube p)‖ <= 2)
    (hfixed : forall p j,
      |thinPlankFiveFixedCoordinates frame x (tube p) j| <=
        thinPlankPackingFixedBound)
    (hwide : forall p j,
      |thinPlankFiveWideCoordinates frame x (tube p) j| <= R)
    (hpairwise : Set.Pairwise (Set.univ : Set parameter) fun p q =>
      EssentiallyDistinct (tube p) (tube q)) :
    Fintype.card parameter <= thinPlankFivePackingNatCap R := by
  classical
  let Code :=
    BoundedCode (Fin 3) thinPlankPackingMesh thinPlankPackingFixedBound ×
      BoundedCode (Fin 2) thinPlankPackingMesh R
  let code : parameter -> Code :=
    thinPlankFiveCode frame x tube R hfixed hwide
  have hcodeInjective : Function.Injective code := by
    intro p q hpq
    by_contra hpqNe
    have hfixedCode := congrArg Prod.fst hpq
    have hwideCode := congrArg Prod.snd hpq
    have hfixedFloor :
        floorCode thinPlankPackingMesh
            (thinPlankFiveFixedCoordinates frame x ∘ tube) p =
          floorCode thinPlankPackingMesh
            (thinPlankFiveFixedCoordinates frame x ∘ tube) q := by
      funext j
      exact congrArg Subtype.val (congrFun hfixedCode j)
    have hwideFloor :
        floorCode thinPlankPackingMesh
            (thinPlankFiveWideCoordinates frame x ∘ tube) p =
          floorCode thinPlankPackingMesh
            (thinPlankFiveWideCoordinates frame x ∘ tube) q := by
      funext j
      exact congrArg Subtype.val (congrFun hwideCode j)
    have hclose := wide_anisotropic_close_of_thinPlankFive_floorCodes_eq
      frame x (tube p) (tube q) hdeltaPos (hforward p) (hforward q)
      (htransverse p) (htransverse q) hfixedFloor hwideFloor
    obtain ⟨aligned, haligned⟩ := (tube p).exists_alignedFrame
    have hnot := not_essentiallyDistinct_of_wide_anisotropic_close
      x (tube p) (tube q) aligned haligned hdeltaPos hdeltaSmall
      (hlong p) hclose.1 hclose.2.1 hclose.2.2
    exact hnot (hpairwise (Set.mem_univ p) (Set.mem_univ q) hpqNe)
  calc
    Fintype.card parameter <= Fintype.card Code :=
      Fintype.card_le_of_injective code hcodeInjective
    _ = thinPlankFivePackingNatCap R := by
      simpa only [Code] using thinPlankFiveCodeSpace_card_eq R

#print axioms direction_inner_tubePointTransverse_eq_zero
#print axioms abs_third_transverse_sub_lt_twentyEight_mul
#print axioms wide_anisotropic_close_of_thinPlankFive_floorCodes_eq
#print axioms thinPlankFiveCodeSpace_card_eq
#print axioms card_le_thinPlankFivePackingNatCap

end
end Family8ThinPlankFiveParameterPackingV2
