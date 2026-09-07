import Family8Grounding.Family8PaperConflictWideAnisotropicOverlapV1
import FamilyStickyRandomFiniteFloorParameterNetV1
import Mathlib.Tactic

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 4000000

open Set
open scoped NNReal InnerProductSpace

namespace Family8ThinPlankEssentialDistinctPackingV4

open LeanEval.Analysis.WangZahlKakeya
open Submission.Kakeya.ConvexGeometry
open Family4GlobalExtremalUpstream
open Family8CommonPointTubePackingV1
open Family8PaperConflictWideAnisotropicOverlapV1
open FamilyStickyRandomFiniteFloorParameterNetV1

noncomputable section

/-!
# Quadratic packing of essentially-distinct tubes in a thin plank

This is the finite geometric core of the packing step in Proposition 6.6(A).
After choosing the long coordinate, a unit tube in a
`delta x (R * delta) x 1` plank has four parameters in fixed-size boxes and
only two parameters in boxes of width `R`.  We encode precisely those six
parameters.  The last direction coordinate is recovered from unit length
and a common positive orientation, so it is not charged as a third wide
parameter.

The theorem below deliberately assumes concrete coordinate bounds, not a
cardinality estimate.  A downstream affine-plank connector only has to prove
these coordinate bounds from literal containment.
-/

/-- Mesh small enough for the quantitative overlap contradiction. -/
def thinPlankPackingMesh : Real := (1 : Real) / 100000

/-- Fixed box for longitudinal, thin-transverse, long-transverse, and
thin-direction coordinates. -/
def thinPlankPackingFixedBound : Real := 100

/-- The four coordinates whose ranges are independent of the aspect ratio. -/
def thinPlankFixedCoordinates {delta : NNReal} (x : Space)
    (T : Tube delta) : Fin 4 -> Real :=
  ![tubePointLongitudinal x T,
    tubePointTransverse x T 0 / (delta : Real),
    tubePointTransverse x T 2 / (delta : Real),
    T.axis.direction 0 / (delta : Real)]

/-- The two coordinates whose ranges grow with the plank aspect ratio. -/
def thinPlankWideCoordinates {delta : NNReal} (x : Space)
    (T : Tube delta) : Fin 2 -> Real :=
  ![tubePointTransverse x T 1 / (delta : Real),
    T.axis.direction 1 / (delta : Real)]

/-- Exact natural size of the fixed four-coordinate grid. -/
def thinPlankFixedCodeCount : Nat :=
  ((Int.floor (thinPlankPackingFixedBound / thinPlankPackingMesh) + 1 -
      Int.floor (-thinPlankPackingFixedBound / thinPlankPackingMesh)).toNat) ^ 4

/-- Exact natural size of the two-coordinate aspect-ratio grid. -/
def thinPlankWideCodeCount (R : Real) : Nat :=
  ((Int.floor (R / thinPlankPackingMesh) + 1 -
      Int.floor (-R / thinPlankPackingMesh)).toNat) ^ 2

/-- Explicit quadratic-in-`R` packing cap. -/
def thinPlankPackingNatCap (R : Real) : Nat :=
  thinPlankFixedCodeCount * thinPlankWideCodeCount R

/-- A unit vector's omitted third coordinate is controlled by its first two
coordinates once both vectors have the same positive orientation. -/
theorem abs_third_sub_lt_four_mul_of_unit_forward
    {u v : Space} {epsilon : Real}
    (hu : ‖u‖ = 1) (hv : ‖v‖ = 1)
    (huForward : (1 : Real) / 2 <= u 2)
    (hvForward : (1 : Real) / 2 <= v 2)
    (h0 : |u 0 - v 0| < epsilon)
    (h1 : |u 1 - v 1| < epsilon) :
    |u 2 - v 2| < 4 * epsilon := by
  have hu0 : |u 0| <= 1 := by
    simpa only [hu] using abs_apply_le_norm u (0 : Fin 3)
  have hu1 : |u 1| <= 1 := by
    simpa only [hu] using abs_apply_le_norm u (1 : Fin 3)
  have hv0 : |v 0| <= 1 := by
    simpa only [hv] using abs_apply_le_norm v (0 : Fin 3)
  have hv1 : |v 1| <= 1 := by
    simpa only [hv] using abs_apply_le_norm v (1 : Fin 3)
  have hsum0 : |u 0 + v 0| <= 2 := by
    calc
      |u 0 + v 0| <= |u 0| + |v 0| := abs_add_le _ _
      _ <= 1 + 1 := add_le_add hu0 hv0
      _ = 2 := by norm_num
  have hsum1 : |u 1 + v 1| <= 2 := by
    calc
      |u 1 + v 1| <= |u 1| + |v 1| := abs_add_le _ _
      _ <= 1 + 1 := add_le_add hu1 hv1
      _ = 2 := by norm_num
  have hunitU : u 0 ^ 2 + u 1 ^ 2 + u 2 ^ 2 = 1 := by
    have hsquare := congrArg (fun z : Real => z ^ 2) hu
    rw [EuclideanSpace.real_norm_sq_eq, Fin.sum_univ_three] at hsquare
    norm_num at hsquare
    nlinarith
  have hunitV : v 0 ^ 2 + v 1 ^ 2 + v 2 ^ 2 = 1 := by
    have hsquare := congrArg (fun z : Real => z ^ 2) hv
    rw [EuclideanSpace.real_norm_sq_eq, Fin.sum_univ_three] at hsquare
    norm_num at hsquare
    nlinarith
  have hfactor :
      (u 2 - v 2) * (u 2 + v 2) =
        -((u 0 - v 0) * (u 0 + v 0) +
          (u 1 - v 1) * (u 1 + v 1)) := by
    nlinarith [hunitU, hunitV]
  have hterm0 :
      |(u 0 - v 0) * (u 0 + v 0)| < 2 * epsilon := by
    rw [abs_mul]
    calc
      |u 0 - v 0| * |u 0 + v 0| <= |u 0 - v 0| * 2 :=
        mul_le_mul_of_nonneg_left hsum0 (abs_nonneg _)
      _ < epsilon * 2 :=
        mul_lt_mul_of_pos_right h0 (by norm_num : (0 : Real) < 2)
      _ = 2 * epsilon := by ring
  have hterm1 :
      |(u 1 - v 1) * (u 1 + v 1)| < 2 * epsilon := by
    rw [abs_mul]
    calc
      |u 1 - v 1| * |u 1 + v 1| <= |u 1 - v 1| * 2 :=
        mul_le_mul_of_nonneg_left hsum1 (abs_nonneg _)
      _ < epsilon * 2 :=
        mul_lt_mul_of_pos_right h1 (by norm_num : (0 : Real) < 2)
      _ = 2 * epsilon := by ring
  have hrhs :
      |(u 0 - v 0) * (u 0 + v 0) +
        (u 1 - v 1) * (u 1 + v 1)| < 4 * epsilon := by
    calc
      |(u 0 - v 0) * (u 0 + v 0) +
          (u 1 - v 1) * (u 1 + v 1)| <=
          |(u 0 - v 0) * (u 0 + v 0)| +
            |(u 1 - v 1) * (u 1 + v 1)| := abs_add_le _ _
      _ < 2 * epsilon + 2 * epsilon := add_lt_add hterm0 hterm1
      _ = 4 * epsilon := by ring
  have hsum : 1 <= |u 2 + v 2| := by
    rw [abs_of_nonneg (by linarith)]
    linarith
  have hproduct :
      |u 2 - v 2| * |u 2 + v 2| < 4 * epsilon := by
    rw [<- abs_mul, hfactor, abs_neg]
    exact hrhs
  calc
    |u 2 - v 2| = |u 2 - v 2| * 1 := by ring
    _ <= |u 2 - v 2| * |u 2 + v 2| :=
      mul_le_mul_of_nonneg_left hsum (abs_nonneg _)
    _ < 4 * epsilon := hproduct

/-- Coordinate accuracy `delta/10000` implies the direction accuracy
`delta/1000` used by the wide-anchor overlap lemma. -/
theorem dist_le_delta_div_thousand_of_coordinate_close
    {delta : NNReal} {v w : Space}
    (hcoord : forall k : Fin 3,
      |v k - w k| < (delta : Real) / 10000) :
    dist v w <= (delta : Real) / 1000 := by
  have sq_le_sq_of_abs_le' {z a : Real} (h : |z| <= a) : z ^ 2 <= a ^ 2 := by
    have ha : 0 <= a := (abs_nonneg z).trans h
    have hsquare := (sq_le_sq₀ (abs_nonneg z) ha).2 h
    simpa only [sq_abs] using hsquare
  have h0 := sq_le_sq_of_abs_le' (hcoord (0 : Fin 3)).le
  have h1 := sq_le_sq_of_abs_le' (hcoord (1 : Fin 3)).le
  have h2 := sq_le_sq_of_abs_le' (hcoord (2 : Fin 3)).le
  apply (sq_le_sq₀ dist_nonneg (by positivity)).mp
  rw [dist_eq_norm, EuclideanSpace.real_norm_sq_eq, Fin.sum_univ_three]
  norm_num at h0 h1 h2 ⊢
  nlinarith [sq_nonneg (delta : Real)]

/-- Equal fixed and wide floor codes give the exact anisotropic closeness
needed to contradict essential distinctness. -/
theorem wide_anisotropic_close_of_thinPlank_floorCodes_eq
    {delta : NNReal} (x : Space) (T U : Tube delta)
    (hdeltaPos : 0 < delta)
    (hTForward : (1 : Real) / 2 <= T.axis.direction 2)
    (hUForward : (1 : Real) / 2 <= U.axis.direction 2)
    (hfixed :
      floorCode thinPlankPackingMesh (thinPlankFixedCoordinates x) T =
        floorCode thinPlankPackingMesh (thinPlankFixedCoordinates x) U)
    (hwide :
      floorCode thinPlankPackingMesh (thinPlankWideCoordinates x) T =
        floorCode thinPlankPackingMesh (thinPlankWideCoordinates x) U) :
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
      (thinPlankFixedCoordinates x) hfixed j
  have wideClose (j : Fin 2) :=
    abs_coord_sub_lt_of_floorCode_eq hmesh
      (thinPlankWideCoordinates x) hwide j
  have hlong :
      |tubePointLongitudinal x T - tubePointLongitudinal x U| <
        (1 : Real) / 100000 := by
    simpa [thinPlankFixedCoordinates, thinPlankPackingMesh] using fixedClose 0
  have normalized_to_physical {a b : Real}
      (h : |a / (delta : Real) - b / (delta : Real)| <
        (1 : Real) / 100000) :
      |a - b| < (delta : Real) / 100000 := by
    rw [<- sub_div, abs_div, abs_of_pos hdeltaReal] at h
    have hscaled := (div_lt_iff₀ hdeltaReal).mp h
    simpa only [div_eq_mul_inv, one_mul, mul_comm] using hscaled
  have he0 :
      |tubePointTransverse x T 0 - tubePointTransverse x U 0| <
        (delta : Real) / 100000 := by
    apply normalized_to_physical
    simpa [thinPlankFixedCoordinates, thinPlankPackingMesh] using fixedClose 1
  have he2 :
      |tubePointTransverse x T 2 - tubePointTransverse x U 2| <
        (delta : Real) / 100000 := by
    apply normalized_to_physical
    simpa [thinPlankFixedCoordinates, thinPlankPackingMesh] using fixedClose 2
  have hd0 :
      |T.axis.direction 0 - U.axis.direction 0| <
        (delta : Real) / 100000 := by
    apply normalized_to_physical
    simpa [thinPlankFixedCoordinates, thinPlankPackingMesh] using fixedClose 3
  have he1 :
      |tubePointTransverse x T 1 - tubePointTransverse x U 1| <
        (delta : Real) / 100000 := by
    apply normalized_to_physical
    simpa [thinPlankWideCoordinates, thinPlankPackingMesh] using wideClose 0
  have hd1 :
      |T.axis.direction 1 - U.axis.direction 1| <
        (delta : Real) / 100000 := by
    apply normalized_to_physical
    simpa [thinPlankWideCoordinates, thinPlankPackingMesh] using wideClose 1
  have hd2 :
      |T.axis.direction 2 - U.axis.direction 2| <
        (delta : Real) / 25000 := by
    have hthird := abs_third_sub_lt_four_mul_of_unit_forward
      T.axis.norm_direction U.axis.norm_direction hTForward hUForward hd0 hd1
    convert hthird using 1
    all_goals ring
  refine ⟨hlong.le.trans (by norm_num), ?_, ?_⟩
  · apply dist_le_delta_div_hundred_of_coordinate_close
    intro j
    fin_cases j
    · exact he0.trans_le (by
        have hd : 0 <= (delta : Real) := NNReal.zero_le_coe
        nlinarith)
    · exact he1.trans_le (by
        have hd : 0 <= (delta : Real) := NNReal.zero_le_coe
        nlinarith)
    · exact he2.trans_le (by
        have hd : 0 <= (delta : Real) := NNReal.zero_le_coe
        nlinarith)
  · apply dist_le_delta_div_thousand_of_coordinate_close
    intro j
    fin_cases j
    · exact hd0.trans_le (by
        have hd : 0 <= (delta : Real) := NNReal.zero_le_coe
        nlinarith)
    · exact hd1.trans_le (by
        have hd : 0 <= (delta : Real) := NNReal.zero_le_coe
        nlinarith)
    · exact hd2.trans_le (by
        have hd : 0 <= (delta : Real) := NNReal.zero_le_coe
        nlinarith)

/-- Concrete split floor code.  Four coordinates have fixed range and only
two coordinates pay the aspect-ratio range. -/
def thinPlankCode
    {delta : NNReal} {parameter : Type}
    (x : Space) (tube : parameter -> Tube delta)
    (R : Real)
    (hfixed : forall p j,
      |thinPlankFixedCoordinates x (tube p) j| <= thinPlankPackingFixedBound)
    (hwide : forall p j,
      |thinPlankWideCoordinates x (tube p) j| <= R)
    (p : parameter) :
    BoundedCode (Fin 4) thinPlankPackingMesh thinPlankPackingFixedBound ×
      BoundedCode (Fin 2) thinPlankPackingMesh R :=
  (boundedFloorCode thinPlankPackingMesh thinPlankPackingFixedBound
      (by norm_num [thinPlankPackingMesh])
      (thinPlankFixedCoordinates x ∘ tube) hfixed p,
    boundedFloorCode thinPlankPackingMesh R
      (by norm_num [thinPlankPackingMesh])
      (thinPlankWideCoordinates x ∘ tube) hwide p)

/-- The split code space has exactly the advertised fixed-times-quadratic
size. -/
theorem thinPlankCodeSpace_card_eq (R : Real) :
    Fintype.card
      (BoundedCode (Fin 4) thinPlankPackingMesh thinPlankPackingFixedBound ×
        BoundedCode (Fin 2) thinPlankPackingMesh R) =
      thinPlankPackingNatCap R := by
  rw [Fintype.card_prod]
  unfold thinPlankPackingNatCap thinPlankFixedCodeCount thinPlankWideCodeCount
  congr 1
  · rw [Fintype.card_fun, Fintype.card_coe]
    unfold codeInterval
    rw [Int.card_Icc, Fintype.card_fin]
  · rw [Fintype.card_fun, Fintype.card_coe]
    unfold codeInterval
    rw [Int.card_Icc, Fintype.card_fin]

/-- An essentially-distinct finite family satisfying the honest thin-plank
coordinate windows has cardinality at most a constant times a quadratic
two-coordinate grid. -/
theorem card_le_thinPlankPackingNatCap
    {delta : NNReal} {parameter : Type} [Fintype parameter]
    [DecidableEq parameter]
    (x : Space) (tube : parameter -> Tube delta) (R : Real)
    (hdeltaPos : 0 < delta) (hdeltaSmall : delta <= (1 / 100 : NNReal))
    (hlong : forall p, |tubePointLongitudinal x (tube p)| <= 2)
    (hforward : forall p, (1 : Real) / 2 <= (tube p).axis.direction 2)
    (hfixed : forall p j,
      |thinPlankFixedCoordinates x (tube p) j| <= thinPlankPackingFixedBound)
    (hwide : forall p j,
      |thinPlankWideCoordinates x (tube p) j| <= R)
    (hpairwise : Set.Pairwise (Set.univ : Set parameter) fun p q =>
      EssentiallyDistinct (tube p) (tube q)) :
    Fintype.card parameter <= thinPlankPackingNatCap R := by
  classical
  let Code :=
    BoundedCode (Fin 4) thinPlankPackingMesh thinPlankPackingFixedBound ×
      BoundedCode (Fin 2) thinPlankPackingMesh R
  let code : parameter -> Code := thinPlankCode x tube R hfixed hwide
  have hcodeInjective : Function.Injective code := by
    intro p q hpq
    by_contra hpqNe
    have hfixedCode := congrArg Prod.fst hpq
    have hwideCode := congrArg Prod.snd hpq
    have hfixedFloor :
        floorCode thinPlankPackingMesh
            (thinPlankFixedCoordinates x ∘ tube) p =
          floorCode thinPlankPackingMesh
            (thinPlankFixedCoordinates x ∘ tube) q := by
      funext j
      exact congrArg Subtype.val (congrFun hfixedCode j)
    have hwideFloor :
        floorCode thinPlankPackingMesh
            (thinPlankWideCoordinates x ∘ tube) p =
          floorCode thinPlankPackingMesh
            (thinPlankWideCoordinates x ∘ tube) q := by
      funext j
      exact congrArg Subtype.val (congrFun hwideCode j)
    have hclose := wide_anisotropic_close_of_thinPlank_floorCodes_eq
      x (tube p) (tube q) hdeltaPos (hforward p) (hforward q)
      hfixedFloor hwideFloor
    obtain ⟨frame, hframe⟩ := (tube p).exists_alignedFrame
    have hnot := not_essentiallyDistinct_of_wide_anisotropic_close
      x (tube p) (tube q) frame hframe hdeltaPos hdeltaSmall
      (hlong p) hclose.1 hclose.2.1 hclose.2.2
    exact hnot (hpairwise (Set.mem_univ p) (Set.mem_univ q) hpqNe)
  calc
    Fintype.card parameter <= Fintype.card Code :=
      Fintype.card_le_of_injective code hcodeInjective
    _ = thinPlankPackingNatCap R := by
      simpa only [Code] using thinPlankCodeSpace_card_eq R

#print axioms abs_third_sub_lt_four_mul_of_unit_forward
#print axioms dist_le_delta_div_thousand_of_coordinate_close
#print axioms wide_anisotropic_close_of_thinPlank_floorCodes_eq
#print axioms thinPlankCode
#print axioms thinPlankCodeSpace_card_eq
#print axioms card_le_thinPlankPackingNatCap

end
end Family8ThinPlankEssentialDistinctPackingV4
