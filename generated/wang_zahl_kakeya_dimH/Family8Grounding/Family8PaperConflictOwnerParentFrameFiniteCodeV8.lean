import Family8Grounding.Family8PaperConflictOwnerParentFrameBoundsV2
import FamilyStickyRandomFiniteFloorParameterNetV1
import Mathlib.Tactic

set_option autoImplicit false
set_option warningAsError true

open Set
open scoped NNReal InnerProductSpace

namespace Family8PaperConflictOwnerParentFrameFiniteCodeV8

open LeanEval.Analysis.WangZahlKakeya
open Submission.Kakeya.ConvexGeometry
open Submission.Kakeya.Uniformity
open Family8CommonPointTubePackingV1
open Family8PaperConflictOwnerParentFrameBoundsV2
open Family8PaperEssentialDistinctOwnerClusterRetentionV3
open FamilyStickyAtEveryScaleCoreV1
open FamilyStickyTubeParentDirectionCoherenceV1
open FamilyStickyRandomFiniteFloorParameterNetV1

noncomputable section

/-!
# A finite parent-frame code for conflict owners

For one old `rho`-parent, transverse position and direction are normalized
by `rho` and put on fixed grids.  The longitudinal coordinate lies only in
`[-4,4]`, so its mesh is `rho`.  The resulting honest number of codes is
`O(rho⁻¹)`, not a scale-independent constant.

Equal codes give `rho`-accuracy in all seven physical parent-frame
coordinates.  A literal common coarse-tube containment is deliberately not
postulated here.
-/

/-- Orient an owner direction deterministically toward the old parent. -/
def parentOrientedDirection {delta rho : NNReal}
    (parent : Tube rho) (owner : Tube delta) : Space :=
  if ‖owner.axis.direction - parent.axis.direction‖ ≤ 14 * (rho : Real) then
    owner.axis.direction
  else
    -owner.axis.direction

theorem norm_parentOrientedDirection_sub_parent_le_fourteen_mul
    {delta rho : NNReal} {parent : Tube rho} {owner : Tube delta}
    (hclose : UnorientedDirectionClose owner.axis parent.axis
      (14 * (rho : Real))) :
    ‖parentOrientedDirection parent owner - parent.axis.direction‖ ≤
      14 * (rho : Real) := by
  rw [parentOrientedDirection]
  split_ifs with hforward
  · exact hforward
  · rcases hclose with hclose | hclose
    · exact (hforward hclose).elim
    · have heq :
          (-owner.axis.direction) - parent.axis.direction =
            -(owner.axis.direction + parent.axis.direction) := by
        module
      rw [heq, norm_neg]
      exact hclose

def parentFrameLongCoordinates {delta rho : NNReal}
    (parent : Tube rho) (owner : Tube delta) : Fin 1 → Real :=
  ![parentFrameLongitudinalOffset parent owner]

def parentFrameShapeCoordinates {delta rho : NNReal}
    (parent : Tube rho) (owner : Tube delta) : Fin 6 → Real :=
  ![parentFrameTransverseOffset parent owner 0 / (rho : Real),
    parentFrameTransverseOffset parent owner 1 / (rho : Real),
    parentFrameTransverseOffset parent owner 2 / (rho : Real),
    (parentOrientedDirection parent owner - parent.axis.direction) 0 /
      (rho : Real),
    (parentOrientedDirection parent owner - parent.axis.direction) 1 /
      (rho : Real),
    (parentOrientedDirection parent owner - parent.axis.direction) 2 /
      (rho : Real)]

theorem abs_parentFrameLongCoordinates_le_four
    {delta rho : NNReal} {parameter : Type}
    (parent : Tube rho) (owner : parameter → Tube delta)
    (hlong : ∀ p,
      |parentFrameLongitudinalOffset parent (owner p)| ≤ 4)
    (p : parameter) (j : Fin 1) :
    |parentFrameLongCoordinates parent (owner p) j| ≤ 4 := by
  fin_cases j
  simpa [parentFrameLongCoordinates] using hlong p

theorem abs_parentFrameShapeCoordinates_le_hundred
    {delta rho : NNReal} (hrhoPos : 0 < rho)
    {parameter : Type} (parent : Tube rho) (owner : parameter → Tube delta)
    (hdirection : ∀ p,
      UnorientedDirectionClose (owner p).axis parent.axis
        (14 * (rho : Real)))
    (htransverse : ∀ p,
      ‖parentFrameTransverseOffset parent (owner p)‖ ≤ 94 * (rho : Real))
    (p : parameter) (j : Fin 6) :
    |parentFrameShapeCoordinates parent (owner p) j| ≤ 100 := by
  have hrhoReal : 0 < (rho : Real) := NNReal.coe_pos.mpr hrhoPos
  have hdir :
      ‖parentOrientedDirection parent (owner p) - parent.axis.direction‖ ≤
        14 * (rho : Real) :=
    norm_parentOrientedDirection_sub_parent_le_fourteen_mul (hdirection p)
  have htrans := htransverse p
  fin_cases j <;>
    change |_ / (rho : Real)| ≤ 100 <;>
    rw [abs_div, abs_of_pos hrhoReal] <;>
    apply (div_le_iff₀ hrhoReal).2
  · exact (abs_apply_le_norm
      (parentFrameTransverseOffset parent (owner p)) 0).trans
        (htrans.trans (by nlinarith [hrhoReal.le]))
  · exact (abs_apply_le_norm
      (parentFrameTransverseOffset parent (owner p)) 1).trans
        (htrans.trans (by nlinarith [hrhoReal.le]))
  · exact (abs_apply_le_norm
      (parentFrameTransverseOffset parent (owner p)) 2).trans
        (htrans.trans (by nlinarith [hrhoReal.le]))
  · exact (abs_apply_le_norm
      (parentOrientedDirection parent (owner p) - parent.axis.direction) 0).trans
        (hdir.trans (by nlinarith [hrhoReal.le]))
  · exact (abs_apply_le_norm
      (parentOrientedDirection parent (owner p) - parent.axis.direction) 1).trans
        (hdir.trans (by nlinarith [hrhoReal.le]))
  · exact (abs_apply_le_norm
      (parentOrientedDirection parent (owner p) - parent.axis.direction) 2).trans
        (hdir.trans (by nlinarith [hrhoReal.le]))

def parentFrameLongCodeCount (rho : NNReal) : Nat :=
  (Int.floor (4 / (rho : Real)) + 1 -
    Int.floor (-4 / (rho : Real))).toNat

def parentFrameShapeCodeCount : Nat := (Int.toNat 201) ^ 6

def parentFrameCodeCount (rho : NNReal) : Nat :=
  parentFrameLongCodeCount rho * parentFrameShapeCodeCount

def parentFrameCode
    {delta rho : NNReal} {parameter : Type}
    (hrhoPos : 0 < rho) (parent : Tube rho)
    (owner : parameter → Tube delta)
    (hlong : ∀ p,
      |parentFrameLongitudinalOffset parent (owner p)| ≤ 4)
    (hdirection : ∀ p,
      UnorientedDirectionClose (owner p).axis parent.axis
        (14 * (rho : Real)))
    (htransverse : ∀ p,
      ‖parentFrameTransverseOffset parent (owner p)‖ ≤ 94 * (rho : Real))
    (p : parameter) :
    BoundedCode (Fin 1) (rho : Real) 4 × BoundedCode (Fin 6) 1 100 :=
  (boundedFloorCode (rho : Real) 4 (NNReal.coe_pos.mpr hrhoPos)
      (parentFrameLongCoordinates parent ∘ owner)
      (abs_parentFrameLongCoordinates_le_four parent owner hlong) p,
    boundedFloorCode 1 100 (by norm_num)
      (parentFrameShapeCoordinates parent ∘ owner)
      (abs_parentFrameShapeCoordinates_le_hundred hrhoPos parent owner
        hdirection htransverse) p)

theorem parentFrameCode_image_card_le
    {delta rho : NNReal} (hrhoPos : 0 < rho)
    {parameter : Type} [Fintype parameter] [DecidableEq parameter]
    (parent : Tube rho) (owner : parameter → Tube delta)
    (hlong : ∀ p,
      |parentFrameLongitudinalOffset parent (owner p)| ≤ 4)
    (hdirection : ∀ p,
      UnorientedDirectionClose (owner p).axis parent.axis
        (14 * (rho : Real)))
    (htransverse : ∀ p,
      ‖parentFrameTransverseOffset parent (owner p)‖ ≤ 94 * (rho : Real)) :
    ((Finset.univ : Finset parameter).image
      (parentFrameCode hrhoPos parent owner hlong hdirection htransverse)).card ≤
      parentFrameCodeCount rho := by
  classical
  let Code :=
    BoundedCode (Fin 1) (rho : Real) 4 × BoundedCode (Fin 6) 1 100
  have hsubset :
      (Finset.univ : Finset parameter).image
          (parentFrameCode hrhoPos parent owner hlong hdirection htransverse) ⊆
        (Finset.univ : Finset Code) := by
    simp
  calc
    ((Finset.univ : Finset parameter).image
        (parentFrameCode hrhoPos parent owner hlong hdirection htransverse)).card ≤
        (Finset.univ : Finset Code).card := Finset.card_le_card hsubset
    _ = parentFrameCodeCount rho := by
      rw [Finset.card_univ]
      dsimp only [Code]
      rw [Fintype.card_prod]
      unfold parentFrameCodeCount
      congr 1
      · rw [Fintype.card_fun, Fintype.card_coe]
        unfold codeInterval parentFrameLongCodeCount
        rw [Int.card_Icc]
        simp
      · rw [Fintype.card_fun, Fintype.card_coe]
        unfold codeInterval parentFrameShapeCodeCount
        rw [Int.card_Icc]
        norm_num

theorem parentFrameCode_eq_coordinate_close
    {delta rho : NNReal} (hrhoPos : 0 < rho)
    {parameter : Type} (parent : Tube rho)
    (owner : parameter → Tube delta)
    (hlong : ∀ p,
      |parentFrameLongitudinalOffset parent (owner p)| ≤ 4)
    (hdirection : ∀ p,
      UnorientedDirectionClose (owner p).axis parent.axis
        (14 * (rho : Real)))
    (htransverse : ∀ p,
      ‖parentFrameTransverseOffset parent (owner p)‖ ≤ 94 * (rho : Real))
    {p q : parameter}
    (hcode : parentFrameCode hrhoPos parent owner hlong hdirection htransverse p =
      parentFrameCode hrhoPos parent owner hlong hdirection htransverse q) :
    |parentFrameLongitudinalOffset parent (owner p) -
        parentFrameLongitudinalOffset parent (owner q)| < (rho : Real) ∧
      ∀ j : Fin 6,
        |parentFrameShapeCoordinates parent (owner p) j -
          parentFrameShapeCoordinates parent (owner q) j| < 1 := by
  have hlongCode := congrArg Prod.fst hcode
  have hshapeCode := congrArg Prod.snd hcode
  have hlongFloor :
      floorCode (rho : Real) (parentFrameLongCoordinates parent ∘ owner) p =
        floorCode (rho : Real) (parentFrameLongCoordinates parent ∘ owner) q := by
    funext j
    exact congrArg Subtype.val (congrFun hlongCode j)
  have hshapeFloor :
      floorCode 1 (parentFrameShapeCoordinates parent ∘ owner) p =
        floorCode 1 (parentFrameShapeCoordinates parent ∘ owner) q := by
    funext j
    exact congrArg Subtype.val (congrFun hshapeCode j)
  constructor
  · simpa [parentFrameLongCoordinates] using
      abs_coord_sub_lt_of_floorCode_eq (NNReal.coe_pos.mpr hrhoPos)
        (parentFrameLongCoordinates parent ∘ owner) hlongFloor (0 : Fin 1)
  · intro j
    exact abs_coord_sub_lt_of_floorCode_eq (by norm_num)
      (parentFrameShapeCoordinates parent ∘ owner) hshapeFloor j

theorem exists_scaleCover_owner_parentFrameCode
    {delta rho : NNReal} {index : Type} [Fintype index]
    [DecidableEq index] {fine : UniformTubeFamily delta index}
    {weight : index → ENNReal}
    (C : PaperConflictOwnerClustering
      (Finset.univ : Finset index) fine.tubes weight)
    (S : StickyScaleCover fine rho)
    (hdeltaSmall : delta ≤ (1 / 100 : NNReal))
    (hdeltaRho : delta ≤ rho) (hrhoPos : 0 < rho) (hrhoOne : rho ≤ 1)
    (k : Fin S.coarseCard) :
    ∃ code : ↥(C.sourceOwnerImage (S.fiber k)) →
        BoundedCode (Fin 1) (rho : Real) 4 × BoundedCode (Fin 6) 1 100,
      ((Finset.univ : Finset ↥(C.sourceOwnerImage (S.fiber k))).image code).card ≤
        parentFrameCodeCount rho ∧
      ∀ p q, code p = code q →
        |parentFrameLongitudinalOffset (S.coarse.tubes k) (fine.tubes p.1) -
          parentFrameLongitudinalOffset (S.coarse.tubes k) (fine.tubes q.1)| <
            (rho : Real) ∧
        ∀ j : Fin 6,
          |parentFrameShapeCoordinates (S.coarse.tubes k) (fine.tubes p.1) j -
            parentFrameShapeCoordinates (S.coarse.tubes k) (fine.tubes q.1) j| <
              1 := by
  classical
  let Parameter := ↥(C.sourceOwnerImage (S.fiber k))
  let parent : Tube rho := S.coarse.tubes k
  let owner : Parameter → Tube delta := fun p => fine.tubes p.1
  have hbounds : ∀ p : Parameter,
      UnorientedDirectionClose (owner p).axis parent.axis
          (14 * (rho : Real)) ∧
        ‖parentFrameTransverseOffset parent (owner p)‖ ≤ 94 * (rho : Real) ∧
        |parentFrameLongitudinalOffset parent (owner p)| ≤ 4 := by
    intro p
    obtain ⟨a, ha, howner⟩ := Finset.mem_image.mp p.property
    have h := scaleCover_owner_parentFrame_bounds C S hdeltaSmall
      hdeltaRho hrhoOne k a ha
    simpa only [owner, parent, howner] using h
  let hlong : ∀ p : Parameter,
      |parentFrameLongitudinalOffset parent (owner p)| ≤ 4 :=
    fun p => (hbounds p).2.2
  let hdirection : ∀ p : Parameter,
      UnorientedDirectionClose (owner p).axis parent.axis
        (14 * (rho : Real)) := fun p => (hbounds p).1
  let htransverse : ∀ p : Parameter,
      ‖parentFrameTransverseOffset parent (owner p)‖ ≤ 94 * (rho : Real) :=
    fun p => (hbounds p).2.1
  let code : Parameter →
      BoundedCode (Fin 1) (rho : Real) 4 × BoundedCode (Fin 6) 1 100 :=
    parentFrameCode hrhoPos parent owner hlong hdirection htransverse
  refine ⟨code, ?_, ?_⟩
  · exact parentFrameCode_image_card_le hrhoPos parent owner hlong
      hdirection htransverse
  · intro p q hpq
    simpa only [Parameter, parent, owner, code] using
      parentFrameCode_eq_coordinate_close hrhoPos parent owner hlong
        hdirection htransverse hpq

#print axioms norm_parentOrientedDirection_sub_parent_le_fourteen_mul
#print axioms abs_parentFrameShapeCoordinates_le_hundred
#print axioms parentFrameCode_image_card_le
#print axioms parentFrameCode_eq_coordinate_close
#print axioms exists_scaleCover_owner_parentFrameCode

end
end Family8PaperConflictOwnerParentFrameFiniteCodeV8
