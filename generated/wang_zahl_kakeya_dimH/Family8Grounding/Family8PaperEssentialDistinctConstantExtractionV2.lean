import Family8Grounding.Family8PaperConflictOrientedCoordinatesV5
import Family8Grounding.Family8PaperConflictWideAnisotropicOverlapV1
import FamilyStickyGrounding.Cinematic.FamilyStickyCinematicL32Lemma316FiniteGreedyIncomparableSelectionV1
import Mathlib.Tactic

set_option autoImplicit false
set_option warningAsError true

open Set
open scoped ENNReal NNReal BigOperators InnerProductSpace

namespace Family8PaperEssentialDistinctConstantExtractionV2

open LeanEval.Analysis.WangZahlKakeya
open Submission.Kakeya.ConvexGeometry
open Family4GlobalExtremalUpstream
open Family8Def212ConvexWolffAtEveryScaleV2
open Family8CommonPointTubePackingV1
open Family8PaperConflictAnisotropicBoundsV4
open Family8PaperConflictOrientedCoreV1
open Family8PaperConflictOrientedCoordinatesV5
open Family8PaperConflictWideAnisotropicOverlapV1
open FamilyStickyCinematicL32Lemma316FiniteGreedyIncomparableSelectionV1

noncomputable section

/-! Scale-independent paper-conflict degree and weighted greedy extraction. -/

def paperConflictIndices
    {delta : NNReal} {index : Type*} [DecidableEq index]
    (vertices : Finset index) (tube : index → Tube delta) (a : index) :
    Finset index := by
  classical
  exact vertices.filter fun b => PaperConflict (tube a) (tube b)

def paperConflictConstantCodeLoss : Nat :=
  ((Int.floor (40 / paperConflictConstantMesh) + 1 -
      Int.floor (-40 / paperConflictConstantMesh)).toNat) ^ 7

theorem paperConflict_iff_not_paperEssentiallyDistinct
    {delta : NNReal} (T U : Tube delta) :
    PaperConflict T U ↔ ¬ PaperEssentiallyDistinct T U := by
  simp only [PaperConflict, PaperEssentiallyDistinct,
    not_and_or, Classical.not_not]

theorem paperConflictIndices_card_le_constant
    {delta : NNReal} {index : Type*} [DecidableEq index]
    (vertices : Finset index) (tube : index → Tube delta)
    (hdeltaPos : 0 < delta) (hdeltaSmall : delta ≤ (1 / 100 : NNReal))
    (hpairwise : Set.Pairwise (↑vertices : Set index) fun i j =>
      EssentiallyDistinct (tube i) (tube j))
    (anchor : index) :
    (paperConflictIndices vertices tube anchor).card ≤
      paperConflictConstantCodeLoss := by
  classical
  let active : Finset index := paperConflictIndices vertices tube anchor
  let Parameter := ↥active
  let mesh : Real := paperConflictConstantMesh
  let bound : Real := 40
  let coord : Parameter → Fin 7 → Real := fun p =>
    paperConflictNormalizedCoordinates (tube anchor) (tube p.1)
  have hmesh : 0 < mesh := by
    norm_num [mesh, paperConflictConstantMesh]
  have hbound : ∀ p : Parameter, ∀ k, |coord p k| ≤ bound := by
    intro p k
    have hp : p.1 ∈ vertices ∧
        PaperConflict (tube anchor) (tube p.1) := by
      simpa only [active, paperConflictIndices, Finset.mem_filter] using
        p.property
    simpa only [coord, bound] using
      abs_paperConflictNormalizedCoordinates_le_forty
        hdeltaPos hdeltaSmall hp.2 k
  let Code :=
    FamilyStickyRandomFiniteFloorParameterNetV1.OccupiedCode
      mesh bound hmesh coord hbound
  let code : Parameter → Code := fun p =>
    FamilyStickyRandomFiniteFloorParameterNetV1.ownCode
      mesh bound hmesh coord hbound p
  have hcodeInjective : Function.Injective code := by
    intro p q hpq
    apply Subtype.ext
    by_contra hpqVal
    have hpData : p.1 ∈ vertices ∧
        PaperConflict (tube anchor) (tube p.1) := by
      simpa only [active, paperConflictIndices, Finset.mem_filter] using
        p.property
    have hqData : q.1 ∈ vertices ∧
        PaperConflict (tube anchor) (tube q.1) := by
      simpa only [active, paperConflictIndices, Finset.mem_filter] using
        q.property
    have hboundedEq :
        FamilyStickyRandomFiniteFloorParameterNetV1.boundedFloorCode
            mesh bound hmesh coord hbound p =
          FamilyStickyRandomFiniteFloorParameterNetV1.boundedFloorCode
            mesh bound hmesh coord hbound q :=
      congrArg Subtype.val hpq
    have hfloorEq :
        FamilyStickyRandomFiniteFloorParameterNetV1.floorCode mesh coord p =
          FamilyStickyRandomFiniteFloorParameterNetV1.floorCode mesh coord q := by
      funext k
      exact congrArg Subtype.val (congrFun hboundedEq k)
    have hfloorTube :
        FamilyStickyRandomFiniteFloorParameterNetV1.floorCode
            paperConflictConstantMesh
            (paperConflictNormalizedCoordinates (tube anchor)) (tube p.1) =
          FamilyStickyRandomFiniteFloorParameterNetV1.floorCode
            paperConflictConstantMesh
            (paperConflictNormalizedCoordinates (tube anchor)) (tube q.1) := by
      funext k
      have hk := congrFun hfloorEq k
      change Int.floor
          (paperConflictNormalizedCoordinates (tube anchor) (tube p.1) k /
            paperConflictConstantMesh) =
        Int.floor
          (paperConflictNormalizedCoordinates (tube anchor) (tube q.1) k /
            paperConflictConstantMesh) at hk
      exact hk
    have hclose := wide_anisotropic_close_of_floorCode_eq
      hdeltaPos (tube anchor) (tube p.1) (tube q.1) hfloorTube
    let T' := paperConflictOrientedTube (tube anchor) (tube p.1)
    let U' := paperConflictOrientedTube (tube anchor) (tube q.1)
    have hconflictT' : PaperConflict (tube anchor) T' := by
      simpa only [T'] using paperConflict_oriented_right hpData.2
    have haT :
        |tubePointLongitudinal (tubeAxisMidpoint (tube anchor)) T'| ≤ 2 :=
      abs_tubePointLongitudinal_anchor_le_two hdeltaSmall hconflictT'
    obtain ⟨frame, hframe⟩ := T'.exists_alignedFrame
    have hnot : ¬ EssentiallyDistinct T' U' :=
      not_essentiallyDistinct_of_wide_anisotropic_close
        (tubeAxisMidpoint (tube anchor)) T' U' frame hframe
        hdeltaPos hdeltaSmall haT hclose.1 hclose.2.1 hclose.2.2
    have hessential : EssentiallyDistinct (tube p.1) (tube q.1) :=
      hpairwise hpData.1 hqData.1 hpqVal
    have hessential' : EssentiallyDistinct T' U' :=
      (essentiallyDistinct_oriented_iff
        (tube anchor) (tube p.1) (tube q.1)).2 hessential
    exact hnot hessential'
  have hparamCode : Fintype.card Parameter ≤ Fintype.card Code :=
    Fintype.card_le_of_injective code hcodeInjective
  have hcodeCard : Fintype.card Code ≤ paperConflictConstantCodeLoss := by
    have h := FamilyStickyRandomFiniteFloorParameterNetV1.card_occupiedCode_le
      mesh bound hmesh coord hbound
    simpa only [Code, mesh, bound, paperConflictConstantCodeLoss,
      Fintype.card_fin] using h
  change active.card ≤ paperConflictConstantCodeLoss
  calc
    active.card = Fintype.card Parameter := by
      simp only [Parameter, Fintype.card_coe]
    _ ≤ Fintype.card Code := hparamCode
    _ ≤ paperConflictConstantCodeLoss := hcodeCard

def paperClosedConflictIndices
    {delta : NNReal} {index : Type*} [DecidableEq index]
    (vertices : Finset index) (tube : index → Tube delta) (a : index) :
    Finset index := by
  classical
  exact vertices.filter fun b => b = a ∨ PaperConflict (tube a) (tube b)

theorem paperClosedConflictIndices_card_le_constant
    {delta : NNReal} {index : Type*} [DecidableEq index]
    (vertices : Finset index) (tube : index → Tube delta)
    (hdeltaPos : 0 < delta) (hdeltaSmall : delta ≤ (1 / 100 : NNReal))
    (hpairwise : Set.Pairwise (↑vertices : Set index) fun i j =>
      EssentiallyDistinct (tube i) (tube j))
    (a : index) :
    (paperClosedConflictIndices vertices tube a).card ≤
      paperConflictConstantCodeLoss + 1 := by
  classical
  have hsubset : paperClosedConflictIndices vertices tube a ⊆
      insert a (paperConflictIndices vertices tube a) := by
    intro b hb
    have hb' : b ∈ vertices ∧
        (b = a ∨ PaperConflict (tube a) (tube b)) := by
      simpa only [paperClosedConflictIndices, Finset.mem_filter] using hb
    rcases hb'.2 with rfl | hconflict
    · exact Finset.mem_insert_self _ _
    · exact Finset.mem_insert_of_mem
        (by simpa only [paperConflictIndices, Finset.mem_filter] using
          And.intro hb'.1 hconflict)
  calc
    (paperClosedConflictIndices vertices tube a).card ≤
        (insert a (paperConflictIndices vertices tube a)).card :=
      Finset.card_le_card hsubset
    _ ≤ (paperConflictIndices vertices tube a).card + 1 :=
      Finset.card_insert_le _ _
    _ ≤ paperConflictConstantCodeLoss + 1 :=
      Nat.add_le_add_right
        (paperConflictIndices_card_le_constant vertices tube hdeltaPos
          hdeltaSmall hpairwise a) 1

theorem exists_paperEssentiallyDistinct_constant_greedyExtraction
    {delta : NNReal} {index : Type*} [DecidableEq index]
    (vertices : Finset index) (tube : index → Tube delta)
    (hdeltaPos : 0 < delta) (hdeltaSmall : delta ≤ (1 / 100 : NNReal))
    (hpairwise : Set.Pairwise (↑vertices : Set index) fun i j =>
      EssentiallyDistinct (tube i) (tube j))
    (weight : index → ENNReal) :
    ∃ selected : Finset index,
      selected ⊆ vertices ∧
      (vertices.Nonempty → selected.Nonempty) ∧
      (Set.Pairwise (↑selected : Set index) fun i j =>
        PaperEssentiallyDistinct (tube i) (tube j)) ∧
      (vertices.card : ENNReal) ≤
        (paperConflictConstantCodeLoss + 1 : Nat) *
          (selected.card : ENNReal) ∧
      (∑ i ∈ vertices, weight i) ≤
        (paperConflictConstantCodeLoss + 1 : Nat) *
          ∑ i ∈ selected, weight i := by
  classical
  have hneighbour : ∀ a, a ∈ vertices →
      ((vertices.filter fun b =>
        b = a ∨ PaperConflict (tube a) (tube b)).card : ENNReal) ≤
        (paperConflictConstantCodeLoss + 1 : Nat) := by
    intro a _ha
    change ((paperClosedConflictIndices vertices tube a).card : ENNReal) ≤
      (paperConflictConstantCodeLoss + 1 : Nat)
    exact_mod_cast paperClosedConflictIndices_card_le_constant
      vertices tube hdeltaPos hdeltaSmall hpairwise a
  have hsymm : Std.Symm (fun i j => PaperConflict (tube i) (tube j)) := by
    constructor
    intro i j hij
    exact paperConflict_symm.symm (tube i) (tube j) hij
  obtain ⟨selected, hselected, hnonempty, hpair, hcard, hmass⟩ :=
    exists_greedy_pairwise_not_relation vertices
      (fun i j => PaperConflict (tube i) (tube j))
      hsymm weight (paperConflictConstantCodeLoss + 1 : Nat) hneighbour
  refine ⟨selected, hselected, hnonempty, ?_, hcard, hmass⟩
  intro i hi j hj hij
  have hnotConflict := hpair hi hj hij
  by_contra hnotPaper
  exact hnotConflict
    ((paperConflict_iff_not_paperEssentiallyDistinct (tube i) (tube j)).2
      hnotPaper)

#print axioms paperConflictIndices_card_le_constant
#print axioms paperClosedConflictIndices_card_le_constant
#print axioms exists_paperEssentiallyDistinct_constant_greedyExtraction

end

end Family8PaperEssentialDistinctConstantExtractionV2
