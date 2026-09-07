import Family8Grounding.Family8CellularCommonInnerLevelV1
import Family8Grounding.Family8CellularJointShadingFromEdgesV1
import Mathlib.Tactic

/-!
# Pointwise P3--P5 from one cellular edge set

This module connects the repair-J1 common inner level to the measurable
shading selected by a finite parent--cell edge set.  The same edge set is
used for the child shading, the parent regions, and the right degree.

The key point is whole-incidence compatibility.  Once one child over a
parent is retained at `x`, the selected parent region contains `x`, so every
J1 child over that parent and point is retained.  Pairwise-disjoint cells
also identify parent-region multiplicity at a point of a cell with the
right degree of that very cell.  These two exact identities feed the finite
P5 lemma without an independent compatibility assumption.
-/

set_option autoImplicit false
set_option warningAsError true
set_option linter.unusedSectionVars false

open Set MeasureTheory
open scoped BigOperators ENNReal NNReal

namespace Family8CellularJointPointwiseP3P5BridgeV1

open LeanEval.Analysis.WangZahlKakeya
open Submission.Kakeya.ConvexGeometry
open Family8CellularCommonInnerLevelV1
open Family8ComparableMultiplicityBucketsV1
open Family8CellularEqualVolumeEdgeMassV1
open Family8CellularEqualVolumeEdgeMassV1.EqualVolumeCells
open Family8CellularJointFactoringFiniteCoreV1
open Family8CellularJointShadingFromEdgesV1

noncomputable section

variable {child parent cell : Type*}
  [Fintype child] [DecidableEq child]
  [Fintype parent] [DecidableEq parent]
  [Fintype cell] [DecidableEq cell]
  {F : ConvexFamily child}

/-! ## P3: whole-incidence preservation inside one selected parent region -/

/-- At a retained child incidence, cellular selection preserves the entire
parent-point fibre, not merely the distinguished child. -/
theorem parentLocalFiberMultiplicity_selectedChildShading_eq
    (Y0 : Shading F) (C : EqualVolumeCells cell)
    (parentOf : child -> parent) (E : Finset (parent × cell))
    (i : child) (x : Space)
    (hx : x ∈ (selectedChildShading Y0 C parentOf E).carrier i) :
    parentLocalFiberMultiplicity (selectedChildShading Y0 C parentOf E)
        parentOf (parentOf i) x =
      parentLocalFiberMultiplicity Y0 parentOf (parentOf i) x := by
  classical
  unfold parentLocalFiberMultiplicity
  apply congrArg Finset.card
  ext j
  simp only [Finset.mem_filter, Finset.mem_univ, true_and]
  constructor
  · rintro ⟨hparent, hxj⟩
    exact ⟨hparent, hxj.1⟩
  · rintro ⟨hparent, hxj⟩
    refine ⟨hparent, hxj, ?_⟩
    simpa [hparent] using hx.2

/-- Pointwise P3 for the selected shading: the J1 dyadic band survives
cellular selection because the latter retains whole parent-point fibres. -/
theorem selectedChildShading_parentLocalFiberMultiplicity_positiveBand
    (Y : Shading F) (C : EqualVolumeCells cell)
    (parentOf : child -> parent) (E : Finset (parent × cell))
    (b : Nat) (i : child) (x : Space)
    (hx : x ∈ (selectedChildShading
      (commonInnerRestriction Y parentOf b) C parentOf E).carrier i) :
    0 < comparableBase b ∧
      comparableBase b ≤
        parentLocalFiberMultiplicity
          (selectedChildShading
            (commonInnerRestriction Y parentOf b) C parentOf E)
          parentOf (parentOf i) x ∧
      parentLocalFiberMultiplicity
          (selectedChildShading
            (commonInnerRestriction Y parentOf b) C parentOf E)
          parentOf (parentOf i) x < 2 * comparableBase b := by
  have hj1 := recomputed_parentLocalFiberMultiplicity_positiveBand
    Y parentOf b i x hx.1
  rw [parentLocalFiberMultiplicity_selectedChildShading_eq
    (commonInnerRestriction Y parentOf b) C parentOf E i x hx]
  exact hj1

/-! ## P4: parent-region multiplicity is the right degree -/

/-- Number of cellular parent regions containing `x`. -/
def parentRegionMultiplicity (C : EqualVolumeCells cell)
    (E : Finset (parent × cell)) (x : Space) : Nat := by
  classical
  exact (Finset.univ.filter fun p => x ∈ C.parentRegion E p).card

/-- At a point of cell `q`, membership in the region of parent `p` is
equivalent to the labelled edge `(p,q)`.  Pairwise disjointness is the
uniqueness input. -/
theorem mem_parentRegion_iff_edge_of_mem_cell
    (C : EqualVolumeCells cell) (E : Finset (parent × cell))
    (p : parent) (q : cell) (x : Space) (hxq : x ∈ C.carrier q) :
    x ∈ C.parentRegion E p ↔ (p, q) ∈ E := by
  constructor
  · intro hx
    rw [parentRegion] at hx
    obtain ⟨q', hxq'⟩ := Set.mem_iUnion.mp hx
    have heq : q'.1 = q := by
      by_contra hne
      have hd : Disjoint (C.carrier q'.1) (C.carrier q) :=
        C.pairwise_disjoint hne
      exact Set.disjoint_left.1 hd hxq' hxq
    subst q
    exact (Finset.mem_filter.mp q'.2).2
  · intro hpq
    rw [parentRegion]
    let q' : {q' // q' ∈ incidentCells E p} :=
      ⟨q, Finset.mem_filter.mpr ⟨Finset.mem_univ q, hpq⟩⟩
    exact Set.mem_iUnion.mpr ⟨q', hxq⟩

/-- Exact P4 identity on a cell. -/
theorem parentRegionMultiplicity_eq_rightDegree_of_mem_cell
    (C : EqualVolumeCells cell) (E : Finset (parent × cell))
    (q : cell) (x : Space) (hxq : x ∈ C.carrier q) :
    parentRegionMultiplicity C E x = rightDegree E q := by
  classical
  unfold parentRegionMultiplicity rightDegree activeParentsAt
  apply congrArg Finset.card
  ext p
  simp only [Finset.mem_filter, Finset.mem_univ, true_and]
  exact mem_parentRegion_iff_edge_of_mem_cell C E p q x hxq

/-- A finite right-degree band therefore becomes the pointwise P4 band on
every point of every selected cell. -/
theorem parentRegionMultiplicity_positiveBand
    (C : EqualVolumeCells cell) (E : Finset (parent × cell))
    (selected : Finset cell) (d : Nat)
    (hband : HasRightDegreeBand E selected d)
    (q : cell) (hq : q ∈ selected) (x : Space)
    (hxq : x ∈ C.carrier q) :
    d ≤ parentRegionMultiplicity C E x ∧
      parentRegionMultiplicity C E x < 2 * d := by
  rw [parentRegionMultiplicity_eq_rightDegree_of_mem_cell C E q x hxq]
  exact hband.2 q hq

/-! ## P5: exact decomposition followed by the finite product bound -/

/-- At a point of cell `q`, the selected child multiplicity is exactly the
sum of its parent-local fibres over the parents active at `q`. -/
theorem selectedChildShading_pointMultiplicity_eq_totalChildMultiplicityAt
    (Y0 : Shading F) (C : EqualVolumeCells cell)
    (parentOf : child -> parent) (E : Finset (parent × cell))
    (q : cell) (x : Space) (hxq : x ∈ C.carrier q) :
    (selectedChildShading Y0 C parentOf E).pointMultiplicity x =
      totalChildMultiplicityAt E
        (fun p _q => parentLocalFiberMultiplicity
          (selectedChildShading Y0 C parentOf E) parentOf p x) q := by
  classical
  let Y1 := selectedChildShading Y0 C parentOf E
  let s : Finset child := Finset.univ.filter fun i => x ∈ Y1.carrier i
  have hmaps : (s : Set child).MapsTo parentOf (activeParentsAt E q) := by
    intro i hi
    have hxi : x ∈ Y1.carrier i := (Finset.mem_filter.mp hi).2
    have hpq : (parentOf i, q) ∈ E :=
      (mem_parentRegion_iff_edge_of_mem_cell C E (parentOf i) q x hxq).1 hxi.2
    exact (mem_activeParentsAt_iff E (parentOf i) q).2 hpq
  change s.card = ∑ p ∈ activeParentsAt E q,
    parentLocalFiberMultiplicity Y1 parentOf p x
  rw [Finset.card_eq_sum_card_fiberwise hmaps]
  apply Finset.sum_congr rfl
  intro p hp
  apply congrArg Finset.card
  ext i
  simp [s, Y1, and_comm]

/-- Every active parent contributes less than twice the common J1 inner
level, including the zero-fibre case. -/
theorem activeParent_innerMultiplicity_lt_two_comparableBase
    (Y : Shading F) (C : EqualVolumeCells cell)
    (parentOf : child -> parent) (E : Finset (parent × cell))
    (b : Nat) (q : cell) (x : Space) (_hxq : x ∈ C.carrier q)
    (p : parent) (_hp : p ∈ activeParentsAt E q)
    (hbpos : 0 < comparableBase b) :
    parentLocalFiberMultiplicity
        (selectedChildShading
          (commonInnerRestriction Y parentOf b) C parentOf E)
        parentOf p x < 2 * comparableBase b := by
  classical
  let Y1 := selectedChildShading
    (commonInnerRestriction Y parentOf b) C parentOf E
  by_cases hex : ∃ i : child, parentOf i = p ∧ x ∈ Y1.carrier i
  · obtain ⟨i, hparent, hxi⟩ := hex
    have hband :=
      selectedChildShading_parentLocalFiberMultiplicity_positiveBand
        Y C parentOf E b i x hxi
    simpa [Y1, hparent] using hband.2.2
  · have hzero : parentLocalFiberMultiplicity Y1 parentOf p x = 0 := by
      simp only [parentLocalFiberMultiplicity, Finset.card_eq_zero,
        Finset.filter_eq_empty_iff, Finset.mem_univ, true_implies]
      intro i hi
      exact hex ⟨i, hi.1, hi.2⟩
    rw [hzero]
    omega

/-- Pointwise P5 from the J1 P3 band and the cellular P4 right-degree band. -/
theorem selectedChildShading_pointMultiplicity_lt_four_mul
    (Y : Shading F) (C : EqualVolumeCells cell)
    (parentOf : child -> parent) (E : Finset (parent × cell))
    (selected : Finset cell) (b d : Nat)
    (hbpos : 0 < comparableBase b)
    (hband : HasRightDegreeBand E selected d)
    (q : cell) (hq : q ∈ selected) (x : Space)
    (hxq : x ∈ C.carrier q) :
    (selectedChildShading
      (commonInnerRestriction Y parentOf b) C parentOf E).pointMultiplicity x <
      4 * comparableBase b * d := by
  rw [selectedChildShading_pointMultiplicity_eq_totalChildMultiplicityAt
    (commonInnerRestriction Y parentOf b) C parentOf E q x hxq]
  apply p5_totalChildMultiplicityAt_lt_four_mul
  · exact hbpos
  · intro p hp
    exact activeParent_innerMultiplicity_lt_two_comparableBase
      Y C parentOf E b q x hxq p hp hbpos
  · exact (hband.2 q hq).2

#print axioms parentLocalFiberMultiplicity_selectedChildShading_eq
#print axioms selectedChildShading_parentLocalFiberMultiplicity_positiveBand
#print axioms parentRegionMultiplicity_eq_rightDegree_of_mem_cell
#print axioms selectedChildShading_pointMultiplicity_eq_totalChildMultiplicityAt
#print axioms selectedChildShading_pointMultiplicity_lt_four_mul

end
end Family8CellularJointPointwiseP3P5BridgeV1
