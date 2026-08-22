import Submission.Kakeya.ConvexFactoring.IndexPartition
import Submission.Kakeya.ConvexFactoring.Refinement

namespace Submission.Kakeya.ConvexFactoring

open LeanEval.Analysis.WangZahlKakeya
open Submission.Kakeya.ConvexGeometry

/-!
# Geometric convex factorizations

This module combines an index factorization with geometric containment of each
active fine body in its assigned coarse body.  It constructs the induced coarse
shading and records the exact pointwise multiplicity identities supplied by the
finite partition.
-/

/-- A geometric factorization: fine bodies are assigned to containing coarse bodies. -/
structure ConvexFactorization {ι κ : Type*} [DecidableEq ι] [DecidableEq κ]
    (F : ConvexFamily ι) (W : ConvexFamily κ) where
  index : IndexFactorization ι κ
  contained : ∀ i ∈ index.fine, (F i : Set Space) ⊆ (W (index.parent i) : Set Space)

namespace ConvexFactorization

variable {ι κ : Type*} [DecidableEq ι] [DecidableEq κ]
  {F : ConvexFamily ι} {W : ConvexFamily κ}

/-- The union of active fine bodies. -/
def fineUnion (P : ConvexFactorization F W) : Set Space :=
  ⋃ i : {i // i ∈ P.index.fine}, (F i.1 : Set Space)

/-- The union of active coarse bodies. -/
def coarseUnion (P : ConvexFactorization F W) : Set Space :=
  ⋃ k : {k // k ∈ P.index.coarse}, (W k.1 : Set Space)

/-- Containment witnesses make the active fine union coverable by the active coarse union. -/
theorem fineUnion_subset_coarseUnion (P : ConvexFactorization F W) :
    P.fineUnion ⊆ P.coarseUnion := by
  intro x hx
  obtain ⟨i, hxi⟩ := Set.mem_iUnion.mp hx
  let k : {k // k ∈ P.index.coarse} :=
    ⟨P.index.parent i.1, P.index.parent_mem i.1 i.2⟩
  exact Set.mem_iUnion.mpr ⟨k, P.contained i.1 i.2 hxi⟩

/-- The coarse shading obtained by taking the union of the shaded fine fibers. -/
def inducedShading (P : ConvexFactorization F W) (Y : Shading F) : Shading W where
  carrier := fun k ↦ if hk : k ∈ P.index.coarse then
    ⋃ i : {i // i ∈ P.index.fiber k}, Y.carrier i.1
    else ∅
  measurable_carrier := fun k ↦ by
    split_ifs with hk
    · exact MeasurableSet.iUnion fun i ↦ Y.measurable_carrier i.1
    · exact MeasurableSet.empty
  carrier_subset := fun k ↦ by
    split_ifs with hk
    · intro x hx
      obtain ⟨i, hxi⟩ := Set.mem_iUnion.mp hx
      have hmem := P.index.mem_fiber i.1 k |>.1 i.2
      have hxW := P.contained i.1 hmem.1 (Y.carrier_subset i.1 hxi)
      simpa [hmem.2] using hxW
    · exact Set.empty_subset _

/-- Membership in the induced coarse shading is witnessed by an active fine fiber. -/
theorem mem_inducedShading_carrier_iff (P : ConvexFactorization F W)
    (Y : Shading F) (k : κ) (x : Space) :
    x ∈ (P.inducedShading Y).carrier k ↔
      k ∈ P.index.coarse ∧ ∃ i ∈ P.index.fiber k, x ∈ Y.carrier i := by
  classical
  simp [inducedShading]

/-- The induced coarse shading has exactly the same union as the active fine shading. -/
theorem inducedShading_shadedUnion_eq
    (P : ConvexFactorization F W) (Y : Shading F) :
    (P.inducedShading Y).shadedUnion =
      (IndexedShadingRefinement.restrictTo Y P.index.fine).shading.shadedUnion := by
  ext x
  constructor
  · intro hx
    obtain ⟨k, hxk⟩ := Set.mem_iUnion.mp hx
    obtain ⟨_hk, i, hiFiber, hxi⟩ :=
      (P.mem_inducedShading_carrier_iff Y k x).1 hxk
    exact Set.mem_iUnion.mpr ⟨i, by
      simp only [IndexedShadingRefinement.restrictTo_carrier]
      rw [if_pos (P.index.fiber_subset_fine k hiFiber)]
      exact hxi⟩
  · intro hx
    obtain ⟨i, hxi⟩ := Set.mem_iUnion.mp hx
    have hiFine : i ∈ P.index.fine := by
      by_contra hi
      simp [IndexedShadingRefinement.restrictTo_carrier, hi] at hxi
    have hxiY : x ∈ Y.carrier i := by
      rw [IndexedShadingRefinement.restrictTo_carrier, if_pos hiFine] at hxi
      exact hxi
    let k := P.index.parent i
    apply Set.mem_iUnion.mpr
    refine ⟨k, (P.mem_inducedShading_carrier_iff Y k x).2 ?_⟩
    exact ⟨P.index.parent_mem i hiFine, i,
      (P.index.mem_fiber i k).2 ⟨hiFine, rfl⟩, hxiY⟩

/-- Fine shaded multiplicity restricted to the active indices. -/
noncomputable def fineMultiplicity (P : ConvexFactorization F W)
    (Y : Shading F) (x : Space) : ℕ := by
  classical
  exact (P.index.fine.filter fun i ↦ x ∈ Y.carrier i).card

/-- Multiplicity inside one fine fiber. -/
noncomputable def fiberMultiplicity (P : ConvexFactorization F W) (Y : Shading F)
    (k : κ) (x : Space) : ℕ := by
  classical
  exact ((P.index.fiber k).filter fun i ↦ x ∈ Y.carrier i).card

/-- Number of active coarse fibers whose induced shading contains a point. -/
noncomputable def outerMultiplicity (P : ConvexFactorization F W)
    (Y : Shading F) (x : Space) : ℕ := by
  classical
  exact (P.index.coarse.filter fun k ↦
    x ∈ (P.inducedShading Y).carrier k).card

private theorem card_filter_eq_sum_indicator {α : Type*} [DecidableEq α]
    (s : Finset α) (p : α → Prop) [DecidablePred p] :
    (s.filter p).card = ∑ i ∈ s, if p i then 1 else 0 := by
  induction s using Finset.induction_on with
  | empty => simp
  | @insert a s ha ih => simp_all

/-- Fine multiplicity is the exact sum of the fiber multiplicities. -/
theorem fineMultiplicity_eq_sum_fiberMultiplicity
    (P : ConvexFactorization F W) (Y : Shading F) (x : Space) :
    P.fineMultiplicity Y x =
      ∑ k ∈ P.index.coarse, P.fiberMultiplicity Y k x := by
  classical
  rw [fineMultiplicity, card_filter_eq_sum_indicator]
  simp_rw [fiberMultiplicity, card_filter_eq_sum_indicator]
  exact P.index.sum_fiberwise (fun i ↦ if x ∈ Y.carrier i then 1 else 0)

/-- An induced coarse fiber is occupied exactly when its fine multiplicity is positive. -/
theorem mem_inducedShading_iff_fiberMultiplicity_pos
    (P : ConvexFactorization F W) (Y : Shading F) (k : κ) (x : Space) :
    x ∈ (P.inducedShading Y).carrier k ↔ 0 < P.fiberMultiplicity Y k x := by
  classical
  rw [P.mem_inducedShading_carrier_iff Y k x]
  constructor
  · rintro ⟨_hk, i, hiFiber, hxi⟩
    rw [fiberMultiplicity, Finset.card_pos]
    exact ⟨i, Finset.mem_filter.mpr ⟨hiFiber, hxi⟩⟩
  · intro hpos
    rw [fiberMultiplicity, Finset.card_pos] at hpos
    obtain ⟨i, hi⟩ := hpos
    obtain ⟨hiFiber, hxi⟩ := Finset.mem_filter.mp hi
    have hiFine := P.index.fiber_subset_fine k hiFiber
    have hparent : P.index.parent i = k := (P.index.mem_fiber i k).1 hiFiber |>.2
    exact ⟨hparent ▸ P.index.parent_mem i hiFine, i, hiFiber, hxi⟩

/-- Pointwise multiplicity factors through outer multiplicity and a uniform
upper bound for every active fiber. -/
theorem fineMultiplicity_le_outer_mul
    (P : ConvexFactorization F W) (Y : Shading F) (x : Space) (M : ℕ)
    (hM : ∀ k ∈ P.index.coarse, P.fiberMultiplicity Y k x ≤ M) :
    P.fineMultiplicity Y x ≤ P.outerMultiplicity Y x * M := by
  classical
  rw [P.fineMultiplicity_eq_sum_fiberMultiplicity Y x]
  let occupied := P.index.coarse.filter fun k ↦
    x ∈ (P.inducedShading Y).carrier k
  have hsum :
      (∑ k ∈ occupied, P.fiberMultiplicity Y k x) =
        ∑ k ∈ P.index.coarse, P.fiberMultiplicity Y k x := by
    apply Finset.sum_subset (Finset.filter_subset _ _)
    intro k hkcoarse hkoccupied
    have hknot : x ∉ (P.inducedShading Y).carrier k := fun hx ↦
      hkoccupied (Finset.mem_filter.mpr ⟨hkcoarse, hx⟩)
    have hnpos : ¬ 0 < P.fiberMultiplicity Y k x := by
      simpa [P.mem_inducedShading_iff_fiberMultiplicity_pos Y k x] using hknot
    exact Nat.eq_zero_of_not_pos hnpos
  rw [← hsum]
  calc
    (∑ k ∈ occupied, P.fiberMultiplicity Y k x) ≤ ∑ _k ∈ occupied, M :=
      Finset.sum_le_sum fun k hk ↦ hM k ((Finset.mem_filter.mp hk).1)
    _ = occupied.card * M := by simp
    _ = P.outerMultiplicity Y x * M := by rfl

/-- With a finite coarse index type, outer multiplicity is the ordinary point
multiplicity of the induced coarse shading. -/
theorem pointMultiplicity_inducedShading_eq_outer [Fintype κ]
    (P : ConvexFactorization F W) (Y : Shading F) (x : Space) :
    (P.inducedShading Y).pointMultiplicity x = P.outerMultiplicity Y x := by
  classical
  unfold Shading.pointMultiplicity outerMultiplicity
  apply congrArg Finset.card
  ext k
  simp [P.mem_inducedShading_carrier_iff Y k x]

end ConvexFactorization

end Submission.Kakeya.ConvexFactoring
