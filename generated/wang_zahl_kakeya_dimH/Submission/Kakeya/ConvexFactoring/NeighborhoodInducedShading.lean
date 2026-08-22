import Submission.Kakeya.ConvexFactoring.Factorization

namespace Submission.Kakeya.ConvexFactoring

open LeanEval.Analysis.WangZahlKakeya
open Submission.Kakeya.ConvexGeometry

/-!
# Neighborhood-induced coarse shadings

Unlike `ConvexFactorization.inducedShading`, whose coarse carrier is exactly the
union of the fine shaded pieces in a fiber, the construction below uses the
paper-style open neighborhood

`W k ∩ Metric.thickening r (fiberShadedUnion P Y k)`.
-/

namespace ConvexFactorization

variable {ι κ : Type*} [DecidableEq ι] [DecidableEq κ]
  {F : ConvexFamily ι} {W : ConvexFamily κ}

/-- The union of the fine shaded pieces assigned to a fixed coarse index. -/
def fiberShadedUnion (P : ConvexFactorization F W) (Y : Shading F) (k : κ) :
    Set Space :=
  ⋃ i : {i // i ∈ P.index.fiber k}, Y.carrier i.1

/-- A fiber shaded union is measurable because its indexing subtype is finite. -/
theorem fiberShadedUnion_measurableSet (P : ConvexFactorization F W)
    (Y : Shading F) (k : κ) : MeasurableSet (P.fiberShadedUnion Y k) :=
  MeasurableSet.iUnion fun i ↦ Y.measurable_carrier i.1

/-- Every shaded fine fiber remains inside its assigned coarse body. -/
theorem fiberShadedUnion_subset_coarseBody (P : ConvexFactorization F W)
    (Y : Shading F) (k : κ) :
    P.fiberShadedUnion Y k ⊆ (W k : Set Space) := by
  intro x hx
  obtain ⟨i, hxi⟩ := Set.mem_iUnion.mp hx
  have hiFine : i.1 ∈ P.index.fine := P.index.fiber_subset_fine k i.2
  have hiParent : P.index.parent i.1 = k := (P.index.mem_fiber i.1 k).1 i.2 |>.2
  have hxParent := P.contained i.1 hiFine (Y.carrier_subset i.1 hxi)
  simpa [hiParent] using hxParent

/-- The paper-style coarse shading: intersect a coarse body with the open
`r`-neighborhood of the union of the fine shaded pieces assigned to it. -/
def neighborhoodInducedShading (P : ConvexFactorization F W) (Y : Shading F)
    (r : ℝ) : Shading W where
  carrier := fun k ↦
    (W k : Set Space) ∩ Metric.thickening r (P.fiberShadedUnion Y k)
  measurable_carrier := fun k ↦
    (W k).isCompact.measurableSet.inter Metric.isOpen_thickening.measurableSet
  carrier_subset := fun _ ↦ Set.inter_subset_left

@[simp] theorem neighborhoodInducedShading_carrier
    (P : ConvexFactorization F W) (Y : Shading F) (r : ℝ) (k : κ) :
    (P.neighborhoodInducedShading Y r).carrier k =
      (W k : Set Space) ∩ Metric.thickening r (P.fiberShadedUnion Y k) :=
  rfl

/-- Each neighborhood-induced carrier is measurable. -/
theorem neighborhoodInducedShading_measurableSet
    (P : ConvexFactorization F W) (Y : Shading F) (r : ℝ) (k : κ) :
    MeasurableSet ((P.neighborhoodInducedShading Y r).carrier k) :=
  (P.neighborhoodInducedShading Y r).measurable_carrier k

/-- Each neighborhood-induced carrier is a subset of its coarse body. -/
theorem neighborhoodInducedShading_subset_coarseBody
    (P : ConvexFactorization F W) (Y : Shading F) (r : ℝ) (k : κ) :
    (P.neighborhoodInducedShading Y r).carrier k ⊆ (W k : Set Space) :=
  (P.neighborhoodInducedShading Y r).carrier_subset k

/-- Positive-radius thickening does not discard any shaded point in a fiber. -/
theorem fiberShadedUnion_subset_neighborhoodInducedShading
    (P : ConvexFactorization F W) (Y : Shading F) {r : ℝ} (hr : 0 < r) (k : κ) :
    P.fiberShadedUnion Y k ⊆
      (P.neighborhoodInducedShading Y r).carrier k := by
  intro x hx
  exact ⟨P.fiberShadedUnion_subset_coarseBody Y k hx,
    Metric.self_subset_thickening hr _ hx⟩

/-- The union of the shaded pieces at all active fine indices. -/
def activeFineShadedUnion (P : ConvexFactorization F W) (Y : Shading F) :
    Set Space :=
  ⋃ i : {i // i ∈ P.index.fine}, Y.carrier i.1

/-- All active fine shaded points lie in the union of the neighborhood-induced
coarse shading. -/
theorem activeFineShadedUnion_subset_neighborhoodShadedUnion
    (P : ConvexFactorization F W) (Y : Shading F) {r : ℝ} (hr : 0 < r) :
    P.activeFineShadedUnion Y ⊆
      (P.neighborhoodInducedShading Y r).shadedUnion := by
  intro x hx
  obtain ⟨i, hxi⟩ := Set.mem_iUnion.mp hx
  let k := P.index.parent i.1
  apply Set.mem_iUnion.mpr
  refine ⟨k, P.fiberShadedUnion_subset_neighborhoodInducedShading Y hr k ?_⟩
  exact Set.mem_iUnion.mpr ⟨
    ⟨i.1, (P.index.mem_fiber i.1 k).2 ⟨i.2, rfl⟩⟩, hxi⟩

/-- Pointwise membership has the expected paper interpretation: a point lies
in the coarse body and is within distance `r` of a shaded point in its fiber. -/
theorem mem_neighborhoodInducedShading_carrier_iff
    (P : ConvexFactorization F W) (Y : Shading F) (r : ℝ) (k : κ) (x : Space) :
    x ∈ (P.neighborhoodInducedShading Y r).carrier k ↔
      x ∈ (W k : Set Space) ∧
        ∃ y ∈ P.fiberShadedUnion Y k, dist x y < r := by
  change x ∈ (W k : Set Space) ∩ Metric.thickening r (P.fiberShadedUnion Y k) ↔ _
  rw [Set.mem_inter_iff, Metric.mem_thickening_iff]

/-- The pre-existing `inducedShading` carrier is exactly the unthickened fiber
shaded union. Its conditional on active coarse indices only forces inactive,
necessarily empty fibers to have empty carrier. -/
theorem inducedShading_carrier_eq_fiberShadedUnion
    (P : ConvexFactorization F W) (Y : Shading F) (k : κ) :
    (P.inducedShading Y).carrier k = P.fiberShadedUnion Y k := by
  ext x
  constructor
  · intro hx
    obtain ⟨_hk, i, hiFiber, hxi⟩ :=
      (P.mem_inducedShading_carrier_iff Y k x).1 hx
    exact Set.mem_iUnion.mpr ⟨⟨i, hiFiber⟩, hxi⟩
  · intro hx
    obtain ⟨i, hxi⟩ := Set.mem_iUnion.mp hx
    have hiFine : i.1 ∈ P.index.fine := P.index.fiber_subset_fine k i.2
    have hiParent : P.index.parent i.1 = k :=
      (P.index.mem_fiber i.1 k).1 i.2 |>.2
    have hkCoarse : k ∈ P.index.coarse := by
      simpa [hiParent] using P.index.parent_mem i.1 hiFine
    exact (P.mem_inducedShading_carrier_iff Y k x).2
      ⟨hkCoarse, i.1, i.2, hxi⟩

/-- The old exact-union induced shading is contained in, but is not definitionally
the same as, the positive-radius neighborhood-induced shading. -/
theorem inducedShading_carrier_subset_neighborhoodInducedShading
    (P : ConvexFactorization F W) (Y : Shading F) {r : ℝ} (hr : 0 < r) (k : κ) :
    (P.inducedShading Y).carrier k ⊆
      (P.neighborhoodInducedShading Y r).carrier k := by
  intro x hx
  obtain ⟨_hk, i, hiFiber, hxi⟩ :=
    (P.mem_inducedShading_carrier_iff Y k x).1 hx
  apply P.fiberShadedUnion_subset_neighborhoodInducedShading Y hr k
  exact Set.mem_iUnion.mpr ⟨⟨i, hiFiber⟩, hxi⟩

/-- The number of active coarse neighborhood-carriers containing a point. -/
noncomputable def neighborhoodOuterMultiplicity
    (P : ConvexFactorization F W) (Y : Shading F) (r : ℝ) (x : Space) : ℕ := by
  classical
  exact (P.index.coarse.filter fun k ↦
    x ∈ (P.neighborhoodInducedShading Y r).carrier k).card

/-- Positive neighborhood outer multiplicity is exactly witnessed by an active
coarse carrier containing the point. -/
theorem neighborhoodOuterMultiplicity_pos_iff
    (P : ConvexFactorization F W) (Y : Shading F) (r : ℝ) (x : Space) :
    0 < P.neighborhoodOuterMultiplicity Y r x ↔
      ∃ k ∈ P.index.coarse,
        x ∈ (P.neighborhoodInducedShading Y r).carrier k := by
  classical
  unfold neighborhoodOuterMultiplicity
  rw [Finset.card_pos, Finset.filter_nonempty_iff]

/-- Enlarging exact fiber unions to positive-radius neighborhoods can only
increase outer multiplicity. -/
theorem outerMultiplicity_le_neighborhoodOuterMultiplicity
    (P : ConvexFactorization F W) (Y : Shading F) {r : ℝ} (hr : 0 < r)
    (x : Space) :
    P.outerMultiplicity Y x ≤ P.neighborhoodOuterMultiplicity Y r x := by
  classical
  unfold outerMultiplicity neighborhoodOuterMultiplicity
  apply Finset.card_le_card
  intro k hk
  rw [Finset.mem_filter] at hk ⊢
  exact ⟨hk.1,
    P.inducedShading_carrier_subset_neighborhoodInducedShading Y hr k hk.2⟩

/-- Hence the existing fiberwise upper bound remains valid when the outer
multiplicity is computed using the paper-style neighborhoods. -/
theorem fineMultiplicity_le_neighborhoodOuter_mul
    (P : ConvexFactorization F W) (Y : Shading F) {r : ℝ} (hr : 0 < r)
    (x : Space) (M : ℕ)
    (hM : ∀ k ∈ P.index.coarse, P.fiberMultiplicity Y k x ≤ M) :
    P.fineMultiplicity Y x ≤ P.neighborhoodOuterMultiplicity Y r x * M := by
  exact (P.fineMultiplicity_le_outer_mul Y x M hM).trans
    (Nat.mul_le_mul_right M (P.outerMultiplicity_le_neighborhoodOuterMultiplicity Y hr x))

/-- In particular, every active fine shaded point has positive neighborhood
outer multiplicity. -/
theorem mem_activeFineShadedUnion_imp_neighborhoodOuterMultiplicity_pos
    (P : ConvexFactorization F W) (Y : Shading F) {r : ℝ} (hr : 0 < r)
    {x : Space} (hx : x ∈ P.activeFineShadedUnion Y) :
    0 < P.neighborhoodOuterMultiplicity Y r x := by
  rw [P.neighborhoodOuterMultiplicity_pos_iff Y r x]
  obtain ⟨i, hxi⟩ := Set.mem_iUnion.mp hx
  let k := P.index.parent i.1
  refine ⟨k, P.index.parent_mem i.1 i.2, ?_⟩
  apply P.fiberShadedUnion_subset_neighborhoodInducedShading Y hr k
  exact Set.mem_iUnion.mpr ⟨
    ⟨i.1, (P.index.mem_fiber i.1 k).2 ⟨i.2, rfl⟩⟩, hxi⟩

end ConvexFactorization

end Submission.Kakeya.ConvexFactoring
