import Family8Grounding.Family8PlankHeavyRetainedOwnerActualDatumV2
import Family8Grounding.Family8AllSlabUnionCancellationBudgetV1
import Mathlib.Tactic

/-!
# Fixed-theta catalogue of all occupied heavy-owner slab rows

The Frostman plank argument uses all rows at one common scale `theta`; it
does not select one arbitrary certified query.  This file records the least
geometric data needed to speak about that construction on the actual
deduplicated thick-owner family:

* a finite catalogue of occupied `theta x 1 x 1` slabs;
* one unique row assignment for every retained thick owner;
* containment of that owner body in its assigned slab.

The row families and row shadings are then literal subtype restrictions of
`heavyRetainedOwnerThickenedFamily` and
`heavyRetainedOwnerThickenedShading`.  Their sigma type reindexes the global
owner type, and the union of all row shaded unions is proved equal to the
global coarse shaded union (hence also to the retained source shaded union).

The unavailable analytic/geometric part is isolated at the end in
`FixedThetaAllSlabEq43AssemblyObligation`.  It has exactly the two aggregate
inequalities consumed by `AllSlabUnionCancellationBudget`: the summed row
lower bound after Eq. (43) and Family 7, and the Jacobian/bounded-overlap
assembly bound.  No single-row forward or copy-factor premise occurs.
-/

set_option autoImplicit false
set_option warningAsError true
set_option linter.unusedSectionVars false
set_option maxHeartbeats 5000000

open Set MeasureTheory
open scoped BigOperators ENNReal NNReal InnerProductSpace

namespace Family8PlankFixedThetaAllSlabRowsV1

open LeanEval.Analysis.WangZahlKakeya
open Submission.Kakeya.ConvexGeometry
open Submission.Kakeya.ConvexFactoring
open Submission.Kakeya.ConvexFactoring.HeavyParentSelection
open Family6AffinePlankAnalyticHypothesesStableV1
open Family8PlankThickControlMutualContainmentClusteringV2
open Family8PlankThickControlOwnerFiberLogBucketV2
open Family8PlankThickControlRetainedOwnerFamilyV3
open Family8PlankRetainedOwnerHeavyMassSelectionV3
open Family8PlankHeavyRetainedOwnerActualDatumV2
open Family8AllSlabUnionCancellationBudgetV1

noncomputable section

universe u v

variable {iota : Type u} [Fintype iota] [DecidableEq iota]
variable {a b : NNReal}

/-- A finite catalogue of all occupied slab rows at one fixed scale.

The owner type is exactly the index type of
`heavyRetainedOwnerThickenedFamily D C q`.  Surjectivity says that the
catalogue has no empty bookkeeping rows.  The containment field is the
minimal geometric content not supplied by the current query-by-query
certified incidence. -/
structure FixedThetaAllSlabRows
    (D : ShadedConvexPlankFamily iota a b) {theta : NNReal}
    (C : MutualThickeningClustering D theta)
    (q : Fin (Nat.log 2 (Fintype.card iota) + 1))
    (rowIndex : Type v) [Fintype rowIndex] [DecidableEq rowIndex]
    (slabComparisonConstant : NNReal) where
  slab : rowIndex -> ConvexBody Space
  slab_isSlab : forall r,
    IsSlab slabComparisonConstant theta (slab r)
  ownerToRow : {s // s ∈ heavyRetainedOwners C q} -> rowIndex
  ownerToRow_surjective : Function.Surjective ownerToRow
  ownerBody_subset_assignedSlab : forall s,
    (heavyRetainedOwnerThickenedFamily D C q s : Set Space) ⊆
      (slab (ownerToRow s) : Set Space)

/-- The owners assigned to one catalogue row. -/
def FixedThetaAllSlabRows.rowOwners
    {D : ShadedConvexPlankFamily iota a b} {theta : NNReal}
    {C : MutualThickeningClustering D theta}
    {q : Fin (Nat.log 2 (Fintype.card iota) + 1)}
    {rowIndex : Type v} [Fintype rowIndex] [DecidableEq rowIndex]
    {slabComparisonConstant : NNReal}
    (R : FixedThetaAllSlabRows D C q rowIndex slabComparisonConstant)
    (r : rowIndex) : Finset {s // s ∈ heavyRetainedOwners C q} :=
  Finset.univ.filter fun s => R.ownerToRow s = r

@[simp] theorem FixedThetaAllSlabRows.mem_rowOwners
    {D : ShadedConvexPlankFamily iota a b} {theta : NNReal}
    {C : MutualThickeningClustering D theta}
    {q : Fin (Nat.log 2 (Fintype.card iota) + 1)}
    {rowIndex : Type v} [Fintype rowIndex] [DecidableEq rowIndex]
    {slabComparisonConstant : NNReal}
    (R : FixedThetaAllSlabRows D C q rowIndex slabComparisonConstant)
    (r : rowIndex) (s : {s // s ∈ heavyRetainedOwners C q}) :
    s ∈ R.rowOwners r ↔ R.ownerToRow s = r := by
  simp [FixedThetaAllSlabRows.rowOwners]

/-- Every catalogue row is genuinely occupied. -/
theorem FixedThetaAllSlabRows.rowOwners_nonempty
    {D : ShadedConvexPlankFamily iota a b} {theta : NNReal}
    {C : MutualThickeningClustering D theta}
    {q : Fin (Nat.log 2 (Fintype.card iota) + 1)}
    {rowIndex : Type v} [Fintype rowIndex] [DecidableEq rowIndex]
    {slabComparisonConstant : NNReal}
    (R : FixedThetaAllSlabRows D C q rowIndex slabComparisonConstant)
    (r : rowIndex) : (R.rowOwners r).Nonempty := by
  obtain ⟨s, hs⟩ := R.ownerToRow_surjective r
  exact ⟨s, (R.mem_rowOwners r s).2 hs⟩

/-- The literal deduplicated thick-owner family in one row. -/
def FixedThetaAllSlabRows.rowFamily
    {D : ShadedConvexPlankFamily iota a b} {theta : NNReal}
    {C : MutualThickeningClustering D theta}
    {q : Fin (Nat.log 2 (Fintype.card iota) + 1)}
    {rowIndex : Type v} [Fintype rowIndex] [DecidableEq rowIndex]
    {slabComparisonConstant : NNReal}
    (R : FixedThetaAllSlabRows D C q rowIndex slabComparisonConstant)
    (r : rowIndex) : ConvexFamily {s // s ∈ R.rowOwners r} :=
  selectedCoarseFamily (heavyRetainedOwnerThickenedFamily D C q)
    (R.rowOwners r)

/-- The induced coarse shading restricted to one literal row. -/
def FixedThetaAllSlabRows.rowShading
    {D : ShadedConvexPlankFamily iota a b} {theta : NNReal}
    {C : MutualThickeningClustering D theta}
    {q : Fin (Nat.log 2 (Fintype.card iota) + 1)}
    {rowIndex : Type v} [Fintype rowIndex] [DecidableEq rowIndex]
    {slabComparisonConstant : NNReal}
    (R : FixedThetaAllSlabRows D C q rowIndex slabComparisonConstant)
    (r : rowIndex) : Shading (R.rowFamily r) :=
  selectedCoarseShading (heavyRetainedOwnerThickenedShading D C q)
    (R.rowOwners r)

@[simp] theorem FixedThetaAllSlabRows.rowFamily_apply
    {D : ShadedConvexPlankFamily iota a b} {theta : NNReal}
    {C : MutualThickeningClustering D theta}
    {q : Fin (Nat.log 2 (Fintype.card iota) + 1)}
    {rowIndex : Type v} [Fintype rowIndex] [DecidableEq rowIndex]
    {slabComparisonConstant : NNReal}
    (R : FixedThetaAllSlabRows D C q rowIndex slabComparisonConstant)
    (r : rowIndex) (s : {s // s ∈ R.rowOwners r}) :
    R.rowFamily r s = heavyRetainedOwnerThickenedFamily D C q s.1 := rfl

@[simp] theorem FixedThetaAllSlabRows.rowShading_carrier
    {D : ShadedConvexPlankFamily iota a b} {theta : NNReal}
    {C : MutualThickeningClustering D theta}
    {q : Fin (Nat.log 2 (Fintype.card iota) + 1)}
    {rowIndex : Type v} [Fintype rowIndex] [DecidableEq rowIndex]
    {slabComparisonConstant : NNReal}
    (R : FixedThetaAllSlabRows D C q rowIndex slabComparisonConstant)
    (r : rowIndex) (s : {s // s ∈ R.rowOwners r}) :
    (R.rowShading r).carrier s =
      (heavyRetainedOwnerThickenedShading D C q).carrier s.1 := rfl

/-- Each literal row body lies in its catalogue slab. -/
theorem FixedThetaAllSlabRows.rowFamily_subset_slab
    {D : ShadedConvexPlankFamily iota a b} {theta : NNReal}
    {C : MutualThickeningClustering D theta}
    {q : Fin (Nat.log 2 (Fintype.card iota) + 1)}
    {rowIndex : Type v} [Fintype rowIndex] [DecidableEq rowIndex]
    {slabComparisonConstant : NNReal}
    (R : FixedThetaAllSlabRows D C q rowIndex slabComparisonConstant)
    (r : rowIndex) (s : {s // s ∈ R.rowOwners r}) :
    (R.rowFamily r s : Set Space) ⊆ (R.slab r : Set Space) := by
  have hs : R.ownerToRow s.1 = r := (R.mem_rowOwners r s.1).1 s.2
  simpa only [FixedThetaAllSlabRows.rowFamily_apply, hs] using
    R.ownerBody_subset_assignedSlab s.1

/-- The sigma type of row members is canonically the global thick-owner
index type.  This is the exact finite reindexing bridge; no cardinality
comparison is assumed. -/
def FixedThetaAllSlabRows.rowOwnerSigmaEquiv
    {D : ShadedConvexPlankFamily iota a b} {theta : NNReal}
    {C : MutualThickeningClustering D theta}
    {q : Fin (Nat.log 2 (Fintype.card iota) + 1)}
    {rowIndex : Type v} [Fintype rowIndex] [DecidableEq rowIndex]
    {slabComparisonConstant : NNReal}
    (R : FixedThetaAllSlabRows D C q rowIndex slabComparisonConstant) :
    (Σ r : rowIndex, {s // s ∈ R.rowOwners r}) ≃
      {s // s ∈ heavyRetainedOwners C q} :=
  (Equiv.sigmaCongrRight fun r =>
      Equiv.subtypeEquivRight fun s => R.mem_rowOwners r s).trans
    (Equiv.sigmaFiberEquiv R.ownerToRow)

@[simp] theorem FixedThetaAllSlabRows.rowOwnerSigmaEquiv_apply
    {D : ShadedConvexPlankFamily iota a b} {theta : NNReal}
    {C : MutualThickeningClustering D theta}
    {q : Fin (Nat.log 2 (Fintype.card iota) + 1)}
    {rowIndex : Type v} [Fintype rowIndex] [DecidableEq rowIndex]
    {slabComparisonConstant : NNReal}
    (R : FixedThetaAllSlabRows D C q rowIndex slabComparisonConstant)
    (x : Σ r : rowIndex, {s // s ∈ R.rowOwners r}) :
    R.rowOwnerSigmaEquiv x = x.2.1 := rfl

/-- Global owner cardinality is the exact sum of row cardinalities. -/
theorem FixedThetaAllSlabRows.card_eq_sum_rowOwners_card
    {D : ShadedConvexPlankFamily iota a b} {theta : NNReal}
    {C : MutualThickeningClustering D theta}
    {q : Fin (Nat.log 2 (Fintype.card iota) + 1)}
    {rowIndex : Type v} [Fintype rowIndex] [DecidableEq rowIndex]
    {slabComparisonConstant : NNReal}
    (R : FixedThetaAllSlabRows D C q rowIndex slabComparisonConstant) :
    Fintype.card {s // s ∈ heavyRetainedOwners C q} =
      ∑ r : rowIndex, (R.rowOwners r).card := by
  have hmaps :
      (((Finset.univ : Finset {s // s ∈ heavyRetainedOwners C q})) :
          Set {s // s ∈ heavyRetainedOwners C q}).MapsTo
        R.ownerToRow (Finset.univ : Finset rowIndex) := by
    intro s _hs
    exact Finset.mem_univ _
  calc
    Fintype.card {s // s ∈ heavyRetainedOwners C q} =
        (Finset.univ : Finset {s // s ∈ heavyRetainedOwners C q}).card := by
      rw [Finset.card_univ]
    _ = ∑ r ∈ (Finset.univ : Finset rowIndex),
        ((Finset.univ : Finset {s // s ∈ heavyRetainedOwners C q}).filter
          fun s => R.ownerToRow s = r).card :=
      Finset.card_eq_sum_card_fiberwise hmaps
    _ = ∑ r : rowIndex, (R.rowOwners r).card := by
      simp only [FixedThetaAllSlabRows.rowOwners]

/-- The global multiplicity-counted thick-owner body mass is exactly the sum
of the corresponding row masses.  Unlike a uniform row-retention premise,
this follows formally from the sigma reindexing and permits row-dependent
losses to cancel after summation. -/
theorem FixedThetaAllSlabRows.familyVolume_eq_sum_rowFamily_familyVolume
    {D : ShadedConvexPlankFamily iota a b} {theta : NNReal}
    {C : MutualThickeningClustering D theta}
    {q : Fin (Nat.log 2 (Fintype.card iota) + 1)}
    {rowIndex : Type v} [Fintype rowIndex] [DecidableEq rowIndex]
    {slabComparisonConstant : NNReal}
    (R : FixedThetaAllSlabRows D C q rowIndex slabComparisonConstant) :
    familyVolume (heavyRetainedOwnerThickenedFamily D C q) =
      ∑ r : rowIndex, familyVolume (R.rowFamily r) := by
  let e := R.rowOwnerSigmaEquiv
  calc
    familyVolume (heavyRetainedOwnerThickenedFamily D C q) =
        ∑ s : {s // s ∈ heavyRetainedOwners C q},
          volume (heavyRetainedOwnerThickenedFamily D C q s : Set Space) :=
      rfl
    _ = ∑ x : (Σ r : rowIndex, {s // s ∈ R.rowOwners r}),
          volume
            (heavyRetainedOwnerThickenedFamily D C q (e x) : Set Space) :=
      (e.sum_comp fun s =>
        volume (heavyRetainedOwnerThickenedFamily D C q s : Set Space)).symm
    _ = ∑ x : (Σ r : rowIndex, {s // s ∈ R.rowOwners r}),
          volume (R.rowFamily x.1 x.2 : Set Space) := by
      apply Finset.sum_congr rfl
      intro x _hx
      simp only [e, FixedThetaAllSlabRows.rowOwnerSigmaEquiv_apply,
        FixedThetaAllSlabRows.rowFamily_apply]
    _ = ∑ r : rowIndex, familyVolume (R.rowFamily r) := by
      rw [Fintype.sum_sigma]
      rfl

/-- Taking all literal row shaded unions reconstructs the global coarse
shaded union exactly. -/
theorem FixedThetaAllSlabRows.iUnion_rowShadedUnion_eq_globalCoarse
    {D : ShadedConvexPlankFamily iota a b} {theta : NNReal}
    {C : MutualThickeningClustering D theta}
    {q : Fin (Nat.log 2 (Fintype.card iota) + 1)}
    {rowIndex : Type v} [Fintype rowIndex] [DecidableEq rowIndex]
    {slabComparisonConstant : NNReal}
    (R : FixedThetaAllSlabRows D C q rowIndex slabComparisonConstant) :
    (⋃ r : rowIndex, (R.rowShading r).shadedUnion) =
      (heavyRetainedOwnerThickenedShading D C q).shadedUnion := by
  ext x
  constructor
  · intro hx
    obtain ⟨r, hx⟩ := Set.mem_iUnion.mp hx
    obtain ⟨s, hxs⟩ := Set.mem_iUnion.mp hx
    exact Set.mem_iUnion.mpr ⟨s.1, by simpa using hxs⟩
  · intro hx
    obtain ⟨s, hxs⟩ := Set.mem_iUnion.mp hx
    let sr : {t // t ∈ R.rowOwners (R.ownerToRow s)} :=
      ⟨s, (R.mem_rowOwners _ s).2 rfl⟩
    exact Set.mem_iUnion.mpr ⟨R.ownerToRow s,
      Set.mem_iUnion.mpr ⟨sr, by simpa [sr] using hxs⟩⟩

/-- The same all-row union is the retained original source shaded union,
using the already-proved owner-fibre reconstruction. -/
theorem FixedThetaAllSlabRows.iUnion_rowShadedUnion_eq_heavySource
    {D : ShadedConvexPlankFamily iota a b} {theta : NNReal}
    {C : MutualThickeningClustering D theta}
    {q : Fin (Nat.log 2 (Fintype.card iota) + 1)}
    {rowIndex : Type v} [Fintype rowIndex] [DecidableEq rowIndex]
    {slabComparisonConstant : NNReal}
    (R : FixedThetaAllSlabRows D C q rowIndex slabComparisonConstant) :
    (⋃ r : rowIndex, (R.rowShading r).shadedUnion) =
      (heavyRetainedOwnerPlankFamily D C q).shading.shadedUnion := by
  rw [R.iUnion_rowShadedUnion_eq_globalCoarse]
  exact heavyRetainedOwnerThickenedShading_shadedUnion_eq D C q

/-- The two still-missing paper-level aggregate estimates, stated on the
literal fixed-theta rows above.

`eq43_family7_rows_lower` is the sum of the normalized Family 7 row bounds
after inserting the Eq. (43) Frostman coefficient.  It is deliberately an
aggregate premise, weaker than a bound for every row.

`jacobian_rows_le_global` is precisely the affine-Jacobian and bounded-overlap
reassembly from Lemma 6.13.  Its right side is the actual global thick-owner
shaded union, already identified above with the retained source union. -/
structure FixedThetaAllSlabEq43AssemblyObligation
    {D : ShadedConvexPlankFamily iota a b} {theta : NNReal}
    {C : MutualThickeningClustering D theta}
    {q : Fin (Nat.log 2 (Fintype.card iota) + 1)}
    {rowIndex : Type v} [Fintype rowIndex] [DecidableEq rowIndex]
    {slabComparisonConstant : NNReal}
    (R : FixedThetaAllSlabRows D C q rowIndex slabComparisonConstant)
    (localCore assemblyLoss : ENNReal) where
  rowWeight : rowIndex -> ENNReal
  normalizedRowUnion : rowIndex -> ENNReal
  totalWeight : ENNReal
  totalWeight_ne_zero : totalWeight ≠ 0
  totalWeight_ne_top : totalWeight ≠ ⊤
  weight_sum : (∑ r : rowIndex, rowWeight r) = totalWeight
  eq43_family7_rows_lower :
    totalWeight * (localCore / totalWeight) <=
      ∑ r : rowIndex, rowWeight r * normalizedRowUnion r
  jacobian_rows_le_global :
    (∑ r : rowIndex, rowWeight r * normalizedRowUnion r) <=
      assemblyLoss *
        volume ((heavyRetainedOwnerThickenedShading D C q).shadedUnion)

/-- Forget the fixed-theta geometry after the two aggregate estimates have
been proved.  This is the exact input expected by the generic cancellation
kernel. -/
def FixedThetaAllSlabEq43AssemblyObligation.toCancellationBudget
    {D : ShadedConvexPlankFamily iota a b} {theta : NNReal}
    {C : MutualThickeningClustering D theta}
    {q : Fin (Nat.log 2 (Fintype.card iota) + 1)}
    {rowIndex : Type v} [Fintype rowIndex] [DecidableEq rowIndex]
    {slabComparisonConstant : NNReal}
    {R : FixedThetaAllSlabRows D C q rowIndex slabComparisonConstant}
    {localCore assemblyLoss : ENNReal}
    (H : FixedThetaAllSlabEq43AssemblyObligation R localCore assemblyLoss) :
    AllSlabUnionCancellationBudget rowIndex localCore
      (volume ((heavyRetainedOwnerThickenedShading D C q).shadedUnion))
      assemblyLoss where
  rowWeight := H.rowWeight
  normalizedRowUnion := H.normalizedRowUnion
  totalWeight := H.totalWeight
  totalWeight_ne_zero := H.totalWeight_ne_zero
  totalWeight_ne_top := H.totalWeight_ne_top
  weight_sum := H.weight_sum
  aggregate_rows_lower := H.eq43_family7_rows_lower
  weighted_rows_le_global := H.jacobian_rows_le_global

/-- Exact all-slab cancellation on the actual global thick-owner union. -/
theorem FixedThetaAllSlabEq43AssemblyObligation.localCore_le_globalCoarse
    {D : ShadedConvexPlankFamily iota a b} {theta : NNReal}
    {C : MutualThickeningClustering D theta}
    {q : Fin (Nat.log 2 (Fintype.card iota) + 1)}
    {rowIndex : Type v} [Fintype rowIndex] [DecidableEq rowIndex]
    {slabComparisonConstant : NNReal}
    {R : FixedThetaAllSlabRows D C q rowIndex slabComparisonConstant}
    {localCore assemblyLoss : ENNReal}
    (H : FixedThetaAllSlabEq43AssemblyObligation R localCore assemblyLoss) :
    localCore <= assemblyLoss *
      volume ((heavyRetainedOwnerThickenedShading D C q).shadedUnion) :=
  H.toCancellationBudget.localCore_le

/-- Re-express the result on the retained original source union. -/
theorem FixedThetaAllSlabEq43AssemblyObligation.localCore_le_heavySource
    {D : ShadedConvexPlankFamily iota a b} {theta : NNReal}
    {C : MutualThickeningClustering D theta}
    {q : Fin (Nat.log 2 (Fintype.card iota) + 1)}
    {rowIndex : Type v} [Fintype rowIndex] [DecidableEq rowIndex]
    {slabComparisonConstant : NNReal}
    {R : FixedThetaAllSlabRows D C q rowIndex slabComparisonConstant}
    {localCore assemblyLoss : ENNReal}
    (H : FixedThetaAllSlabEq43AssemblyObligation R localCore assemblyLoss) :
    localCore <= assemblyLoss *
      volume ((heavyRetainedOwnerPlankFamily D C q).shading.shadedUnion) := by
  rw [← heavyRetainedOwnerThickenedShading_shadedUnion_eq D C q]
  exact H.localCore_le_globalCoarse

#print axioms FixedThetaAllSlabRows.mem_rowOwners
#print axioms FixedThetaAllSlabRows.rowOwners_nonempty
#print axioms FixedThetaAllSlabRows.rowFamily_subset_slab
#print axioms FixedThetaAllSlabRows.rowOwnerSigmaEquiv
#print axioms FixedThetaAllSlabRows.rowOwnerSigmaEquiv_apply
#print axioms FixedThetaAllSlabRows.card_eq_sum_rowOwners_card
#print axioms FixedThetaAllSlabRows.familyVolume_eq_sum_rowFamily_familyVolume
#print axioms FixedThetaAllSlabRows.iUnion_rowShadedUnion_eq_globalCoarse
#print axioms FixedThetaAllSlabRows.iUnion_rowShadedUnion_eq_heavySource
#print axioms FixedThetaAllSlabEq43AssemblyObligation.toCancellationBudget
#print axioms FixedThetaAllSlabEq43AssemblyObligation.localCore_le_globalCoarse
#print axioms FixedThetaAllSlabEq43AssemblyObligation.localCore_le_heavySource

end
end Family8PlankFixedThetaAllSlabRowsV1
