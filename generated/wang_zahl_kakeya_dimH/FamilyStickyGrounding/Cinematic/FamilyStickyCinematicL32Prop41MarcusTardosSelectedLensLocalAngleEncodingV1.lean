import FamilyStickyGrounding.Cinematic.FamilyStickyCinematicL32Prop41MarcusTardosSelectedLensClassificationV1
import FamilyStickyGrounding.Cinematic.FamilyStickyCinematicL32Prop41MarcusTardosTripleCharacterizationV1
import Mathlib.Data.Prod.Lex

set_option autoImplicit false

namespace FamilyStickyCinematicL32Prop41MarcusTardosSelectedLensLocalAngleEncodingV1

open FamilyStickyCinematicL32Prop41FirstGenerationLensCarrierV1
open FamilyStickyCinematicL32Prop41MarcusTardosCyclicCoreV1
open FamilyStickyCinematicL32Prop41MarcusTardosCyclicCoreV1.DistinctCyclicSequence
open FamilyStickyCinematicL32Prop41MarcusTardosLensListIncidenceV1
open FamilyStickyCinematicL32Prop41MarcusTardosLensListIncidenceV1.LensListEncoding
open FamilyStickyCinematicL32Prop41MarcusTardosForbiddenTripleV1
open FamilyStickyCinematicL32Prop41MarcusTardosTripleCharacterizationV1
open FamilyStickyCinematicL32Prop41MarcusTardosSelectedLensClassificationV1

noncomputable section

/-!
# Faithful side-entry lists with a local-angle secondary key

The primary key is the scalar parameter of the entry point on the oriented
skirt loop.  Several proper crossings may occur at the same point, so a
finite arbitrary tie-break is not geometrically faithful there.  We instead
use the local tangent-angle key as a secondary key.  The finite enumeration
is consulted only if both geometric keys agree; A3 excludes that case for
two different neighbors of one host.
-/

variable {point curve : Type*} [DecidableEq curve]
variable {curves : Finset curve}

/-- Classification geometry together with the oriented local tangent-angle
key at each side entry. -/
structure SelectedFixedSlotLensLocalAngleGeometry
    (point curve : Type*) [DecidableEq curve] (curves : Finset curve)
    extends SelectedFixedSlotLensGeometry point curve curves where
  entryAngleKey : FirstGenerationCurvePair curves ->
    FirstGenerationCurve curves -> Real

/-- Selected lenses are the literal used unordered pairs. -/
abbrev LocalAngleSelectedFixedSlotLens
    (items : Finset (FirstGenerationCurvePair curves)) :=
  {p : FirstGenerationCurvePair curves // p ∈ items}

/-- Literal neighbor relation, with class and host computed from the two
side-polarity bits. -/
def localAngleSelectedLensNeighborRelation
    (D : SelectedFixedSlotLensLocalAngleGeometry point curve curves)
    (items : Finset (FirstGenerationCurvePair curves))
    (k : ProperLensKind) (c d : FirstGenerationCurve curves) : Prop :=
  ∃ p : FirstGenerationCurvePair curves, p ∈ items ∧
    selectedLensAssignedTo D.toSelectedFixedSlotLensGeometry k c p ∧
      p.1 = s(c, d)

/-- Literal finite carrier of one class/host neighbor list. -/
noncomputable def localAngleSelectedLensNeighborFinset
    (D : SelectedFixedSlotLensLocalAngleGeometry point curve curves)
    (items : Finset (FirstGenerationCurvePair curves))
    (k : ProperLensKind) (c : FirstGenerationCurve curves) :
    Finset (FirstGenerationCurve curves) := by
  classical
  exact Finset.univ.filter
    (fun d => localAngleSelectedLensNeighborRelation D items k c d)

@[simp]
theorem mem_localAngleSelectedLensNeighborFinset_iff
    (D : SelectedFixedSlotLensLocalAngleGeometry point curve curves)
    (items : Finset (FirstGenerationCurvePair curves))
    (k : ProperLensKind) (c d : FirstGenerationCurve curves) :
    d ∈ localAngleSelectedLensNeighborFinset D items k c ↔
      localAngleSelectedLensNeighborRelation D items k c d := by
  classical
  simp [localAngleSelectedLensNeighborFinset]

/-- The actual scalar loop entry of the unique selected unordered pair. -/
noncomputable def localAngleSelectedLensNeighborEntryKey
    (D : SelectedFixedSlotLensLocalAngleGeometry point curve curves)
    (items : Finset (FirstGenerationCurvePair curves))
    (k : ProperLensKind) (c d : FirstGenerationCurve curves) : Real := by
  classical
  exact if h : localAngleSelectedLensNeighborRelation D items k c d then
    D.entryKey (Classical.choose h) c
  else 0

/-- The actual oriented local tangent-angle key at that same side entry. -/
noncomputable def localAngleSelectedLensNeighborAngleKey
    (D : SelectedFixedSlotLensLocalAngleGeometry point curve curves)
    (items : Finset (FirstGenerationCurvePair curves))
    (k : ProperLensKind) (c d : FirstGenerationCurve curves) : Real := by
  classical
  exact if h : localAngleSelectedLensNeighborRelation D items k c d then
    D.entryAngleKey (Classical.choose h) c
  else 0

/-- Finite order lifted lexicographically from the actual entry parameter,
then the local tangent angle, and only then a deterministic enumeration. -/
@[instance_reducible] noncomputable def keyedFiniteEntryAngleLinearOrder
    {alpha : Type*} [Fintype alpha]
    (entry angle : alpha -> Real) : LinearOrder alpha :=
  LinearOrder.lift'
    (fun a => toLex
      (entry a, toLex (angle a, Fintype.equivFin alpha a))) (by
        intro a b hab
        exact (Fintype.equivFin alpha).injective
          (congrArg (fun z => (ofLex (ofLex z).2).2) hab))

/-- If primary entry parameters differ, the local-angle and finite keys are
invisible. -/
theorem keyedFiniteEntryAngleLinearOrder_lt_iff_of_entry_ne
    {alpha : Type*} [Fintype alpha] (entry angle : alpha -> Real)
    {a b : alpha} (hentry : entry a ≠ entry b) :
    @LT.lt alpha (keyedFiniteEntryAngleLinearOrder entry angle).toLT a b ↔
      entry a < entry b := by
  change toLex (entry a, toLex (angle a, Fintype.equivFin alpha a)) <
      toLex (entry b, toLex (angle b, Fintype.equivFin alpha b)) ↔
        entry a < entry b
  rw [Prod.Lex.toLex_lt_toLex]
  simp [hentry]

/-- At one common entry point, unequal tangent-angle keys completely decide
the order; the finite enumeration remains invisible. -/
theorem keyedFiniteEntryAngleLinearOrder_lt_iff_of_entry_eq_angle_ne
    {alpha : Type*} [Fintype alpha] (entry angle : alpha -> Real)
    {a b : alpha} (hentry : entry a = entry b)
    (hangle : angle a ≠ angle b) :
    @LT.lt alpha (keyedFiniteEntryAngleLinearOrder entry angle).toLT a b ↔
      angle a < angle b := by
  change toLex (entry a, toLex (angle a, Fintype.equivFin alpha a)) <
      toLex (entry b, toLex (angle b, Fintype.equivFin alpha b)) ↔
        angle a < angle b
  rw [Prod.Lex.toLex_lt_toLex]
  simp only [hentry, lt_self_iff_false, false_or, true_and]
  rw [Prod.Lex.toLex_lt_toLex]
  simp [hangle]

/-- The faithful cyclic-list representative, sorted first by loop entry and
then by the local side angle. -/
noncomputable def localAngleSelectedLensNeighborOrder
    (D : SelectedFixedSlotLensLocalAngleGeometry point curve curves)
    (items : Finset (FirstGenerationCurvePair curves))
    (k : ProperLensKind) (c : FirstGenerationCurve curves) :
    List (FirstGenerationCurve curves) := by
  letI : LinearOrder (FirstGenerationCurve curves) :=
    keyedFiniteEntryAngleLinearOrder
      (localAngleSelectedLensNeighborEntryKey D items k c)
      (localAngleSelectedLensNeighborAngleKey D items k c)
  exact (localAngleSelectedLensNeighborFinset D items k c).sort
    (fun a b => a <= b)

theorem localAngleSelectedLensNeighborOrder_nodup
    (D : SelectedFixedSlotLensLocalAngleGeometry point curve curves)
    (items : Finset (FirstGenerationCurvePair curves))
    (k : ProperLensKind) (c : FirstGenerationCurve curves) :
    (localAngleSelectedLensNeighborOrder D items k c).Nodup := by
  classical
  unfold localAngleSelectedLensNeighborOrder
  exact Finset.sort_nodup _ _

/-- The three class-indexed faithful cyclic neighbor-list families. -/
noncomputable def localAngleSelectedLensNeighborSequence
    (D : SelectedFixedSlotLensLocalAngleGeometry point curve curves)
    (items : Finset (FirstGenerationCurvePair curves))
    (k : ProperLensKind) (c : FirstGenerationCurve curves) :
    DistinctCyclicSequence (FirstGenerationCurve curves) where
  order := localAngleSelectedLensNeighborOrder D items k c
  nodup_order := localAngleSelectedLensNeighborOrder_nodup D items k c

@[simp]
theorem mem_localAngleSelectedLensNeighborSequence_support_iff
    (D : SelectedFixedSlotLensLocalAngleGeometry point curve curves)
    (items : Finset (FirstGenerationCurvePair curves))
    (k : ProperLensKind) (c d : FirstGenerationCurve curves) :
    d ∈ (localAngleSelectedLensNeighborSequence D items k c).support ↔
      localAngleSelectedLensNeighborRelation D items k c d := by
  classical
  simp [localAngleSelectedLensNeighborSequence, support,
    localAngleSelectedLensNeighborOrder,
    localAngleSelectedLensNeighborFinset]

/-- Every selected lens has its automatically determined list occurrence. -/
noncomputable def localAngleSelectedLensOccurrence
    (D : SelectedFixedSlotLensLocalAngleGeometry point curve curves)
    (items : Finset (FirstGenerationCurvePair curves))
    (L : LocalAngleSelectedFixedSlotLens items) :
    ListOccurrence (localAngleSelectedLensNeighborSequence D items) := by
  let p := L.1
  let G := D.toSelectedFixedSlotLensGeometry
  let k := selectedProperLensKind G p
  let c := selectedLensHost G p
  let d := selectedLensNeighbor G p
  refine ⟨k, c, ⟨d, ?_⟩⟩
  rw [mem_localAngleSelectedLensNeighborSequence_support_iff]
  exact ⟨p, L.2, selectedLensAssignedTo_chosenHost G p,
    pair_eq_selectedLensHost_selectedLensNeighbor G p⟩

/-- Decode one occurrence to its literal host-neighbor unordered pair. -/
def localAngleListOccurrenceCurvePair
    (lists : ProperLensKind -> FirstGenerationCurve curves ->
      DistinctCyclicSequence (FirstGenerationCurve curves))
    (o : ListOccurrence lists) : Sym2 (FirstGenerationCurve curves) :=
  s(o.2.1, o.2.2.1)

/-- Total decoder for the curve-or-list occurrence sum. -/
def localAngleLensListCodeCurvePair
    (lists : ProperLensKind -> FirstGenerationCurve curves ->
      DistinctCyclicSequence (FirstGenerationCurve curves)) :
    Sum (FirstGenerationCurve curves) (ListOccurrence lists) ->
      Sym2 (FirstGenerationCurve curves)
  | Sum.inl c => s(c, c)
  | Sum.inr o => localAngleListOccurrenceCurvePair lists o

theorem localAngleLensListCodeCurvePair_selectedLensOccurrence
    (D : SelectedFixedSlotLensLocalAngleGeometry point curve curves)
    (items : Finset (FirstGenerationCurvePair curves))
    (L : LocalAngleSelectedFixedSlotLens items) :
    localAngleLensListCodeCurvePair
        (localAngleSelectedLensNeighborSequence D items)
        (Sum.inr (localAngleSelectedLensOccurrence D items L)) = L.1.1 := by
  let G := D.toSelectedFixedSlotLensGeometry
  change s(selectedLensHost G L.1, selectedLensNeighbor G L.1) = L.1.1
  exact (pair_eq_selectedLensHost_selectedLensNeighbor G L.1).symm

theorem localAngleSelectedLensOccurrence_injective
    (D : SelectedFixedSlotLensLocalAngleGeometry point curve curves)
    (items : Finset (FirstGenerationCurvePair curves)) :
    Function.Injective (fun L : LocalAngleSelectedFixedSlotLens items =>
      (Sum.inr (localAngleSelectedLensOccurrence D items L) :
        Sum (FirstGenerationCurve curves)
          (ListOccurrence
            (localAngleSelectedLensNeighborSequence D items)))) := by
  intro L N hcode
  apply Subtype.ext
  apply Subtype.ext
  have hpairs := congrArg
    (localAngleLensListCodeCurvePair
      (localAngleSelectedLensNeighborSequence D items)) hcode
  simpa [localAngleLensListCodeCurvePair_selectedLensOccurrence] using hpairs

/-- Automatic faithful occurrence embedding. -/
noncomputable def localAngleSelectedLensEmbedding
    (D : SelectedFixedSlotLensLocalAngleGeometry point curve curves)
    (items : Finset (FirstGenerationCurvePair curves)) :
    LocalAngleSelectedFixedSlotLens items ↪
      Sum (FirstGenerationCurve curves)
        (ListOccurrence (localAngleSelectedLensNeighborSequence D items)) where
  toFun L := Sum.inr (localAngleSelectedLensOccurrence D items L)
  inj' := localAngleSelectedLensOccurrence_injective D items

/-- Complete local-angle classification/list/injection output. -/
noncomputable def localAngleSelectedLensListEncoding
    (D : SelectedFixedSlotLensLocalAngleGeometry point curve curves)
    (items : Finset (FirstGenerationCurvePair curves)) :
    LensListEncoding (FirstGenerationCurve curves)
      (LocalAngleSelectedFixedSlotLens items) where
  lists := localAngleSelectedLensNeighborSequence D items
  lensCode := localAngleSelectedLensEmbedding D items

/-- Pure finite card reduction after faithful local-angle sorting. -/
theorem localAngleSelectedFixedSlotLens_card_le_curve_add_sum_list_length
    (D : SelectedFixedSlotLensLocalAngleGeometry point curve curves)
    (items : Finset (FirstGenerationCurvePair curves)) :
    items.card <= curves.card +
      ∑ k : ProperLensKind, ∑ c : FirstGenerationCurve curves,
        (localAngleSelectedLensNeighborSequence D items k c).order.length := by
  simpa only [Fintype.card_coe] using
    card_finset_le_curve_add_sum_list_length items
      (localAngleSelectedLensNeighborSequence D items)
      (localAngleSelectedLensEmbedding D items)

/-- The sole five-curve geometry residual after all classification, ordering,
and injection data have been constructed. -/
theorem localAngleSelectedLensListEncoding_pairwiseIntersectionReverse
    (D : SelectedFixedSlotLensLocalAngleGeometry point curve curves)
    (items : Finset (FirstGenerationCurvePair curves))
    (hforbidden : forall k,
      FixedKindForbidsSameTriple
        (localAngleSelectedLensNeighborSequence D items k)) :
    (localAngleSelectedLensListEncoding D items).ListsPairwiseIntersectionReverse := by
  exact lensListEncoding_pairwiseIntersectionReverse
    (tripleCharacterizationCore (FirstGenerationCurve curves))
    (localAngleSelectedLensListEncoding D items) hforbidden

#print axioms SelectedFixedSlotLensLocalAngleGeometry
#print axioms keyedFiniteEntryAngleLinearOrder
#print axioms keyedFiniteEntryAngleLinearOrder_lt_iff_of_entry_ne
#print axioms keyedFiniteEntryAngleLinearOrder_lt_iff_of_entry_eq_angle_ne
#print axioms localAngleSelectedLensNeighborSequence
#print axioms localAngleSelectedLensOccurrence_injective
#print axioms localAngleSelectedLensListEncoding
#print axioms localAngleSelectedFixedSlotLens_card_le_curve_add_sum_list_length
#print axioms localAngleSelectedLensListEncoding_pairwiseIntersectionReverse

end

end FamilyStickyCinematicL32Prop41MarcusTardosSelectedLensLocalAngleEncodingV1
