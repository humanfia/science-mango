import Submission.Kakeya.Uniformity.DyadicLevel
import Mathlib.Combinatorics.Pigeonhole

namespace Submission.Kakeya.Uniformity

/-!
# Finite dyadic pigeonhole principles

This module extracts a populated dyadic fiber from a finite family and records
the exact cardinality loss.  It also supplies the weighted finite pigeonhole
estimate used by later multiscale refinements.
-/

/-- The fiber of a finite family over a specified bucket. -/
def dyadicFiber {ι β : Type*} [DecidableEq ι] [DecidableEq β]
    (s : Finset ι) (bucket : ι → β) (b : β) : Finset ι :=
  s.filter fun i ↦ bucket i = b

/-- Membership in a fiber is membership in the source together with the
specified bucket value. -/
@[simp]
theorem mem_dyadicFiber {ι β : Type*} [DecidableEq ι] [DecidableEq β]
    (s : Finset ι) (bucket : ι → β) (b : β) (i : ι) :
    i ∈ dyadicFiber s bucket b ↔ i ∈ s ∧ bucket i = b := by
  simp [dyadicFiber]

/-- A populated dyadic fiber together with its explicit finite loss. -/
structure DyadicPigeonhole (α : Type*) [DecidableEq α] where
  source : Finset α
  label : α → DyadicLevel
  level : DyadicLevel
  selected : Finset α
  selected_eq : selected = source.filter fun x ↦ label x = level
  selected_nonempty : selected.Nonempty
  selected_subset : selected ⊆ source
  loss : Nat
  card_le_loss_mul : source.card ≤ loss * selected.card

/-- Among finitely many candidate dyadic levels, some populated fiber retains
at least a `1 / candidates.card` fraction of the source cardinality. -/
theorem exists_dyadic_pigeonhole
    {α : Type*} [DecidableEq α]
    (family : Finset α) (label : α → DyadicLevel)
    (candidates : Finset DyadicLevel) (hfamily : family.Nonempty)
    (hlabel : ∀ x ∈ family, label x ∈ candidates) :
    ∃ witness : DyadicPigeonhole α,
      witness.source = family ∧
        witness.label = label ∧
        witness.level ∈ candidates ∧
        witness.selected = family.filter (fun x ↦ label x = witness.level) ∧
        witness.selected.Nonempty ∧
        witness.selected ⊆ family ∧
        (∀ x ∈ witness.selected, label x = witness.level) ∧
        witness.loss = candidates.card ∧
        family.card ≤ witness.loss * witness.selected.card := by
  classical
  have hcandidates : candidates.Nonempty := by
    obtain ⟨x, hx⟩ := hfamily
    exact ⟨label x, hlabel x hx⟩
  let fiberCard : DyadicLevel → Nat := fun level ↦
    (family.filter fun x ↦ label x = level).card
  obtain ⟨level, hlevel, hmax⟩ :=
    Finset.exists_max_image candidates fiberCard hcandidates
  let selected := family.filter fun x ↦ label x = level
  have hcard : family.card ≤ candidates.card * selected.card := by
    calc
      family.card = ∑ l ∈ candidates, (family.filter fun x ↦ label x = l).card :=
        Finset.card_eq_sum_card_fiberwise hlabel
      _ ≤ ∑ _l ∈ candidates, selected.card := by
        apply Finset.sum_le_sum
        intro l hl
        exact hmax l hl
      _ = candidates.card * selected.card := by simp
  have hselected : selected.Nonempty := by
    by_contra hempty
    have hzero : selected.card = 0 := by
      exact Nat.eq_zero_of_not_pos fun hpos ↦ hempty (Finset.card_pos.mp hpos)
    rw [hzero, mul_zero] at hcard
    exact hfamily.ne_empty (Finset.card_eq_zero.mp (Nat.le_zero.mp hcard))
  let witness : DyadicPigeonhole α :=
    { source := family
      label := label
      level := level
      selected := selected
      selected_eq := rfl
      selected_nonempty := hselected
      selected_subset := Finset.filter_subset _ _
      loss := candidates.card
      card_le_loss_mul := hcard }
  refine ⟨witness, rfl, rfl, hlevel, rfl, hselected,
    Finset.filter_subset _ _, ?_, rfl, ?_⟩
  · intro x hx
    exact (Finset.mem_filter.mp hx).2
  · exact hcard

/-- A weighted finite pigeonhole principle over every bucket of a nonempty
finite type. Empty fibers are permitted, so no nonemptiness assumption on the
source family is needed. -/
theorem exists_large_weighted_fiber
    {ι β : Type*} [DecidableEq ι] [DecidableEq β] [Fintype β] [Nonempty β]
    (s : Finset ι) (bucket : ι → β) (w : ι → NNReal) :
    ∃ b : β,
      Finset.sum s w ≤
        Fintype.card β • Finset.sum (dyadicFiber s bucket b) w := by
  classical
  let fiberWeight : β → NNReal := fun b ↦
    ∑ i ∈ dyadicFiber s bucket b, w i
  have huniv : (Finset.univ : Finset β).Nonempty := Finset.univ_nonempty
  obtain ⟨b, _hb, hmax⟩ :=
    Finset.exists_max_image (Finset.univ : Finset β) fiberWeight huniv
  refine ⟨b, ?_⟩
  calc
    Finset.sum s w = ∑ b' ∈ (Finset.univ : Finset β), fiberWeight b' := by
      change (∑ i ∈ s, w i) =
        ∑ b' ∈ (Finset.univ : Finset β), ∑ i ∈ s with bucket i = b', w i
      exact (Finset.sum_fiberwise_of_maps_to
        (s := s) (t := (Finset.univ : Finset β)) (g := bucket)
        (fun i hi ↦ Finset.mem_univ (bucket i)) w).symm
    _ ≤ (Finset.univ : Finset β).card • fiberWeight b :=
      Finset.sum_le_card_nsmul (Finset.univ : Finset β) fiberWeight
        (fiberWeight b) (fun b' hb' ↦ hmax b' hb')
    _ = Fintype.card β • Finset.sum (dyadicFiber s bucket b) w := by
      simp [fiberWeight]

end Submission.Kakeya.Uniformity
