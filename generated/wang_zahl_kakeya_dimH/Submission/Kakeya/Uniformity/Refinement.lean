import Submission.Kakeya.Uniformity.Pigeonhole
import Submission.Kakeya.Uniformity.Profile

namespace Submission.Kakeya.Uniformity

/-!
# Multiscale uniform refinements

Iterating finite dyadic pigeonholing over a finite set of scales produces a
nonempty subfamily on which every prescribed dyadic label is constant.  This
module records both the exact cumulative cardinality loss and its weighted
analogue for `NNReal`-valued weights.
-/

/-- A simultaneous finite-scale uniform refinement with cumulative loss. -/
structure UniformRefinement (α : Type*) [DecidableEq α] where
  profile : MultiscaleProfile α
  refined : Finset α
  refined_subset : refined ⊆ profile.family
  uniform : profile.UniformOn refined profile.scales
  loss : Nat
  card_le_loss_mul : profile.family.card ≤ loss * refined.card

private theorem exists_uniform_on_scales
    {α : Type*} [DecidableEq α] (profile : MultiscaleProfile α)
    (candidates : Nat → Finset DyadicLevel) (scales : Finset Nat)
    (hfamily : profile.family.Nonempty)
    (hscales : scales ⊆ profile.scales)
    (hlabel : ∀ r ∈ profile.scales, ∀ x ∈ profile.family,
      profile.label r x ∈ candidates r) :
    ∃ refined : Finset α,
      refined.Nonempty ∧
        refined ⊆ profile.family ∧
        profile.UniformOn refined scales ∧
        profile.family.card ≤
          scales.prod (fun r ↦ (candidates r).card) * refined.card := by
  classical
  induction scales using Finset.induction_on with
  | empty =>
      exact ⟨profile.family, hfamily, Finset.Subset.rfl,
        by simp [MultiscaleProfile.UniformOn], by simp⟩
  | @insert r scales hr ih =>
      have hscales' : scales ⊆ profile.scales :=
        Finset.Subset.trans (Finset.subset_insert r scales) hscales
      obtain ⟨current, hcurrent, hcurrent_sub, huniform, hcard⟩ :=
        ih hscales'
      have hr_profile : r ∈ profile.scales :=
        hscales (Finset.mem_insert_self r scales)
      have hcurrent_label :
          ∀ x ∈ current, profile.label r x ∈ candidates r := by
        intro x hx
        exact hlabel r hr_profile x (hcurrent_sub hx)
      obtain ⟨step, hstep_source, _hstep_label, _hstep_level,
        _hstep_selected_eq, hstep_nonempty, hstep_subset, hstep_uniform,
        hstep_loss, hstep_card_with_loss⟩ :=
        exists_dyadic_pigeonhole current (profile.label r) (candidates r)
          hcurrent hcurrent_label
      have hstep_selected_sub_current : step.selected ⊆ current := hstep_subset
      have hstep_selected_sub : step.selected ⊆ profile.family :=
        Finset.Subset.trans hstep_selected_sub_current hcurrent_sub
      have hnew_uniform : profile.UniformOn step.selected (insert r scales) := by
        intro q hq
        rcases Finset.mem_insert.mp hq with hqr | hq
        · refine ⟨step.level, ?_⟩
          intro x hx
          simpa [hqr] using hstep_uniform x hx
        · obtain ⟨level, hlevel⟩ := huniform q hq
          exact ⟨level, fun x hx ↦ hlevel x (hstep_selected_sub_current hx)⟩
      have hstep_card :
          current.card ≤ (candidates r).card * step.selected.card := by
        simpa [hstep_loss] using hstep_card_with_loss
      refine ⟨step.selected, hstep_nonempty, hstep_selected_sub,
        hnew_uniform, ?_⟩
      calc
        profile.family.card ≤
            scales.prod (fun q ↦ (candidates q).card) * current.card := hcard
        _ ≤ scales.prod (fun q ↦ (candidates q).card) *
              ((candidates r).card * step.selected.card) :=
          Nat.mul_le_mul_left _ hstep_card
        _ = (insert r scales).prod (fun q ↦ (candidates q).card) *
              step.selected.card := by
          rw [Finset.prod_insert hr]
          ac_rfl

/-- Simultaneous pigeonholing on every scale of a profile, with the product
of the candidate counts as the exact recorded loss. -/
theorem exists_multiscale_uniform_refinement
    {α : Type*} [DecidableEq α]
    (profile : MultiscaleProfile α)
    (candidates : Nat → Finset DyadicLevel)
    (hfamily : profile.family.Nonempty)
    (hlabel : ∀ r ∈ profile.scales, ∀ x ∈ profile.family,
      profile.label r x ∈ candidates r) :
    ∃ refinement : UniformRefinement α,
      refinement.profile = profile ∧
        refinement.refined.Nonempty ∧
        refinement.refined ⊆ profile.family ∧
        profile.UniformOn refinement.refined profile.scales ∧
        refinement.loss = profile.scales.prod (fun r ↦ (candidates r).card) ∧
        profile.family.card ≤ refinement.loss * refinement.refined.card := by
  classical
  obtain ⟨refined, hrefined, hsubset, huniform, hcard⟩ :=
    exists_uniform_on_scales profile candidates profile.scales hfamily
      Finset.Subset.rfl hlabel
  let refinement : UniformRefinement α :=
    { profile := profile
      refined := refined
      refined_subset := hsubset
      uniform := huniform
      loss := profile.scales.prod fun r ↦ (candidates r).card
      card_le_loss_mul := hcard }
  refine ⟨refinement, rfl, hrefined, hsubset, huniform, rfl, ?_⟩
  exact hcard

private theorem exists_large_weighted_candidate_fiber
    {α : Type*} [DecidableEq α]
    (source : Finset α) (label : α → DyadicLevel)
    (candidates : Finset DyadicLevel) (w : α → NNReal)
    (hsource : source.Nonempty)
    (hlabel : ∀ x ∈ source, label x ∈ candidates) :
    ∃ level : DyadicLevel,
      level ∈ candidates ∧
        (source.filter fun x ↦ label x = level).Nonempty ∧
        source.filter (fun x ↦ label x = level) ⊆ source ∧
        (∀ x ∈ source.filter (fun x ↦ label x = level), label x = level) ∧
        (∑ x ∈ source, w x) ≤
          candidates.card • ∑ x ∈ source.filter (fun x ↦ label x = level), w x := by
  classical
  let levels : Finset DyadicLevel := source.image label
  have hlevels : levels.Nonempty := hsource.image label
  let fiberWeight : DyadicLevel → NNReal := fun level ↦
    ∑ x ∈ source with label x = level, w x
  obtain ⟨level, hlevel, hmax⟩ :=
    Finset.exists_max_image levels fiberWeight hlevels
  have hlevel_candidates : level ∈ candidates := by
    obtain ⟨x, hx, hxl⟩ := Finset.mem_image.mp hlevel
    exact hxl ▸ hlabel x hx
  have hselected : (source.filter fun x ↦ label x = level).Nonempty := by
    obtain ⟨x, hx, hxl⟩ := Finset.mem_image.mp hlevel
    exact ⟨x, Finset.mem_filter.mpr ⟨hx, hxl⟩⟩
  have hlevels_subset : levels ⊆ candidates := by
    intro level' hlevel'
    obtain ⟨x, hx, hxl⟩ := Finset.mem_image.mp hlevel'
    exact hxl ▸ hlabel x hx
  have hweight :
      (∑ x ∈ source, w x) ≤
        candidates.card • ∑ x ∈ source.filter (fun x ↦ label x = level), w x := by
    calc
      (∑ x ∈ source, w x) = ∑ l ∈ levels, fiberWeight l :=
        (Finset.sum_fiberwise_of_maps_to
          (s := source) (t := levels) (g := label)
          (fun x hx ↦ Finset.mem_image.mpr ⟨x, hx, rfl⟩) w).symm
      _ ≤ levels.card • fiberWeight level :=
        Finset.sum_le_card_nsmul levels fiberWeight (fiberWeight level)
          fun l hl ↦ hmax l hl
      _ ≤ candidates.card • fiberWeight level :=
        nsmul_le_nsmul_left (show 0 ≤ fiberWeight level from bot_le)
          (Finset.card_le_card hlevels_subset)
      _ = candidates.card •
          ∑ x ∈ source.filter (fun x ↦ label x = level), w x := by
        simp [fiberWeight]
  exact ⟨level, hlevel_candidates, hselected, Finset.filter_subset _ _,
    fun x hx ↦ (Finset.mem_filter.mp hx).2, hweight⟩

private theorem exists_weighted_uniform_on_scales
    {α : Type*} [DecidableEq α] (profile : MultiscaleProfile α)
    (candidates : Nat → Finset DyadicLevel) (w : α → NNReal)
    (scales : Finset Nat) (hfamily : profile.family.Nonempty)
    (hscales : scales ⊆ profile.scales)
    (hlabel : ∀ r ∈ profile.scales, ∀ x ∈ profile.family,
      profile.label r x ∈ candidates r) :
    ∃ refined : Finset α,
      refined.Nonempty ∧
        refined ⊆ profile.family ∧
        profile.UniformOn refined scales ∧
        (∑ x ∈ profile.family, w x) ≤
          scales.prod (fun r ↦ (candidates r).card) • ∑ x ∈ refined, w x := by
  classical
  induction scales using Finset.induction_on with
  | empty =>
      exact ⟨profile.family, hfamily, Finset.Subset.rfl,
        by simp [MultiscaleProfile.UniformOn], by simp⟩
  | @insert r scales hr ih =>
      have hscales' : scales ⊆ profile.scales :=
        Finset.Subset.trans (Finset.subset_insert r scales) hscales
      obtain ⟨current, hcurrent, hcurrent_sub, huniform, hweight⟩ :=
        ih hscales'
      have hr_profile : r ∈ profile.scales :=
        hscales (Finset.mem_insert_self r scales)
      have hcurrent_label :
          ∀ x ∈ current, profile.label r x ∈ candidates r := by
        intro x hx
        exact hlabel r hr_profile x (hcurrent_sub hx)
      obtain ⟨level, _, hselected, hselected_sub_current,
        hselected_uniform, hstep_weight⟩ :=
        exists_large_weighted_candidate_fiber current (profile.label r)
          (candidates r) w hcurrent hcurrent_label
      let selected := current.filter fun x ↦ profile.label r x = level
      have hselected_sub : selected ⊆ profile.family :=
        Finset.Subset.trans hselected_sub_current hcurrent_sub
      have hnew_uniform : profile.UniformOn selected (insert r scales) := by
        intro q hq
        rcases Finset.mem_insert.mp hq with hqr | hq
        · exact ⟨level, fun x hx ↦ by
            simpa [selected, hqr] using hselected_uniform x hx⟩
        · obtain ⟨oldLevel, holdLevel⟩ := huniform q hq
          exact ⟨oldLevel, fun x hx ↦
            holdLevel x (hselected_sub_current hx)⟩
      refine ⟨selected, hselected, hselected_sub, hnew_uniform, ?_⟩
      calc
        (∑ x ∈ profile.family, w x) ≤
            scales.prod (fun q ↦ (candidates q).card) • ∑ x ∈ current, w x := hweight
        _ ≤ scales.prod (fun q ↦ (candidates q).card) •
            ((candidates r).card • ∑ x ∈ selected, w x) :=
          nsmul_le_nsmul_right hstep_weight _
        _ = (insert r scales).prod (fun q ↦ (candidates q).card) •
            ∑ x ∈ selected, w x := by
          rw [Finset.prod_insert hr]
          simp only [nsmul_eq_mul, Nat.cast_mul]
          ac_rfl

/-- Weighted simultaneous pigeonholing, retaining at least the reciprocal of
the product of candidate counts in total `NNReal` weight. -/
theorem exists_weighted_multiscale_uniform_refinement
    {α : Type*} [DecidableEq α]
    (profile : MultiscaleProfile α)
    (candidates : Nat → Finset DyadicLevel) (w : α → NNReal)
    (hfamily : profile.family.Nonempty)
    (hlabel : ∀ r ∈ profile.scales, ∀ x ∈ profile.family,
      profile.label r x ∈ candidates r) :
    ∃ refined : Finset α,
      refined.Nonempty ∧
        refined ⊆ profile.family ∧
        profile.UniformOn refined profile.scales ∧
        Finset.sum profile.family w ≤
          profile.scales.prod (fun r ↦ (candidates r).card) •
            Finset.sum refined w :=
  exists_weighted_uniform_on_scales profile candidates w profile.scales
    hfamily Finset.Subset.rfl hlabel

end Submission.Kakeya.Uniformity
