import Family8Grounding.Family8NormalizedCFDividingWitnessBridgeV2
import Mathlib.Tactic

/-!
# Normalized CF maximum on an already selected parent set

The factor-first LongCore route must run the stopping comparison only after
the mass/fine-label selector has fixed the parents that survive at the
candidate middle scale.  This file contains the finite constructive core of
that redesign.

Unlike `parentNormalizedFiberCFMax`, the statistic below takes its supremum
only over a caller-specified nonempty subset of the literal active parents.
Consequently a lower barrier for it produces a parent which is simultaneously
selected and high-CF.  Any memberwise mass floor carried by the selected set
then holds at that very same parent.

No selector, stopping callback, or geometric existence hypothesis is packaged
here.  The selected set and its proved active-parent inclusion are literal
inputs.
-/

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 1200000

open scoped ENNReal NNReal

namespace Family8SelectedParentCFMaxOnV1

open Submission.Kakeya.Uniformity
open Family8NormalizedCFDividingWitnessBridgeV2.StickyScaleCover
open FamilyStickyAtEveryScaleCoreV1

noncomputable section

variable {delta rho : NNReal} {index : Type*}
  [Fintype index] [DecidableEq index]
  {fine : UniformTubeFamily delta index}

/-- The worst normalized fibre constant among one literal selected set of
active parents. -/
def parentNormalizedFiberCFMaxOn
    (S : StickyScaleCover fine rho)
    (selected : Finset (Fin S.coarseCard))
    (hselectedActive : selected ⊆ S.activeCoarse) : ENNReal :=
  ⨆ q : {q // q ∈ selected},
    parentNormalizedFiberCFAt S
      ⟨q.1, hselectedActive q.2⟩

/-- The selected maximum is bounded by the old cover-wide maximum.  Thus the
factor-first statistic is a genuine strengthening of the old stopping
barrier, rather than an identification of unrelated maximizers. -/
theorem parentNormalizedFiberCFMaxOn_le_full
    (S : StickyScaleCover fine rho)
    (selected : Finset (Fin S.coarseCard))
    (hselectedActive : selected ⊆ S.activeCoarse) :
    parentNormalizedFiberCFMaxOn S selected hselectedActive ≤
      parentNormalizedFiberCFMax S := by
  unfold parentNormalizedFiberCFMaxOn
  apply iSup_le
  intro q
  exact parentNormalizedFiberCFAt_le S
    ⟨q.1, hselectedActive q.2⟩

/-- A lower barrier for the selected-set maximum is attained at one literal
selected active parent. -/
theorem exists_selected_parent_cfAt_lower
    (S : StickyScaleCover fine rho)
    (selected : Finset (Fin S.coarseCard))
    (hselectedActive : selected ⊆ S.activeCoarse)
    (hselected : selected.Nonempty)
    {lower : ENNReal}
    (hlower : lower ≤
      parentNormalizedFiberCFMaxOn S selected hselectedActive) :
    ∃ q : {q // q ∈ S.activeCoarse},
      q.1 ∈ selected ∧ lower ≤ parentNormalizedFiberCFAt S q := by
  classical
  let f : {q // q ∈ selected} → ENNReal := fun q ↦
    parentNormalizedFiberCFAt S ⟨q.1, hselectedActive q.2⟩
  have huniv : (Finset.univ : Finset {q // q ∈ selected}).Nonempty := by
    obtain ⟨q, hq⟩ := hselected
    exact ⟨⟨q, hq⟩, Finset.mem_univ _⟩
  obtain ⟨q, _hq, hqMax⟩ :=
    Finset.exists_mem_eq_sup
      (Finset.univ : Finset {q // q ∈ selected}) huniv f
  have hattains :
      parentNormalizedFiberCFMaxOn S selected hselectedActive = f q := by
    rw [parentNormalizedFiberCFMaxOn, ← Finset.sup_univ_eq_iSup]
    exact hqMax
  let qActive : {q // q ∈ S.activeCoarse} :=
    ⟨q.1, hselectedActive q.2⟩
  refine ⟨qActive, q.2, ?_⟩
  change lower ≤ f q
  rw [← hattains]
  exact hlower

/-- Constructive same-object coupling used by the redesigned producer: if
every parent surviving the factor/fine-label selection has a quantitative
weight floor, the parent attaining the selected CF barrier has that floor as
well. -/
theorem exists_selected_parent_cfAt_lower_and_weight_floor
    (S : StickyScaleCover fine rho)
    (selected : Finset (Fin S.coarseCard))
    (hselectedActive : selected ⊆ S.activeCoarse)
    (hselected : selected.Nonempty)
    (weight : Fin S.coarseCard → ENNReal)
    {lower floor : ENNReal}
    (hfloor : ∀ q ∈ selected, floor ≤ weight q)
    (hlower : lower ≤
      parentNormalizedFiberCFMaxOn S selected hselectedActive) :
    ∃ q : {q // q ∈ S.activeCoarse},
      q.1 ∈ selected ∧
      lower ≤ parentNormalizedFiberCFAt S q ∧
      floor ≤ weight q.1 := by
  obtain ⟨q, hqSelected, hqCF⟩ :=
    exists_selected_parent_cfAt_lower
      S selected hselectedActive hselected hlower
  exact ⟨q, hqSelected, hqCF, hfloor q.1 hqSelected⟩

#print axioms parentNormalizedFiberCFMaxOn
#print axioms parentNormalizedFiberCFMaxOn_le_full
#print axioms exists_selected_parent_cfAt_lower
#print axioms exists_selected_parent_cfAt_lower_and_weight_floor

end

end Family8SelectedParentCFMaxOnV1
