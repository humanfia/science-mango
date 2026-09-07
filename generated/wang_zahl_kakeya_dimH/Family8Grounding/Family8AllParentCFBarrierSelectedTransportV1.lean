import Family8Grounding.Family8SelectedParentCFMaxOnV1

/-!
# Transport of an all-parent normalized-CF barrier through selection

The paper's long-core barrier is memberwise on the parents at the middle
scale.  This is stronger than a lower bound for the cover-wide maximum and
is exactly stable under a mass, fine-label, or popularity selection: every
surviving parent still satisfies the same barrier.

This file packages that literal memberwise datum and its finite selected-set
consequences.  It does not construct the upstream stopping witness.
-/

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 1200000

open scoped ENNReal NNReal

namespace Family8AllParentCFBarrierSelectedTransportV1

open Submission.Kakeya.Uniformity
open Family8NormalizedCFDividingWitnessBridgeV2.StickyScaleCover
open Family8SelectedParentCFMaxOnV1
open FamilyStickyAtEveryScaleCoreV1

noncomputable section

variable {delta rho : NNReal} {index : Type*}
  [Fintype index] [DecidableEq index]
  {fine : UniformTubeFamily delta index}

/-- The paper-faithful middle barrier: every literal active parent, rather
than merely one maximizer, has normalized fibre concentration at least the
displayed threshold. -/
structure AllActiveParentCFBarrier
    (S : StickyScaleCover fine rho) (lower : ENNReal) : Prop where
  lower_at : ∀ q : {q // q ∈ S.activeCoarse},
    lower ≤ parentNormalizedFiberCFAt S q

namespace AllActiveParentCFBarrier

variable {S : StickyScaleCover fine rho} {lower : ENNReal}

/-- Every member of an arbitrary selected active set retains the literal
same-parent barrier. -/
theorem selected_member_lower
    (H : AllActiveParentCFBarrier S lower)
    (selected : Finset (Fin S.coarseCard))
    (hselectedActive : selected ⊆ S.activeCoarse)
    (q : Fin S.coarseCard) (hq : q ∈ selected) :
    lower ≤ parentNormalizedFiberCFAt S
      ⟨q, hselectedActive hq⟩ := by
  exact H.lower_at ⟨q, hselectedActive hq⟩

/-- A selection-friendly form retaining the activity proof together with
the parentwise CF inequality. -/
theorem selected_forall_lower
    (H : AllActiveParentCFBarrier S lower)
    (selected : Finset (Fin S.coarseCard))
    (hselectedActive : selected ⊆ S.activeCoarse) :
    ∀ q ∈ selected, ∃ hqActive : q ∈ S.activeCoarse,
      lower ≤ parentNormalizedFiberCFAt S ⟨q, hqActive⟩ := by
  intro q hq
  exact ⟨hselectedActive hq, H.selected_member_lower
    selected hselectedActive q hq⟩

/-- On every nonempty selected set, the selected-set maximum inherits the
same lower barrier.  This is the exact bridge needed by factor-first
stopping and avoids comparing unrelated maximizers. -/
theorem lower_le_parentNormalizedFiberCFMaxOn
    (H : AllActiveParentCFBarrier S lower)
    (selected : Finset (Fin S.coarseCard))
    (hselectedActive : selected ⊆ S.activeCoarse)
    (hselected : selected.Nonempty) :
    lower ≤ parentNormalizedFiberCFMaxOn S selected hselectedActive := by
  obtain ⟨q, hq⟩ := hselected
  unfold parentNormalizedFiberCFMaxOn
  calc
    lower ≤ parentNormalizedFiberCFAt S
        ⟨q, hselectedActive hq⟩ :=
      H.selected_member_lower selected hselectedActive q hq
    _ ≤ ⨆ p : {p // p ∈ selected},
        parentNormalizedFiberCFAt S
          ⟨p.1, hselectedActive p.2⟩ := by
      exact le_iSup
        (fun p : {p // p ∈ selected} =>
          parentNormalizedFiberCFAt S
            ⟨p.1, hselectedActive p.2⟩) ⟨q, hq⟩

/-- The selected CF maximum therefore supplies the standard same-object
parent together with any memberwise quantitative weight floor. -/
theorem exists_selected_parent_lower_and_weight_floor
    (H : AllActiveParentCFBarrier S lower)
    (selected : Finset (Fin S.coarseCard))
    (hselectedActive : selected ⊆ S.activeCoarse)
    (hselected : selected.Nonempty)
    (weight : Fin S.coarseCard → ENNReal) {floor : ENNReal}
    (hfloor : ∀ q ∈ selected, floor ≤ weight q) :
    ∃ q : {q // q ∈ S.activeCoarse},
      q.1 ∈ selected ∧
      lower ≤ parentNormalizedFiberCFAt S q ∧
      floor ≤ weight q.1 := by
  exact exists_selected_parent_cfAt_lower_and_weight_floor
    S selected hselectedActive hselected weight hfloor
      (H.lower_le_parentNormalizedFiberCFMaxOn
        selected hselectedActive hselected)

#print axioms AllActiveParentCFBarrier
#print axioms selected_member_lower
#print axioms selected_forall_lower
#print axioms lower_le_parentNormalizedFiberCFMaxOn
#print axioms exists_selected_parent_lower_and_weight_floor

end AllActiveParentCFBarrier

end
end Family8AllParentCFBarrierSelectedTransportV1
