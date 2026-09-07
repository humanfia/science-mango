import Family8Grounding.Family8Def212ConvexWolffAtEveryScaleV2
import Mathlib.Tactic

set_option autoImplicit false
set_option warningAsError true

open Set MeasureTheory
open scoped ENNReal NNReal

namespace Family8CardinalCWAReindexV1

open LeanEval.Analysis.WangZahlKakeya
open Submission.Kakeya.ConvexGeometry
open Family8Def212ConvexWolffAtEveryScaleV2

noncomputable section

/-!
# Cardinal Convex Wolff axioms under finite reindexing

An equivalence of finite index types changes neither the multiplicity counted
by `containedIndices` nor the total cardinality used to normalize the Convex
Wolff axioms.  This file records the exact transport needed when a retained
parent fibre is reindexed by a new scale-cover construction.
-/

/-- Reindex a convex family along an equivalence of finite index types. -/
def reindexConvexFamily
    {source target : Type*}
    (e : source ≃ target) (F : ConvexFamily source) :
    ConvexFamily target :=
  fun j ↦ F (e.symm j)

@[simp]
theorem reindexConvexFamily_apply
    {source target : Type*}
    (e : source ≃ target) (F : ConvexFamily source) (j : target) :
    reindexConvexFamily e F j = F (e.symm j) := rfl

/-- The indices captured after reindexing are exactly the image of the old
captured indices. -/
theorem containedIndices_reindexConvexFamily
    {source target : Type*} [Fintype source] [Fintype target]
    (e : source ≃ target) (F : ConvexFamily source)
    (K : ConvexBody Space) :
    containedIndices (reindexConvexFamily e F) K =
      (containedIndices F K).map e.toEmbedding := by
  classical
  ext j
  simp [reindexConvexFamily,
    Submission.Kakeya.ConvexFactoring.mem_containedIndices]

/-- Reindexing preserves the exact number of family members captured by
every convex body. -/
theorem containedIndices_reindexConvexFamily_card
    {source target : Type*} [Fintype source] [Fintype target]
    (e : source ≃ target) (F : ConvexFamily source)
    (K : ConvexBody Space) :
    (containedIndices (reindexConvexFamily e F) K).card =
      (containedIndices F K).card := by
  rw [containedIndices_reindexConvexFamily]
  exact Finset.card_map e.toEmbedding

/-- Equivalent finite types have the same cardinality, stated in the exact
orientation used by the CWA transport. -/
theorem fintype_card_eq_of_equiv
    {source target : Type*} [Fintype source] [Fintype target]
    (e : source ≃ target) :
    Fintype.card target = Fintype.card source := by
  exact (Fintype.card_congr e).symm

/-- Cardinal-normalized Convex Wolff axioms are invariant under finite
reindexing. -/
theorem satisfiesConvexWolffAxioms_reindexConvexFamily_iff
    {source target : Type*} [Fintype source] [Fintype target]
    (e : source ≃ target) (F : ConvexFamily source) (C : ENNReal) :
    SatisfiesConvexWolffAxioms C (reindexConvexFamily e F) ↔
      SatisfiesConvexWolffAxioms C F := by
  constructor
  · intro h K
    have hK := h K
    rw [containedIndices_reindexConvexFamily_card e F K,
      fintype_card_eq_of_equiv e] at hK
    exact hK
  · intro h K
    rw [containedIndices_reindexConvexFamily_card e F K,
      fintype_card_eq_of_equiv e]
    exact h K

/-- Forward transport of CWA along a finite equivalence. -/
theorem SatisfiesConvexWolffAxioms.reindexConvexFamily
    {source target : Type*} [Fintype source] [Fintype target]
    {e : source ≃ target} {F : ConvexFamily source} {C : ENNReal}
    (h : SatisfiesConvexWolffAxioms C F) :
    SatisfiesConvexWolffAxioms C (reindexConvexFamily e F) :=
  (satisfiesConvexWolffAxioms_reindexConvexFamily_iff e F C).2 h

#print axioms reindexConvexFamily_apply
#print axioms containedIndices_reindexConvexFamily
#print axioms containedIndices_reindexConvexFamily_card
#print axioms fintype_card_eq_of_equiv
#print axioms satisfiesConvexWolffAxioms_reindexConvexFamily_iff
#print axioms SatisfiesConvexWolffAxioms.reindexConvexFamily

end
end Family8CardinalCWAReindexV1
