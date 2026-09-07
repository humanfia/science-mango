import Family8Grounding.Family8Def212ConvexWolffAtEveryScaleV2
import Mathlib.Tactic

set_option autoImplicit false
set_option warningAsError true

open Set MeasureTheory
open scoped ENNReal NNReal

namespace Family8ConvexWolffReindexV1

open LeanEval.Analysis.WangZahlKakeya
open Submission.Kakeya.ConvexGeometry
open Family8Def212ConvexWolffAtEveryScaleV2

noncomputable section

/-! Convex Wolff axioms are invariant under an equivalence of the finite
index type.  This is pure reindexing: no cardinal loss occurs. -/

def reindexConvexFamily
    {alpha beta : Type*} (e : beta ≃ alpha)
    (F : ConvexFamily alpha) : ConvexFamily beta :=
  fun b ↦ F (e b)

@[simp]
theorem reindexConvexFamily_apply
    {alpha beta : Type*} (e : beta ≃ alpha)
    (F : ConvexFamily alpha) (b : beta) :
    reindexConvexFamily e F b = F (e b) := rfl

theorem containedIndices_reindex_card_eq
    {alpha beta : Type*} [Fintype alpha] [Fintype beta]
    (e : beta ≃ alpha) (F : ConvexFamily alpha)
    (K : ConvexBody Space) :
    (containedIndices (reindexConvexFamily e F) K).card =
      (containedIndices F K).card := by
  classical
  let emb : beta ↪ alpha := e.toEmbedding
  have hmap :
      (containedIndices (reindexConvexFamily e F) K).map emb =
        containedIndices F K := by
    ext a
    simp [containedIndices, reindexConvexFamily, emb]
  rw [← hmap, Finset.card_map]

theorem satisfiesConvexWolffAxioms_reindex
    {alpha beta : Type*} [Fintype alpha] [Fintype beta]
    (e : beta ≃ alpha) {F : ConvexFamily alpha} {C : ENNReal}
    (hCWA : SatisfiesConvexWolffAxioms C F) :
    SatisfiesConvexWolffAxioms C (reindexConvexFamily e F) := by
  intro K
  rw [containedIndices_reindex_card_eq e F K,
    show Fintype.card beta = Fintype.card alpha from
      Fintype.card_congr e]
  exact hCWA K

#print axioms containedIndices_reindex_card_eq
#print axioms satisfiesConvexWolffAxioms_reindex

end
end Family8ConvexWolffReindexV1
