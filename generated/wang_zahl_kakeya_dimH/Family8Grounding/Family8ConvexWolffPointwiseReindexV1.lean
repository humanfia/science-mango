import Family8Grounding.Family8ConvexWolffReindexV1

/-!
# Pointwise transport of the Convex Wolff axioms

This keeps the equality between two concrete families local to a generic,
small theorem.  Consumers therefore do not need to export a large equality
whose type contains both fully instantiated families.
-/

set_option autoImplicit false
set_option warningAsError true

open Set MeasureTheory
open scoped ENNReal NNReal

namespace Family8ConvexWolffPointwiseReindexV1

open LeanEval.Analysis.WangZahlKakeya
open Submission.Kakeya.ConvexGeometry
open Family8Def212ConvexWolffAtEveryScaleV2
open Family8ConvexWolffReindexV1

noncomputable section

/-- Convex Wolff bounds transport along an index equivalence when the two
families agree pointwise after reindexing. -/
theorem satisfiesConvexWolffAxioms_equiv_of_pointwise_eq
    {alpha beta : Type*} [Fintype alpha] [Fintype beta]
    (e : beta ≃ alpha) {F : ConvexFamily alpha} {G : ConvexFamily beta}
    {C : ENNReal} (hpoint : ∀ b, G b = F (e b))
    (hCWA : SatisfiesConvexWolffAxioms C F) :
    SatisfiesConvexWolffAxioms C G := by
  have hfamily : G = reindexConvexFamily e F := by
    funext b
    exact hpoint b
  rw [hfamily]
  exact satisfiesConvexWolffAxioms_reindex e hCWA

#print axioms satisfiesConvexWolffAxioms_equiv_of_pointwise_eq

end
end Family8ConvexWolffPointwiseReindexV1
