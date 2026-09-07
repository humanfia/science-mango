import Family8Grounding.Family8ExactAssemblyActualAverageBridgeV1
import Mathlib.Tactic

/-!
# Source-average retention for every exact multiplicity assembly

`ExactAssembly.retained` is a genuine mass-retention field.  Carrier
containment and the certified active-fine support turn it into the
direction-safe average-multiplicity comparison needed to place an analytic
bound on the assembly's actual refinement into a source-scale product.
-/

open Set MeasureTheory
open scoped ENNReal NNReal

namespace Family8ExactAssemblySourceAverageRetentionV1

open LeanEval.Analysis.WangZahlKakeya
open Submission.Kakeya.ConvexGeometry
open Submission.Kakeya.ConvexFactoring
open Submission.Kakeya.ConvexFactoring.FactoringMultiplicityAssembly

noncomputable section

set_option autoImplicit false
set_option warningAsError true

local instance (p : Prop) : Decidable p := Classical.propDecidable p

namespace ExactAssembly

variable {iota kappa : Type*} [Fintype iota] [Fintype kappa]
  [DecidableEq iota] [DecidableEq kappa]
  {F : ConvexFamily iota} {W : ConvexFamily kappa}
  {P : ConvexFactorization F W} {Y : Shading F} {loss : Nat}

/-- The final refinement union lies in the literal active source union. -/
theorem refinement_shadedUnion_subset_restrictTo_source
    (A : FactoringMultiplicityAssembly.ExactAssembly P Y loss) :
    A.refinement.shading.shadedUnion ⊆
      (IndexedShadingRefinement.restrictTo Y
        P.index.fine).shading.shadedUnion := by
  intro x hx
  obtain ⟨i, hxi⟩ := Set.mem_iUnion.mp hx
  have hi : i ∈ A.refinement.indices := by
    by_contra hni
    rw [A.refinement.carrier_eq_empty_of_not_mem i hni] at hxi
    exact hxi
  have hif : i ∈ P.index.fine := A.indices_subset_fine hi
  apply Set.mem_iUnion.mpr
  refine ⟨i, ?_⟩
  rw [IndexedShadingRefinement.restrictTo_carrier, if_pos hif]
  exact A.refinement.carrier_subset i hxi

/-- Exact-assembly mass retention implies the corresponding actual-average
retention, with precisely its stored natural loss. -/
theorem restrictTo_source_averageMultiplicity_le_loss_mul_refinement
    (A : FactoringMultiplicityAssembly.ExactAssembly P Y loss) :
    (IndexedShadingRefinement.restrictTo Y
      P.index.fine).shading.averageMultiplicity ≤
      (loss : ENNReal) * A.refinement.shading.averageMultiplicity := by
  have hmass :
      (IndexedShadingRefinement.restrictTo Y
        P.index.fine).shading.shadingMass ≤
        (loss : ENNReal) * A.refinement.shading.shadingMass := by
    simpa only [WithinFactor, nsmul_eq_mul] using A.retained
  have hunion := refinement_shadedUnion_subset_restrictTo_source A
  unfold Shading.averageMultiplicity
  calc
    (IndexedShadingRefinement.restrictTo Y
          P.index.fine).shading.shadingMass /
        volume (IndexedShadingRefinement.restrictTo Y
          P.index.fine).shading.shadedUnion ≤
      ((loss : ENNReal) * A.refinement.shading.shadingMass) /
        volume (IndexedShadingRefinement.restrictTo Y
          P.index.fine).shading.shadedUnion :=
        ENNReal.div_le_div_right hmass _
    _ ≤ ((loss : ENNReal) * A.refinement.shading.shadingMass) /
        volume A.refinement.shading.shadedUnion :=
      ENNReal.div_le_div_left (measure_mono hunion) _
    _ = (loss : ENNReal) *
        (A.refinement.shading.shadingMass /
          volume A.refinement.shading.shadedUnion) := by
      simp only [div_eq_mul_inv]
      ac_rfl

#print axioms refinement_shadedUnion_subset_restrictTo_source
#print axioms
  restrictTo_source_averageMultiplicity_le_loss_mul_refinement

end ExactAssembly

end
end Family8ExactAssemblySourceAverageRetentionV1
