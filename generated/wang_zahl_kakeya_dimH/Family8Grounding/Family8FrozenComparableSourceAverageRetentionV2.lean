import Family8Grounding.Family8FrozenComparableActualAverageMassDensityV1
import Submission.Kakeya.ConvexFactoring.RefinementMultiplicity

set_option autoImplicit false
set_option warningAsError true

open Set MeasureTheory
open scoped ENNReal NNReal

namespace Family8FrozenComparableSourceAverageRetentionV2

open LeanEval.Analysis.WangZahlKakeya
open Submission.Kakeya.ConvexGeometry
open Submission.Kakeya.ConvexFactoring
open Family8FrozenNeighborhoodAssemblyV1
open Family8FrozenComparableActualAverageMassDensityV1
open Family8FrozenComparableActualAverageMassDensityV1.Assembly

noncomputable section

/-!
# Source-average retention for the literal frozen comparable assembly

The canonical frozen assembly already proves mass retention on the literal
final subtype.  This file supplies the corresponding direction-safe average
multiplicity statement on exactly the same data.  It is a formal consequence
of carrier inclusion and contains no analytic estimate or callback.

V1 is a failed namespace-shadowing draft and is not imported.
-/

namespace SourceAverage

variable {iota kappa : Type*} [Fintype iota] [Fintype kappa]
  [DecidableEq iota] [DecidableEq kappa]
  {F : ConvexFamily iota} {W : ConvexFamily kappa}
  {P : ConvexFactorization F W} {Y : Shading F} {r : Real}

/-- The final literal subtype shading is contained in the literal source
active-fine shading. -/
theorem actualRefinementShading_shadedUnion_subset_sourceActiveFineShading
    (A : Family8FrozenNeighborhoodAssemblyV1.Assembly P Y r) :
    (actualRefinementShading A).shadedUnion ⊆
      (sourceActiveFineShading P Y).shadedUnion := by
  intro x hx
  obtain ⟨i, hxi⟩ := Set.mem_iUnion.mp hx
  apply Set.mem_iUnion.mpr
  refine ⟨actualRefinementToSourceActiveFine A i, ?_⟩
  change x ∈ A.refinement.shading.carrier i.1 at hxi
  change x ∈ Y.carrier i.1
  exact A.refinement.carrier_subset i.1 hxi

/-- The source active-fine average multiplicity is at most the explicit
frozen comparable loss times the actual final average multiplicity.  The
quotient proof is valid even when a shaded union has zero volume. -/
theorem sourceActiveFineShading_averageMultiplicity_le_loss_mul_actualRefinement
    (A : Family8FrozenNeighborhoodAssemblyV1.Assembly P Y r) :
    (sourceActiveFineShading P Y).averageMultiplicity ≤
      (A.loss : ENNReal) * (actualRefinementShading A).averageMultiplicity := by
  have hmass :=
    sourceActiveFineShading_mass_le_loss_mul_actualRefinementShading A
  have hunion :=
    actualRefinementShading_shadedUnion_subset_sourceActiveFineShading A
  unfold Shading.averageMultiplicity
  calc
    (sourceActiveFineShading P Y).shadingMass /
          volume (sourceActiveFineShading P Y).shadedUnion ≤
        ((A.loss : ENNReal) *
            (actualRefinementShading A).shadingMass) /
          volume (sourceActiveFineShading P Y).shadedUnion :=
      ENNReal.div_le_div_right hmass _
    _ ≤ ((A.loss : ENNReal) *
            (actualRefinementShading A).shadingMass) /
          volume (actualRefinementShading A).shadedUnion :=
      ENNReal.div_le_div_left (measure_mono hunion) _
    _ = (A.loss : ENNReal) *
        ((actualRefinementShading A).shadingMass /
          volume (actualRefinementShading A).shadedUnion) := by
      simp only [div_eq_mul_inv]
      ac_rfl

#print axioms
  actualRefinementShading_shadedUnion_subset_sourceActiveFineShading
#print axioms
  sourceActiveFineShading_averageMultiplicity_le_loss_mul_actualRefinement

end SourceAverage

end

end Family8FrozenComparableSourceAverageRetentionV2
