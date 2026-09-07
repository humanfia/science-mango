import Family8Grounding.Family8SourceActiveFineActualAverageIdentityV2
import Mathlib.Tactic

set_option autoImplicit false
set_option warningAsError true

open Set MeasureTheory
open scoped ENNReal NNReal

namespace Family8SameAssemblyRetainedMiddleThirdCompositionV1

open Submission.Kakeya.ConvexGeometry
open Submission.Kakeya.ConvexFactoring
open Family8FrozenComparableActualAverageMassDensityV1
open Family8FrozenComparableActualAverageMassDensityV1.Assembly
open Family8SourceActiveFineActualAverageIdentityV2

noncomputable section

/-!
# Retained middle and third factors on one frozen assembly

The selected-fine relative-power endpoint naturally estimates the actual
refinement of a frozen assembly, while the third-factor endpoint estimates
that same assembly's frozen coarse shading.  Source-average retention joins
those estimates without identifying the selected middle parent with the
positive fibre used by a separate product proof.
-/

variable {iota kappa : Type*} [Fintype iota] [Fintype kappa]
  [DecidableEq iota] [DecidableEq kappa]
  {F : ConvexFamily iota} {W : ConvexFamily kappa}
  {P : ConvexFactorization F W} {Y : Shading F} {r : Real}

/-- A middle estimate for the actual refinement and a third estimate for the
literal frozen coarse shading compose after the genuine retention loss. -/
theorem restrictTo_source_averageMultiplicity_le_retained_middle_third
    (A : Family8FrozenNeighborhoodAssemblyV1.Assembly P Y r)
    {middleFactor thirdFactor : ENNReal}
    (hmiddle :
      (actualRefinementShading A).averageMultiplicity <=
        4 * (A.frozenCoarse.averageMultiplicity * middleFactor))
    (hthird : A.frozenCoarse.averageMultiplicity <= thirdFactor) :
    (IndexedShadingRefinement.restrictTo Y
      P.index.fine).shading.averageMultiplicity <=
      (A.loss : ENNReal) * (4 * (thirdFactor * middleFactor)) := by
  have hretained :=
    restrictTo_source_averageMultiplicity_le_loss_mul_actualRefinement A
  calc
    (IndexedShadingRefinement.restrictTo Y
        P.index.fine).shading.averageMultiplicity <=
        (A.loss : ENNReal) *
          (actualRefinementShading A).averageMultiplicity := hretained
    _ <= (A.loss : ENNReal) *
          (4 * (A.frozenCoarse.averageMultiplicity * middleFactor)) :=
      mul_le_mul' le_rfl hmiddle
    _ <= (A.loss : ENNReal) * (4 * (thirdFactor * middleFactor)) :=
      mul_le_mul' le_rfl (mul_le_mul' le_rfl (mul_le_mul' hthird le_rfl))

#print axioms
  restrictTo_source_averageMultiplicity_le_retained_middle_third

end
end Family8SameAssemblyRetainedMiddleThirdCompositionV1
