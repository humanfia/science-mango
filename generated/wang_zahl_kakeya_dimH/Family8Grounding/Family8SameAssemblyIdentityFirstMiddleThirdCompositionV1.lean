import Family8Grounding.Family8SourceActiveFineActualAverageIdentityV2
import Mathlib.Tactic

/-!
# Same-assembly middle/third product with an identity first factor

At the endpoint scale the first Section-8 factor is an identity.  The honest
retention loss therefore stays with the middle average, while the third
average remains the frozen-coarse average of the very same assembly.
-/

set_option autoImplicit false
set_option warningAsError true

open Set MeasureTheory
open scoped ENNReal NNReal

namespace Family8SameAssemblyIdentityFirstMiddleThirdCompositionV1

open Submission.Kakeya.ConvexGeometry
open Submission.Kakeya.ConvexFactoring
open Family8FrozenComparableActualAverageMassDensityV1
open Family8FrozenComparableActualAverageMassDensityV1.Assembly
open Family8SourceActiveFineActualAverageIdentityV2

noncomputable section

variable {iota kappa : Type*} [Fintype iota] [Fintype kappa]
  [DecidableEq iota] [DecidableEq kappa]
  {F : ConvexFamily iota} {W : ConvexFamily kappa}
  {P : ConvexFactorization F W} {Y : Shading F} {r : Real}

/-- A retained same-assembly middle estimate gives the literal three-factor
product with `firstAverage = 1`, `middleAverage = 4 * loss * middleFactor`,
and `thirdAverage = frozenCoarse.averageMultiplicity`. -/
theorem restrictTo_source_averageMultiplicity_le_identityFirst_middle_third
    (A : Family8FrozenNeighborhoodAssemblyV1.Assembly P Y r)
    {middleFactor : ENNReal}
    (hmiddle :
      (actualRefinementShading A).averageMultiplicity <=
        4 * (A.frozenCoarse.averageMultiplicity * middleFactor)) :
    (IndexedShadingRefinement.restrictTo Y
      P.index.fine).shading.averageMultiplicity <=
      1 * (((4 * (A.loss : ENNReal)) * middleFactor) *
        A.frozenCoarse.averageMultiplicity) := by
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
    _ = 1 * (((4 * (A.loss : ENNReal)) * middleFactor) *
          A.frozenCoarse.averageMultiplicity) := by
      ac_rfl

#print axioms
  restrictTo_source_averageMultiplicity_le_identityFirst_middle_third

end
end Family8SameAssemblyIdentityFirstMiddleThirdCompositionV1
