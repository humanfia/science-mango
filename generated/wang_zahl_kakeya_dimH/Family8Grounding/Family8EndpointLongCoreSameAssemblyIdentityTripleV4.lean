import Family8Grounding.Family8SameAssemblyIdentityFirstMiddleThirdCompositionV1
import Family8Grounding.Family8KatzTaoFrostmanPropertiesV1
import Mathlib.Tactic

/-!
# Endpoint long-core identity-first same-assembly triple, V4

This adapter consumes the two exact average identities established by the
endpoint transports, then combines them with the retained middle estimate on
the same frozen assembly.  V1--V3 are failed drafts and are not imported.
-/

set_option autoImplicit false
set_option warningAsError true

open scoped ENNReal NNReal

namespace Family8EndpointLongCoreSameAssemblyIdentityTripleV4

open Submission.Kakeya.ConvexGeometry
open Submission.Kakeya.ConvexFactoring
open Family8FrozenComparableActualAverageMassDensityV1
open Family8FrozenComparableActualAverageMassDensityV1.Assembly
open Family8KatzTaoFrostmanPropertiesV1
open Family8SameAssemblyIdentityFirstMiddleThirdCompositionV1

noncomputable section

variable {delta : NNReal} {index iota kappa : Type}
  [Fintype index] [DecidableEq index]
  [Fintype iota] [Fintype kappa]
  [DecidableEq iota] [DecidableEq kappa]
  {F : ConvexFamily iota} {G : ConvexFamily kappa}
  {Q : ConvexFactorization F G} {Y : Shading F} {r : Real}

/-- Exact source/tau transports plus the same-assembly retention inequality
give the literal identity-first three-factor estimate on the original actual
datum. -/
theorem actualDatum_averageMultiplicity_le_identityFirst_middle_third
    (D : ActualTubeDatum delta index)
    (A : Family8FrozenNeighborhoodAssemblyV1.Assembly Q Y r)
    {tauAverage middleFactor : ENNReal}
    (hTau : tauAverage = D.shading.averageMultiplicity)
    (hBounded :
      (IndexedShadingRefinement.restrictTo Y
        Q.index.fine).shading.averageMultiplicity = tauAverage)
    (hMiddle :
      (actualRefinementShading A).averageMultiplicity <=
        4 * (A.frozenCoarse.averageMultiplicity * middleFactor)) :
    D.shading.averageMultiplicity <=
      1 * (((4 * (A.loss : ENNReal)) * middleFactor) *
        A.frozenCoarse.averageMultiplicity) := by
  calc
    D.shading.averageMultiplicity = tauAverage := hTau.symm
    _ = (IndexedShadingRefinement.restrictTo Y
          Q.index.fine).shading.averageMultiplicity := hBounded.symm
    _ <= 1 * (((4 * (A.loss : ENNReal)) * middleFactor) *
          A.frozenCoarse.averageMultiplicity) :=
      restrictTo_source_averageMultiplicity_le_identityFirst_middle_third
        A hMiddle

#print axioms
  actualDatum_averageMultiplicity_le_identityFirst_middle_third

end
end Family8EndpointLongCoreSameAssemblyIdentityTripleV4
