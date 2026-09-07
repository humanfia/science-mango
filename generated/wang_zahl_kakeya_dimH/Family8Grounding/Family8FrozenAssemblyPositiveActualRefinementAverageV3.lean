import Family8Grounding.Family8FrozenComparableActualAverageMassDensityV1
import Family8Grounding.Family8ExactAssemblyActualAverageBridgeV1

/-!
# Positive actual refinement averages for frozen assemblies, V3

Any frozen assembly retaining nonzero source mass has nonzero refinement
mass, hence positive shaded-union volume and actual average multiplicity at
least one.  V1--V2 are elaboration/syntax drafts and are not imported.
-/

set_option autoImplicit false
set_option warningAsError true

open Set MeasureTheory
open scoped ENNReal NNReal

namespace Family8FrozenAssemblyPositiveActualRefinementAverageV3

open LeanEval.Analysis.WangZahlKakeya
open Submission.Kakeya.ConvexGeometry
open Submission.Kakeya.ConvexFactoring
open Family8FrozenComparableActualAverageMassDensityV1
open Family8FrozenComparableActualAverageMassDensityV1.Assembly

noncomputable section

variable {iota kappa : Type*}
  [Fintype iota] [Fintype kappa]
  [DecidableEq iota] [DecidableEq kappa]
  {F : ConvexFamily iota} {W : ConvexFamily kappa}
  {P : ConvexFactorization F W} {Y : Shading F} {r : Real}

/-- A retained nonzero source forces the literal actual refinement average
to be at least one. -/
theorem Assembly.one_le_actualRefinementShading_averageMultiplicity
    (A : Family8FrozenNeighborhoodAssemblyV1.Assembly P Y r)
    (hsource :
      (IndexedShadingRefinement.restrictTo
        Y P.index.fine).shading.shadingMass ≠ 0) :
    1 <= (actualRefinementShading A).averageMultiplicity := by
  have hrefinement : A.refinement.shading.shadingMass ≠ 0 :=
    refinement_shadingMass_ne_zero A hsource
  have hactualMass : (actualRefinementShading A).shadingMass ≠ 0 := by
    rwa [actualRefinementShading_shadingMass]
  have hvolume : volume (actualRefinementShading A).shadedUnion ≠ 0 :=
    Family8ExactAssemblyActualAverageBridgeV1.volume_shadedUnion_ne_zero_of_shadingMass_ne_zero
      (actualRefinementShading A) hactualMass
  have hone := natCast_le_averageMultiplicity_of_pointMultiplicity_lower
    (actualRefinementShading A) 1 hvolume (fun x hx => by
      exact Nat.one_le_iff_ne_zero.mpr <|
        ne_of_gt <|
          ((actualRefinementShading A).pointMultiplicity_pos_iff_mem_shadedUnion x).2 hx)
  simpa only [Nat.cast_one] using hone

#print axioms
  Assembly.one_le_actualRefinementShading_averageMultiplicity

end
end Family8FrozenAssemblyPositiveActualRefinementAverageV3
