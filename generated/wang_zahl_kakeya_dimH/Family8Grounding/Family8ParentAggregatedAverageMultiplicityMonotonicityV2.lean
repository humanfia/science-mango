import FamilyStickyGrounding.FamilyStickyHierarchyEndpointPrefixShadingTransportV1

/-!
# Parent aggregation decreases average multiplicity, V2

Parent aggregation preserves the shaded union and can only decrease shading
mass.  Hence its actual average multiplicity is no larger than that of the
active fine shading.  V1 omitted the convex-geometry namespace and is not
imported.
-/

set_option autoImplicit false
set_option warningAsError true

open Set MeasureTheory
open scoped ENNReal NNReal

namespace Family8ParentAggregatedAverageMultiplicityMonotonicityV2

open LeanEval.Analysis.WangZahlKakeya
open Submission.Kakeya.ConvexGeometry
open Submission.Kakeya.ConvexFactoring
open Submission.Kakeya.Uniformity
open FamilyStickyAtEveryScaleCoreV1
open FamilyStickyHierarchyEndpointPrefixShadingTransportV1.StickyScaleCover

noncomputable section

variable {delta rho : NNReal} {index : Type}
  [Fintype index] [DecidableEq index]

/-- Regrouping active fine pieces by their literal parents cannot increase
average multiplicity: the numerator decreases and the shaded union is
unchanged. -/
theorem StickyScaleCover.parentAggregatedShading_averageMultiplicity_le_activeFineShading
    {F : UniformTubeFamily delta index}
    (S : StickyScaleCover F rho)
    (Y : Shading F.bodyFamily) :
    (parentAggregatedShading S Y).averageMultiplicity <=
      (activeFineShading S Y).averageMultiplicity := by
  unfold Shading.averageMultiplicity
  rw [parentAggregatedShading_shadedUnion S Y]
  exact ENNReal.div_le_div_right
    (parentAggregatedShading_shadingMass_le S Y) _

#print axioms
  StickyScaleCover.parentAggregatedShading_averageMultiplicity_le_activeFineShading

end
end Family8ParentAggregatedAverageMultiplicityMonotonicityV2
