import FamilyStickyGrounding.FamilyStickyWZ2AmbientRestrictedIntegralAdapterV1
import Mathlib.MeasureTheory.Measure.WithDensity

/-!
# Projected active shading mass as an actual measure

The projected active multiplicity is the fibre integral of the literal
three-dimensional shading multiplicity.  Using it as a density on projection
space packages the exact Tonelli identity into a measure.  This lets the
existing arbitrary-measure all-centre selection retain genuine shading mass,
rather than only planar area or a qualitative positive fibre floor.
-/

set_option autoImplicit false
set_option warningAsError true

open Set MeasureTheory
open scoped BigOperators ENNReal

namespace Family8ProjectedActiveShadingMassMeasureV1

open LeanEval.Analysis.WangZahlKakeya
open Submission.Kakeya.ConvexGeometry
open FamilyStickyWZ2AmbientRestrictedIntegralAdapterV1
open FamilyStickyWZ2ProjectionSliceRetentionV1
open FamilyStickyWZ2ShadingPopularityV2

noncomputable section

universe u

variable {iota : Type u} {F : ConvexFamily iota}

/-- The genuine projected mass measure of a finite active part of a shading. -/
noncomputable def projectedActiveShadingMassMeasure
    (Y : Shading F) (active : Finset iota)
    (f : Real → Real) : Measure ProjectionSpace :=
  (volume : Measure ProjectionSpace).withDensity
    (projectedActiveMultiplicity Y active f)

/-- On every measurable projected set, the new measure is exactly the sum of
the corresponding restricted three-dimensional shading masses. -/
theorem projectedActiveShadingMassMeasure_apply
    (Y : Shading F) (active : Finset iota)
    (f : Real → Real) (hf : Measurable f)
    {X : Set ProjectionSpace} (hX : MeasurableSet X) :
    projectedActiveShadingMassMeasure Y active f X =
      ∑ i ∈ active,
        restrictedMass Y (twistedProjection f ⁻¹' X) i := by
  rw [projectedActiveShadingMassMeasure,
    MeasureTheory.withDensity_apply _ hX]
  exact lintegral_projectedActiveMultiplicity_eq_sum_restrictedMass
    Y active f hf X

/-- With every index active, the total projected mass is the literal shading
mass.  No fibre lower bound or dyadic truncation is used. -/
theorem projectedFullShadingMassMeasure_univ
    [Fintype iota]
    (Y : Shading F) (f : Real → Real) (hf : Measurable f) :
    projectedActiveShadingMassMeasure Y Finset.univ f Set.univ =
      Y.shadingMass := by
  rw [projectedActiveShadingMassMeasure_apply Y Finset.univ f hf
    MeasurableSet.univ]
  simp only [restrictedMass, preimage_univ, inter_univ,
    Shading.shadingMass]

#print axioms projectedActiveShadingMassMeasure
#print axioms projectedActiveShadingMassMeasure_apply
#print axioms projectedFullShadingMassMeasure_univ

end
end Family8ProjectedActiveShadingMassMeasureV1
