import FamilyStickyGrounding.FamilyStickyHierarchyWZ2TranslatedCollisionCellPopularFloorUnionV1

set_option autoImplicit false
set_option warningAsError true

open Set MeasureTheory
open scoped BigOperators ENNReal

namespace FamilyStickyWZ2ProjectedShadedUnionMassV1

open LeanEval.Analysis.WangZahlKakeya
open Submission.Kakeya.ConvexGeometry
open FamilyStickyWZ2ShadingPopularityV2
open FamilyStickyWZ2ProjectionSliceRetentionV1
open FamilyStickyWZ2AmbientRestrictedIntegralAdapterV1
open FamilyStickyHierarchyWZ2TranslatedCollisionCellPopularFloorUnionV1

noncomputable section

/-!
# Full shading mass on its projected shaded union

Restrict the twisted-projection multiplicity to the literal projection of
the full shaded union.  Every shading carrier is then contained in the
ambient preimage of that projection, so every restricted carrier mass is its
full mass.  The projected restricted integral is consequently exactly the
source shading mass.  This supplies the natural callback-free restricted-
integral instance for the WZ2 popularity endpoint.
-/

variable {iota : Type*} {F : ConvexFamily iota}

/-- Every shaded carrier lies over the projection of the full shaded union. -/
theorem carrier_subset_twistedProjection_preimage_projectedShadedUnion
    (Y : Shading F) (f : Real → Real) (i : iota) :
    Y.carrier i ⊆
      twistedProjection f ⁻¹' (twistedProjection f '' Y.shadedUnion) := by
  intro p hp
  exact ⟨p, Set.mem_iUnion.mpr ⟨i, hp⟩, rfl⟩

/-- Restriction to the preimage of the projected shaded union loses no mass
from any source carrier. -/
theorem restrictedMass_projectedShadedUnion
    (Y : Shading F) (f : Real → Real) (i : iota) :
    restrictedMass Y
        (twistedProjection f ⁻¹' (twistedProjection f '' Y.shadedUnion)) i =
      volume (Y.carrier i) := by
  unfold restrictedMass
  rw [Set.inter_eq_left.mpr]
  exact carrier_subset_twistedProjection_preimage_projectedShadedUnion Y f i

/-- Summing the restricted masses over every index gives exactly the full
source shading mass. -/
theorem sum_restrictedMass_projectedShadedUnion_eq_shadingMass
    [Fintype iota]
    (Y : Shading F) (f : Real → Real) :
    (∑ i ∈ (Finset.univ : Finset iota),
        restrictedMass Y
          (twistedProjection f ⁻¹' (twistedProjection f '' Y.shadedUnion)) i) =
      Y.shadingMass := by
  simp only [restrictedMass_projectedShadedUnion]
  rfl

/-- The projected multiplicity integral over the literal projected shaded
union is the complete shading mass. -/
theorem lintegral_projectedActiveMultiplicity_projectedShadedUnion_eq_shadingMass
    [Fintype iota]
    (Y : Shading F) (f : Real → Real) (hf : Measurable f) :
    (∫⁻ u in twistedProjection f '' Y.shadedUnion,
        projectedActiveMultiplicity Y (Finset.univ : Finset iota) f u
          ∂(volume : Measure ProjectionSpace)) =
      Y.shadingMass := by
  rw [lintegral_projectedActiveMultiplicity_eq_sum_restrictedMass
    Y (Finset.univ : Finset iota) f hf
      (twistedProjection f '' Y.shadedUnion)]
  exact sum_restrictedMass_projectedShadedUnion_eq_shadingMass Y f

/-- Real-valued producer in precisely the form consumed by projected-slice
popularity.  Its sole numerical input is the transparent source shading-mass
bound. -/
theorem projectedShadedUnion_massLower
    [Fintype iota]
    (Y : Shading F) (f : Real → Real) (hf : Measurable f)
    (alpha cap : Real)
    (hmass : alpha * Fintype.card iota * cap ≤ Y.shadingMass.toReal) :
    alpha * (Finset.univ : Finset iota).card * cap ≤
      (∫⁻ u in twistedProjection f '' Y.shadedUnion,
        projectedActiveMultiplicity Y (Finset.univ : Finset iota) f u
          ∂(volume : Measure ProjectionSpace)).toReal := by
  rw [lintegral_projectedActiveMultiplicity_projectedShadedUnion_eq_shadingMass
    Y f hf]
  simpa using hmass

#print axioms carrier_subset_twistedProjection_preimage_projectedShadedUnion
#print axioms restrictedMass_projectedShadedUnion
#print axioms sum_restrictedMass_projectedShadedUnion_eq_shadingMass
#print axioms lintegral_projectedActiveMultiplicity_projectedShadedUnion_eq_shadingMass
#print axioms projectedShadedUnion_massLower

end

end FamilyStickyWZ2ProjectedShadedUnionMassV1
