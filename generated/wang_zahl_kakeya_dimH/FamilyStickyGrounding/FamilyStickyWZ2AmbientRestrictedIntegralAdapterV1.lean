import FamilyStickyGrounding.FamilyStickyWZ2TwistedFiberVolumeV1

set_option autoImplicit false

open scoped BigOperators ENNReal
open MeasureTheory

namespace FamilyStickyWZ2AmbientRestrictedIntegralAdapterV1

open FamilyStickyWZ2ProjectionSliceRetentionV1
open FamilyStickyWZ2ShadingPopularityV2
open FamilyStickyWZ2TwistedFiberVolumeV1
open Submission.Kakeya.ConvexGeometry
open LeanEval.Analysis.WangZahlKakeya

noncomputable section

/-!
# WZ2 ambient restricted-integral adapter

This module closes the change-of-variables gap between the tracked WZ2
slice-Tonelli producer and the tracked volume-preserving twisted fiber chart.
It proves that integrating fiber multiplicity over a restricted projection
set is exactly the ambient restricted integral over its twisted-projection
preimage.  The final specializations use the actual finite `Shading`
multiplicity and its independently proved finite double count.

No projection estimate, integral lower bound, or popularity conclusion is
assumed as a callback.
-/

/-- A measurable slope gives a measurable twisted projection. -/
theorem twistedProjection_measurable
    (f : Real -> Real) (hf : Measurable f) :
    Measurable (twistedProjection f) := by
  unfold twistedProjection
  fun_prop

/-- The inverse coordinates of the twisted fiber chart are measurable. -/
theorem twistedFiberCoordinates_measurable
    (f : Real -> Real) (hf : Measurable f) :
    Measurable (twistedFiberCoordinates f) := by
  unfold twistedFiberCoordinates
  exact (twistedProjection_measurable f hf).prodMk (by fun_prop)

/-- The algebraic twisted-fiber equivalence as a measurable equivalence. -/
def twistedFiberMeasurableEquiv
    (f : Real -> Real) (hf : Measurable f) :
    ProjectionSpace × Real ≃ᵐ Space where
  toEquiv := (twistedFiberEquiv f).symm
  measurable_toFun := (twistedFiberChart_measurePreserving f hf).measurable
  measurable_invFun := twistedFiberCoordinates_measurable f hf

@[simp] theorem twistedFiberMeasurableEquiv_apply
    (f : Real -> Real) (hf : Measurable f)
    (q : ProjectionSpace × Real) :
    twistedFiberMeasurableEquiv f hf q = twistedFiberChart f q := rfl

/-- Change variables from the product fiber chart to an ambient restricted
integral over a twisted-projection preimage. -/
theorem lintegral_twistedFiberChart_product_preimage
    (f : Real -> Real) (hf : Measurable f)
    (multiplicity : Space -> ENNReal) (X : Set ProjectionSpace) :
    (∫⁻ q in X ×ˢ (Set.univ : Set Real),
        multiplicity (twistedFiberChart f q)
          ∂((volume : Measure ProjectionSpace).prod
            (volume : Measure Real))) =
      ∫⁻ p in twistedProjection f ⁻¹' X,
        multiplicity p ∂volume := by
  have h :=
    (twistedFiberChart_measurePreserving f hf).setLIntegral_comp_preimage_emb
      (twistedFiberMeasurableEquiv f hf).measurableEmbedding
      multiplicity (twistedProjection f ⁻¹' X)
  rw [twistedFiberChart_preimage_twistedProjection_preimage] at h
  simpa only [Measure.volume_eq_prod] using h

/-- The missing WZ2 adapter: the restricted integral of projected fiber
multiplicity is exactly the ambient restricted integral on the corresponding
twisted-projection preimage. -/
theorem lintegral_projectedSlice_eq_ambient_restrict
    (f : Real -> Real) (hf : Measurable f)
    (multiplicity : Space -> ENNReal) (hmultiplicity : Measurable multiplicity)
    (X : Set ProjectionSpace) :
    (∫⁻ u in X,
        projectedSliceMultiplicity (volume : Measure Real)
          (fun r => multiplicity (twistedFiberChart f r)) u
          ∂(volume : Measure ProjectionSpace)) =
      ∫⁻ p in twistedProjection f ⁻¹' X,
        multiplicity p ∂volume := by
  calc
    (∫⁻ u in X,
        projectedSliceMultiplicity (volume : Measure Real)
          (fun r => multiplicity (twistedFiberChart f r)) u
          ∂(volume : Measure ProjectionSpace)) =
        ∫⁻ r in X ×ˢ (Set.univ : Set Real),
          multiplicity (twistedFiberChart f r)
            ∂((volume : Measure ProjectionSpace).prod
              (volume : Measure Real)) :=
      lintegral_projectedSliceMultiplicity_restrict
        (volume : Measure Real) (volume : Measure ProjectionSpace)
        (fun r => multiplicity (twistedFiberChart f r)) X
        (hmultiplicity.comp
          (twistedFiberChart_measurePreserving f hf).measurable)
    _ = ∫⁻ p in twistedProjection f ⁻¹' X,
          multiplicity p ∂volume :=
      lintegral_twistedFiberChart_product_preimage f hf multiplicity X

variable {iota : Type*} {F : ConvexFamily iota}

/-- The ENNReal-valued active shading multiplicity is measurable. -/
theorem activePointMultiplicity_cast_measurable
    (Y : Shading F) (active : Finset iota) :
    Measurable fun p : Space =>
      (activePointMultiplicity Y active p : ENNReal) := by
  classical
  simp_rw [activePointMultiplicity_cast_eq_sum_indicator]
  refine Finset.measurable_fun_sum active fun i _hi => ?_
  exact measurable_const.indicator (Y.measurable_carrier i)

/-- Projected fiber multiplicity of an actual finite active shading. -/
noncomputable def projectedActiveMultiplicity
    (Y : Shading F) (active : Finset iota)
    (f : Real -> Real) (u : ProjectionSpace) : ENNReal :=
  projectedSliceMultiplicity (volume : Measure Real)
    (fun r =>
      (activePointMultiplicity Y active
        (twistedFiberChart f r) : ENNReal)) u

/-- Actual-shading specialization of the ambient restricted-integral
adapter. -/
theorem lintegral_projectedActiveMultiplicity_eq_ambient_restrict
    (Y : Shading F) (active : Finset iota)
    (f : Real -> Real) (hf : Measurable f)
    (X : Set ProjectionSpace) :
    (∫⁻ u in X, projectedActiveMultiplicity Y active f u
        ∂(volume : Measure ProjectionSpace)) =
      ∫⁻ p in twistedProjection f ⁻¹' X,
        (activePointMultiplicity Y active p : ENNReal) ∂volume := by
  exact lintegral_projectedSlice_eq_ambient_restrict
    f hf (fun p => (activePointMultiplicity Y active p : ENNReal))
    (activePointMultiplicity_cast_measurable Y active) X

/-- Combining change of variables with the tracked finite double count gives
the exact sum of actual restricted shading masses. -/
theorem lintegral_projectedActiveMultiplicity_eq_sum_restrictedMass
    (Y : Shading F) (active : Finset iota)
    (f : Real -> Real) (hf : Measurable f)
    (X : Set ProjectionSpace) :
    (∫⁻ u in X, projectedActiveMultiplicity Y active f u
        ∂(volume : Measure ProjectionSpace)) =
      ∑ i ∈ active,
        restrictedMass Y (twistedProjection f ⁻¹' X) i := by
  calc
    (∫⁻ u in X, projectedActiveMultiplicity Y active f u
        ∂(volume : Measure ProjectionSpace)) =
        ∫⁻ p in twistedProjection f ⁻¹' X,
          (activePointMultiplicity Y active p : ENNReal) ∂volume :=
      lintegral_projectedActiveMultiplicity_eq_ambient_restrict
        Y active f hf X
    _ = ∑ i ∈ active,
          restrictedMass Y (twistedProjection f ⁻¹' X) i :=
      lintegral_activePointMultiplicity_restrict
        Y active (twistedProjection f ⁻¹' X)

/-- Real-valued form of the exact projected-slice/ambient double count. -/
theorem sum_restrictedMassReal_eq_projectedActiveMultiplicity_toReal
    (Y : Shading F) (active : Finset iota)
    (f : Real -> Real) (hf : Measurable f)
    (X : Set ProjectionSpace) :
    (∑ i ∈ active,
        restrictedMassReal Y (twistedProjection f ⁻¹' X) i) =
      (∫⁻ u in X, projectedActiveMultiplicity Y active f u
        ∂(volume : Measure ProjectionSpace)).toReal := by
  rw [sum_restrictedMassReal_eq_lintegral_toReal]
  congr 1
  exact (lintegral_projectedActiveMultiplicity_eq_ambient_restrict
    Y active f hf X).symm

/-- A projected-slice integral lower bound now feeds the already grounded
finite popularity theorem on the literal ambient preimage. -/
theorem half_density_card_le_popularRestricted_card_of_projectedSlice
    (Y : Shading F) (active : Finset iota)
    (f : Real -> Real) (hf : Measurable f)
    (X : Set ProjectionSpace)
    (alpha cap : Real) (halpha0 : 0 <= alpha) (hcap0 : 0 < cap)
    (hcarrierCap : forall i, i ∈ active ->
      (volume (Y.carrier i)).toReal <= cap)
    (hmass : alpha * active.card * cap <=
      (∫⁻ u in X, projectedActiveMultiplicity Y active f u
        ∂(volume : Measure ProjectionSpace)).toReal) :
    alpha / 2 * active.card <=
      (popularRestrictedIndices Y active
        (twistedProjection f ⁻¹' X) alpha cap).card := by
  apply half_density_card_le_popularRestricted_card_of_lintegral
    Y active (twistedProjection f ⁻¹' X) alpha cap
    halpha0 hcap0 hcarrierCap
  rw [← lintegral_projectedActiveMultiplicity_eq_ambient_restrict
    Y active f hf X]
  exact hmass

#print axioms lintegral_twistedFiberChart_product_preimage
#print axioms lintegral_projectedSlice_eq_ambient_restrict
#print axioms activePointMultiplicity_cast_measurable
#print axioms lintegral_projectedActiveMultiplicity_eq_ambient_restrict
#print axioms lintegral_projectedActiveMultiplicity_eq_sum_restrictedMass
#print axioms sum_restrictedMassReal_eq_projectedActiveMultiplicity_toReal
#print axioms half_density_card_le_popularRestricted_card_of_projectedSlice

end

end FamilyStickyWZ2AmbientRestrictedIntegralAdapterV1
