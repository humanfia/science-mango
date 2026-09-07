import Family8Grounding.Family8ContractedJohnActualTubeProxyV1
import Family8Grounding.Family8Family7NativeHighCriticalScaleProxyGeometryV1
import Family8Grounding.Family8FullCoefficientActualMassCriticalScaleV5
import Family8Grounding.Family8FullCoefficientActualMassProxyGeometryV7
import Family8Grounding.Family8WeightedCanonicalCriticalScaleProxyAverageV2
import Family8Grounding.Family8SelectedParentPlankFineProxyCarrierV3
import FamilyStickyGrounding.FamilyStickyWZ2ProjectionSliceRetentionV1
import FamilyStickyGrounding.FamilyStickyWZ2ShadingPopularityV2
import Mathlib.Tactic

/-!
# Exact average transport for the ten-radius full-coefficient actual-mass proxy, V10

The source shading is the literal active-family restriction of the original
shading to one measurable projected window.  Its mass is exactly the genuine
projected active shading-mass measure.  The exponent-zero full-coefficient
critical ball retains that mass with constant one, and its union is contained
in the source union.  Hence average multiplicity passes losslessly to the
same-object critical-scale proxy.
-/

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 1800000

open Set MeasureTheory
open scoped BigOperators ENNReal NNReal

namespace Family8FullCoefficientActualMassProxyAverageV10

open LeanEval.Analysis.WangZahlKakeya
open Submission.Kakeya.ConvexGeometry
open Family8ActualRestrictedMassWeightedCriticalBallShadingV4
open Family8ContractedJohnActualTubeProxyV1
open Family8Family7NativeHighCriticalScaleProxyGeometryV1
open Family8Family7NativeHighWeightedCriticalBallV1
open Family8FullCoefficientActualMassCriticalScaleV5
open Family8FullCoefficientActualMassProxyGeometryV7
open Family8ProjectedActiveShadingMassMeasureV1
open Family8SelectedParentPlankFineProxyCarrierV3
open Family8WeightedCanonicalCriticalScaleAffineEquivV1
open Family8WeightedCanonicalCriticalScalePositiveV1
open Family8WeightedCanonicalCriticalScaleProxyAverageV2
open Family8WeightedCanonicalCriticalScaleProxyShadingV1
open FamilyStickyCinematicL32WZL3UniformTubeSourceV1
open FamilyStickyWZ2AmbientRestrictedIntegralAdapterV1
open FamilyStickyWZ2ProjectionSliceRetentionV1
open FamilyStickyWZ2ShadingPopularityV2

noncomputable section

universe u

/-- The genuine restricted shading on the literal active-family subtype. -/
def activeRestrictedShading
    {radius : NNReal} {iota : Type u} [Fintype iota] [DecidableEq iota]
    (S : WZL3UniformTubeSource radius iota)
    (Y : Shading S.family.bodyFamily) (active : Finset iota)
    (X : Set Space) (hX : MeasurableSet X) :
    Shading (S.family.restrictTo active).bodyFamily where
  carrier i := Y.carrier i.1 ∩ X
  measurable_carrier i := (Y.measurable_carrier i.1).inter hX
  carrier_subset i := by
    change Y.carrier i.1 ∩ X ⊆ (S.family.tubes i.1).body
    exact inter_subset_left.trans (Y.carrier_subset i.1)

@[simp] theorem activeRestrictedShading_carrier
    {radius : NNReal} {iota : Type u} [Fintype iota] [DecidableEq iota]
    (S : WZL3UniformTubeSource radius iota)
    (Y : Shading S.family.bodyFamily) (active : Finset iota)
    (X : Set Space) (hX : MeasurableSet X)
    (i : {i // i ∈ active}) :
    (activeRestrictedShading S Y active X hX).carrier i =
      Y.carrier i.1 ∩ X :=
  rfl

/-- Its mass is the exact active finite sum of restricted tube masses. -/
theorem activeRestrictedShading_shadingMass
    {radius : NNReal} {iota : Type u} [Fintype iota] [DecidableEq iota]
    (S : WZL3UniformTubeSource radius iota)
    (Y : Shading S.family.bodyFamily) (active : Finset iota)
    (X : Set Space) (hX : MeasurableSet X) :
    (activeRestrictedShading S Y active X hX).shadingMass =
      ∑ i ∈ active, restrictedMass Y X i := by
  unfold Shading.shadingMass
  change (∑ i : {i // i ∈ active}, volume (Y.carrier i.1 ∩ X)) = _
  exact Finset.sum_subtype active (fun _i => Iff.rfl)
    (fun i => volume (Y.carrier i ∩ X)) |>.symm

/-- The critical-ball restricted union is contained in the exact active
source union, not merely in the ambient full-family union. -/
theorem fullCoefficientCriticalBallShading_shadedUnion_subset_activeRestricted
    {radius : NNReal} {iota : Type u} [Fintype iota] [DecidableEq iota]
    (S : WZL3UniformTubeSource radius iota)
    (Y : Shading S.family.bodyFamily)
    (active : Finset iota) (hactive : active.Nonempty)
    (hradius : 0 < radius) (htenRadiusSixteen : 10 * (radius : Real) ≤ 16)
    (X : Set Space) (hX : MeasurableSet X) :
    let W := fullCoefficientActualMassNormData S active hactive
      hradius htenRadiusSixteen Y X
    (weightedCanonicalCriticalBallShading S W
      (restrictedShading Y X hX)).shadedUnion ⊆
        (activeRestrictedShading S Y active X hX).shadedUnion := by
  dsimp only
  let W := fullCoefficientActualMassNormData S active hactive
    hradius htenRadiusSixteen Y X
  intro x hx
  obtain ⟨i, hi⟩ := Set.mem_iUnion.mp hx
  refine Set.mem_iUnion.mpr
    ⟨⟨i.1, W.criticalBall_subset_family i.2⟩, ?_⟩
  exact hi

/-- The full-coefficient critical ball raises the exact active restricted
average multiplicity with constant one. -/
theorem activeRestricted_averageMultiplicity_le_fullCoefficientCriticalBall
    {radius : NNReal} {iota : Type u} [Fintype iota] [DecidableEq iota]
    (S : WZL3UniformTubeSource radius iota)
    (Y : Shading S.family.bodyFamily)
    (active : Finset iota) (hactive : active.Nonempty)
    (f : Real → Real) (hf : Measurable f)
    (E : Set (Real × Real)) (hE : MeasurableSet E)
    (hradius : 0 < radius) (htenRadiusSixteen : 10 * (radius : Real) ≤ 16)
    (hactiveSource : active ⊆ S.source)
    (hcontained : ∀ i, i ∈ active →
      (S.family.tubes i).carrier ⊆ Metric.closedBall (0 : Space) 1) :
    let X := twistedProjection f ⁻¹' E
    let hX : MeasurableSet X := (twistedProjection_measurable f hf) hE
    let W := fullCoefficientActualMassNormData S active hactive
      hradius htenRadiusSixteen Y X
    (activeRestrictedShading S Y active X hX).averageMultiplicity ≤
      (weightedCanonicalCriticalBallShading S W
        (restrictedShading Y X hX)).averageMultiplicity := by
  let X := twistedProjection f ⁻¹' E
  let hX : MeasurableSet X := (twistedProjection_measurable f hf) hE
  let W := fullCoefficientActualMassNormData S active hactive
    hradius htenRadiusSixteen Y X
  have hsourceMass :
      (activeRestrictedShading S Y active X hX).shadingMass =
        projectedActiveShadingMassMeasure Y active f E := by
    rw [activeRestrictedShading_shadingMass]
    symm
    simpa only [X] using
      projectedActiveShadingMassMeasure_apply Y active f hf hE
  have hmass :
      (activeRestrictedShading S Y active X hX).shadingMass ≤
        (weightedCanonicalCriticalBallShading S W
          (restrictedShading Y X hX)).shadingMass := by
    rw [hsourceMass]
    exact projectedActiveShadingMass_le_fullCoefficientCriticalBallShadingMass
      S Y active hactive f hf E hE hradius htenRadiusSixteen
        hactiveSource hcontained
  have hunion :
      (weightedCanonicalCriticalBallShading S W
        (restrictedShading Y X hX)).shadedUnion ⊆
          (activeRestrictedShading S Y active X hX).shadedUnion :=
    fullCoefficientCriticalBallShading_shadedUnion_subset_activeRestricted
      S Y active hactive hradius htenRadiusSixteen X hX
  unfold Shading.averageMultiplicity
  calc
    (activeRestrictedShading S Y active X hX).shadingMass /
        volume (activeRestrictedShading S Y active X hX).shadedUnion ≤
      (weightedCanonicalCriticalBallShading S W
          (restrictedShading Y X hX)).shadingMass /
        volume (activeRestrictedShading S Y active X hX).shadedUnion :=
      ENNReal.div_le_div_right hmass _
    _ ≤ (weightedCanonicalCriticalBallShading S W
          (restrictedShading Y X hX)).shadingMass /
        volume (weightedCanonicalCriticalBallShading S W
          (restrictedShading Y X hX)).shadedUnion :=
      ENNReal.div_le_div_left (measure_mono hunion) _

/-- After the canonical affine normalization, the same exact average
retention holds on the literal round proxy shading. -/
theorem exists_fullCoefficientActualMass_proxyAverageRetention
    {radius : NNReal} {iota : Type}
    [Fintype iota] [DecidableEq iota]
    (S : WZL3UniformTubeSource radius iota)
    (Y : Shading S.family.bodyFamily)
    (active : Finset iota) (hactive : active.Nonempty)
    (f : Real → Real) (hf : Measurable f)
    (E : Set (Real × Real)) (hE : MeasurableSet E)
    (hradius : 0 < radius) (htenRadiusSixteen : 10 * (radius : Real) ≤ 16)
    (hactiveSource : active ⊆ S.source)
    (hcontained : ∀ i, i ∈ active →
      (S.family.tubes i).carrier ⊆ Metric.closedBall (0 : Space) 1) :
    let X := twistedProjection f ⁻¹' E
    let hX : MeasurableSet X := (twistedProjection_measurable f hf) hE
    let W := fullCoefficientActualMassNormData S active hactive
      hradius htenRadiusSixteen Y X
    ∃ (haxis : ∀ i : {i // i ∈ W.criticalBall},
        ‖affineImageAxisVector
          (weightedCanonicalCriticalScaleAffineEquiv S W)
          (S.family.tubes i.1)‖ ≤ 1)
      (htransverse :
        affineLinearOperatorNorm
            (weightedCanonicalCriticalScaleAffineEquiv S W) *
              (radius : Real) ≤
          (criticalScaleProxyRadius radius W.criticalScale
            (weightedCanonicalCriticalScale_pos W) : Real)),
      (activeRestrictedShading S Y active X hX).averageMultiplicity ≤
        (weightedCanonicalCriticalScaleProxyShading S W
          (restrictedShading Y X hX) haxis htransverse).averageMultiplicity := by
  let X := twistedProjection f ⁻¹' E
  let hX : MeasurableSet X := (twistedProjection_measurable f hf) hE
  let W := fullCoefficientActualMassNormData S active hactive
    hradius htenRadiusSixteen Y X
  obtain ⟨haxis, htransverse, _hchart⟩ :=
    exists_fullCoefficientActualMass_proxyGeometry
      S active hactive hradius htenRadiusSixteen Y X hactiveSource
  refine ⟨haxis, htransverse, ?_⟩
  rw [weightedCanonicalCriticalScaleProxyShading_averageMultiplicity]
  exact activeRestricted_averageMultiplicity_le_fullCoefficientCriticalBall
    S Y active hactive f hf E hE hradius htenRadiusSixteen
      hactiveSource hcontained

#print axioms activeRestrictedShading
#print axioms activeRestrictedShading_shadingMass
#print axioms
  fullCoefficientCriticalBallShading_shadedUnion_subset_activeRestricted
#print axioms
  activeRestricted_averageMultiplicity_le_fullCoefficientCriticalBall
#print axioms exists_fullCoefficientActualMass_proxyAverageRetention

end
end Family8FullCoefficientActualMassProxyAverageV10
