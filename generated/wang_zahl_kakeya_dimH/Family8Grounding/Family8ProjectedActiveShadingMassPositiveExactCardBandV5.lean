import Family8Grounding.Family8Family7FiniteProjectedPositiveExactCardBandV1
import Family8Grounding.Family8Family7ShadingMassPositiveProjectedActiveRegionV1
import Family8Grounding.Family8ProjectedActiveShadingMassMeasureV1
import Mathlib.Tactic

/-!
# A positive exact-card band for projected shading mass, V5

This clean successor uses an explicit semicolon proof for the measurable
nonempty-active region, avoiding the strict unnecessary-sequence linter.
Failed predecessors are not imported.
-/

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 2000000

open Set MeasureTheory
open scoped BigOperators ENNReal

namespace Family8ProjectedActiveShadingMassPositiveExactCardBandV5

open LeanEval.Analysis.WangZahlKakeya
open Submission.Kakeya.ConvexGeometry
open Family8Family7FiniteProjectedPositiveExactCardBandV1
open Family8Family7ShadingMassPositiveProjectedActiveRegionV1
open Family8ProjectedActiveShadingMassMeasureV1
open Family8ShadingAwareProjectedPhysicalV3
open FamilyStickyCinematicL32FiniteProjectedShadingMultiplicitySliceV1
open FamilyStickyWZ2AmbientRestrictedIntegralAdapterV1
open FamilyStickyWZ2ProjectionSliceRetentionV1

noncomputable section

universe u

/-- Positive literal mass in a shading window gives positive mass to the
nonempty active-pattern region for the projected shading-mass measure. -/
theorem positive_projectedActiveShadingMassMeasure_activeRegion
    {iota : Type u} [Fintype iota] [DecidableEq iota]
    {F : ConvexFamily iota}
    (Y : Shading F) (active : Finset iota)
    (f : Real → Real) (hf : Measurable f)
    (X : Set ProjectionSpace) (hX : MeasurableSet X)
    (I : Set Real) (hI : MeasurableSet I)
    (hmass : 0 < ∑ i ∈ active,
      volume ((shadingWindowRestriction Y f hf X hX I hI).carrier i)) :
    0 < projectedActiveShadingMassMeasure
      (shadingWindowRestriction Y f hf X hX I hI) active f
      {u | u ∈ (shadingAwareProjectedPhysical
          Y active f hf X hX I hI).base ∧
        ((shadingAwareProjectedPhysical
          Y active f hf X hX I hI).activeAtPoint u).Nonempty} := by
  classical
  let Yw := shadingWindowRestriction Y f hf X hX I hI
  let Z := shadingAwareProjectedPhysical Y active f hf X hX I hI
  let g : ProjectionSpace → ENNReal := fun u =>
    projectedActiveMultiplicity Yw active f u
  let R : Set ProjectionSpace :=
    {u | u ∈ Z.base ∧ (Z.activeAtPoint u).Nonempty}
  have hg : Measurable g := by
    have hsum : Measurable fun u : ProjectionSpace =>
        ∑ i ∈ active, shadingFiberMass Yw f i u := by
      refine Finset.measurable_fun_sum active fun i _hi => ?_
      exact measurable_shadingFiberMass Yw f hf i
    simpa only [g, projectedActiveMultiplicity_eq_sum_shadingFiberMass
      Yw active f hf] using hsum
  have hcardMeasurable : Measurable fun u : ProjectionSpace =>
      (Z.activeAtPoint u).card :=
    Z.measurable_activeValue fun s => s.card
  have hnonemptyMeasurable :
      MeasurableSet {u : ProjectionSpace | (Z.activeAtPoint u).Nonempty} := by
    have hpreimage := hcardMeasurable
      (Set.to_countable {n : Nat | 1 ≤ n}).measurableSet
    convert hpreimage using 1
    ext u
    simp [Finset.one_le_card]
  have hR : MeasurableSet R := by
    exact Z.measurable_base.inter hnonemptyMeasurable
  have hvolR : 0 < volume R := by
    simpa only [R, Z, Yw] using
      positive_projectedActiveRegion_of_activeShadingMass
        Y active f hf X hX I hI hmass
  have hRSupport : R ⊆ Function.support g := by
    intro u hu
    obtain ⟨huX, i, hi⟩ := hu
    have hidata := (mem_activeAtPoint_shadingAwareProjectedPhysical
      Y active f hf X hX I hI u i).mp hi
    apply ne_of_gt
    change 0 < projectedActiveMultiplicity Yw active f u
    rw [projectedActiveMultiplicity_eq_sum_shadingFiberMass
      Yw active f hf u, Finset.sum_pos_iff]
    exact ⟨i, hidata.1, hidata.2.2⟩
  have hsupportInter : Function.support g ∩ R = R := by
    exact Set.inter_eq_right.mpr hRSupport
  have hweightedPos : 0 < ∫⁻ u in R, g u
      ∂(volume : Measure ProjectionSpace) := by
    rw [setLIntegral_pos_iff hg, hsupportInter]
    exact hvolR
  change 0 < (volume.withDensity g) R
  rw [MeasureTheory.withDensity_apply _ hR]
  exact hweightedPos

/-- The finite active-card pigeonhole can therefore be run using genuine
projected shading mass instead of planar volume. -/
theorem exists_positive_exactCard_projectedActiveShadingMassBand
    {iota : Type u} [Fintype iota] [DecidableEq iota]
    {F : ConvexFamily iota}
    (Y : Shading F) (active : Finset iota)
    (f : Real → Real) (hf : Measurable f)
    (X : Set ProjectionSpace) (hX : MeasurableSet X)
    (I : Set Real) (hI : MeasurableSet I)
    (hmass : 0 < ∑ i ∈ active,
      volume ((shadingWindowRestriction Y f hf X hX I hI).carrier i)) :
    let Yw := shadingWindowRestriction Y f hf X hX I hI
    let Z := shadingAwareProjectedPhysical Y active f hf X hX I hI
    ∃ n : Nat, 1 ≤ n ∧ n ≤ Z.ambient.card ∧
      0 < projectedActiveShadingMassMeasure Yw active f
        (Z.multiplicityBand n n) := by
  dsimp only
  exact exists_positive_exactCard_multiplicityBand
    (projectedActiveShadingMassMeasure
      (shadingWindowRestriction Y f hf X hX I hI) active f)
    (shadingAwareProjectedPhysical Y active f hf X hX I hI)
    (positive_projectedActiveShadingMassMeasure_activeRegion
      Y active f hf X hX I hI hmass)

#print axioms positive_projectedActiveShadingMassMeasure_activeRegion
#print axioms exists_positive_exactCard_projectedActiveShadingMassBand

end
end Family8ProjectedActiveShadingMassPositiveExactCardBandV5
