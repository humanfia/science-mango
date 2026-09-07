import Family8Grounding.Family8ShadingAwareProjectedPhysicalV3
import Mathlib.Tactic

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 1800000

open Set MeasureTheory
open scoped BigOperators ENNReal

namespace Family8Family7ShadingMassPositiveProjectedActiveRegionV1

open LeanEval.Analysis.WangZahlKakeya
open Submission.Kakeya.ConvexGeometry
open Family8ShadingAwareProjectedPhysicalV3
open FamilyStickyCinematicL32FiniteProjectedShadingMultiplicitySliceV1
open FamilyStickyWZ2AmbientRestrictedIntegralAdapterV1
open FamilyStickyWZ2ProjectionSliceRetentionV1
open FamilyStickyWZ2ShadingPopularityV2

noncomputable section

universe u

/-!
# Positive selected shading mass gives a positive projected active region

The statement uses the literal window-restricted carriers and their actual
active index set.  Tonelli turns their positive total mass into positive
measure of the support of projected multiplicity; on the projected base,
that support is definitionally the nonempty active-pattern region.
-/

theorem restrictedMass_shadingWindowRestriction_projectedBase
    {iota : Type u} {F : ConvexFamily iota}
    (Y : Shading F) (f : Real → Real) (hf : Measurable f)
    (X : Set ProjectionSpace) (hX : MeasurableSet X)
    (I : Set Real) (hI : MeasurableSet I) (i : iota) :
    restrictedMass (shadingWindowRestriction Y f hf X hX I hI)
        (twistedProjection f ⁻¹' X) i =
      volume ((shadingWindowRestriction Y f hf X hX I hI).carrier i) := by
  unfold restrictedMass
  rw [Set.inter_eq_left.mpr]
  intro p hp
  rw [shadingWindowRestriction, Shading.restrictSet_carrier] at hp
  simp only [shadingProjectionWindow, Set.mem_inter_iff,
    Set.mem_preimage] at hp
  exact hp.2.1

theorem positive_projectedActiveRegion_of_activeShadingMass
    {iota : Type u} [Fintype iota] [DecidableEq iota]
    {F : ConvexFamily iota}
    (Y : Shading F) (active : Finset iota)
    (f : Real → Real) (hf : Measurable f)
    (X : Set ProjectionSpace) (hX : MeasurableSet X)
    (I : Set Real) (hI : MeasurableSet I)
    (hmass : 0 < ∑ i ∈ active,
      volume ((shadingWindowRestriction Y f hf X hX I hI).carrier i)) :
    0 < volume
      {u | u ∈ (shadingAwareProjectedPhysical
          Y active f hf X hX I hI).base ∧
        ((shadingAwareProjectedPhysical
          Y active f hf X hX I hI).activeAtPoint u).Nonempty} := by
  classical
  let Yw := shadingWindowRestriction Y f hf X hX I hI
  let Z := shadingAwareProjectedPhysical Y active f hf X hX I hI
  let g : ProjectionSpace → ENNReal := fun u =>
    projectedActiveMultiplicity Yw active f u
  have hg : Measurable g := by
    have hsum : Measurable fun u : ProjectionSpace =>
        ∑ i ∈ active, shadingFiberMass Yw f i u := by
      refine Finset.measurable_fun_sum active fun i _hi => ?_
      exact measurable_shadingFiberMass Yw f hf i
    simpa only [g, projectedActiveMultiplicity_eq_sum_shadingFiberMass
      Yw active f hf] using hsum
  have hintegral : 0 < ∫⁻ u in X, g u
      ∂(volume : Measure ProjectionSpace) := by
    rw [lintegral_projectedActiveMultiplicity_eq_sum_restrictedMass
      Yw active f hf X]
    simpa only [g, Yw,
      restrictedMass_shadingWindowRestriction_projectedBase] using hmass
  have hsupport : Function.support g ∩ X =
      {u | u ∈ Z.base ∧ (Z.activeAtPoint u).Nonempty} := by
    ext u
    simp only [Function.mem_support, ne_eq, Set.mem_inter_iff,
      Set.mem_ofPred_eq]
    change (g u ≠ 0 ∧ u ∈ X) ↔
      (u ∈ X ∧ (Z.activeAtPoint u).Nonempty)
    constructor
    · rintro ⟨hgu, huX⟩
      have hsumPos : 0 < ∑ i ∈ active,
          shadingFiberMass Yw f i u := by
        rw [← projectedActiveMultiplicity_eq_sum_shadingFiberMass
          Yw active f hf u]
        exact pos_iff_ne_zero.mpr hgu
      obtain ⟨i, hi, himass⟩ := Finset.sum_pos_iff.mp hsumPos
      refine ⟨huX, ⟨i, ?_⟩⟩
      exact (mem_activeAtPoint_shadingAwareProjectedPhysical
        Y active f hf X hX I hI u i).mpr ⟨hi, huX, himass⟩
    · rintro ⟨huX, ⟨i, hi⟩⟩
      have hidata := (mem_activeAtPoint_shadingAwareProjectedPhysical
        Y active f hf X hX I hI u i).mp hi
      refine ⟨?_, huX⟩
      apply ne_of_gt
      change 0 < projectedActiveMultiplicity Yw active f u
      rw [projectedActiveMultiplicity_eq_sum_shadingFiberMass
        Yw active f hf u, Finset.sum_pos_iff]
      exact ⟨i, hidata.1, hidata.2.2⟩
  have hsupportPos : 0 < volume (Function.support g ∩ X) :=
    (setLIntegral_pos_iff hg).mp hintegral
  simpa only [Z, hsupport] using hsupportPos

#print axioms restrictedMass_shadingWindowRestriction_projectedBase
#print axioms positive_projectedActiveRegion_of_activeShadingMass

end

end Family8Family7ShadingMassPositiveProjectedActiveRegionV1
