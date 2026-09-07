import Family8Grounding.Family8DoubledParentConflictWeightedFrostmanConnectorV2
import Mathlib.Tactic

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 3000000

open Set MeasureTheory
open scoped ENNReal NNReal BigOperators

namespace Family8DoubledParentConflictWeightedActiveFineFrostmanConnectorV2

open LeanEval.Analysis.WangZahlKakeya
open Submission.Kakeya.ConvexGeometry
open Submission.Kakeya.ConvexFactoring
open Submission.Kakeya.ConvexFactoring.InducedShadingDensityAlgebra
open Submission.Kakeya.Uniformity
open Family8KatzTaoFrostmanPropertiesV1
open Family8GeneralizedKatzTaoMultiplicityV1
open Family8RestrictedActualDatumDensityRetentionV1
open Family8FiniteRandomRigidMotionFrostmanConnectorV1
open Family8DoubledParentConflictWeightedRetentionV3.ScaleCover
open Family8DoubledParentConflictWeightedShadingMassBridgeV2.ScaleCover
open Family8DoubledParentConflictWeightedFrostmanConnectorV2.ScaleCover
open FamilyStickyAtEveryScaleCoreV1

noncomputable section

/-!
# The full active-fine restriction to the selected Frostman endpoint

An interval scale cover need not have `activeFine = univ`.  Its honest source
datum is instead the literal restriction to `S.activeFine`.  The selected
fine set is a subset of that source, so its family volume and shaded union
are monotone.  Together with the exact parent-weight mass inequality this
gives density and average-multiplicity retention with the same sharp degree
loss, without any full-activity premise.
-/

namespace ScaleCover

/-- The selected fine indices are contained in the active source indices. -/
theorem weightedSelectedFineIndices_subset_activeFine
    {delta rho : NNReal} {index : Type} [Fintype index]
    [DecidableEq index] (D : ActualTubeDatum delta index)
    {S : StickyScaleCover D.family rho} {B : ENNReal}
    (W : DoubledParentConflictWeightedSelection S
      (parentShadingWeight S D.shading) B) :
    weightedSelectedFineIndices D.shading W ⊆ S.activeFine :=
  Finset.filter_subset _ _

/-- The selected actual-family volume is bounded by the literal active-fine
source restriction. -/
theorem weightedSelected_actualFamilyVolume_le_activeFine
    {delta rho : NNReal} {index : Type} [Fintype index]
    [DecidableEq index] (D : ActualTubeDatum delta index)
    {S : StickyScaleCover D.family rho} {B : ENNReal}
    (W : DoubledParentConflictWeightedSelection S
      (parentShadingWeight S D.shading) B) :
    (restrictActualTubeDatum D
        (weightedSelectedFineIndices D.shading W)).actualFamilyVolume ≤
      (restrictActualTubeDatum D S.activeFine).actualFamilyVolume := by
  rw [restrictActualTubeDatum_actualFamilyVolume,
    restrictActualTubeDatum_actualFamilyVolume]
  exact Finset.sum_le_sum_of_subset
    (weightedSelectedFineIndices_subset_activeFine D W)

/-- The selected shaded union is a literal subset of the active-fine source
shaded union. -/
theorem weightedSelected_shadedUnion_subset_activeFine
    {delta rho : NNReal} {index : Type} [Fintype index]
    [DecidableEq index] (D : ActualTubeDatum delta index)
    {S : StickyScaleCover D.family rho} {B : ENNReal}
    (W : DoubledParentConflictWeightedSelection S
      (parentShadingWeight S D.shading) B) :
    (restrictActualTubeDatum D
        (weightedSelectedFineIndices D.shading W)).shading.shadedUnion ⊆
      (restrictActualTubeDatum D S.activeFine).shading.shadedUnion := by
  intro x hx
  obtain ⟨i, hi⟩ := Set.mem_iUnion.mp hx
  have hiActive : i.1 ∈ S.activeFine :=
    weightedSelectedFineIndices_subset_activeFine D W i.2
  refine Set.mem_iUnion.mpr ⟨⟨i.1, hiActive⟩, ?_⟩
  exact hi

/-- The parent-weight inequality is exactly the mass retention from the
active-fine source restriction to the selected actual datum. -/
theorem activeFine_restrict_shadingMass_le_mul_weightedSelected
    {delta rho : NNReal} {index : Type} [Fintype index]
    [DecidableEq index] (D : ActualTubeDatum delta index)
    {S : StickyScaleCover D.family rho} {B : ENNReal}
    (W : DoubledParentConflictWeightedSelection S
      (parentShadingWeight S D.shading) B) :
    (restrictActualTubeDatum D S.activeFine).shading.shadingMass ≤
      B * (restrictActualTubeDatum D
        (weightedSelectedFineIndices D.shading W)).shading.shadingMass := by
  rw [restrictActualTubeDatum_shadingMass]
  exact activeFine_shadingMass_le_mul_restrict_shadingMass D W

/-- The active-fine source density loses at most the same exact graph-degree
factor on the selected actual datum. -/
theorem activeFine_shadingDensity_div_le_weightedSelected
    {delta rho : NNReal} {index : Type} [Fintype index]
    [DecidableEq index] (D : ActualTubeDatum delta index)
    {S : StickyScaleCover D.family rho} {B : ENNReal}
    (W : DoubledParentConflictWeightedSelection S
      (parentShadingWeight S D.shading) B) :
    (restrictActualTubeDatum D S.activeFine).shading.shadingDensity / B ≤
      (restrictActualTubeDatum D
        (weightedSelectedFineIndices D.shading W)).shading.shadingDensity := by
  let active := restrictActualTubeDatum D S.activeFine
  let selected := restrictActualTubeDatum D
    (weightedSelectedFineIndices D.shading W)
  have hfamily : familyVolume selected.family.bodyFamily ≤
      familyVolume active.family.bodyFamily := by
    simpa only [ActualTubeDatum.actualFamilyVolume] using
      weightedSelected_actualFamilyVolume_le_activeFine D W
  have hmass : active.shading.shadingMass ≤
      B * selected.shading.shadingMass :=
    activeFine_restrict_shadingMass_le_mul_weightedSelected D W
  have hsource : active.shading.shadingDensity ≤
      B * selected.shading.shadingDensity := by
    by_cases hzero : familyVolume active.family.bodyFamily = 0
    · have hmassZero : active.shading.shadingMass = 0 :=
        nonpos_iff_eq_zero.mp
          (active.shading.shadingMass_le_familyVolume.trans_eq hzero)
      simp [Shading.shadingDensity, hzero, hmassZero]
    · rw [← ENNReal.mul_le_mul_iff_right hzero
        (familyVolume_ne_top active.family.bodyFamily)]
      calc
        familyVolume active.family.bodyFamily *
            active.shading.shadingDensity =
            active.shading.shadingMass := by
          rw [mul_comm, shadingDensity_mul_familyVolume]
        _ ≤ B * selected.shading.shadingMass := hmass
        _ = B * (selected.shading.shadingDensity *
            familyVolume selected.family.bodyFamily) := by
          rw [shadingDensity_mul_familyVolume]
        _ ≤ B * (selected.shading.shadingDensity *
            familyVolume active.family.bodyFamily) := by
          gcongr
        _ = familyVolume active.family.bodyFamily *
            (B * selected.shading.shadingDensity) := by
          ac_rfl
  exact ENNReal.div_le_of_le_mul' hsource

/-- Average multiplicity of the honest active-fine source restriction is
retained with exactly the weighted conflict-degree loss. -/
theorem activeFine_averageMultiplicity_le_mul_weightedSelected
    {delta rho : NNReal} {index : Type} [Fintype index]
    [DecidableEq index] (D : ActualTubeDatum delta index)
    {S : StickyScaleCover D.family rho} {B : ENNReal}
    (W : DoubledParentConflictWeightedSelection S
      (parentShadingWeight S D.shading) B) :
    (restrictActualTubeDatum D S.activeFine).shading.averageMultiplicity ≤
      B * (restrictActualTubeDatum D
        (weightedSelectedFineIndices D.shading W)).shading.averageMultiplicity := by
  let active := restrictActualTubeDatum D S.activeFine
  let selected := restrictActualTubeDatum D
    (weightedSelectedFineIndices D.shading W)
  have hmass : active.shading.shadingMass ≤
      B * selected.shading.shadingMass :=
    activeFine_restrict_shadingMass_le_mul_weightedSelected D W
  have hunion : selected.shading.shadedUnion ⊆
      active.shading.shadedUnion :=
    weightedSelected_shadedUnion_subset_activeFine D W
  unfold Shading.averageMultiplicity
  calc
    active.shading.shadingMass / volume active.shading.shadedUnion ≤
        (B * selected.shading.shadingMass) /
          volume active.shading.shadedUnion :=
      ENNReal.div_le_div_right hmass _
    _ ≤ (B * selected.shading.shadingMass) /
          volume selected.shading.shadedUnion :=
      ENNReal.div_le_div_left (measure_mono hunion) _
    _ = B * (selected.shading.shadingMass /
          volume selected.shading.shadedUnion) := by
      simp only [div_eq_mul_inv]
      ac_rfl

/-- Direct Frostman endpoint for an arbitrary interval cover.  It consumes
the active-fine source restriction rather than assuming the interval cover
is full-active. -/
theorem activeFine_averageMultiplicity_le_mul_frostmanRHS_of_weightedSelection
    {beta epsilon eta : Real} {delta0 delta rho : NNReal}
    {index : Type} [Fintype index] [DecidableEq index]
    (hF : FrostmanAtParameters beta epsilon eta delta0)
    (D : ActualTubeDatum delta index) (hD : D.IsAdmissible)
    {S : StickyScaleCover D.family rho} {B C : ENNReal}
    (W : DoubledParentConflictWeightedSelection S
      (parentShadingWeight S D.shading) B)
    (hdelta0 : delta ≤ delta0)
    (hKT : IsKatzTao C D.family.bodyFamily)
    (hdensityBudget : (delta : ENNReal) ^ eta ≤
      (restrictActualTubeDatum D S.activeFine).shading.shadingDensity / B)
    (hbaseBudget : C * volume (unitBallBody : Set Space) ≤
      (delta : ENNReal) ^ (-eta) *
        (restrictActualTubeDatum D
          (weightedSelectedFineIndices D.shading W)).actualFamilyVolume) :
    (restrictActualTubeDatum D S.activeFine).shading.averageMultiplicity ≤
      B * frostmanMultiplicityRHS delta
        (restrictActualTubeDatum D
          (weightedSelectedFineIndices D.shading W)).actualFamilyVolume
        epsilon beta := by
  let active := restrictActualTubeDatum D S.activeFine
  let selected := restrictActualTubeDatum D
    (weightedSelectedFineIndices D.shading W)
  have hadmissible : selected.IsAdmissible :=
    Family8GeneralizedKatzTaoMultiplicityV1.ActualTubeDatum.IsAdmissible.restrictTo
      hD (weightedSelectedFineIndices D.shading W)
  have hselectedDensity : (delta : ENNReal) ^ eta ≤
      selected.shading.shadingDensity :=
    hdensityBudget.trans
      (activeFine_shadingDensity_div_le_weightedSelected D W)
  have hselectedKT : IsKatzTao C selected.family.bodyFamily :=
    restrictActualTubeDatum_weightedSelected_isKatzTao D W hKT
  have hselectedFrostman : FrostmanHypotheses selected eta :=
    frostmanHypotheses_of_density_isKatzTao_base
      selected hadmissible eta C hselectedDensity hselectedKT hbaseBudget
  have hselectedMultiplicity :=
    FrostmanAtParameters.apply hF selected hadmissible hdelta0
      hselectedFrostman
  have hsourceMultiplicity : active.shading.averageMultiplicity ≤
      B * selected.shading.averageMultiplicity :=
    activeFine_averageMultiplicity_le_mul_weightedSelected D W
  exact hsourceMultiplicity.trans
    (mul_le_mul' le_rfl hselectedMultiplicity)

#print axioms weightedSelectedFineIndices_subset_activeFine
#print axioms weightedSelected_actualFamilyVolume_le_activeFine
#print axioms weightedSelected_shadedUnion_subset_activeFine
#print axioms activeFine_restrict_shadingMass_le_mul_weightedSelected
#print axioms activeFine_shadingDensity_div_le_weightedSelected
#print axioms activeFine_averageMultiplicity_le_mul_weightedSelected
#print axioms activeFine_averageMultiplicity_le_mul_frostmanRHS_of_weightedSelection

end ScaleCover
end
end Family8DoubledParentConflictWeightedActiveFineFrostmanConnectorV2
