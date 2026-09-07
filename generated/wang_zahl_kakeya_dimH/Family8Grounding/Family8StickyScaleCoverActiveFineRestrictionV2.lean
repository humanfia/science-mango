import Family8Grounding.Family8DoubledParentConflictWeightedActiveFineFrostmanConnectorV2
import FamilyStickyGrounding.FamilyStickyHierarchyEndpointPrefixShadingTransportV1
import Mathlib.Tactic

set_option autoImplicit false
set_option warningAsError true

open Set MeasureTheory
open scoped ENNReal NNReal BigOperators

namespace Family8StickyScaleCoverActiveFineRestrictionV2

open LeanEval.Analysis.WangZahlKakeya
open Submission.Kakeya.ConvexGeometry
open Submission.Kakeya.ConvexFactoring
open Submission.Kakeya.Uniformity
open Family8KatzTaoFrostmanPropertiesV1
open Family8GeneralizedKatzTaoMultiplicityV1
open Family8RestrictedActualDatumDensityRetentionV1
open FamilyStickyAtEveryScaleCoreV1
open FamilyStickyAdjacentScaleStepV2.StickyScaleCover
open FamilyStickyHierarchyEndpointPrefixShadingTransportV1.StickyScaleCover

noncomputable section

/-!
# The honest active-fine source of an interval scale cover

An interval cover generally does not have `activeFine = univ`. Its literal
source is the subtype indexed by `S.activeFine`. This module reindexes the
same cover over that subtype and identifies the restricted actual shading
with the hierarchy's existing `activeFineShading`.

No density lower bound is asserted for an arbitrary refinement: such a
statement is false without retained source mass. The final theorem exposes
the exact retained-mass inequality sufficient when starting from a larger
ambient datum.
-/

namespace ScaleCover

variable {delta rho : NNReal} {index : Type} [Fintype index]
  [DecidableEq index] {fine : UniformTubeFamily delta index}

noncomputable def activeFineRestrictedFamily
    (S : StickyScaleCover fine rho) :
    UniformTubeFamily delta {i // i ∈ S.activeFine} :=
  fine.restrictTo S.activeFine

@[simp]
theorem activeFineRestrictedFamily_tubes
    (S : StickyScaleCover fine rho) (i : {i // i ∈ S.activeFine}) :
    (activeFineRestrictedFamily S).tubes i = fine.tubes i.1 :=
  rfl

/-- The same geometric cover, reindexed so both active sets are literal
universes. -/
noncomputable def activeFineRestrictedScaleCover
    (S : StickyScaleCover fine rho) :
    StickyScaleCover (activeFineRestrictedFamily S) rho := by
  classical
  let e : {k // k ∈ S.activeCoarse} ≃ Fin S.activeCoarse.card :=
    S.activeCoarse.equivFin
  let coarse : UniformTubeFamily rho (Fin S.activeCoarse.card) :=
    { tubes := fun q ↦ S.coarse.tubes (e.symm q).1
      refinement := UniformRefinement.ofFinset Finset.univ }
  exact
    { coarseCard := S.activeCoarse.card
      coarse := coarse
      activeFine := Finset.univ
      activeCoarse := Finset.univ
      parent := fun i ↦ e ⟨S.parent i.1, S.parent_mem i.1 i.2⟩
      activeFine_eq_refined := rfl
      activeCoarse_eq_refined := rfl
      parent_mem := by simp
      parent_surjective := by
        intro q _hq
        have hqActive : (e.symm q).1 ∈ S.activeCoarse := (e.symm q).2
        obtain ⟨i, hiActive, hiParent⟩ :=
          S.parent_surjective (e.symm q).1 hqActive
        let p : {i // i ∈ S.activeFine} := ⟨i, hiActive⟩
        refine ⟨p, Finset.mem_univ p, ?_⟩
        change e ⟨S.parent i, S.parent_mem i hiActive⟩ = q
        have hp :
            (⟨S.parent i, S.parent_mem i hiActive⟩ :
              {k // k ∈ S.activeCoarse}) = e.symm q := by
          apply Subtype.ext
          exact hiParent
        rw [hp, e.apply_symm_apply]
      carrier_subset := by
        intro i _hi
        have hsource := S.carrier_subset i.1 i.2
        change (fine.tubes i.1).carrier ⊆
          (S.coarse.tubes
            (e.symm (e ⟨S.parent i.1, S.parent_mem i.1 i.2⟩)).1).carrier
        rw [e.symm_apply_apply]
        exact hsource }

@[simp]
theorem activeFineRestrictedScaleCover_activeFine
    (S : StickyScaleCover fine rho) :
    (activeFineRestrictedScaleCover S).activeFine = Finset.univ :=
  rfl

@[simp]
theorem activeFineRestrictedScaleCover_activeCoarse
    (S : StickyScaleCover fine rho) :
    (activeFineRestrictedScaleCover S).activeCoarse = Finset.univ :=
  rfl

theorem restrictActualTubeDatum_activeFine_shadingMass_eq
    (D : ActualTubeDatum delta index)
    (S : StickyScaleCover D.family rho) :
    (restrictActualTubeDatum D S.activeFine).shading.shadingMass =
      (activeFineShading S D.shading).shadingMass := by
  rfl

theorem restrictActualTubeDatum_activeFine_shadingDensity_eq
    (D : ActualTubeDatum delta index)
    (S : StickyScaleCover D.family rho) :
    (restrictActualTubeDatum D S.activeFine).shading.shadingDensity =
      (activeFineShading S D.shading).shadingDensity := by
  rfl

theorem restrictActualTubeDatum_activeFine_refined_eq_univ
    (D : ActualTubeDatum delta index)
    (S : StickyScaleCover D.family rho) :
    (restrictActualTubeDatum D S.activeFine).family.refinement.refined =
      Finset.univ :=
  D.family.restrictTo_refined S.activeFine

/-- A hierarchy density bound on `activeFineShading` applies literally to
the actual restricted datum. -/
theorem activeFine_densityLower_to_restrictActualTubeDatum
    {eta : Real} (D : ActualTubeDatum delta index)
    (S : StickyScaleCover D.family rho)
    (hdensity : (delta : ENNReal) ^ eta ≤
      (activeFineShading S D.shading).shadingDensity) :
    (delta : ENNReal) ^ eta ≤
      (restrictActualTubeDatum D S.activeFine).shading.shadingDensity := by
  simpa only [restrictActualTubeDatum_activeFine_shadingDensity_eq D S] using
    hdensity

/-- Minimal honest ambient-to-active density interface. The premise is the
literal mass retained by `S.activeFine`; it cannot be removed for an
arbitrary refinement. -/
theorem source_shadingDensity_div_loss_le_activeFine
    (D : ActualTubeDatum delta index)
    (S : StickyScaleCover D.family rho) (loss : ENNReal)
    (hretained : D.shading.shadingMass ≤
      loss * (activeFineShading S D.shading).shadingMass) :
    D.shading.shadingDensity / loss ≤
      (restrictActualTubeDatum D S.activeFine).shading.shadingDensity := by
  apply source_shadingDensity_div_loss_le_restrictActualTubeDatum
    D S.activeFine loss
  simpa only [restrictActualTubeDatum_activeFine_shadingMass_eq D S] using
    hretained

#print axioms activeFineRestrictedFamily_tubes
#print axioms activeFineRestrictedScaleCover
#print axioms restrictActualTubeDatum_activeFine_shadingMass_eq
#print axioms restrictActualTubeDatum_activeFine_shadingDensity_eq
#print axioms restrictActualTubeDatum_activeFine_refined_eq_univ
#print axioms activeFine_densityLower_to_restrictActualTubeDatum
#print axioms source_shadingDensity_div_loss_le_activeFine

end ScaleCover

end

end Family8StickyScaleCoverActiveFineRestrictionV2
