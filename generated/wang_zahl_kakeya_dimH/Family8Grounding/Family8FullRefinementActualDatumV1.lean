import Family8Grounding.Family8AllFrostmanStickyUnionProducerV1
import Submission.Kakeya.ConvexFactoring.TubeHierarchyInfrastructure

open Set MeasureTheory
open scoped ENNReal NNReal BigOperators

namespace Family8FullRefinementActualDatumV1

open LeanEval.Analysis.WangZahlKakeya
open Submission.Kakeya.ConvexGeometry
open Submission.Kakeya.ConvexFactoring
open Submission.Kakeya.Uniformity
open Family8KatzTaoFrostmanPropertiesV1
open Family8AllFrostmanStickyUnionProducerV1

noncomputable section

set_option autoImplicit false
set_option warningAsError true

/-!
# Replace only the refinement metadata by the full finite family

The analytic properties quantify over the actual tubes and shading; the
uniform-refinement field is bookkeeping used by the later Sticky hierarchy.
This construction keeps every tube and every carrier definitionally unchanged
and installs the loss-one, scale-empty refinement on `Finset.univ`.

It therefore lets the source-to-scale covers see the entire shading, without
assuming that an arbitrary refinement originally stored in the datum already
contains every positive carrier.
-/

variable {delta : NNReal} {iota : Type}
  [Fintype iota] [DecidableEq iota]

/-- The same indexed tube family with full refinement metadata. -/
def fullRefinementFamily (D : ActualTubeDatum delta iota) :
    UniformTubeFamily delta iota where
  tubes := D.family.tubes
  refinement := UniformRefinement.ofFinset Finset.univ

@[simp]
theorem fullRefinementFamily_tubes
    (D : ActualTubeDatum delta iota) (i : iota) :
    (fullRefinementFamily D).tubes i = D.family.tubes i :=
  rfl

@[simp]
theorem fullRefinementFamily_refined
    (D : ActualTubeDatum delta iota) :
    (fullRefinementFamily D).refinement.refined = Finset.univ :=
  rfl

/-- The same actual datum, changing only its uniform-refinement metadata. -/
def fullRefinementDatum (D : ActualTubeDatum delta iota) :
    ActualTubeDatum delta iota where
  family := fullRefinementFamily D
  shading := D.shading

@[simp]
theorem fullRefinementDatum_family_tubes
    (D : ActualTubeDatum delta iota) (i : iota) :
    (fullRefinementDatum D).family.tubes i = D.family.tubes i :=
  rfl

@[simp]
theorem fullRefinementDatum_refined
    (D : ActualTubeDatum delta iota) :
    (fullRefinementDatum D).family.refinement.refined = Finset.univ :=
  rfl

@[simp]
theorem fullRefinementDatum_shading_carrier
    (D : ActualTubeDatum delta iota) (i : iota) :
    (fullRefinementDatum D).shading.carrier i = D.shading.carrier i :=
  rfl

theorem fullRefinementDatum_actualFamilyVolume
    (D : ActualTubeDatum delta iota) :
    (fullRefinementDatum D).actualFamilyVolume = D.actualFamilyVolume :=
  rfl

theorem fullRefinementDatum_shadingMass
    (D : ActualTubeDatum delta iota) :
    (fullRefinementDatum D).shading.shadingMass = D.shading.shadingMass :=
  rfl

theorem fullRefinementDatum_shadedUnion
    (D : ActualTubeDatum delta iota) :
    (fullRefinementDatum D).shading.shadedUnion = D.shading.shadedUnion :=
  rfl

theorem fullRefinementDatum_shadingDensity
    (D : ActualTubeDatum delta iota) :
    (fullRefinementDatum D).shading.shadingDensity =
      D.shading.shadingDensity :=
  rfl

theorem fullRefinementDatum_averageMultiplicity
    (D : ActualTubeDatum delta iota) :
    (fullRefinementDatum D).shading.averageMultiplicity =
      D.shading.averageMultiplicity :=
  rfl

/-- Admissibility is insensitive to the refinement metadata. -/
theorem fullRefinementDatum_isAdmissible
    {D : ActualTubeDatum delta iota} (hD : D.IsAdmissible) :
    (fullRefinementDatum D).IsAdmissible where
  delta_pos := hD.delta_pos
  delta_le_half := hD.delta_le_half
  contained_in_unit_ball := hD.contained_in_unit_ball
  pairwise_essentiallyDistinct := hD.pairwise_essentiallyDistinct

theorem fullRefinementDatum_katzTaoHypotheses_iff
    (D : ActualTubeDatum delta iota) (eta : Real) :
    KatzTaoHypotheses (fullRefinementDatum D) eta ↔
      KatzTaoHypotheses D eta :=
  Iff.rfl

theorem fullRefinementDatum_frostmanHypotheses_iff
    (D : ActualTubeDatum delta iota) (eta : Real) :
    FrostmanHypotheses (fullRefinementDatum D) eta ↔
      FrostmanHypotheses D eta :=
  Iff.rfl

/-- Restricting the unchanged shading to the new refinement loses no mass. -/
theorem fullRefinementDatum_restricted_shadingMass
    (D : ActualTubeDatum delta iota) :
    (IndexedShadingRefinement.restrictTo
      (fullRefinementDatum D).shading
      (fullRefinementDatum D).family.refinement.refined).shading.shadingMass =
        D.shading.shadingMass := by
  rw [fullRefinementDatum_refined, shadingMass_restrictTo_eq_sum]
  rfl

/-- Frostman density makes the full-refinement active source mass nonzero. -/
theorem fullRefinementDatum_restricted_shadingMass_ne_zero_of_frostman
    (D : ActualTubeDatum delta iota) (hD : D.IsAdmissible)
    {eta : Real} (hF : FrostmanHypotheses D eta) :
    (IndexedShadingRefinement.restrictTo
      (fullRefinementDatum D).shading
      (fullRefinementDatum D).family.refinement.refined).shading.shadingMass ≠
        0 := by
  rw [fullRefinementDatum_restricted_shadingMass]
  have hfloor : (delta : ENNReal) ^ (2 * eta) ≤
      D.shading.shadingMass :=
    delta_rpow_two_eta_le_shadingMass_of_frostman D hD hF
  have hpositive : 0 < (delta : ENNReal) ^ (2 * eta) :=
    ENNReal.rpow_pos (ENNReal.coe_pos.mpr hD.delta_pos) ENNReal.coe_ne_top
  exact ne_of_gt (hpositive.trans_le hfloor)

#print axioms fullRefinementDatum_isAdmissible
#print axioms fullRefinementDatum_katzTaoHypotheses_iff
#print axioms fullRefinementDatum_frostmanHypotheses_iff
#print axioms fullRefinementDatum_restricted_shadingMass
#print axioms
  fullRefinementDatum_restricted_shadingMass_ne_zero_of_frostman

end

end Family8FullRefinementActualDatumV1
