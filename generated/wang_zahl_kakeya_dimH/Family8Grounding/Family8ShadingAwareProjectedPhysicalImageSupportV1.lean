import Family8Grounding.Family8ShadingAwareProjectedPhysicalV3
import FamilyStickyCinematicL32ProjectedTubeCarrierMeasurabilityV1
import Mathlib.Tactic

/-!
# Image support of the shading-aware projected physical datum

A positive fibre integral supplies an actual point of the corresponding
window-restricted shading carrier.  Since every shading carrier lies in its
source tube, each carrier of the shading-aware projected physical datum is
contained in the exact twisted-projection image of that tube.  This is the
first, measure-theoretic half of the graph-strip support needed by the
measured-low branch.
-/

set_option autoImplicit false
set_option warningAsError true

open Set MeasureTheory
open scoped ENNReal

namespace Family8ShadingAwareProjectedPhysicalImageSupportV1

open LeanEval.Analysis.WangZahlKakeya
open Submission.Kakeya.ConvexGeometry
open Submission.Kakeya.Uniformity
open Family8ShadingAwareProjectedPhysicalV3
open FamilyStickyCinematicL32ProjectedTubeCarrierMeasurabilityV1
open FamilyStickyWZ2ProjectionSliceRetentionV1

noncomputable section

universe u

variable {iota : Type u} {F : ConvexFamily iota}

/-- Positive fibre mass cannot occur without an actual point of that fibre
in the shading carrier. -/
theorem exists_mem_carrier_of_shadingFiberMass_pos
    (Y : Shading F) (f : Real → Real) (i : iota)
    (u : ProjectionSpace) (hpos : 0 < shadingFiberMass Y f i u) :
    ∃ y : Real, twistedFiberChart f (u, y) ∈ Y.carrier i := by
  by_contra hnone
  push Not at hnone
  have hintegrand :
      (fun y : Real =>
        (Y.carrier i).indicator (fun _ => (1 : ENNReal))
          (twistedFiberChart f (u, y))) = fun _ => 0 := by
    funext y
    simp only [Set.indicator_of_notMem (hnone y)]
  unfold shadingFiberMass at hpos
  rw [hintegrand] at hpos
  simp at hpos

/-- Every shading-aware projected carrier is supported in the exact
twisted-projection image of its source tube. -/
theorem shadingAwareProjectedPhysical_carrier_subset_projectedTubeImageCarrier
    {radius : NNReal} [DecidableEq iota]
    (F : UniformTubeFamily radius iota)
    (Y : Shading F.bodyFamily) (active : Finset iota)
    (f : Real → Real) (hf : Measurable f)
    (X : Set ProjectionSpace) (hX : MeasurableSet X)
    (I : Set Real) (hI : MeasurableSet I) (i : iota) :
    (shadingAwareProjectedPhysical Y active f hf X hX I hI).carrier i ⊆
      projectedTubeImageCarrier f (F.tubes i) := by
  intro u hu
  change u ∈ X ∧
    0 < shadingFiberMass
      (shadingWindowRestriction Y f hf X hX I hI) f i u at hu
  obtain ⟨y, hy⟩ := exists_mem_carrier_of_shadingFiberMass_pos
    (shadingWindowRestriction Y f hf X hX I hI) f i u hu.2
  have hyY : twistedFiberChart f (u, y) ∈ Y.carrier i := by
    rw [shadingWindowRestriction, Shading.restrictSet_carrier] at hy
    exact hy.1
  refine ⟨twistedFiberChart f (u, y), Y.carrier_subset i hyY, ?_⟩
  simpa only [projectedTwistedProjection, twistedProjection] using
    (twistedProjection_twistedFiberChart f (u, y))

#print axioms exists_mem_carrier_of_shadingFiberMass_pos
#print axioms
  shadingAwareProjectedPhysical_carrier_subset_projectedTubeImageCarrier

end
end Family8ShadingAwareProjectedPhysicalImageSupportV1
