import Family8Grounding.Family8Family7NativeHighFirstHitCriticalBallOwnerEventV1
import Family8Grounding.Family8ShadingAwareProjectedPhysicalV3
import Mathlib.Tactic

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 3000000

open Set MeasureTheory
open scoped BigOperators ENNReal NNReal

namespace Family8Family7CriticalOwnerEventFiberMassLiftV3

open LeanEval.Analysis.WangZahlKakeya
open Submission.Kakeya.ConvexGeometry
open Family8Family7NativeHighFirstHitCriticalBallOwnerEventV1
open Family8Family7NativeHighFirstHitCriticalBallOwnerEventV1.ActualGPrimeE2FirstHitOwnerData
open Family8ShadingAwareProjectedPhysicalV3
open FamilyStickyCinematicL32FiniteProjectedPositiveMultiplicityDyadicV1
open FamilyStickyCinematicL32Lemma55E2FineRectangleFirstHitY2V1
open FamilyStickyCinematicL32Prop41ActualGPrimeLabelFirstFineSeparatedPairMassProducerV1
open FamilyStickyCinematicL32Prop41CoarseRectangleIncidenceDataV1
open FamilyStickyCinematicL32Prop41CanonicalMaximizerNonconcentrationV1
open FamilyStickyWZ2AmbientRestrictedIntegralAdapterV1
open FamilyStickyWZ2ProjectionSliceRetentionV1
open FamilyStickyWZ2ShadingPopularityV2

noncomputable section

universe u v

/-!
# Lift a first-hit owner event to literal three-dimensional shading mass

V1 and V2 were namespace drafts and are not imported.  This ADD-only
successor proves the exact Tonelli handoff needed after an upstream
heavy-fibre, pattern-first construction.

If every point of a first-hit piece sees its chosen owner with one-dimensional
shading fibre mass at least `fibreFloor`, then the area of the selected owner
event, multiplied by that floor, is bounded by the original three-dimensional
shading mass carried by the same weighted critical ball.
-/

variable {radius : NNReal} {iota : Type u} [DecidableEq iota]
variable {fineLabel : Type v} [DecidableEq fineLabel]
variable {N : CanonicalNormNonconcentrationData iota}
variable {D : CoarseRectangleIncidenceData (point := Real × Real)
  (radius := radius) (iota := iota) fineLabel}
variable {label : Int}
variable {F : ConvexFamily iota}

theorem fibreFloor_mul_volume_criticalOwnerEvent_le_ballShadingMass
    (P : ActualGPrimeE2FirstHitOwnerData N D label)
    (Y : Shading F) (f : Real → Real) (hf : Measurable f)
    (fibreFloor : ENNReal)
    (hfloor : ∀ r, r ∈ D.fineLabels → ∀ u,
      u ∈ firstHitFineRectangleY2
        (projectedPositiveMultiplicityDyadicCell D.shading label)
        D.fineLabels D.fineRectangleAt (radius : Real) r →
      fibreFloor ≤ shadingFiberMass Y f (P.owner r) u) :
    fibreFloor * volume P.criticalOwnerEvent ≤
      ∑ i ∈ P.weightedNormData.criticalBall, volume (Y.carrier i) := by
  classical
  have hpoint : ∀ u, u ∈ P.criticalOwnerEvent →
      fibreFloor ≤ projectedActiveMultiplicity Y
        P.weightedNormData.criticalBall f u := by
    intro u hu
    obtain ⟨r, hr, hur, hdistance⟩ :=
      P.mem_criticalOwnerEvent_owner_distance_to_center hu
    have hownerBall : P.owner r ∈ P.weightedNormData.criticalBall := by
      exact Finset.mem_filter.mpr ⟨P.owner_mem_family hr, hdistance⟩
    rw [projectedActiveMultiplicity_eq_sum_shadingFiberMass
      Y P.weightedNormData.criticalBall f hf u]
    exact (hfloor r hr u hur).trans
      (Finset.single_le_sum
        (fun _ _ => show (0 : ENNReal) ≤ _ from bot_le) hownerBall)
  calc
    fibreFloor * volume P.criticalOwnerEvent =
        ∫⁻ _u in P.criticalOwnerEvent, fibreFloor
          ∂(volume : Measure (Real × Real)) := by
      rw [setLIntegral_const]
    _ ≤ ∫⁻ u in P.criticalOwnerEvent,
        projectedActiveMultiplicity Y P.weightedNormData.criticalBall f u
          ∂(volume : Measure (Real × Real)) := by
      exact setLIntegral_mono'
        P.measurableSet_criticalOwnerEvent hpoint
    _ = ∑ i ∈ P.weightedNormData.criticalBall,
        restrictedMass Y
          (twistedProjection f ⁻¹' P.criticalOwnerEvent) i := by
      exact lintegral_projectedActiveMultiplicity_eq_sum_restrictedMass
        Y P.weightedNormData.criticalBall f hf P.criticalOwnerEvent
    _ ≤ ∑ i ∈ P.weightedNormData.criticalBall,
        volume (Y.carrier i) := by
      exact Finset.sum_le_sum fun i _hi =>
        restrictedMass_le_carrierMass Y
          (twistedProjection f ⁻¹' P.criticalOwnerEvent) i

theorem fibreFloor_mul_criticalBallOwnerWeight_le_ballShadingMass
    (P : ActualGPrimeE2FirstHitOwnerData N D label)
    (Y : Shading F) (f : Real → Real) (hf : Measurable f)
    (fibreFloor : ENNReal)
    (hfloor : ∀ r, r ∈ D.fineLabels → ∀ u,
      u ∈ firstHitFineRectangleY2
        (projectedPositiveMultiplicityDyadicCell D.shading label)
        D.fineLabels D.fineRectangleAt (radius : Real) r →
      fibreFloor ≤ shadingFiberMass Y f (P.owner r) u) :
    fibreFloor *
        (∑ i ∈ P.weightedNormData.criticalBall, P.ownerWeight i) ≤
      ∑ i ∈ P.weightedNormData.criticalBall, volume (Y.carrier i) := by
  rw [← P.volume_criticalOwnerEvent_eq_criticalBallWeight]
  exact fibreFloor_mul_volume_criticalOwnerEvent_le_ballShadingMass
    P Y f hf fibreFloor hfloor

#print axioms fibreFloor_mul_volume_criticalOwnerEvent_le_ballShadingMass
#print axioms fibreFloor_mul_criticalBallOwnerWeight_le_ballShadingMass

end
end Family8Family7CriticalOwnerEventFiberMassLiftV3
