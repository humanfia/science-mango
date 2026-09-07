import Family8Grounding.Family8Family7LowerBucketGenericNativeBranchCoreV1
import FamilyStickyCinematicL32ContinuumCriticalSingleDyadicSelectionV1
import Mathlib.Tactic

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 1200000

open Set MeasureTheory
open scoped ENNReal NNReal

namespace Family8Family7LowerBucketSourceMassFiniteV3

open Submission.Kakeya.ConvexGeometry
open Family8Family7LowerBucketGenericNativeBranchCoreV1
open Family8ShadingAwareProjectedPhysicalLowerBucketV1
open Family8ShadingAwareProjectedPhysicalV3
open Family8ShadingAwareGenericNativeBranchCoreV2
open FamilyStickyCinematicL32ContinuumCriticalSingleDyadicSelectionV1
open FamilyStickyCinematicL32FiniteProjectedShadingMultiplicitySliceV1
open FamilyStickyCinematicL32WZL3UniformTubeSourceV1

noncomputable section

universe u

/-- A LowerBucket source assembled from one norm cell has finite mass as soon
as the original projected base `X` has finite volume. -/
theorem lowerBucket_sourceMass_ne_top_of_normCell_eq
    {radius : NNReal} {iota : Type u}
    [Fintype iota] [DecidableEq iota]
    {S : WZL3UniformTubeSource radius iota}
    {Y : Shading S.family.bodyFamily} {active : Finset iota}
    {f : Real → Real} {hfContinuous : Continuous f}
    {X : Set (Real × Real)} {hX : MeasurableSet X}
    {I : Set Real} {hI : MeasurableSet I} {fibreFloor : ENNReal}
    (D : LowerBucketNativeBranchCore S Y active f hfContinuous
      X hX I hI fibreFloor)
    (normScale : (Real × Real) → Real) (normLabel : Int)
    (lower upper : Nat)
    (hEq : volume (continuumCriticalSingleDyadicCell
      ((shadingAwareProjectedPhysicalLowerBucket Y active f
        hfContinuous.measurable X hX I hI fibreFloor).multiplicityBand
          lower upper) normScale normLabel) = D.sourceMass)
    (hXfinite : volume X ≠ ∞) :
    D.sourceMass ≠ ∞ := by
  rw [← hEq]
  apply ne_top_of_le_ne_top hXfinite
  apply measure_mono
  intro u hu
  have huband : u ∈
      (shadingAwareProjectedPhysicalLowerBucket Y active f
        hfContinuous.measurable X hX I hI fibreFloor).multiplicityBand
          lower upper := by
    exact hu.1
  have hbase :=
    ((shadingAwareProjectedPhysicalLowerBucket Y active f
      hfContinuous.measurable X hX I hI fibreFloor).mem_multiplicityBand).mp
        huband |>.1
  simpa only [shadingAwareProjectedPhysicalLowerBucket] using hbase

#print axioms lowerBucket_sourceMass_ne_top_of_normCell_eq

end
end Family8Family7LowerBucketSourceMassFiniteV3
