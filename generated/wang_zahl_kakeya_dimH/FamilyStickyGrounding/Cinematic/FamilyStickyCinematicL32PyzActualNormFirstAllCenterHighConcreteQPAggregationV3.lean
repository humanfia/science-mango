import FamilyStickyGrounding.Cinematic.FamilyStickyCinematicL32PyzActualNormFirstAllCenterHighConcreteQPOutcomeV4
import Mathlib.Tactic

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 2000000

open Set MeasureTheory
open scoped BigOperators ENNReal NNReal

namespace FamilyStickyCinematicL32PyzActualNormFirstAllCenterHighConcreteQPAggregationV3

open Submission.Kakeya.ConvexGeometry
open Submission.Kakeya.Uniformity
open FamilyStickyCinematicL32PyzActualNormFirstAllCenterMassWeightedBranchTypesV5C
open FamilyStickyCinematicL32Prop41ActualPositiveCenterHighPayloadWeightedFullyActualConnectorV1
open FamilyStickyCinematicL32PyzActualNormFirstAllCenterHighConcreteQPRetentionV4
open FamilyStickyCinematicL32PyzActualNormFirstAllCenterHighConcreteQPOutcomeV4

noncomputable section

universe u

/-!
# Honest cross-center aggregation of the concrete Q/P high branch

V1 and V2 were failed multiplication-lemma drafts and are deliberately not
imported.  The remaining geometric input is split into exactly the two facts
a packing argument must prove: a pointwise bound for every literal Q/P
right-hand side, and a bound for the sum of its coefficients.  The actual
common mass is the volume of the projected physical shading base in `D`.
-/

/-- The common actual projected mass used in every center's packing bound. -/
noncomputable def nativeHighPhysicalMass
    {radius : NNReal} {iota : Type u} [Fintype iota] [DecidableEq iota]
    (D : NativeBranchCore radius iota) : ENNReal :=
  volume D.physical.base

/-- Summing pointwise bounds for the explicit concrete-Q/P right-hand sides
and then summing their coefficients gives the global high-branch estimate.

`hpoint` is uniform in the local proof `h`: it may inspect the named Q and P
selected from that proof by V4, but cannot replace them by an unrelated
chosen scalar. -/
theorem NativeHighConcreteQPOutcome.sourceMass_half_le_coefficient_mul_physicalMass
    {radius : NNReal} {iota : Type u} [Fintype iota] [DecidableEq iota]
    {D : NativeBranchCore radius iota} {G : NativeHighGeometry D}
    (hout : NativeHighConcreteQPOutcome D G)
    (coefficient : D.HighCenter -> ENNReal) (totalCoefficient : ENNReal)
    (hpoint : forall (c : D.HighCenter)
      (h : PositiveCenterHighPayloadBaseWeightedGlobalSampledLensConclusion
        (D.highBase c) (D.highBase_measurable c) D.S.family D.physical
        D.f D.f1 D.f2 D.outerA D.outerB D.hOuter D.hf D.hf1 D.globalScale
          c.1.1 D.tangencyExponent D.normExponent D.logCount
            (D.chosenHighPayloadAt c) (G.mesh c) (G.ballRadius c)),
      positiveCenterHighPayload_baseConcreteSampledLensRHS
          (D.highBase c) (D.highBase_measurable c) D.S.family D.physical
          D.f D.f1 D.f2 D.outerA D.outerB D.hOuter D.hf D.hf1
            D.globalScale c.1.1 D.tangencyExponent D.normExponent D.logCount
              (D.chosenHighPayloadAt c) (G.mesh c) (G.ballRadius c) h <=
        coefficient c * nativeHighPhysicalMass D)
    (hcoefficient : (∑ c : D.HighCenter, coefficient c) <=
      totalCoefficient) :
    D.sourceMass / 2 <= totalCoefficient * nativeHighPhysicalMass D := by
  obtain ⟨hlocal, hsum⟩ := hout
  calc
    D.sourceMass / 2 <= ∑ c : D.HighCenter,
        positiveCenterHighPayload_baseConcreteSampledLensRHS
          (D.highBase c) (D.highBase_measurable c) D.S.family D.physical
          D.f D.f1 D.f2 D.outerA D.outerB D.hOuter D.hf D.hf1
            D.globalScale c.1.1 D.tangencyExponent D.normExponent D.logCount
              (D.chosenHighPayloadAt c) (G.mesh c) (G.ballRadius c)
                (hlocal c) := hsum
    _ <= ∑ c : D.HighCenter,
        coefficient c * nativeHighPhysicalMass D := by
      apply Finset.sum_le_sum
      intro c _hc
      exact hpoint c (hlocal c)
    _ = (∑ c : D.HighCenter, coefficient c) *
        nativeHighPhysicalMass D := by
      rw [Finset.sum_mul]
    _ <= totalCoefficient * nativeHighPhysicalMass D := by
      simpa only [mul_comm] using
        (mul_le_mul_right hcoefficient (nativeHighPhysicalMass D))

#print axioms nativeHighPhysicalMass
#print axioms
  NativeHighConcreteQPOutcome.sourceMass_half_le_coefficient_mul_physicalMass

end

end FamilyStickyCinematicL32PyzActualNormFirstAllCenterHighConcreteQPAggregationV3
