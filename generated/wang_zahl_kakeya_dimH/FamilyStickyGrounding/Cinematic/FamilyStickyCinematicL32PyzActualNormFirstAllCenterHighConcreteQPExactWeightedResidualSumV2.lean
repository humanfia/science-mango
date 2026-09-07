import FamilyStickyGrounding.Cinematic.FamilyStickyCinematicL32PyzActualNormFirstAllCenterHighConcreteQPWeightedGeometricSumV2
import Mathlib.Tactic

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 3000000

open Set MeasureTheory
open scoped BigOperators ENNReal NNReal

namespace FamilyStickyCinematicL32PyzActualNormFirstAllCenterHighConcreteQPExactWeightedResidualSumV2

open Submission.Kakeya.ConvexGeometry
open Submission.Kakeya.Uniformity
open FamilyStickyCinematicL32Prop41ActualPositiveCenterHighPayloadWeightedFullyActualConnectorV1
open FamilyStickyCinematicL32PyzActualNormFirstAllCenterHighConcreteQPRetentionV4
open FamilyStickyCinematicL32PyzActualNormFirstAllCenterHighConcreteQPOutcomeV4
open FamilyStickyCinematicL32PyzActualNormFirstAllCenterHighConcreteQPThreeBallPackingV4
open FamilyStickyCinematicL32PyzActualNormFirstAllCenterHighConcreteQPResidualEnvelopeV3
open FamilyStickyCinematicL32PyzActualNormFirstAllCenterHighConcreteQPWeightedGeometricSumV2
open FamilyStickyCinematicL32PyzActualNormFirstAllCenterHighThreeBallCoefficientV3
open FamilyStickyCinematicL32PyzActualNormFirstAllCenterMassWeightedBranchTypesV5C

noncomputable section

universe u

/-!
# Exact weighted residual sum before every global envelope

This is the strongest direct cross-centre consumer of the elementary
rich-pair square bound.  It does not replace the literal sampled-lens factor
by a global ambient-card envelope, does not replace the local geometric
factor by a maximum, and does not invoke pairwise essential distinctness.

Only the single ambient-card factor used to turn one local square into
`ambient.card * localThreeBallCard` remains outside.  The exact remaining
quantity is a finite weighted sum, so a future packing or mass identity may
act on it without first undoing a coarse `ambient.card ^ 2` bound.
-/

/-- The exact residual factor weighted by the local projected three-ball
cardinality, using the actual local conclusions selected by the outcome. -/
noncomputable def nativeHighConcreteWeightedResidualNormBudget
    {radius : NNReal} {iota : Type u} [Fintype iota] [DecidableEq iota]
    {D : NativeBranchCore radius iota} {G : NativeHighGeometry D}
    (hout : NativeHighConcreteQPOutcome D G) : ENNReal :=
  ∑ c : D.HighCenter,
    nativeHighConcreteResidualFactor D G c
        (nativeHighConcreteQPLocalAt hout c) *
      (nativeHighNormFamilyCard D c : ENNReal)

/-- Exact callback-free cross-centre bound with one ambient-card factor and
the literal residual weighted sum. -/
theorem NativeHighConcreteQPOutcome.sourceMass_half_le_ambient_mul_weightedResidualNormBudget
    {radius : NNReal} {iota : Type u} [Fintype iota] [DecidableEq iota]
    {D : NativeBranchCore radius iota} {G : NativeHighGeometry D}
    (hout : NativeHighConcreteQPOutcome D G) :
    D.sourceMass / 2 <=
      (D.ambient.card : ENNReal) *
        nativeHighConcreteWeightedResidualNormBudget hout := by
  calc
    D.sourceMass / 2 <=
        ∑ c : D.HighCenter,
          positiveCenterHighPayload_baseConcreteSampledLensRHS
            (D.highBase c) (D.highBase_measurable c) D.S.family D.physical
            D.f D.f1 D.f2 D.outerA D.outerB D.hOuter D.hf D.hf1
              D.globalScale c.1.1 D.tangencyExponent D.normExponent
                D.logCount (D.chosenHighPayloadAt c) (G.mesh c)
                  (G.ballRadius c) (nativeHighConcreteQPLocalAt hout c) :=
      sourceMass_half_le_sum_concreteRHS_of_localAt hout
    _ <= ∑ c : D.HighCenter,
        (D.ambient.card : ENNReal) *
          (nativeHighConcreteResidualFactor D G c
              (nativeHighConcreteQPLocalAt hout c) *
            (nativeHighNormFamilyCard D c : ENNReal)) := by
      apply Finset.sum_le_sum
      intro c _hc
      let h := nativeHighConcreteQPLocalAt hout c
      calc
        positiveCenterHighPayload_baseConcreteSampledLensRHS
            (D.highBase c) (D.highBase_measurable c) D.S.family D.physical
            D.f D.f1 D.f2 D.outerA D.outerB D.hOuter D.hf D.hf1
              D.globalScale c.1.1 D.tangencyExponent D.normExponent
                D.logCount (D.chosenHighPayloadAt c) (G.mesh c)
                  (G.ballRadius c) h <=
          (nativeHighConcreteResidualFactor D G c h *
              (D.ambient.card : ENNReal)) *
            (nativeHighNormFamilyCard D c : ENNReal) :=
          concreteSampledLensRHS_le_residual_mul_ambient_mul_normCard
            D G c h
        _ = (D.ambient.card : ENNReal) *
            (nativeHighConcreteResidualFactor D G c h *
              (nativeHighNormFamilyCard D c : ENNReal)) := by
          ac_rfl
    _ = (D.ambient.card : ENNReal) *
        nativeHighConcreteWeightedResidualNormBudget hout := by
      unfold nativeHighConcreteWeightedResidualNormBudget
      rw [Finset.mul_sum]

/-- The exact residual weighted sum is controlled by the deterministic
sampled-lens envelope times the weighted geometric sum.  This is stated
separately so downstream users may choose whether or not to spend that
envelope. -/
theorem nativeHighConcreteWeightedResidualNormBudget_le_globalEnvelope_mul_geometricBudget
    {radius : NNReal} {iota : Type u} [Fintype iota] [DecidableEq iota]
    {D : NativeBranchCore radius iota} {G : NativeHighGeometry D}
    (hout : NativeHighConcreteQPOutcome D G) :
    nativeHighConcreteWeightedResidualNormBudget hout <=
      nativeHighGlobalSampledLensCardinalEnvelope D *
        nativeHighConcreteWeightedGeometricNormBudget hout := by
  unfold nativeHighConcreteWeightedResidualNormBudget
    nativeHighConcreteWeightedGeometricNormBudget
  rw [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro c _hc
  let h := nativeHighConcreteQPLocalAt hout c
  have hresidual :
      nativeHighConcreteResidualFactor D G c h <=
        nativeHighConcreteGeometricFactor D G c h *
          nativeHighGlobalSampledLensCardinalEnvelope D :=
    nativeHighConcreteResidualFactor_le_geometric_mul_globalEnvelope D G c h
  calc
    nativeHighConcreteResidualFactor D G c h *
        (nativeHighNormFamilyCard D c : ENNReal) <=
      (nativeHighConcreteGeometricFactor D G c h *
          nativeHighGlobalSampledLensCardinalEnvelope D) *
        (nativeHighNormFamilyCard D c : ENNReal) :=
      mul_le_mul' hresidual le_rfl
    _ = nativeHighGlobalSampledLensCardinalEnvelope D *
        (nativeHighConcreteGeometricFactor D G c h *
          (nativeHighNormFamilyCard D c : ENNReal)) := by
      ac_rfl

#print axioms nativeHighConcreteWeightedResidualNormBudget
#print axioms
  NativeHighConcreteQPOutcome.sourceMass_half_le_ambient_mul_weightedResidualNormBudget
#print axioms
  nativeHighConcreteWeightedResidualNormBudget_le_globalEnvelope_mul_geometricBudget

end

end FamilyStickyCinematicL32PyzActualNormFirstAllCenterHighConcreteQPExactWeightedResidualSumV2
