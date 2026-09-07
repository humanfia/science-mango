import FamilyStickyGrounding.Cinematic.FamilyStickyCinematicL32PyzActualNormFirstAllCenterHighConcreteQPResidualEnvelopeV3
import Mathlib.Tactic

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 4000000

open Set MeasureTheory
open scoped BigOperators ENNReal NNReal

namespace FamilyStickyCinematicL32PyzActualNormFirstAllCenterHighConcreteQPWeightedGeometricSumV2

open Submission.Kakeya.ConvexGeometry
open Submission.Kakeya.Uniformity
open FamilyStickyCinematicL32Prop41ActualPositiveCenterHighPayloadWeightedFullyActualConnectorV1
open FamilyStickyCinematicL32PyzActualNormFirstAllCenterHighConcreteQPRetentionV4
open FamilyStickyCinematicL32PyzActualNormFirstAllCenterHighConcreteQPOutcomeV4
open FamilyStickyCinematicL32PyzActualNormFirstAllCenterHighConcreteQPThreeBallPackingV4
open FamilyStickyCinematicL32PyzActualNormFirstAllCenterHighConcreteQPResidualEnvelopeV3
open FamilyStickyCinematicL32PyzActualNormFirstAllCenterHighThreeBallCoefficientV3
open FamilyStickyCinematicL32PyzActualNormFirstAllCenterMassWeightedBranchTypesV5C

noncomputable section

universe u

/-!
# The exact weighted geometric sum before the ambient-card-square bound

The uniform-envelope endpoint in the preceding module deliberately exposes
the final `ambient.card ^ 2`.  One copy is intrinsic to the elementary
rich-pair square bound, but the second appears only after replacing every
centre's geometric factor by a common upper bound and then applying the
global three-ball overlap estimate.

This module stops one step earlier.  It retains the literal local proof and
the exact weighted sum

`sum_c geometricFactor(c) * localThreeBallCard(c)`.

Consequently the theorem below is callback-free, needs no pairwise
essential-distinctness hypothesis, and has only one explicit ambient-card
factor.  Any later argument may either exploit the weighted sum directly or
recover the coarser square bound.  No claim that either cardinal factor is a
small loss is made here.
-/

/-- The actual family of local high conclusions selected by the concrete-Q/P
outcome.  This is a choice of the witnesses already proved to exist, not a
choice of an unrelated scalar right-hand side. -/
theorem nativeHighConcreteQPLocalAt
    {radius : NNReal} {iota : Type u} [Fintype iota] [DecidableEq iota]
    {D : NativeBranchCore radius iota} {G : NativeHighGeometry D}
    (hout : NativeHighConcreteQPOutcome D G) :
    forall c : D.HighCenter,
      PositiveCenterHighPayloadBaseWeightedGlobalSampledLensConclusion
        (D.highBase c) (D.highBase_measurable c) D.S.family D.physical
        D.f D.f1 D.f2 D.outerA D.outerB D.hOuter D.hf D.hf1
          D.globalScale c.1.1 D.tangencyExponent D.normExponent D.logCount
            (D.chosenHighPayloadAt c) (G.mesh c) (G.ballRadius c) :=
  Classical.choose hout

/-- The chosen local conclusions retain the exact half-source-mass sum from
the concrete-Q/P outcome. -/
theorem sourceMass_half_le_sum_concreteRHS_of_localAt
    {radius : NNReal} {iota : Type u} [Fintype iota] [DecidableEq iota]
    {D : NativeBranchCore radius iota} {G : NativeHighGeometry D}
    (hout : NativeHighConcreteQPOutcome D G) :
    D.sourceMass / 2 <=
      ∑ c : D.HighCenter,
        positiveCenterHighPayload_baseConcreteSampledLensRHS
          (D.highBase c) (D.highBase_measurable c) D.S.family D.physical
          D.f D.f1 D.f2 D.outerA D.outerB D.hOuter D.hf D.hf1
            D.globalScale c.1.1 D.tangencyExponent D.normExponent D.logCount
              (D.chosenHighPayloadAt c) (G.mesh c) (G.ballRadius c)
                (nativeHighConcreteQPLocalAt hout c) := by
  exact Classical.choose_spec hout

/-- The literal geometric factor weighted by the actual local projected
three-ball cardinality. -/
noncomputable def nativeHighConcreteWeightedGeometricNormBudget
    {radius : NNReal} {iota : Type u} [Fintype iota] [DecidableEq iota]
    {D : NativeBranchCore radius iota} {G : NativeHighGeometry D}
    (hout : NativeHighConcreteQPOutcome D G) : ENNReal :=
  ∑ c : D.HighCenter,
    nativeHighConcreteGeometricFactor D G c
        (nativeHighConcreteQPLocalAt hout c) *
      (nativeHighNormFamilyCard D c : ENNReal)

/-- Callback-free cross-centre estimate before the coarse
`ambient.card ^ 2` collapse.  The sampled-lens term is already the common
deterministic cardinal envelope, while all remaining local geometry is kept
inside its genuine three-ball-card weighted sum. -/
theorem NativeHighConcreteQPOutcome.sourceMass_half_le_globalEnvelope_mul_ambient_mul_weightedGeometricNormBudget
    {radius : NNReal} {iota : Type u} [Fintype iota] [DecidableEq iota]
    {D : NativeBranchCore radius iota} {G : NativeHighGeometry D}
    (hout : NativeHighConcreteQPOutcome D G) :
    D.sourceMass / 2 <=
      (nativeHighGlobalSampledLensCardinalEnvelope D *
          (D.ambient.card : ENNReal)) *
        nativeHighConcreteWeightedGeometricNormBudget hout := by
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
        (nativeHighGlobalSampledLensCardinalEnvelope D *
            (D.ambient.card : ENNReal)) *
          (nativeHighConcreteGeometricFactor D G c
              (nativeHighConcreteQPLocalAt hout c) *
            (nativeHighNormFamilyCard D c : ENNReal)) := by
      apply Finset.sum_le_sum
      intro c _hc
      let h := nativeHighConcreteQPLocalAt hout c
      have hresidual :
          nativeHighConcreteResidualFactor D G c h <=
            nativeHighConcreteGeometricFactor D G c h *
              nativeHighGlobalSampledLensCardinalEnvelope D :=
        nativeHighConcreteResidualFactor_le_geometric_mul_globalEnvelope
          D G c h
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
        _ <=
          ((nativeHighConcreteGeometricFactor D G c h *
                nativeHighGlobalSampledLensCardinalEnvelope D) *
              (D.ambient.card : ENNReal)) *
            (nativeHighNormFamilyCard D c : ENNReal) :=
          mul_le_mul'
            (mul_le_mul' hresidual le_rfl) le_rfl
        _ =
          (nativeHighGlobalSampledLensCardinalEnvelope D *
              (D.ambient.card : ENNReal)) *
            (nativeHighConcreteGeometricFactor D G c h *
              (nativeHighNormFamilyCard D c : ENNReal)) := by
          ac_rfl
    _ = (nativeHighGlobalSampledLensCardinalEnvelope D *
          (D.ambient.card : ENNReal)) *
        nativeHighConcreteWeightedGeometricNormBudget hout := by
      unfold nativeHighConcreteWeightedGeometricNormBudget
      rw [Finset.mul_sum]

#print axioms nativeHighConcreteQPLocalAt
#print axioms sourceMass_half_le_sum_concreteRHS_of_localAt
#print axioms nativeHighConcreteWeightedGeometricNormBudget
#print axioms
  NativeHighConcreteQPOutcome.sourceMass_half_le_globalEnvelope_mul_ambient_mul_weightedGeometricNormBudget

end

end FamilyStickyCinematicL32PyzActualNormFirstAllCenterHighConcreteQPWeightedGeometricSumV2
