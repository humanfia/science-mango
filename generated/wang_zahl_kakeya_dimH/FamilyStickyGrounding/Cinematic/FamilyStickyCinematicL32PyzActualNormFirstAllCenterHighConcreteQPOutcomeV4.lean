import FamilyStickyGrounding.Cinematic.FamilyStickyCinematicL32PyzActualNormFirstAllCenterHighConcreteQPRetentionV4
import Mathlib.Tactic

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 4000000

open Set MeasureTheory
open scoped BigOperators ENNReal NNReal

namespace FamilyStickyCinematicL32PyzActualNormFirstAllCenterHighConcreteQPOutcomeV4

open Submission.Kakeya.ConvexGeometry
open Submission.Kakeya.Uniformity
open FamilyStickyCinematicL32ActualProjectedNormSourceFamilyV1
open FamilyStickyCinematicL32PyzE2DyadicDegreeWindowV1
open FamilyStickyCinematicL32Prop41ActualGPrimeDegreeRichMassProducerV1
open FamilyStickyCinematicL32Prop41CanonicalMaximizerNonconcentrationV1
open FamilyStickyCinematicL32Prop41ActualPositiveCenterHighPayloadWeightedFullyActualConnectorV1
open FamilyStickyCinematicL32PyzActualNormFirstAllCenterPayloadDichotomyFinalCleanV2
open FamilyStickyCinematicL32PyzActualNormFirstAllCenterHighHalfSampledLensV3
open FamilyStickyCinematicL32PyzActualNormFirstAllCenterMassWeightedBranchCallsV5B
open FamilyStickyCinematicL32PyzActualNormFirstAllCenterMassWeightedBranchTypesV5C
open FamilyStickyCinematicL32PyzActualNormFirstAllCenterMassWeightedBranchHighV5D
open FamilyStickyCinematicL32PyzActualNormFirstAllCenterHighConcreteQPRetentionV4

noncomputable section

universe u

/-!
# The native high branch with its actual Q/P witnesses retained

V1--V3 were failed naming/open drafts and are deliberately not imported.
The local conclusions retain the actual existential Q/P proofs, while the
sum uses V4's named Q and dependent P and their literal `hQP` inequality.
-/

def NativeHighConcreteQPOutcome
    {radius : NNReal} {iota : Type u} [Fintype iota] [DecidableEq iota]
    (D : NativeBranchCore radius iota) (G : NativeHighGeometry D) : Prop :=
  exists hlocal : forall c : D.HighCenter,
    PositiveCenterHighPayloadBaseWeightedGlobalSampledLensConclusion
      (D.highBase c) (D.highBase_measurable c) D.S.family D.physical
      D.f D.f1 D.f2 D.outerA D.outerB D.hOuter D.hf D.hf1 D.globalScale
        c.1.1 D.tangencyExponent D.normExponent D.logCount
          (D.chosenHighPayloadAt c) (G.mesh c) (G.ballRadius c),
    D.sourceMass / 2 <= ∑ c : D.HighCenter,
      positiveCenterHighPayload_baseConcreteSampledLensRHS
        (D.highBase c) (D.highBase_measurable c) D.S.family D.physical
        D.f D.f1 D.f2 D.outerA D.outerB D.hOuter D.hf D.hf1
          D.globalScale c.1.1 D.tangencyExponent D.normExponent D.logCount
            (D.chosenHighPayloadAt c) (G.mesh c) (G.ballRadius c)
              (hlocal c)

/-- The native high-half branch produces a family of literal local
conclusions and a half-mass sum of the corresponding explicit Q/P right-hand
sides.  The old chosen-scalar sum is used only to recover the already-proved
local conclusions; its numerical inequality is discarded. -/
theorem nativeHighConcreteQPOutcome_of_half
    {radius : NNReal} {iota : Type u} [Fintype iota] [DecidableEq iota]
    (D : NativeBranchCore radius iota) (G : NativeHighGeometry D)
    (hhalf : D.sourceMass / 2 <=
      ∑ c ∈ D.high, volume (D.cell c.1)) :
    NativeHighConcreteQPOutcome D G := by
  classical
  have hold := nativeHighOutcome_of_half D G hhalf
  unfold NativeHighGeometry.Outcome at hold
  unfold ActualAllCenterHighNativeOutcome at hold
  obtain ⟨hlocal, _holdSum⟩ := hold
  refine ⟨hlocal, ?_⟩
  have hbaseSum :
      (∑ c : D.HighCenter, volume (D.highBase c)) =
        ∑ c ∈ D.high, volume (D.cell c.1) := by
    simpa only [NativeBranchCore.highBase,
      NativeBranchCore.positiveBase, Finset.univ_eq_attach] using
        Finset.sum_attach D.high (fun c => volume (D.cell c.1))
  have hhalf' : D.sourceMass / 2 <=
      ∑ c : D.HighCenter, volume (D.highBase c) :=
    hhalf.trans_eq hbaseSum.symm
  have hhalfUniv : D.sourceMass / 2 <=
      ∑ c ∈ (Finset.univ : Finset D.HighCenter),
        volume (D.highBase c) := by
    simpa only [Finset.sum_filter, Finset.mem_univ, if_true] using hhalf'
  have hsum := half_sourceMass_le_sum_rhs_of_degreeGap
    (high := (Finset.univ : Finset D.HighCenter))
    (weight := fun c => volume (D.highBase c))
    (rhs := fun c =>
      positiveCenterHighPayload_baseConcreteSampledLensRHS
        (D.highBase c) (D.highBase_measurable c) D.S.family D.physical
        D.f D.f1 D.f2 D.outerA D.outerB D.hOuter D.hf D.hf1
          D.globalScale c.1.1 D.tangencyExponent D.normExponent D.logCount
            (D.chosenHighPayloadAt c) (G.mesh c) (G.ballRadius c)
              (hlocal c))
    (degreeGap := fun c =>
      pyzE2DegreeLower (D.chosenHighPayloadAt c).payload.finalLabel *
        (pyzE2DegreeLower (D.chosenHighPayloadAt c).payload.finalLabel -
          automaticCanonicalNearCap
            (positiveCenterHighPayloadGlobalNormData
              (D.chosenHighPayloadAt c)) (G.ballRadius c)))
    D.sourceMass hhalfUniv
    (by
      intro c _hc
      have hc := G.hroom c
      have hd : 1 <=
          pyzE2DegreeLower (D.chosenHighPayloadAt c).payload.finalLabel := by
        omega
      have hdiff : 1 <=
          pyzE2DegreeLower (D.chosenHighPayloadAt c).payload.finalLabel -
            automaticCanonicalNearCap
              (positiveCenterHighPayloadGlobalNormData
                (D.chosenHighPayloadAt c)) (G.ballRadius c) := by
        omega
      calc
        1 = 1 * 1 := by norm_num
        _ <= pyzE2DegreeLower
              (D.chosenHighPayloadAt c).payload.finalLabel *
            (pyzE2DegreeLower
                (D.chosenHighPayloadAt c).payload.finalLabel -
              automaticCanonicalNearCap
                (positiveCenterHighPayloadGlobalNormData
                  (D.chosenHighPayloadAt c)) (G.ballRadius c)) :=
          Nat.mul_le_mul hd hdiff)
    (by
      intro c _hc
      exact
        positiveCenterHighPayload_base_mul_degree_le_concreteSampledLensRHS
          (D.highBase c) (D.highBase_measurable c) D.S.family D.physical
          D.f D.f1 D.f2 D.outerA D.outerB D.hOuter D.hf D.hf1
            D.globalScale c.1.1 D.tangencyExponent D.normExponent D.logCount
              (D.chosenHighPayloadAt c) (G.mesh c) (G.ballRadius c)
                (hlocal c))
  simpa only [Finset.sum_filter, Finset.mem_univ, if_true] using hsum

#print axioms NativeHighConcreteQPOutcome
#print axioms nativeHighConcreteQPOutcome_of_half

end

end FamilyStickyCinematicL32PyzActualNormFirstAllCenterHighConcreteQPOutcomeV4
