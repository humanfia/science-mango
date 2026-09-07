import Family8Grounding.Family8Family7NativeHighCriticalScaleProxySupportV1
import Family8Grounding.Family8ActualDatumDirectFreshGreedyV1
import Mathlib.Tactic

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 3000000

open Set MeasureTheory
open scoped ENNReal NNReal BigOperators

namespace Family8Family7NativeHighCriticalScaleProxyGreedyV1

open LeanEval.Analysis.WangZahlKakeya
open Submission.Kakeya.ConvexGeometry
open Family8ActualDatumDirectFreshGreedyV1
open Family8FiniteRandomRigidMotionRefinementV1
open Family8GeneralizedKatzTaoMultiplicityV1
open Family8Family7NativeHighCriticalBallDatumV1
open Family8Family7NativeHighCriticalBallRestrictedSourceV1
open Family8Family7NativeHighCriticalScaleProxyGeometryV1
open Family8Family7NativeHighCriticalScaleProxyDatumV1
open Family8Family7NativeHighCriticalScaleProxySupportV1
open Family8Family7NativeHighNearSaturatedNormSplitV1
open Family8SelectedParentPlankFineProxyDatumV1
open Family8RestrictedActualDatumDensityRetentionV1
open FamilyStickyCinematicL32Prop41ActualPositiveCenterHighPayloadWeightedFullyActualConnectorV1
open FamilyStickyCinematicL32PyzActualNormFirstAllCenterMassWeightedBranchTypesV5C

noncomputable section

/-!
# Greedy admissible refinement of the concrete critical-scale proxy

The critical-ball subtype has cardinality at most the native ambient family.
Thus the trivial conflict-degree cap is already polynomially controlled by
the ambient packing theorem, and the direct greedy selector produces a
nonempty admissible refinement while retaining all quantitative fields up to
the single factor `ambient.card + 1`.
-/

theorem nativeHighCriticalBallIndex_card_le_ambient_card
    {radius : NNReal} {iota : Type} [Fintype iota] [DecidableEq iota]
    (D : NativeBranchCore radius iota) (c : D.HighCenter)
    (datum : NativeHighCriticalBallDatum D c) :
    Fintype.card (NativeHighCriticalBallIndex D c) ≤ D.ambient.card := by
  rw [Fintype.card_coe]
  exact Finset.card_le_card datum.subset_physicalAmbient

theorem nativeHighCriticalScaleProxy_directConflict_card_le_ambient_card
    {radius : NNReal} {iota : Type} [Fintype iota] [DecidableEq iota]
    (D : NativeBranchCore radius iota) (G : NativeHighGeometry D)
    (c : D.HighCenter) (datum : NativeHighCriticalBallDatum D c)
    (hambientSource : D.ambient ⊆ D.S.source)
    (Y : Shading D.S.family.bodyFamily)
    (a : NativeHighCriticalBallIndex D c) :
    (directConflictIndices
      (nativeHighCriticalScaleProxyDatum D G c datum hambientSource Y)
      a).card ≤ D.ambient.card := by
  calc
    (directConflictIndices
      (nativeHighCriticalScaleProxyDatum D G c datum hambientSource Y)
      a).card ≤ Fintype.card (NativeHighCriticalBallIndex D c) :=
        Finset.card_le_univ _
    _ ≤ D.ambient.card :=
      nativeHighCriticalBallIndex_card_le_ambient_card D c datum

theorem exists_nativeHighCriticalScaleProxy_greedyAdmissible
    {radius : NNReal} {iota : Type} [Fintype iota] [DecidableEq iota]
    (D : NativeBranchCore radius iota) (G : NativeHighGeometry D)
    {c : D.HighCenter}
    (hc : c ∈ nativeHighNearSaturatedCriticalBallRichCenters D G)
    (datum : NativeHighCriticalBallDatum D c)
    (hambientSource : D.ambient ⊆ D.S.source)
    (Y : Shading D.S.family.bodyFamily) :
    let P := nativeHighCriticalScaleProxyDatum
      D G c datum hambientSource Y
    ∃ selected : Finset (NativeHighCriticalBallIndex D c),
      selected.Nonempty ∧
      (restrictActualTubeDatum P selected).IsAdmissible ∧
      (Fintype.card (NativeHighCriticalBallIndex D c) : ENNReal) ≤
        (D.ambient.card + 1 : Nat) * (selected.card : ENNReal) ∧
      P.shading.shadingMass ≤
        (D.ambient.card + 1 : Nat) *
          (restrictActualTubeDatum P selected).shading.shadingMass ∧
      P.shading.shadingDensity / (D.ambient.card + 1 : Nat) ≤
        (restrictActualTubeDatum P selected).shading.shadingDensity ∧
      P.shading.averageMultiplicity ≤
        (D.ambient.card + 1 : Nat) *
          (restrictActualTubeDatum P selected).shading.averageMultiplicity := by
  classical
  let P := nativeHighCriticalScaleProxyDatum D G c datum hambientSource Y
  let _ : Nonempty (NativeHighCriticalBallIndex D c) := by
    rcases datum.nonempty with ⟨i, hi⟩
    exact ⟨⟨i, hi⟩⟩
  have hdeltaPos : 0 < criticalScaleProxyRadius radius
      (positiveCenterHighPayloadGlobalNormData
        (D.chosenHighPayloadAt c)).criticalScale
      (nativeHighCriticalScale_pos D c) := by
    apply NNReal.coe_pos.mp
    rw [criticalScaleProxyRadius_coe]
    exact div_pos (mul_pos (by norm_num) (NNReal.coe_pos.mpr D.hradius))
      (nativeHighCriticalScale_pos D c)
  have hdeltaHalf : criticalScaleProxyRadius radius
      (positiveCenterHighPayloadGlobalNormData
        (D.chosenHighPayloadAt c)).criticalScale
      (nativeHighCriticalScale_pos D c) ≤ (2 : NNReal)⁻¹ := by
    calc
      criticalScaleProxyRadius radius
          (positiveCenterHighPayloadGlobalNormData
            (D.chosenHighPayloadAt c)).criticalScale
          (nativeHighCriticalScale_pos D c) ≤ (1 / 5 : NNReal) :=
        nativeHighCriticalScaleProxyRadius_le_one_fifth_of_richCenter D G hc
      _ ≤ (2 : NNReal)⁻¹ := by
        apply NNReal.coe_le_coe.mp
        norm_num
  have hsupport : ∀ i : NativeHighCriticalBallIndex D c,
      (P.family.tubes i).carrier ⊆ Metric.closedBall (0 : Space) 1 := by
    intro i
    change (affineAxisProxyTube
      (criticalScaleProxyRadius radius
        (positiveCenterHighPayloadGlobalNormData
          (D.chosenHighPayloadAt c)).criticalScale
        (nativeHighCriticalScale_pos D c))
      (nativeHighCriticalScaleAffineEquiv D c)
      (D.S.family.tubes i.1)).carrier ⊆ Metric.closedBall (0 : Space) 1
    exact nativeHighCriticalScaleProxyFamily_contained_in_unit_ball_of_richCenter
      D G hc datum hambientSource i
  have hconflict : ∀ a : NativeHighCriticalBallIndex D c,
      (directConflictIndices P a).card ≤ D.ambient.card := by
    intro a
    exact nativeHighCriticalScaleProxy_directConflict_card_le_ambient_card
      D G c datum hambientSource Y a
  exact exists_direct_refinement_admissible
    (conflictThreshold := D.ambient.card) P hdeltaPos hdeltaHalf
      hsupport hconflict

#print axioms nativeHighCriticalBallIndex_card_le_ambient_card
#print axioms nativeHighCriticalScaleProxy_directConflict_card_le_ambient_card
#print axioms exists_nativeHighCriticalScaleProxy_greedyAdmissible

end

end Family8Family7NativeHighCriticalScaleProxyGreedyV1
