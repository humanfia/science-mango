import Family8Grounding.Family8Family7GenericNativeHighArbitraryWeightedProxyDatumV1
import Family8Grounding.Family8Family7GenericNativeHighArbitraryWeightedProxySupportV1
import Family8Grounding.Family8ActualDatumDirectFreshGreedyV1
import Mathlib.Tactic

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 2600000

open Set MeasureTheory
open scoped BigOperators ENNReal NNReal

namespace Family8Family7GenericNativeHighArbitraryWeightedProxyGreedyV1

open LeanEval.Analysis.WangZahlKakeya
open Submission.Kakeya.ConvexGeometry
open Family8ActualDatumDirectFreshGreedyV1
open Family8Family7GenericNativeHighArbitraryWeightedProxyDatumV1
open Family8Family7GenericNativeHighArbitraryWeightedProxyDefinitionsV1
open Family8Family7GenericNativeHighArbitraryWeightedProxySupportV1
open Family8Family7GenericNativeHighWeightedNormDataV1
open Family8Family7NativeHighCriticalScaleProxyGeometryV1
open Family8FiniteRandomRigidMotionRefinementV1
open Family8GeneralizedKatzTaoMultiplicityV1
open Family8KatzTaoFrostmanPropertiesV1
open Family8RestrictedActualDatumDensityRetentionV1
open Family8SelectedParentPlankFineProxyDatumV1
open Family8ShadingAwareGenericNativeBranchCoreV2
open FamilyStickyCinematicL32FiniteProjectedShadingMultiplicitySliceV1
open FamilyStickyCinematicL32WZL3UniformTubeSourceV1

noncomputable section

theorem
    genericNativeHighArbitraryWeightedCriticalBallIndex_card_le_ambient_card
    {radius : NNReal} {iota : Type} [Fintype iota] [DecidableEq iota]
    {S : WZL3UniformTubeSource radius iota}
    {physical : FiniteProjectedShading (Real × Real) iota}
    {f : Real → Real} {hfContinuous : Continuous f}
    (D : GenericNativeBranchCore radius iota S physical f hfContinuous)
    (P : GenericNativeHighArbitraryWeightedProxyInput D) :
    Fintype.card
        (GenericNativeHighArbitraryWeightedCriticalBallIndex D P) ≤
      physical.ambient.card := by
  rw [Fintype.card_coe]
  exact Finset.card_le_card
    (genericNativeHighArbitraryWeightedCriticalBall_subset_physicalAmbient
      D P)

theorem
    genericNativeHighArbitraryWeightedProxy_directConflict_card_le_ambient_card
    {radius : NNReal} {iota : Type} [Fintype iota] [DecidableEq iota]
    {S : WZL3UniformTubeSource radius iota}
    {physical : FiniteProjectedShading (Real × Real) iota}
    {f : Real → Real} {hfContinuous : Continuous f}
    (D : GenericNativeBranchCore radius iota S physical f hfContinuous)
    (P : GenericNativeHighArbitraryWeightedProxyInput D)
    (hambientSource : physical.ambient ⊆ S.source)
    (Y : Shading S.family.bodyFamily)
    (a : GenericNativeHighArbitraryWeightedCriticalBallIndex D P) :
    (directConflictIndices
      (genericNativeHighArbitraryWeightedCriticalScaleProxyDatum
        D P hambientSource Y) a).card ≤ physical.ambient.card := by
  calc
    (directConflictIndices
      (genericNativeHighArbitraryWeightedCriticalScaleProxyDatum
        D P hambientSource Y) a).card ≤
        Fintype.card
          (GenericNativeHighArbitraryWeightedCriticalBallIndex D P) :=
      Finset.card_le_univ _
    _ ≤ physical.ambient.card :=
      genericNativeHighArbitraryWeightedCriticalBallIndex_card_le_ambient_card
        D P

theorem
    exists_genericNativeHighArbitraryWeightedProxy_greedyAdmissible
    {radius : NNReal} {iota : Type} [Fintype iota] [DecidableEq iota]
    {S : WZL3UniformTubeSource radius iota}
    {physical : FiniteProjectedShading (Real × Real) iota}
    {f : Real → Real} {hfContinuous : Continuous f}
    (D : GenericNativeBranchCore radius iota S physical f hfContinuous)
    (P : GenericNativeHighArbitraryWeightedProxyInput D)
    (hambientSource : physical.ambient ⊆ S.source)
    (Y : Shading S.family.bodyFamily)
    (hcontained : ∀ i, i ∈ physical.ambient →
      (S.family.tubes i).carrier ⊆ Metric.closedBall (0 : Space) 1)
    (hproxyRadius :
      criticalScaleProxyRadius radius
          (genericNativeHighWeightedNormData
            D P.center P.weight).criticalScale
          (genericNativeHighArbitraryWeightedCriticalScale_pos D P) ≤
        (1 / 5 : NNReal)) :
    let A := genericNativeHighArbitraryWeightedCriticalScaleProxyDatum
      D P hambientSource Y
    ∃ selected : Finset
        (GenericNativeHighArbitraryWeightedCriticalBallIndex D P),
      selected.Nonempty ∧
      (restrictActualTubeDatum A selected).IsAdmissible ∧
      (Fintype.card
          (GenericNativeHighArbitraryWeightedCriticalBallIndex D P) :
          ENNReal) ≤
        (physical.ambient.card + 1 : Nat) *
          (selected.card : ENNReal) ∧
      A.shading.shadingMass ≤
        (physical.ambient.card + 1 : Nat) *
          (restrictActualTubeDatum A selected).shading.shadingMass ∧
      A.shading.shadingDensity /
          (physical.ambient.card + 1 : Nat) ≤
        (restrictActualTubeDatum A selected).shading.shadingDensity ∧
      A.shading.averageMultiplicity ≤
        (physical.ambient.card + 1 : Nat) *
          (restrictActualTubeDatum A selected).shading.averageMultiplicity := by
  classical
  let A := genericNativeHighArbitraryWeightedCriticalScaleProxyDatum
    D P hambientSource Y
  let _ :
      Nonempty
        (GenericNativeHighArbitraryWeightedCriticalBallIndex D P) := by
    rcases (genericNativeHighWeightedNormData
      D P.center P.weight).criticalBall_nonempty with ⟨i, hi⟩
    exact ⟨⟨i, hi⟩⟩
  have hdeltaPos :
      0 < criticalScaleProxyRadius radius
        (genericNativeHighWeightedNormData
          D P.center P.weight).criticalScale
        (genericNativeHighArbitraryWeightedCriticalScale_pos D P) := by
    apply NNReal.coe_pos.mp
    rw [criticalScaleProxyRadius_coe]
    exact div_pos
      (mul_pos (by norm_num) (NNReal.coe_pos.mpr D.hradius))
      (genericNativeHighArbitraryWeightedCriticalScale_pos D P)
  have hdeltaHalf :
      criticalScaleProxyRadius radius
          (genericNativeHighWeightedNormData
            D P.center P.weight).criticalScale
          (genericNativeHighArbitraryWeightedCriticalScale_pos D P) ≤
        (2 : NNReal)⁻¹ :=
    hproxyRadius.trans (by
      exact_mod_cast
        (show (1 / 5 : Real) ≤ (2 : Real)⁻¹ by norm_num))
  have hsupport :
      ∀ i : GenericNativeHighArbitraryWeightedCriticalBallIndex D P,
        ((genericNativeHighArbitraryWeightedCriticalScaleProxyFamily
          D P).tubes i).carrier ⊆ Metric.closedBall (0 : Space) 1 :=
    genericNativeHighArbitraryWeightedProxyFamily_contained_in_unit_ball
      D P hambientSource hcontained hproxyRadius
  have hconflict :
      ∀ a : GenericNativeHighArbitraryWeightedCriticalBallIndex D P,
        (directConflictIndices A a).card ≤ physical.ambient.card := by
    intro a
    exact
      genericNativeHighArbitraryWeightedProxy_directConflict_card_le_ambient_card
        D P hambientSource Y a
  exact exists_direct_refinement_admissible
    (conflictThreshold := physical.ambient.card)
    A hdeltaPos hdeltaHalf hsupport hconflict

#print axioms
  genericNativeHighArbitraryWeightedCriticalBallIndex_card_le_ambient_card
#print axioms
  genericNativeHighArbitraryWeightedProxy_directConflict_card_le_ambient_card
#print axioms
  exists_genericNativeHighArbitraryWeightedProxy_greedyAdmissible

end

end Family8Family7GenericNativeHighArbitraryWeightedProxyGreedyV1
