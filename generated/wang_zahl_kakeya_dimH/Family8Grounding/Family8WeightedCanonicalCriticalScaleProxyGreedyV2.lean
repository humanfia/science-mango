import Family8Grounding.Family8WeightedCanonicalCriticalScaleProxyDatumV4
import Family8Grounding.Family8WeightedCanonicalCriticalBallIndexCardV1
import Family8Grounding.Family8ActualDatumDirectFreshGreedyV1

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 3000000

open Set MeasureTheory
open scoped ENNReal NNReal BigOperators

namespace Family8WeightedCanonicalCriticalScaleProxyGreedyV2

open LeanEval.Analysis.WangZahlKakeya
open Submission.Kakeya.ConvexGeometry
open Family8ActualDatumDirectFreshGreedyV1
open Family8ContractedJohnActualTubeProxyV1
open Family8Family7NativeHighCriticalScaleProxyGeometryV1
open Family8Family7NativeHighWeightedCriticalBallV1
open Family8FiniteRandomRigidMotionRefinementV1
open Family8GeneralizedKatzTaoMultiplicityV1
open Family8KatzTaoFrostmanPropertiesV1
open Family8RestrictedActualDatumDensityRetentionV1
open Family8SelectedParentPlankFineProxyCarrierV3
open Family8WeightedCanonicalCriticalBallIndexCardV1
open Family8WeightedCanonicalCriticalScaleAffineEquivV1
open Family8WeightedCanonicalCriticalScalePositiveV1
open Family8WeightedCanonicalCriticalScaleProxyDatumV4
open Family8WeightedCanonicalCriticalScaleProxyFamilyV3
open FamilyStickyCinematicL32WZL3UniformTubeSourceV1

noncomputable section

/-- Direct greedy/Frostman handoff on the literal weighted canonical
critical-ball datum.  The two displayed geometric inputs are precisely the
scale cap and unit-ball support required by admissibility; all combinatorial
losses are discharged using the source-family cardinality. -/
theorem exists_weightedCanonicalCriticalScaleProxy_greedyAdmissible
    {radius : NNReal} {iota : Type} [Fintype iota] [DecidableEq iota]
    (S : WZL3UniformTubeSource radius iota)
    (W : WeightedCanonicalNormBallData iota)
    (Y : Shading S.family.bodyFamily)
    (hradius : 0 < radius)
    (haxis : ∀ i : {i // i ∈ W.criticalBall},
      ‖affineImageAxisVector
        (weightedCanonicalCriticalScaleAffineEquiv S W)
        (S.family.tubes i.1)‖ ≤ 1)
    (htransverse :
      affineLinearOperatorNorm
          (weightedCanonicalCriticalScaleAffineEquiv S W) *
            (radius : Real) ≤
        (criticalScaleProxyRadius radius W.criticalScale
          (weightedCanonicalCriticalScale_pos W) : Real))
    (hdeltaHalf :
      criticalScaleProxyRadius radius W.criticalScale
          (weightedCanonicalCriticalScale_pos W) ≤
        (2 : NNReal)⁻¹)
    (hsupport : ∀ i : {i // i ∈ W.criticalBall},
      ((weightedCanonicalCriticalScaleProxyFamily S W).tubes i).carrier ⊆
        Metric.closedBall (0 : Space) 1) :
    let A := weightedCanonicalCriticalScaleProxyDatum
      S W Y haxis htransverse
    ∃ selected : Finset {i // i ∈ W.criticalBall},
      selected.Nonempty ∧
      (restrictActualTubeDatum A selected).IsAdmissible ∧
      (Fintype.card {i // i ∈ W.criticalBall} : ENNReal) ≤
        (W.family.card + 1 : Nat) * (selected.card : ENNReal) ∧
      A.shading.shadingMass ≤
        (W.family.card + 1 : Nat) *
          (restrictActualTubeDatum A selected).shading.shadingMass ∧
      A.shading.shadingDensity / (W.family.card + 1 : Nat) ≤
        (restrictActualTubeDatum A selected).shading.shadingDensity ∧
      A.shading.averageMultiplicity ≤
        (W.family.card + 1 : Nat) *
          (restrictActualTubeDatum A selected).shading.averageMultiplicity := by
  classical
  let A := weightedCanonicalCriticalScaleProxyDatum
    S W Y haxis htransverse
  let _ : Nonempty {i // i ∈ W.criticalBall} := by
    rcases W.criticalBall_nonempty with ⟨i, hi⟩
    exact ⟨⟨i, hi⟩⟩
  have hdeltaPos : 0 < criticalScaleProxyRadius radius W.criticalScale
      (weightedCanonicalCriticalScale_pos W) := by
    apply NNReal.coe_pos.mp
    rw [criticalScaleProxyRadius_coe]
    exact div_pos (mul_pos (by norm_num) (NNReal.coe_pos.mpr hradius))
      (weightedCanonicalCriticalScale_pos W)
  have hconflict : ∀ a : {i // i ∈ W.criticalBall},
      (directConflictIndices A a).card ≤ W.family.card := by
    intro a
    calc
      (directConflictIndices A a).card ≤
          Fintype.card {i // i ∈ W.criticalBall} :=
        Finset.card_le_univ _
      _ ≤ W.family.card :=
        weightedCanonicalCriticalBallIndex_card_le_family_card W
  exact exists_direct_refinement_admissible
    (conflictThreshold := W.family.card) A hdeltaPos hdeltaHalf
      hsupport hconflict

end

end Family8WeightedCanonicalCriticalScaleProxyGreedyV2
