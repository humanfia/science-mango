import Family8Grounding.Family8B2NormalizedConflictKatzTaoCapV6
import Family8Grounding.Family8FiniteRandomRigidMotionPaperFixedJohnFreshSelectionV2
import Family8Grounding.Family8FrozenCoarseB2DensityTransportScaleOnlyV1
import Family8Grounding.Family8RestrictedActualDatumDensityRetentionV1
import Mathlib.Tactic

/-!
# Katz--Tao after B2 normalization and fresh selection

This is the B2-native counterpart of the unit-supported endpoint.  The
source family is only required to lie in the closed ball of radius two,
which is exactly the support hypothesis consumed by eighth-normalization.
No pairwise-distinctness premise is imposed on the source datum.
-/

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 3000000

open Set MeasureTheory
open scoped ENNReal NNReal BigOperators

namespace Family8ScaleContainedB2NativeFreshKatzTaoEndpointV1

open LeanEval.Analysis.WangZahlKakeya
open Submission.Kakeya.ConvexGeometry
open Submission.Kakeya.ConvexFactoring
open Family8KatzTaoFrostmanPropertiesV1
open Family8GeneralizedKatzTaoMultiplicityV1
open Family8FiniteRandomRigidMotionB2NormalizedDatumV1
open Family8FiniteRandomRigidMotionB2FreshGreedyV1
open Family8FiniteRandomRigidMotionPaperFixedJohnFreshSelectionV2
open Family8FrozenCoarseB2DensityTransportScaleOnlyV1
open Family8RestrictedActualDatumDensityRetentionV1
open Family8B2NormalizedConflictKatzTaoCapV6

noncomputable section

/-- The fixed conflict threshold attached to a finite source Katz--Tao
constant. -/
def sourceKatzTaoConflictThreshold (C : ENNReal) : Nat :=
  Nat.ceil ((480000 * (128 * C) : ENNReal).toReal)

/-- The corresponding closed-neighbourhood loss of fresh greedy selection. -/
def sourceKatzTaoFreshLoss (C : ENNReal) : Nat :=
  sourceKatzTaoConflictThreshold C + 1

theorem sourceKatzTaoFreshLoss_pos (C : ENNReal) :
    0 < sourceKatzTaoFreshLoss C := by
  unfold sourceKatzTaoFreshLoss
  omega

/-- Apply a genuine Katz--Tao parameter theorem to a fresh admissible subtype
of a possibly non-admissible B2-supported source.  The displayed density and
coefficient premises are the exact costs of normalization and selection. -/
theorem exists_fresh_apply_katzTaoAtParameters_of_scale_contained_B2
    {beta epsilon eta : Real} {delta0 delta : NNReal}
    {iota : Type} [Fintype iota] [Nonempty iota] [DecidableEq iota]
    (hKTP : KatzTaoAtParameters beta epsilon eta delta0)
    (D : ActualTubeDatum delta iota)
    (hdeltaPos : 0 < delta)
    (hdeltaHalf : delta <= (2 : NNReal)⁻¹)
    (hB2 : forall i,
      (D.family.tubes i).carrier ⊆ Metric.closedBall (0 : Space) 2)
    {C : ENNReal} (hCfinite : C ≠ ∞)
    (hKT : IsKatzTao C D.family.bodyFamily)
    (hdelta0 : delta / 8 <= delta0)
    (hdensityBudget :
      (((delta / 8 : NNReal) : ENNReal) ^ eta) *
          (128 * (sourceKatzTaoFreshLoss C : ENNReal)) <=
        D.shading.shadingDensity)
    (hcoefficient :
      128 * C <= ((delta / 8 : NNReal) : ENNReal) ^ (-eta)) :
    exists selected : Finset iota,
      selected.Nonempty ∧
      selected.card <= Fintype.card iota ∧
      D.shading.averageMultiplicity <=
        (sourceKatzTaoFreshLoss C : ENNReal) *
          katzTaoMultiplicityRHS (delta / 8) selected.card epsilon beta := by
  let threshold := sourceKatzTaoConflictThreshold C
  let loss := sourceKatzTaoFreshLoss C
  have hconflict : forall a,
      (normalizedConflictIndices D a).card <= threshold := by
    intro a
    exact normalizedConflictIndices_card_le_sourceFixedKatzTaoNatCap
      D hdeltaPos hdeltaHalf hCfinite hKT a
  obtain ⟨selected, hselected, hadmissible, _hcard, hmass,
      hselectedKT, hsourceAverage⟩ :=
    exists_normalized_refinement_admissible_isKatzTao_of_scale_B2
      D hdeltaPos hdeltaHalf hB2 hconflict hKT
  let refined := restrictActualTubeDatum (eighthNormalizedDatum D) selected
  have hlossEq : threshold + 1 = loss := by
    rfl
  have hlossPos : 0 < loss := by
    simpa only [loss] using sourceKatzTaoFreshLoss_pos C
  have hloss0 : (loss : ENNReal) ≠ 0 := by
    simp [hlossPos.ne']
  have hlossTop : (loss : ENNReal) ≠ ∞ := ENNReal.coe_ne_top
  have hnormalizedDensity :
      D.shading.shadingDensity / 128 <=
        (eighthNormalizedDatum D).shading.shadingDensity :=
    source_shadingDensity_div_128_le_eighthNormalized_of_scale
      D hdeltaPos hdeltaHalf
  have hrefinedDensity :
      (eighthNormalizedDatum D).shading.shadingDensity / (loss : ENNReal) <=
        refined.shading.shadingDensity := by
    apply source_shadingDensity_div_loss_le_restrictActualTubeDatum
    simpa only [refined, loss, threshold, hlossEq] using hmass
  have hbudgetDiv :
      ((delta / 8 : NNReal) : ENNReal) ^ eta <=
        D.shading.shadingDensity / 128 / (loss : ENNReal) := by
    apply (ENNReal.le_div_iff_mul_le
      (Or.inl hloss0) (Or.inl hlossTop)).2
    apply (ENNReal.le_div_iff_mul_le
      (Or.inl (by norm_num : (128 : ENNReal) ≠ 0))
      (Or.inl (by norm_num : (128 : ENNReal) ≠ ∞))).2
    calc
      (((delta / 8 : NNReal) : ENNReal) ^ eta *
          (loss : ENNReal)) * 128 =
        ((delta / 8 : NNReal) : ENNReal) ^ eta *
          (128 * (sourceKatzTaoFreshLoss C : ENNReal)) := by
            dsimp only [loss]
            ac_rfl
      _ <= D.shading.shadingDensity := hdensityBudget
  have hselectedDensity :
      ((delta / 8 : NNReal) : ENNReal) ^ eta <=
        refined.shading.shadingDensity := by
    exact hbudgetDiv.trans
      ((ENNReal.div_le_div_right hnormalizedDensity (loss : ENNReal)).trans
        hrefinedDensity)
  have hselectedHyp : KatzTaoHypotheses refined eta := by
    refine ⟨hselectedDensity, ?_⟩
    rw [maximalConcentration_le_iff_isKatzTao]
    exact hselectedKT.mono hcoefficient
  have hselectedBound :=
    KatzTaoAtParameters.apply hKTP refined hadmissible hdelta0 hselectedHyp
  refine ⟨selected, hselected, Finset.card_le_univ selected, ?_⟩
  have hsourceAverage' :
      D.shading.averageMultiplicity <=
        (loss : ENNReal) * refined.shading.averageMultiplicity := by
    simpa only [loss, threshold, hlossEq, refined] using hsourceAverage
  have hscaled :
      (loss : ENNReal) * refined.shading.averageMultiplicity <=
        (loss : ENNReal) *
          katzTaoMultiplicityRHS (delta / 8) selected.card epsilon beta := by
    gcongr
    simpa using hselectedBound
  exact hsourceAverage'.trans (by simpa only [loss] using hscaled)

#print axioms sourceKatzTaoFreshLoss_pos
#print axioms
  exists_fresh_apply_katzTaoAtParameters_of_scale_contained_B2

end
end Family8ScaleContainedB2NativeFreshKatzTaoEndpointV1
