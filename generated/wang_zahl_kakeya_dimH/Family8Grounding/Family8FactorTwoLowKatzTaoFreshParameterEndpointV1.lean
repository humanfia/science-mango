import Family8Grounding.Family8GreedyHighPrefixActualOccurrenceV1
import Family8Grounding.Family8ScaleContainedB2NativeFreshKatzTaoEndpointV1
import Family8Grounding.Family8RestrictedActualDatumDensityRetentionV1
import Mathlib.Tactic

/-!
# Factor-two low Katz--Tao restriction to a fresh parameter bound

The low branch of the honest greedy dichotomy already supplies one literal
restriction, its factor-two mass and average transport, admissibility, and a
sharp Katz--Tao constant.  This file feeds that exact restricted datum to the
existing B2-native fresh endpoint.  Pairwise distinctness and the second
fresh subtype are constructed internally; no certificate for the ambient
datum is requested.
-/

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 3000000

open Set MeasureTheory
open scoped BigOperators ENNReal NNReal

namespace Family8FactorTwoLowKatzTaoFreshParameterEndpointV1

open LeanEval.Analysis.WangZahlKakeya
open Submission.Kakeya.ConvexGeometry
open Submission.Kakeya.ConvexFactoring
open Family8KatzTaoFrostmanPropertiesV1
open Family8GeneralizedKatzTaoMultiplicityV1
open Family8SharpKatzTaoOrGreedyHighConcentrationV1
open Family8GreedyHighPrefixActualOccurrenceV1
open Family8RestrictedActualDatumDensityRetentionV1
open Family8ScaleContainedB2NativeFreshKatzTaoEndpointV1

noncomputable section

/-- The exact low-branch connector.  The only analytic input not already in
the greedy low witness is the complete source-density product budget. -/
theorem exists_fresh_katzTaoParameter_bound_of_factorTwo_lowRestriction
    {beta epsilon eta : Real} {delta0 delta : NNReal}
    {iota : Type} [Fintype iota] [DecidableEq iota]
    (hKTP : KatzTaoAtParameters beta epsilon eta delta0)
    (D : ActualTubeDatum delta iota)
    (selectedLow : Finset iota)
    (hmass : D.shading.shadingMass <= 2 *
      (restrictActualTubeDatum D selectedLow).shading.shadingMass)
    (hDlow : (restrictActualTubeDatum D selectedLow).IsAdmissible)
    {A : ENNReal}
    (hKTlow : IsKatzTao A
      (restrictActualTubeDatum D selectedLow).family.bodyFamily)
    (hdelta0 : delta / 8 <= delta0)
    (hdensityBudget :
      (((delta / 8 : NNReal) : ENNReal) ^ eta) *
          (2 * (128 * (sourceKatzTaoFreshLoss A : ENNReal))) <=
        D.shading.shadingDensity)
    (hcoefficient :
      128 * A <= ((delta / 8 : NNReal) : ENNReal) ^ (-eta)) :
    exists selectedFresh : Finset {i // i ∈ selectedLow},
      selectedFresh.Nonempty /\
      selectedFresh.card <= selectedLow.card /\
      D.shading.averageMultiplicity <=
        (2 * (sourceKatzTaoFreshLoss A : ENNReal)) *
          katzTaoMultiplicityRHS
            (delta / 8) selectedFresh.card epsilon beta := by
  let Dlow := restrictActualTubeDatum D selectedLow
  have hscalePosNN : 0 < delta / 8 :=
    div_pos hDlow.delta_pos (by norm_num)
  have hscalePos : 0 < (((delta / 8 : NNReal) : ENNReal)) :=
    ENNReal.coe_pos.mpr hscalePosNN
  have hpowerPos :
      0 < ((delta / 8 : NNReal) : ENNReal) ^ eta :=
    ENNReal.rpow_pos hscalePos ENNReal.coe_ne_top
  have hlossPos : 0 < (sourceKatzTaoFreshLoss A : ENNReal) := by
    exact_mod_cast sourceKatzTaoFreshLoss_pos A
  have hdensityPos : 0 < D.shading.shadingDensity := by
    have hproductPos :
        0 < (((delta / 8 : NNReal) : ENNReal) ^ eta) *
          (2 * (128 * (sourceKatzTaoFreshLoss A : ENNReal))) := by positivity
    exact hproductPos.trans_le hdensityBudget
  have hsourceMassNe : D.shading.shadingMass ≠ 0 := by
    intro hzero
    have hdensityZero : D.shading.shadingDensity = 0 := by
      simp [Shading.shadingDensity, hzero]
    rw [hdensityZero] at hdensityPos
    exact (lt_irrefl 0) hdensityPos
  have hlowMassNe : Dlow.shading.shadingMass ≠ 0 := by
    intro hzero
    have hsourceZero : D.shading.shadingMass = 0 := by
      apply nonpos_iff_eq_zero.mp
      have hsourceNonpos : D.shading.shadingMass <= 0 := by
        simpa only [Dlow, hzero, mul_zero] using hmass
      exact hsourceNonpos
    exact hsourceMassNe hsourceZero
  have hselectedLow : selectedLow.Nonempty := by
    by_contra hempty
    have hselectedEmpty : selectedLow = ∅ :=
      Finset.not_nonempty_iff_eq_empty.mp hempty
    apply hlowMassNe
    simp [Dlow, hselectedEmpty, Shading.shadingMass]
  let _ : Nonempty {i // i ∈ selectedLow} :=
    Finset.nonempty_coe_sort.mpr hselectedLow
  have hB2 : forall i,
      (Dlow.family.tubes i).carrier ⊆ Metric.closedBall (0 : Space) 2 := by
    intro i
    exact (hDlow.contained_in_unit_ball i).trans
      (Metric.closedBall_subset_closedBall (by norm_num))
  have hpowerTop :
      ((delta / 8 : NNReal) : ENNReal) ^ (-eta) ≠ ∞ :=
    ENNReal.rpow_ne_top_of_ne_zero hscalePos.ne' ENNReal.coe_ne_top
  have hA_le_power : A <=
      ((delta / 8 : NNReal) : ENNReal) ^ (-eta) := by
    calc
      A = 1 * A := by simp
      _ <= 128 * A := by gcongr; norm_num
      _ <= ((delta / 8 : NNReal) : ENNReal) ^ (-eta) := hcoefficient
  have hAfin : A ≠ ∞ := ne_top_of_le_ne_top hpowerTop hA_le_power
  have hretainedDensity :
      D.shading.shadingDensity / 2 <= Dlow.shading.shadingDensity := by
    simpa only [Dlow] using
      source_shadingDensity_div_loss_le_restrictActualTubeDatum
        D selectedLow (2 : ENNReal) hmass
  have hdensityLow :
      (((delta / 8 : NNReal) : ENNReal) ^ eta) *
          (128 * (sourceKatzTaoFreshLoss A : ENNReal)) <=
        Dlow.shading.shadingDensity := by
    apply le_trans ?_ hretainedDensity
    apply (ENNReal.le_div_iff_mul_le
      (Or.inl (by norm_num : (2 : ENNReal) ≠ 0))
      (Or.inl (by norm_num : (2 : ENNReal) ≠ ∞))).2
    calc
      ((((delta / 8 : NNReal) : ENNReal) ^ eta) *
          (128 * (sourceKatzTaoFreshLoss A : ENNReal))) * 2 =
          (((delta / 8 : NNReal) : ENNReal) ^ eta) *
            (2 * (128 * (sourceKatzTaoFreshLoss A : ENNReal))) := by
              ac_rfl
      _ <= D.shading.shadingDensity := hdensityBudget
  obtain ⟨selectedFresh, hselectedFresh, hcardFresh, hboundLow⟩ :=
    exists_fresh_apply_katzTaoAtParameters_of_scale_contained_B2
      hKTP Dlow hDlow.delta_pos hDlow.delta_le_half hB2 hAfin hKTlow
        hdelta0 hdensityLow hcoefficient
  refine ⟨selectedFresh, hselectedFresh, ?_, ?_⟩
  · simpa only [Fintype.card_coe] using hcardFresh
  · calc
      D.shading.averageMultiplicity <=
          2 * Dlow.shading.averageMultiplicity := by
            simpa only [Dlow] using
              source_averageMultiplicity_le_loss_mul_restrictActualTubeDatum
                D selectedLow (2 : ENNReal) hmass
      _ <= 2 * ((sourceKatzTaoFreshLoss A : ENNReal) *
          katzTaoMultiplicityRHS
            (delta / 8) selectedFresh.card epsilon beta) := by
            gcongr
      _ = (2 * (sourceKatzTaoFreshLoss A : ENNReal)) *
          katzTaoMultiplicityRHS
            (delta / 8) selectedFresh.card epsilon beta := by ac_rfl

#print axioms
  exists_fresh_katzTaoParameter_bound_of_factorTwo_lowRestriction

end
end Family8FactorTwoLowKatzTaoFreshParameterEndpointV1
