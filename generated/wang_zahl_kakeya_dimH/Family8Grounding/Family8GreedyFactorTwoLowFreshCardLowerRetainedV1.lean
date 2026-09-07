import Family8Grounding.Family8GreedyFactorTwoLowFreshRetainedV2
import Family8Grounding.Family8ActualFamilyVolumePackingV1
import Family8Grounding.Family8SharpKatzTaoOrGreedyHighConcentrationV1
import Family8Grounding.Family8Prop66AFrostmanAspectGainAlgebraV1
import Mathlib.Tactic

/-!
# Factor-two low fresh selection retaining the literal card lower bound

The existing fresh endpoint keeps only `selectedFresh.card <= selectedLow.card`.
The underlying conflict-greedy theorem also proves the reverse comparison up
to its literal loss, and proves normalized shading-mass retention for the
same selected set.  This module retains those two facts without rerunning the
selection.

The retained card comparison gives the honest same-object lower estimate

`sourceMass <= 16 * freshLoss * (delta^2 * selectedFresh.card)`.

No ambient/global cardinality bound and no all-scale Katz--Tao hypothesis is
introduced.  The final power lemma keeps the source mass floor, the fresh-loss
power envelope, the fixed-constant absorption, and the exponent ledger as
four separate explicit premises.
-/

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 4000000

open Set MeasureTheory
open scoped BigOperators ENNReal NNReal

namespace Family8GreedyFactorTwoLowFreshCardLowerRetainedV1

open LeanEval.Analysis.WangZahlKakeya
open Submission.Kakeya.ConvexGeometry
open Submission.Kakeya.ConvexFactoring
open Submission.Kakeya.ConvexFactoring.FullConvexMaximalDensity
open Submission.Kakeya.ConvexFactoring.GreedyOccurrenceFactorization
open Submission.Kakeya.ConvexFactoring.GreedyDensityBucketing
open Submission.Kakeya.Uniformity
open Family8ActualFamilyVolumePackingV1
open Family8B2NormalizedConflictKatzTaoCapV6
open Family8FiniteRandomRigidMotionB2FreshGreedyV1
open Family8FiniteRandomRigidMotionB2NormalizedDatumV1
open Family8FiniteRandomRigidMotionPaperFixedJohnFreshSelectionV2
open Family8FrozenCoarseB2DensityTransportScaleOnlyV1
open Family8GeneralizedKatzTaoMultiplicityV1
open Family8GreedyFactorTwoLowFreshRetainedV2
open Family8GreedyHighPrefixActualOccurrenceV1
open Family8KatzTaoFrostmanPropertiesV1
open Family8RestrictedActualDatumDensityRetentionV1
open Family8ScaleContainedB2NativeFreshKatzTaoEndpointV1
open Family8SharpKatzTaoOrGreedyHighConcentrationV1
open Family8Prop66AFrostmanAspectGainAlgebraV1

noncomputable section

/-- Pure ENNReal cancellation used below.  It is kept local so retaining the
fresh-selector card lower bound does not pull in the unrelated sticky-chain
module where the same scalar calculation was first proved. -/
private theorem rpow_le_of_massLoss_powerEnvelopes
    {d : NNReal} {loss C mass X : ENNReal}
    {sourceExponent lossExponent targetExponent absorbExponent : Real}
    (hd : 0 < d) (hdOne : d ≤ 1)
    (hloss : loss ≤ C * (d : ENNReal) ^ (-lossExponent))
    (hC : 8 * C ≤ (d : ENNReal) ^ (-absorbExponent))
    (hexponent :
      sourceExponent ≤ targetExponent - lossExponent - absorbExponent)
    (hmassLower : (d : ENNReal) ^ sourceExponent ≤ mass)
    (hmassUpper : mass ≤ loss * (8 * X)) :
    (d : ENNReal) ^ targetExponent ≤ X := by
  have hd0 : (d : ENNReal) ≠ 0 := ENNReal.coe_ne_zero.mpr hd.ne'
  have hdTop : (d : ENNReal) ≠ ∞ := ENNReal.coe_ne_top
  have hdOneENN : (d : ENNReal) ≤ 1 := by exact_mod_cast hdOne
  have hcoefficient : loss * 8 ≤
      (d : ENNReal) ^ (-(lossExponent + absorbExponent)) := by
    calc
      loss * 8 ≤ (C * (d : ENNReal) ^ (-lossExponent)) * 8 :=
        mul_le_mul' hloss le_rfl
      _ = (8 * C) * (d : ENNReal) ^ (-lossExponent) := by ring
      _ ≤ (d : ENNReal) ^ (-absorbExponent) *
          (d : ENNReal) ^ (-lossExponent) := mul_le_mul' hC le_rfl
      _ = (d : ENNReal) ^ (-(lossExponent + absorbExponent)) := by
        rw [show -(lossExponent + absorbExponent) =
          -absorbExponent + -lossExponent by ring,
          ENNReal.rpow_add _ _ hd0 hdTop]
  have hmassToX : (d : ENNReal) ^ sourceExponent ≤
      (d : ENNReal) ^ (-(lossExponent + absorbExponent)) * X := by
    calc
      (d : ENNReal) ^ sourceExponent ≤ mass := hmassLower
      _ ≤ loss * (8 * X) := hmassUpper
      _ = (loss * 8) * X := by ring
      _ ≤ (d : ENNReal) ^ (-(lossExponent + absorbExponent)) * X :=
        mul_le_mul' hcoefficient le_rfl
  have hexponent' :
      sourceExponent + (lossExponent + absorbExponent) ≤ targetExponent := by
    linarith
  calc
    (d : ENNReal) ^ targetExponent ≤
        (d : ENNReal) ^
          (sourceExponent + (lossExponent + absorbExponent)) :=
      ENNReal.rpow_le_rpow_of_exponent_ge hdOneENN hexponent'
    _ = (d : ENNReal) ^ (lossExponent + absorbExponent) *
        (d : ENNReal) ^ sourceExponent := by
      rw [show sourceExponent + (lossExponent + absorbExponent) =
        (lossExponent + absorbExponent) + sourceExponent by ring,
        ENNReal.rpow_add _ _ hd0 hdTop]
    _ ≤ (d : ENNReal) ^ (lossExponent + absorbExponent) *
        ((d : ENNReal) ^ (-(lossExponent + absorbExponent)) * X) :=
      mul_le_mul' le_rfl hmassToX
    _ = X := by
      rw [← mul_assoc, ← ENNReal.rpow_add _ _ hd0 hdTop]
      norm_num

/-- The factor-two low restriction and its one fresh child, retaining both
cardinality directions and the normalized mass comparison produced by the
literal underlying fresh selector. -/
def RetainedFactorTwoFreshLowWithCardLower
    {delta : NNReal} {index : Type}
    [Fintype index] [DecidableEq index]
    (D : ActualTubeDatum delta index) (A : ENNReal)
    (epsilon beta : Real) : Prop :=
  exists selectedLow : Finset index,
    D.shading.shadingMass <= 2 *
      (restrictActualTubeDatum D selectedLow).shading.shadingMass /\
    (restrictActualTubeDatum D selectedLow).IsAdmissible /\
    IsKatzTao A
      (restrictActualTubeDatum D selectedLow).family.bodyFamily /\
    exists selectedFresh : Finset {i // i ∈ selectedLow},
      selectedFresh.Nonempty /\
      selectedFresh.card <= selectedLow.card /\
      (selectedLow.card : ENNReal) <=
        (sourceKatzTaoFreshLoss A : ENNReal) *
          (selectedFresh.card : ENNReal) /\
      (eighthNormalizedDatum
          (restrictActualTubeDatum D selectedLow)).shading.shadingMass <=
        (sourceKatzTaoFreshLoss A : ENNReal) *
          (restrictActualTubeDatum
            (eighthNormalizedDatum
              (restrictActualTubeDatum D selectedLow))
            selectedFresh).shading.shadingMass /\
      D.shading.averageMultiplicity <=
        (2 * (sourceKatzTaoFreshLoss A : ENNReal)) *
          katzTaoMultiplicityRHS
            (delta / 8) selectedFresh.card epsilon beta

/-- The B2-native fresh endpoint with the two facts erased by its previous
public wrapper restored.  The selected set is the one returned by
`exists_normalized_refinement_admissible_isKatzTao_of_scale_B2`; no second
choice is made. -/
theorem exists_fresh_apply_katzTaoAtParameters_with_cardLower_and_mass
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
      selected.Nonempty /\
      selected.card <= Fintype.card iota /\
      (Fintype.card iota : ENNReal) <=
        (sourceKatzTaoFreshLoss C : ENNReal) *
          (selected.card : ENNReal) /\
      (eighthNormalizedDatum D).shading.shadingMass <=
        (sourceKatzTaoFreshLoss C : ENNReal) *
          (restrictActualTubeDatum
            (eighthNormalizedDatum D) selected).shading.shadingMass /\
      D.shading.averageMultiplicity <=
        (sourceKatzTaoFreshLoss C : ENNReal) *
          katzTaoMultiplicityRHS
            (delta / 8) selected.card epsilon beta := by
  let threshold := sourceKatzTaoConflictThreshold C
  let loss := sourceKatzTaoFreshLoss C
  have hconflict : forall a,
      (normalizedConflictIndices D a).card <= threshold := by
    intro a
    exact normalizedConflictIndices_card_le_sourceFixedKatzTaoNatCap
      D hdeltaPos hdeltaHalf hCfinite hKT a
  obtain ⟨selected, hselected, hadmissible, hcardLower, hmass,
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
      (eighthNormalizedDatum D).shading.shadingDensity /
          (loss : ENNReal) <= refined.shading.shadingDensity := by
    exact source_shadingDensity_div_loss_le_restrictActualTubeDatum
      (eighthNormalizedDatum D) selected (loss : ENNReal)
        (by simpa only [loss, threshold, hlossEq] using hmass)
  have hbudgetDiv :
      ((delta / 8 : NNReal) : ENNReal) ^ eta <=
        D.shading.shadingDensity / 128 / (loss : ENNReal) := by
    apply (ENNReal.le_div_iff_mul_le
      (Or.inl hloss0) (Or.inl hlossTop)).2
    apply (ENNReal.le_div_iff_mul_le
      (Or.inl (by norm_num : (128 : ENNReal) ≠ 0))
      (Or.inl (by norm_num : (128 : ENNReal) ≠ ∞))).2
    calc
      ((((delta / 8 : NNReal) : ENNReal) ^ eta *
          (loss : ENNReal)) * 128) =
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
  have hsourceAverage' :
      D.shading.averageMultiplicity <=
        (loss : ENNReal) * refined.shading.averageMultiplicity := by
    simpa only [loss, threshold, hlossEq, refined] using hsourceAverage
  refine ⟨selected, hselected, Finset.card_le_univ selected, ?_, ?_, ?_⟩
  · simpa only [loss, threshold, hlossEq] using hcardLower
  · simpa only [loss, threshold, hlossEq] using hmass
  · calc
      D.shading.averageMultiplicity <=
          (loss : ENNReal) * refined.shading.averageMultiplicity :=
        hsourceAverage'
      _ <= (loss : ENNReal) *
          katzTaoMultiplicityRHS
            (delta / 8) selected.card epsilon beta := by
        gcongr
        simpa only [refined, Fintype.card_coe] using hselectedBound
      _ = (sourceKatzTaoFreshLoss C : ENNReal) *
          katzTaoMultiplicityRHS
            (delta / 8) selected.card epsilon beta := by rfl

/-- Run the strengthened fresh selector on the one literal factor-two low
restriction. -/
theorem retainedFactorTwoFreshLowWithCardLower_of_lowRestriction
    {beta epsilon eta : Real} {delta0 delta : NNReal}
    {index : Type} [Fintype index] [DecidableEq index]
    (hKTP : KatzTaoAtParameters beta epsilon eta delta0)
    (D : ActualTubeDatum delta index)
    (selectedLow : Finset index)
    (hmass : D.shading.shadingMass <= 2 *
      (restrictActualTubeDatum D selectedLow).shading.shadingMass)
    (hDlow : (restrictActualTubeDatum D selectedLow).IsAdmissible)
    (A : ENNReal)
    (hKTlow : IsKatzTao A
      (restrictActualTubeDatum D selectedLow).family.bodyFamily)
    (hdelta0 : delta / 8 <= delta0)
    (hdensityBudget :
      (((delta / 8 : NNReal) : ENNReal) ^ eta) *
          (2 * (128 * (sourceKatzTaoFreshLoss A : ENNReal))) <=
        D.shading.shadingDensity)
    (hcoefficient :
      128 * A <= ((delta / 8 : NNReal) : ENNReal) ^ (-eta)) :
    RetainedFactorTwoFreshLowWithCardLower D A epsilon beta := by
  let Dlow := restrictActualTubeDatum D selectedLow
  have hscalePos : 0 < (((delta / 8 : NNReal) : ENNReal)) :=
    ENNReal.coe_pos.mpr (div_pos hDlow.delta_pos (by norm_num))
  have hpowerPos :
      0 < ((delta / 8 : NNReal) : ENNReal) ^ eta :=
    ENNReal.rpow_pos hscalePos ENNReal.coe_ne_top
  have hlossPos : 0 < (sourceKatzTaoFreshLoss A : ENNReal) := by
    exact_mod_cast sourceKatzTaoFreshLoss_pos A
  have hdensityPos : 0 < D.shading.shadingDensity := by
    have hproductPos :
        0 < (((delta / 8 : NNReal) : ENNReal) ^ eta) *
          (2 * (128 * (sourceKatzTaoFreshLoss A : ENNReal))) := by
      positivity
    exact hproductPos.trans_le hdensityBudget
  have hsourceMassNe : D.shading.shadingMass ≠ 0 := by
    intro hzero
    have hdensityZero : D.shading.shadingDensity = 0 := by
      simp [Shading.shadingDensity, hzero]
    rw [hdensityZero] at hdensityPos
    exact (lt_irrefl 0) hdensityPos
  have hlowMassNe : Dlow.shading.shadingMass ≠ 0 := by
    intro hzero
    apply hsourceMassNe
    apply nonpos_iff_eq_zero.mp
    have hsourceNonpos : D.shading.shadingMass <= 0 := by
      simpa only [Dlow, hzero, mul_zero] using hmass
    exact hsourceNonpos
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
  have hA_le_power :
      A <= ((delta / 8 : NNReal) : ENNReal) ^ (-eta) := by
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
  obtain ⟨selectedFresh, hselectedFresh, hcardUpper, hcardLower,
      hnormalizedMass, hboundLow⟩ :=
    exists_fresh_apply_katzTaoAtParameters_with_cardLower_and_mass
      hKTP Dlow hDlow.delta_pos hDlow.delta_le_half hB2 hAfin hKTlow
        hdelta0 hdensityLow hcoefficient
  refine ⟨selectedLow, hmass, hDlow, hKTlow, selectedFresh,
    hselectedFresh, ?_, ?_, ?_, ?_⟩
  · simpa only [Fintype.card_coe] using hcardUpper
  · simpa only [Fintype.card_coe] using hcardLower
  · exact hnormalizedMass
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

/-- The literal greedy low/high split with the strengthened fresh bundle on
the low branch.  The underlying dichotomy chooses `selectedLow` once, and
the strengthened selector chooses `selectedFresh` once on that restriction;
the high branch is returned unchanged. -/
theorem retainedFactorTwoFreshLowWithCardLower_or_actualHighOccurrencePrefix
    {beta epsilon eta : Real} {delta0 delta : NNReal}
    {index : Type} [Fintype index] [DecidableEq index]
    (hKTP : KatzTaoAtParameters beta epsilon eta delta0)
    (D : ActualTubeDatum delta index) (hD : D.IsAdmissible)
    (A : ENNReal)
    (hdelta0 : delta / 8 <= delta0)
    (hdensityBudget :
      (((delta / 8 : NNReal) : ENNReal) ^ eta) *
          (2 * (128 * (sourceKatzTaoFreshLoss A : ENNReal))) <=
        D.shading.shadingDensity)
    (hcoefficient :
      128 * A <= ((delta / 8 : NNReal) : ENNReal) ^ (-eta)) :
    RetainedFactorTwoFreshLowWithCardLower D A epsilon beta ∨
      ∃ P : GreedyDensityPartition D.family.bodyFamily
          (hullCandidates (Finset.univ : Finset index))
          (hullContainer D.family.bodyFamily) Finset.univ,
        ∃ selected : Finset index,
          D.shading.shadingMass <= 2 *
            (restrictActualTubeDatum D selected).shading.shadingMass ∧
          D.shading.averageMultiplicity <= 2 *
            (restrictActualTubeDatum D selected).shading.averageMultiplicity ∧
          (restrictActualTubeDatum D selected).IsAdmissible ∧
          ∀ i ∈ selected,
            ∃ q : Fin (blocks D.family.bodyFamily P).length,
              i ∈ (blockAt D.family.bodyFamily P q).fiber ∧
              ActualHighConcentrationOccurrence D P A q := by
  rcases
      Family8GreedyHighPrefixActualOccurrenceV1.exists_factorTwo_lowKatzTaoRestriction_or_actualHighOccurrencePrefix
        D hD A with hlow | hhigh
  · left
    obtain ⟨selectedLow, hmass, _haverage, hDlow, hKTlow⟩ := hlow
    exact retainedFactorTwoFreshLowWithCardLower_of_lowRestriction
      hKTP D selectedLow hmass hDlow A hKTlow hdelta0
        hdensityBudget hcoefficient
  · exact Or.inr hhigh

/-- Raw same-selectedFresh mass-to-card-scale comparison.  This uses the
retained ambient-to-fresh card comparison; the normalized mass field is kept
for downstream consumers but is not needed for this sharper constant. -/
theorem sourceMass_le_sixteen_freshLoss_mul_freshCardScale
    {delta : NNReal} {index : Type}
    [Fintype index] [DecidableEq index]
    (D : ActualTubeDatum delta index)
    (selectedLow : Finset index)
    (hmass : D.shading.shadingMass <= 2 *
      (restrictActualTubeDatum D selectedLow).shading.shadingMass)
    (hDlow : (restrictActualTubeDatum D selectedLow).IsAdmissible)
    (A : ENNReal)
    (selectedFresh : Finset {i // i ∈ selectedLow})
    (hcardLower : (selectedLow.card : ENNReal) <=
      (sourceKatzTaoFreshLoss A : ENNReal) *
        (selectedFresh.card : ENNReal)) :
    D.shading.shadingMass <=
      16 * (sourceKatzTaoFreshLoss A : ENNReal) *
        proposition66ACardScaleVolume delta selectedFresh.card := by
  let Dlow := restrictActualTubeDatum D selectedLow
  have hvolume : Dlow.actualFamilyVolume <=
      (selectedLow.card : ENNReal) * (8 * (delta : ENNReal) ^ 2) := by
    simpa only [Dlow, Fintype.card_coe] using
      actualFamilyVolume_le_card_mul_eight_sq Dlow hDlow.delta_le_half
  calc
    D.shading.shadingMass <= 2 * Dlow.shading.shadingMass := by
      simpa only [Dlow] using hmass
    _ <= 2 * Dlow.actualFamilyVolume :=
      mul_le_mul' le_rfl Dlow.shading.shadingMass_le_familyVolume
    _ <= 2 * ((selectedLow.card : ENNReal) *
        (8 * (delta : ENNReal) ^ 2)) := mul_le_mul' le_rfl hvolume
    _ <= 2 * (((sourceKatzTaoFreshLoss A : ENNReal) *
          (selectedFresh.card : ENNReal)) *
        (8 * (delta : ENNReal) ^ 2)) := by
      gcongr
    _ = 16 * (sourceKatzTaoFreshLoss A : ENNReal) *
        proposition66ACardScaleVolume delta selectedFresh.card := by
      unfold proposition66ACardScaleVolume
      ring

/-- The weakest power form of the previous raw comparison.  Every analytic
cost remains a separate premise. -/
theorem freshCardScale_powerLower_of_sourceMass_and_freshLoss
    {delta : NNReal} {index : Type}
    [Fintype index] [DecidableEq index]
    (D : ActualTubeDatum delta index)
    (selectedLow : Finset index)
    (hmass : D.shading.shadingMass <= 2 *
      (restrictActualTubeDatum D selectedLow).shading.shadingMass)
    (hDlow : (restrictActualTubeDatum D selectedLow).IsAdmissible)
    (A : ENNReal)
    (selectedFresh : Finset {i // i ∈ selectedLow})
    (hcardLower : (selectedLow.card : ENNReal) <=
      (sourceKatzTaoFreshLoss A : ENNReal) *
        (selectedFresh.card : ENNReal))
    {sourceExponent lossExponent absorbExponent etaPrime : Real}
    (hsourceMass : (delta : ENNReal) ^ sourceExponent <=
      D.shading.shadingMass)
    (hloss : (sourceKatzTaoFreshLoss A : ENNReal) <=
      (delta : ENNReal) ^ (-lossExponent))
    (hconstant : (16 : ENNReal) <=
      (delta : ENNReal) ^ (-absorbExponent))
    (hexponent :
      sourceExponent + lossExponent + absorbExponent <= etaPrime) :
    (delta : ENNReal) ^ etaPrime <=
      proposition66ACardScaleVolume delta selectedFresh.card := by
  have hraw := sourceMass_le_sixteen_freshLoss_mul_freshCardScale
    D selectedLow hmass hDlow A selectedFresh hcardLower
  have hloss' :
      2 * (sourceKatzTaoFreshLoss A : ENNReal) <=
        2 * (delta : ENNReal) ^ (-lossExponent) :=
    mul_le_mul' le_rfl hloss
  have hconstant' :
      8 * (2 : ENNReal) <= (delta : ENNReal) ^ (-absorbExponent) := by
    simpa only [show (8 : ENNReal) * 2 = 16 by norm_num] using hconstant
  have hexponent' :
      sourceExponent <= etaPrime - lossExponent - absorbExponent := by
    linarith
  apply rpow_le_of_massLoss_powerEnvelopes
      hDlow.delta_pos (hDlow.delta_le_half.trans (by norm_num))
      hloss' hconstant' hexponent' hsourceMass
  calc
    D.shading.shadingMass <=
        16 * (sourceKatzTaoFreshLoss A : ENNReal) *
          proposition66ACardScaleVolume delta selectedFresh.card := hraw
    _ = (2 * (sourceKatzTaoFreshLoss A : ENNReal)) *
        (8 * proposition66ACardScaleVolume delta selectedFresh.card) := by
      ring

#print axioms RetainedFactorTwoFreshLowWithCardLower
#print axioms exists_fresh_apply_katzTaoAtParameters_with_cardLower_and_mass
#print axioms retainedFactorTwoFreshLowWithCardLower_of_lowRestriction
#print axioms
  retainedFactorTwoFreshLowWithCardLower_or_actualHighOccurrencePrefix
#print axioms sourceMass_le_sixteen_freshLoss_mul_freshCardScale
#print axioms freshCardScale_powerLower_of_sourceMass_and_freshLoss

end
end Family8GreedyFactorTwoLowFreshCardLowerRetainedV1
