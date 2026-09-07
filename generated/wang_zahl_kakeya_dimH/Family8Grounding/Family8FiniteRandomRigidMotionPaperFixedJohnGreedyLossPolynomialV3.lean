import Family8Grounding.Family8FiniteRandomRigidMotionPaperFixedJohnGreedyLossEnvelopeV3
import Family8Grounding.Family8PolynomialJohnFrameBoxCardPowerV1
import Mathlib.Tactic

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 4000000

open Set MeasureTheory
open scoped ENNReal NNReal BigOperators InnerProductSpace

namespace Family8FiniteRandomRigidMotionPaperFixedJohnGreedyLossPolynomialV3

open LeanEval.Analysis.WangZahlKakeya
open Submission.Kakeya.ConvexGeometry
open Family8KatzTaoFrostmanPropertiesV1
open Family8PolynomialJohnFrameBoxTestNetV1
open Family8PolynomialJohnFrameBoxCardPowerV1
open Family8FiniteRandomRigidMotionPaperFixedJohnAutomaticConflictCapV2
open Family8FiniteRandomRigidMotionPaperFixedJohnExactMeanSelectorV4
open Family8FiniteRandomRigidMotionPaperFixedJohnBoundedPackingMeanV5
open Family8FiniteRandomRigidMotionPaperFixedJohnLongAxisRelabelV4
open Family8FiniteRandomRigidMotionPaperFixedJohnCapVsLongMeanV2
open Family8FiniteRandomRigidMotionPaperFixedJohnFrostmanCWAConnectorV2
open Family8FiniteRandomRigidMotionPaperFixedJohnGreedyLossEnvelopeV3

noncomputable section

/-!
# Polynomial envelope for the automatic fixed-John greedy loss

Every occupied John parameter comes from a body clipped to the unit ball, so
each source John side is at most 1152.  The representative test box is only a
two-fold enlargement; after the harmless long-axis relabel every side is at
most 2304.  Combining this absolute test-volume bound with the degree-fifteen
catalogue count gives a completely explicit polynomial envelope for the
sum of paper caps, and hence for the greedy loss.
-/

/-- Relabeling does not change the uniform absolute upper bound on a
representative John side. -/
theorem fixedJohnLongSide_le_2304
    {delta : NNReal} {iota : Type}
    [Fintype iota] [DecidableEq iota]
    (D : ActualTubeDatum delta iota) (hD : D.IsAdmissible)
    (K : FixedJohnTest D hD) (i : Fin 3) :
    fixedJohnLongSide D hD K i ≤ 2304 := by
  let p := fixedJohnRepresentativeParameter D hD K
  let e := fixedJohnLongPermutation D hD K
  change (relabelFrameBox (p.certificate.box.rescale 2) e).side i ≤ 2304
  simp only [relabelFrameBox_side, FrameBox.rescale_side]
  rw [congrFun p.certificate.side_eq (e.symm i)]
  nlinarith [p.side_le_1152 (e.symm i)]

/-- Every fixed-John catalogue body has an absolute volume bound. -/
theorem fixedJohnCatalogueBody_volume_le_2304_cube
    {delta : NNReal} {iota : Type}
    [Fintype iota] [DecidableEq iota]
    (D : ActualTubeDatum delta iota) (hD : D.IsAdmissible)
    (K : FixedJohnTest D hD) :
    volume (fixedJohnCatalogueBody hD K : Set Space) ≤
      (2304 : ENNReal) ^ 3 := by
  rw [fixedJohnCatalogueBody_volume_eq_longSideProduct, Fin.prod_univ_three]
  calc
    (fixedJohnLongSide D hD K 0 : ENNReal) *
          (fixedJohnLongSide D hD K 1 : ENNReal) *
          (fixedJohnLongSide D hD K 2 : ENNReal) ≤
        (2304 : ENNReal) * 2304 * 2304 := by
      gcongr
      · exact_mod_cast fixedJohnLongSide_le_2304 D hD K 0
      · exact_mod_cast fixedJohnLongSide_le_2304 D hD K 1
      · exact_mod_cast fixedJohnLongSide_le_2304 D hD K 2
    _ = (2304 : ENNReal) ^ 3 := by ring

/-- One paper cap is bounded by maximal concentration times the absolute
catalogue volume, divided by the normalized tube-volume scale. -/
theorem fixedJohnTranslationPaperCap_le_absolute
    {delta : NNReal} {iota : Type}
    [Fintype iota] [DecidableEq iota]
    (D : ActualTubeDatum delta iota) (hD : D.IsAdmissible)
    (K : FixedJohnTest D hD) :
    fixedJohnTranslationPaperCap
        (fixedJohnPackingGridVector D hD) D hD K ≤
      (fixedJohnPackingMaximalConcentration D hD).toReal *
          (2304 : Real) ^ 3 /
        ((((delta / 8 : NNReal) : Real) ^ 2) / 2) := by
  rw [fixedJohnTranslationPaperCap_eq_longSideProduct]
  have hM : 0 ≤ (fixedJohnPackingMaximalConcentration D hD).toReal :=
    ENNReal.toReal_nonneg
  have hden : 0 < ((((delta / 8 : NNReal) : Real) ^ 2) / 2) := by
    have hrho : 0 < ((delta / 8 : NNReal) : Real) := by
      exact_mod_cast admissibleNormalizedRadiusPos hD
    positivity
  have hs0 :
      ((fixedJohnLongSide D hD K 0 : NNReal) : Real) ≤ 2304 := by
    exact_mod_cast fixedJohnLongSide_le_2304 D hD K 0
  have hs1 :
      ((fixedJohnLongSide D hD K 1 : NNReal) : Real) ≤ 2304 := by
    exact_mod_cast fixedJohnLongSide_le_2304 D hD K 1
  have hs2 :
      ((fixedJohnLongSide D hD K 2 : NNReal) : Real) ≤ 2304 := by
    exact_mod_cast fixedJohnLongSide_le_2304 D hD K 2
  have hs1nonneg :
      0 ≤ ((fixedJohnLongSide D hD K 1 : NNReal) : Real) := by positivity
  have hs2nonneg :
      0 ≤ ((fixedJohnLongSide D hD K 2 : NNReal) : Real) := by positivity
  apply (div_le_div_iff_of_pos_right hden).2
  calc
    (fixedJohnPackingMaximalConcentration D hD).toReal *
          ((fixedJohnLongSide D hD K 0 : NNReal) : Real) *
          ((fixedJohnLongSide D hD K 1 : NNReal) : Real) *
          ((fixedJohnLongSide D hD K 2 : NNReal) : Real) ≤
        (fixedJohnPackingMaximalConcentration D hD).toReal * 2304 *
          ((fixedJohnLongSide D hD K 1 : NNReal) : Real) *
          ((fixedJohnLongSide D hD K 2 : NNReal) : Real) := by
      apply mul_le_mul_of_nonneg_right _ hs2nonneg
      apply mul_le_mul_of_nonneg_right _ hs1nonneg
      exact mul_le_mul_of_nonneg_left hs0 hM
    _ ≤ (fixedJohnPackingMaximalConcentration D hD).toReal * 2304 * 2304 *
          ((fixedJohnLongSide D hD K 2 : NNReal) : Real) := by
      apply mul_le_mul_of_nonneg_right _ hs2nonneg
      exact mul_le_mul_of_nonneg_left hs1 (by positivity)
    _ ≤ (fixedJohnPackingMaximalConcentration D hD).toReal * 2304 * 2304 * 2304 := by
      exact mul_le_mul_of_nonneg_left hs2 (by positivity)
    _ = (fixedJohnPackingMaximalConcentration D hD).toReal *
          (2304 : Real) ^ 3 := by ring

/-- Sum of all fixed-John caps: exact degree-fifteen catalogue loss and no
hidden floor or callback. -/
theorem sum_fixedJohnTranslationPaperCap_le_polynomial
    {delta : NNReal} {iota : Type}
    [Fintype iota] [DecidableEq iota]
    (D : ActualTubeDatum delta iota) (hD : D.IsAdmissible) :
    (∑ K : FixedJohnTest D hD,
        fixedJohnTranslationPaperCap
          (fixedJohnPackingGridVector D hD) D hD K) ≤
      (46082 / (((delta / 8 : NNReal) : Real))) ^ 15 *
        ((fixedJohnPackingMaximalConcentration D hD).toReal *
            (2304 : Real) ^ 3 /
          ((((delta / 8 : NNReal) : Real) ^ 2) / 2)) := by
  let U : Real :=
    (fixedJohnPackingMaximalConcentration D hD).toReal *
        (2304 : Real) ^ 3 /
      ((((delta / 8 : NNReal) : Real) ^ 2) / 2)
  have hsum :
      (∑ K : FixedJohnTest D hD,
          fixedJohnTranslationPaperCap
            (fixedJohnPackingGridVector D hD) D hD K) ≤
        (Fintype.card (FixedJohnTest D hD) : Real) * U := by
    calc
      (∑ K : FixedJohnTest D hD,
          fixedJohnTranslationPaperCap
            (fixedJohnPackingGridVector D hD) D hD K) ≤
          ∑ _K : FixedJohnTest D hD, U := by
            exact Finset.sum_le_sum fun K _hK =>
              fixedJohnTranslationPaperCap_le_absolute D hD K
      _ = (Fintype.card (FixedJohnTest D hD) : Real) * U := by simp
  have hrhoHalf : delta / 8 ≤ (1 / 2 : NNReal) := by
    simpa only [one_div] using
      (div_le_self (show 0 ≤ delta from bot_le)
        (by norm_num : (1 : NNReal) ≤ 8)).trans hD.delta_le_half
  have hcard :
      (Fintype.card (FixedJohnTest D hD) : Real) ≤
        (46082 / (((delta / 8 : NNReal) : Real))) ^ 15 := by
    simpa only [FixedJohnTest, Fintype.card_fin] using
      card_catalogueIndex_real_le_div_pow
        (delta / 8) (admissibleNormalizedRadiusPos hD) hrhoHalf
  have hU : 0 ≤ U := by
    dsimp only [U]
    positivity
  exact hsum.trans (mul_le_mul_of_nonneg_right hcard hU)

/-- Fully explicit polynomial envelope for the automatic greedy loss. -/
theorem fixedJohnAutomaticGreedyLoss_cast_le_polynomial
    {delta : NNReal} {iota : Type}
    [Fintype iota] [DecidableEq iota]
    (D : ActualTubeDatum delta iota) (hD : D.IsAdmissible) :
    (fixedJohnAutomaticGreedyLoss D hD : Real) ≤
      fixedJohnTailParameter D hD *
        ((46082 / (((delta / 8 : NNReal) : Real))) ^ 15 *
          ((fixedJohnPackingMaximalConcentration D hD).toReal *
              (2304 : Real) ^ 3 /
            ((((delta / 8 : NNReal) : Real) ^ 2) / 2))) +
        2 := by
  have htail : 0 ≤ fixedJohnTailParameter D hD :=
    zero_le_one.trans (one_le_fixedJohnTailParameter D hD)
  have hmul := mul_le_mul_of_nonneg_left
    (sum_fixedJohnTranslationPaperCap_le_polynomial D hD) htail
  exact (fixedJohnAutomaticGreedyLoss_cast_le_envelope D hD).trans (by
    simpa only [add_comm] using add_le_add_right hmul 2)

#print axioms fixedJohnLongSide_le_2304
#print axioms fixedJohnCatalogueBody_volume_le_2304_cube
#print axioms fixedJohnTranslationPaperCap_le_absolute
#print axioms sum_fixedJohnTranslationPaperCap_le_polynomial
#print axioms fixedJohnAutomaticGreedyLoss_cast_le_polynomial

end
end Family8FiniteRandomRigidMotionPaperFixedJohnGreedyLossPolynomialV3
