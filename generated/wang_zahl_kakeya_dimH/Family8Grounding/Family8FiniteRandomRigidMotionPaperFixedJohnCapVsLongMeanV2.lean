import Family8Grounding.Family8FiniteRandomRigidMotionPaperFixedJohnLongPackingMeanV2
import Submission.Kakeya.ConvexFactoring.FrameBoxVolume
import Mathlib.Tactic

open Set MeasureTheory
open scoped ENNReal NNReal BigOperators InnerProductSpace

namespace Family8FiniteRandomRigidMotionPaperFixedJohnCapVsLongMeanV2

open LeanEval.Analysis.WangZahlKakeya
open Submission.Kakeya.ConvexGeometry
open Family8KatzTaoFrostmanPropertiesV1
open Family8FiniteRandomRigidMotionB2NormalizationCoreV1
open Family8FiniteRandomRigidMotionPaperTranslationBodyGridV1
open Family8FiniteRandomRigidMotionPaperFixedJohnAutomaticConflictCapV2
open Family8FiniteRandomRigidMotionPaperFixedJohnExactMeanSelectorV4
open Family8FiniteRandomRigidMotionPaperFixedJohnBoundedPackingMeanV5
open Family8FiniteRandomRigidMotionPaperFixedJohnLongAxisRelabelV4
open Family8FiniteRandomRigidMotionPaperFixedJohnLongPackingMeanV2
open FamilyStickyActualTubeTranslationGridV1
open FamilyStickyActualPaperSingleLoadProducerV1.ActualTubeTranslationGrid

noncomputable section

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 4000000

/-! Exact expansion of the normalized maximal-concentration cap and the
relabeled FrameBox volume.  The only input left is the explicit sufficient
source-density budget `9504 J #T (delta/8)^2 <= Delta_max`. -/

def fixedJohnNormalizedActiveFamily
    {delta : NNReal} {iota : Type}
    [Fintype iota] [DecidableEq iota]
    (D : ActualTubeDatum delta iota) :
    ConvexFamily {i // i ∈ (Finset.univ : Finset iota)} :=
  fun i => (eighthNormalizedTube (D.family.tubes i.1)).body

theorem fixedJohnPacking_activeFamily_eq_normalized
    {delta : NNReal} {iota : Type}
    [Fintype iota] [DecidableEq iota]
    (D : ActualTubeDatum delta iota) (hD : D.IsAdmissible) :
    activeFamily (fixedJohnPackingNormalizedGrid D hD) =
      fixedJohnNormalizedActiveFamily D := by
  rfl

def fixedJohnPackingMaximalConcentration
    {delta : NNReal} {iota : Type}
    [Fintype iota] [DecidableEq iota]
    (D : ActualTubeDatum delta iota) (_hD : D.IsAdmissible) : ENNReal :=
  maximalConcentration (fixedJohnNormalizedActiveFamily D)

theorem fixedJohnPacking_maximalConcentration_eq_normalized
    {delta : NNReal} {iota : Type}
    [Fintype iota] [DecidableEq iota]
    (D : ActualTubeDatum delta iota) (hD : D.IsAdmissible) :
    maximalConcentration
        (activeFamily (fixedJohnPackingNormalizedGrid D hD)) =
      fixedJohnPackingMaximalConcentration D hD := by
  rw [fixedJohnPacking_activeFamily_eq_normalized]
  rfl

theorem fixedJohnCatalogueBody_volume_eq_longSideProduct
    {delta : NNReal} {iota : Type}
    [Fintype iota] [DecidableEq iota]
    (D : ActualTubeDatum delta iota) (hD : D.IsAdmissible)
    (K : FixedJohnTest D hD) :
    volume (fixedJohnCatalogueBody hD K : Set Space) =
      ∏ i, (fixedJohnLongSide D hD K i : ENNReal) := by
  rw [← fixedJohnLongTestBox_body_eq D hD K,
    FrameBox.volume_body]
  rfl

theorem fixedJohnTranslationPaperCap_eq_longSideProduct
    {delta : NNReal} {iota : Type}
    [Fintype iota] [DecidableEq iota]
    (D : ActualTubeDatum delta iota) (hD : D.IsAdmissible)
    (K : FixedJohnTest D hD) :
    fixedJohnTranslationPaperCap
        (fixedJohnPackingGridVector D hD) D hD K =
      (fixedJohnPackingMaximalConcentration D hD).toReal *
          (fixedJohnLongSide D hD K 0 : Real) *
          (fixedJohnLongSide D hD K 1 : Real) *
          (fixedJohnLongSide D hD K 2 : Real) /
        ((((delta / 8 : NNReal) : Real) ^ 2) / 2) := by
  change
    (maximalConcentration
        (activeFamily (fixedJohnPackingNormalizedGrid D hD)) *
      volume (fixedJohnCatalogueBody hD K : Set Space) /
      ((((delta / 8 : NNReal) : ENNReal) ^ 2) / 2)).toReal = _
  rw [fixedJohnPacking_maximalConcentration_eq_normalized,
    fixedJohnCatalogueBody_volume_eq_longSideProduct,
    Fin.prod_univ_three]
  norm_num [ENNReal.toReal_div, ENNReal.toReal_mul,
    ENNReal.toReal_pow]
  ring

theorem fixedJohnLongPackingMean_scale_le_paperCap_of_densityBudget
    {delta : NNReal} {iota : Type}
    [Fintype iota] [DecidableEq iota]
    (D : ActualTubeDatum delta iota) (hD : D.IsAdmissible)
    (J : Nat)
    (hbudget :
      9504 * (J : Real) * (Fintype.card iota : Real) *
          (((delta / 8 : NNReal) : Real) ^ 2) <=
        (fixedJohnPackingMaximalConcentration D hD).toReal)
    (K : FixedJohnTest D hD) :
    (J : Real) * fixedJohnLongPackingMean D hD K <=
      fixedJohnTranslationPaperCap
        (fixedJohnPackingGridVector D hD) D hD K := by
  let rho : Real := ((delta / 8 : NNReal) : Real)
  let s0 : Real := (fixedJohnLongSide D hD K 0 : Real)
  let s1 : Real := (fixedJohnLongSide D hD K 1 : Real)
  let s2 : Real := (fixedJohnLongSide D hD K 2 : Real)
  let M : Real := (fixedJohnPackingMaximalConcentration D hD).toReal
  have hrho : 0 < rho := by
    exact_mod_cast admissibleNormalizedRadiusPos hD
  have hden : 0 < rho ^ 2 / 2 := by positivity
  have hs0 : 0 <= s0 := by positivity
  have hs1 : 0 <= s1 := by positivity
  have hs2 : 1 <= s2 := by
    exact_mod_cast one_le_fixedJohnLongSide_two D hD K
  have hM : 0 <= M := ENNReal.toReal_nonneg
  have hMlong : M <= M * s2 := by
    calc
      M = M * 1 := by ring
      _ <= M * s2 := mul_le_mul_of_nonneg_left hs2 hM
  have hbudgetBase :
      9504 * (J : Real) * (Fintype.card iota : Real) * rho ^ 2 <= M := by
    simpa only [rho, M] using hbudget
  have hbudgetLong :
      9504 * (J : Real) * (Fintype.card iota : Real) * rho ^ 2 <=
        M * s2 := hbudgetBase.trans hMlong
  have hscaled := mul_le_mul_of_nonneg_right hbudgetLong
    (mul_nonneg hs0 hs1)
  rw [fixedJohnTranslationPaperCap_eq_longSideProduct]
  change (J : Real) * fixedJohnLongPackingMean D hD K <=
    M * s0 * s1 * s2 / (rho ^ 2 / 2)
  apply (le_div_iff₀ hden).2
  calc
    (J : Real) * fixedJohnLongPackingMean D hD K * (rho ^ 2 / 2) =
        (9504 * (J : Real) * (Fintype.card iota : Real) * rho ^ 2) *
          (s0 * s1) := by
      unfold fixedJohnLongPackingMean
      norm_num [rho, s0, s1]
      ring
    _ <= (M * s2) * (s0 * s1) := hscaled
    _ = M * s0 * s1 * s2 := by ring

theorem fixedJohnLongPackingMean_scale_le_paperCap_all_of_densityBudget
    {delta : NNReal} {iota : Type}
    [Fintype iota] [DecidableEq iota]
    (D : ActualTubeDatum delta iota) (hD : D.IsAdmissible)
    (J : Nat)
    (hbudget :
      9504 * (J : Real) * (Fintype.card iota : Real) *
          (((delta / 8 : NNReal) : Real) ^ 2) <=
        (fixedJohnPackingMaximalConcentration D hD).toReal) :
    forall K : FixedJohnTest D hD,
      (J : Real) * fixedJohnLongPackingMean D hD K <=
        fixedJohnTranslationPaperCap
          (fixedJohnPackingGridVector D hD) D hD K := by
  intro K
  exact fixedJohnLongPackingMean_scale_le_paperCap_of_densityBudget
    D hD J hbudget K

#print axioms fixedJohnPacking_activeFamily_eq_normalized
#print axioms fixedJohnPacking_maximalConcentration_eq_normalized
#print axioms fixedJohnCatalogueBody_volume_eq_longSideProduct
#print axioms fixedJohnTranslationPaperCap_eq_longSideProduct
#print axioms fixedJohnLongPackingMean_scale_le_paperCap_of_densityBudget
#print axioms fixedJohnLongPackingMean_scale_le_paperCap_all_of_densityBudget

end
end Family8FiniteRandomRigidMotionPaperFixedJohnCapVsLongMeanV2
