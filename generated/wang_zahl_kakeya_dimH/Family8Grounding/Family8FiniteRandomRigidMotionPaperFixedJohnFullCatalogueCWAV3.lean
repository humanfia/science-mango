import Family8Grounding.Family8FiniteRandomRigidMotionPaperFixedJohnCatalogueCapIdentityV1
import Family8Grounding.Family8FiniteRandomRigidMotionPaperFixedJohnFreshSelectionV2
import Family8Grounding.Family8PolynomialJohnFrameBoxCardinalAllConvexV1
import Mathlib.Tactic

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 4000000

open Set MeasureTheory
open scoped ENNReal NNReal BigOperators

namespace Family8FiniteRandomRigidMotionPaperFixedJohnFullCatalogueCWAV3

open LeanEval.Analysis.WangZahlKakeya
open Submission.Kakeya.ConvexGeometry
open Submission.Kakeya.ConvexFactoring
open Family8Def212ConvexWolffAtEveryScaleV2
open Family8KatzTaoFrostmanPropertiesV1
open Family8GeneralizedFrostmanMultiplicityV1
open Family8FiniteRandomRigidMotionIncidenceV1
open Family8FiniteRandomRigidMotionB2NormalizedDatumV1
open Family8FiniteRandomRigidMotionPaperFixedJohnConflictGridV4
open Family8FiniteRandomRigidMotionPaperFixedJohnAutomaticConflictCapV2
open Family8FiniteRandomRigidMotionPaperFixedJohnBoundedPackingMeanV5
open Family8FiniteRandomRigidMotionPaperFixedJohnCapVsLongMeanV2
open Family8FiniteRandomRigidMotionPaperFixedJohnExactMeanSelectorV4
open Family8FiniteRandomRigidMotionPaperFixedJohnAutomaticDensityRepetitionsV2
open Family8FiniteRandomRigidMotionPaperFixedJohnCatalogueCardIdentityV2
open Family8FiniteRandomRigidMotionPaperFixedJohnCatalogueCapIdentityV1
open Family8PolynomialJohnFrameBoxTestNetV1
open Family8PolynomialJohnFrameBoxVolumeV2
open Family8PolynomialJohnFrameBoxCardinalAllConvexV1

noncomputable section

/-! The automatic selector's tail is a literal catalogue cardinality bound.
Dividing its common coefficient by the total number of copied occurrences
gives the exact Definition 2.12 normalization; no selected-card factor is
hidden here. -/

/-- Cardinal-normalized catalogue coefficient of the full normalized copied
family, before the universal John-catalogue volume loss. -/
def fixedJohnFullCopiedCWAParameter
    {delta : NNReal} {iota : Type}
    [Fintype iota] [DecidableEq iota]
    (D : ActualTubeDatum delta iota) (hD : D.IsAdmissible) : ENNReal :=
  (ENNReal.ofReal (fixedJohnTailParameter D hD) *
      fixedJohnPackingMaximalConcentration D hD /
      (((delta / 8 : NNReal) : ENNReal) ^ 2 / 2)) /
    (Fintype.card
      (Fin (fixedJohnAutomaticDensityRepetitions D hD) × iota) : ENNReal)

/-- A selected automatic tuple satisfies the cardinal-normalized Convex
Wolff axioms on its full normalized product family. -/
theorem fullNormalizedCopied_satisfiesConvexWolffAxioms
    {delta : NNReal} {iota : Type}
    [Fintype iota] [Nonempty iota] [DecidableEq iota]
    (D : ActualTubeDatum delta iota) (hD : D.IsAdmissible)
    (omega : Fin (fixedJohnAutomaticDensityRepetitions D hD) ->
      FixedJohnPackingTranslation D hD)
    (htail : forall K : FixedJohnTest D hD,
      (∑ j, (Family8FiniteRandomRigidMotionPaperTranslationBodyGridV1.normalizedTranslationBodyLoadNat
        (fixedJohnPackingGridVector D hD) D
        (fixedJohnCatalogueBody hD) K (omega j) : Real)) <=
        fixedJohnTailParameter D hD *
          fixedJohnTranslationPaperCap
            (fixedJohnPackingGridVector D hD) D hD K) :
    SatisfiesConvexWolffAxioms
      (fixedJohnFullCopiedCWAParameter D hD *
        johnCatalogueVolumeConstant)
      (eighthNormalizedDatum
        (indexedRigidCopyDatum
          (fun j => translationRigidMotion
            (fixedJohnPackingGridVector D hD (omega j))) D)).family.bodyFamily := by
  let J := fixedJohnAutomaticDensityRepetitions D hD
  let gridVector := fixedJohnPackingGridVector D hD
  let copied := indexedRigidCopyDatum
    (fun j : Fin J => translationRigidMotion (gridVector (omega j))) D
  let normalized := eighthNormalizedDatum copied
  let fullCard : ENNReal := Fintype.card (Fin J × iota)
  let lower : ENNReal := (((delta / 8 : NNReal) : ENNReal) ^ 2 / 2)
  let base : ENNReal := fixedJohnPackingMaximalConcentration D hD
  let B : ENNReal :=
    ENNReal.ofReal (fixedJohnTailParameter D hD) * base / lower
  have hJ : 0 < J :=
    one_le_fixedJohnAutomaticDensityRepetitions D hD
  have hfullCard0 : fullCard ≠ 0 := by
    dsimp only [fullCard]
    rw [Fintype.card_prod, Fintype.card_fin]
    exact_mod_cast Nat.mul_ne_zero hJ.ne' Fintype.card_ne_zero
  have hfullCardTop : fullCard ≠ ∞ := by
    dsimp only [fullCard]
    exact ENNReal.coe_ne_top
  have hlowerPos : 0 < lower := by
    dsimp only [lower]
    exact ENNReal.div_pos
      (ENNReal.pow_pos (ENNReal.coe_pos.mpr
        (admissibleNormalizedRadiusPos hD)) 2).ne'
      (by norm_num)
  have hlowerTop : lower ≠ ∞ := by
    dsimp only [lower]
    exact ENNReal.div_ne_top
      (ENNReal.pow_ne_top ENNReal.coe_ne_top) (by norm_num)
  have hbaseTop : base ≠ ∞ := by
    dsimp only [base, fixedJohnPackingMaximalConcentration]
    exact
      (FamilyStickyFiniteFamilyMaximalConcentrationV1.maximalConcentration_lt_top
        (fixedJohnNormalizedActiveFamily D)).ne
  have hunit : forall a : Fin J × iota,
      (normalized.family.tubes a).carrier ⊆
        Metric.closedBall (0 : Space) 1 := by
    intro a
    change
      (Family8FiniteRandomRigidMotionB2NormalizationCoreV1.eighthNormalizedTube
        (rigidTube
          (translationRigidMotion (gridVector (omega a.1)))
          (D.family.tubes a.2))).carrier ⊆
        Metric.closedBall (0 : Space) 1
    exact
      Family8FiniteRandomRigidMotionPaperNormalizedTranslationUnitSupportV1.eighthNormalizedRigidTranslationTube_carrier_subset_unitBall
        (D.family.tubes a.2) (gridVector (omega a.1))
        hD.delta_le_half (hD.contained_in_unit_ball a.2)
        (by
          simpa only [gridVector] using
            fixedJohnPackingGridVector_norm_le_one D hD (omega a.1))
  apply satisfiesConvexWolffAxioms_of_polynomialJohnCatalogue
    (admissibleNormalizedRadiusPos hD) normalized.family.tubes hunit
      (B / fullCard)
  intro q
  let K := normalizedJohnCatalogueIndex q
  let ratio : ENNReal := base *
    volume (representativeTestBody (delta / 8)
      (admissibleNormalizedRadiusPos hD) q : Set Space) / lower
  have hratioTop : ratio ≠ ∞ := by
    dsimp only [ratio]
    apply ENNReal.div_ne_top
    · exact ENNReal.mul_ne_top hbaseTop
        (representativeTestBody (delta / 8)
          (admissibleNormalizedRadiusPos hD) q).isCompact.measure_lt_top.ne
    · exact hlowerPos.ne'
  have htail0 : 0 <= fixedJohnTailParameter D hD :=
    (by linarith [one_le_fixedJohnTailParameter D hD])
  have hcountReal :
      ((containedIndices normalized.family.bodyFamily
        (representativeTestBody (delta / 8)
          (admissibleNormalizedRadiusPos hD) q)).card : Real) <=
        fixedJohnTailParameter D hD * ratio.toReal := by
    have h := htail K
    rw [fixedJohnCatalogue_containedIndices_card_eq_sum_load]
    rw [fixedJohnTranslationPaperCap_catalogueIndex] at h
    simpa only [Nat.cast_sum, K, gridVector, normalized, copied, J,
      ratio, base, lower] using h
  have hcountENN :
      ((containedIndices normalized.family.bodyFamily
        (representativeTestBody (delta / 8)
          (admissibleNormalizedRadiusPos hD) q)).card : ENNReal) <=
        ENNReal.ofReal (fixedJohnTailParameter D hD) * ratio := by
    apply (ENNReal.toReal_le_toReal ENNReal.coe_ne_top
      (ENNReal.mul_ne_top ENNReal.ofReal_ne_top hratioTop)).mp
    calc
      (((containedIndices normalized.family.bodyFamily
          (representativeTestBody (delta / 8)
            (admissibleNormalizedRadiusPos hD) q)).card : ENNReal)).toReal =
          ((containedIndices normalized.family.bodyFamily
            (representativeTestBody (delta / 8)
              (admissibleNormalizedRadiusPos hD) q)).card : Real) := by
        norm_num
      _ <= fixedJohnTailParameter D hD * ratio.toReal := hcountReal
      _ = (ENNReal.ofReal (fixedJohnTailParameter D hD) * ratio).toReal := by
        rw [ENNReal.toReal_mul, ENNReal.toReal_ofReal htail0]
  calc
    ((containedIndices normalized.family.bodyFamily
        (representativeTestBody (delta / 8)
          (admissibleNormalizedRadiusPos hD) q)).card : ENNReal) <=
        ENNReal.ofReal (fixedJohnTailParameter D hD) * ratio := hcountENN
    _ = B * volume (representativeTestBody (delta / 8)
          (admissibleNormalizedRadiusPos hD) q : Set Space) := by
      simp only [B, ratio, div_eq_mul_inv]
      ac_rfl
    _ = (B / fullCard) *
          volume (representativeTestBody (delta / 8)
            (admissibleNormalizedRadiusPos hD) q : Set Space) *
          (Fintype.card (Fin J × iota) : ENNReal) := by
      dsimp only [fullCard]
      symm
      calc
        (B / (Fintype.card (Fin J × iota) : ENNReal)) *
              volume (representativeTestBody (delta / 8)
                (admissibleNormalizedRadiusPos hD) q : Set Space) *
              (Fintype.card (Fin J × iota) : ENNReal) =
            (B / (Fintype.card (Fin J × iota) : ENNReal)) *
              (Fintype.card (Fin J × iota) : ENNReal) *
              volume (representativeTestBody (delta / 8)
                (admissibleNormalizedRadiusPos hD) q : Set Space) := by
          ac_rfl
        _ = B * volume (representativeTestBody (delta / 8)
              (admissibleNormalizedRadiusPos hD) q : Set Space) := by
          rw [ENNReal.div_mul_cancel]
          · exact hfullCard0
          · exact hfullCardTop
    _ = (fixedJohnFullCopiedCWAParameter D hD) *
          volume (representativeTestBody (delta / 8)
            (admissibleNormalizedRadiusPos hD) q : Set Space) *
          (Fintype.card (Fin J × iota) : ENNReal) := by
      rfl

#print axioms fixedJohnFullCopiedCWAParameter
#print axioms fullNormalizedCopied_satisfiesConvexWolffAxioms

end
end Family8FiniteRandomRigidMotionPaperFixedJohnFullCatalogueCWAV3
