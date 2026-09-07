import Family8Grounding.Family8KatzTaoSamplingMultiplicityV1
import Family8Grounding.Family8KatzTaoSamplingDensityBudgetV1
import Family8Grounding.Family8KatzTaoJohnCoefficientBudgetV1
import Family8Grounding.Family8ZeroColorMultiplicityRetentionV1
import FamilyStickyGrounding.FamilyStickyFiniteFamilyMaximalConcentrationV1
import Mathlib.Tactic

open scoped ENNReal NNReal BigOperators
open MeasureTheory Set

namespace Family8GeneralizedKatzTaoPolynomialSamplingV1

open LeanEval.Analysis.WangZahlKakeya
open Submission.Kakeya.ConvexGeometry
open Submission.Kakeya.ConvexFactoring
open Submission.Kakeya.Uniformity
open Family8KatzTaoFrostmanPropertiesV1
open Family8GeneralizedKatzTaoMultiplicityV1
open Family8ZeroColorPolynomialJohnKatzTaoV1
open Family8KatzTaoSamplingMultiplicityV1
open Family8KatzTaoSamplingDensityBudgetV1
open Family8KatzTaoJohnCoefficientBudgetV1
open Family8ZeroColorMultiplicityRetentionV1
open Family8RestrictedActualDatumDensityRetentionV1
open Family8PolynomialJohnFrameBoxVolumeV2
open FamilyStickyCinematicL32Prop41FiniteRandomSamplingExtractionV1
open FamilyStickyFiniteFamilyMaximalConcentrationV1

noncomputable section

set_option autoImplicit false
set_option warningAsError true
set_option linter.unusedSectionVars false
set_option maxHeartbeats 2000000

/-!
# Polynomial John sampling returned to the source datum

This module keeps the literal colouring selected by the polynomial John
catalogue argument.  The same colouring supplies the sampled cardinality,
the actual Katz--Tao estimate on the restricted datum, and the deterministic
`2k` return of average multiplicity to the source datum.
-/

/-- Fixed-`k` source-return form of the actual polynomial-catalogue sampling
argument.  No independent choice of a second good colouring occurs. -/
theorem exists_zeroColorActualDatum_apply_katzTaoAtParameters_with_source
    {beta epsilon eta : Real} {delta0 delta : NNReal}
    {iota : Type} [Fintype iota] [DecidableEq iota]
    (hKT : KatzTaoAtParameters beta epsilon eta delta0)
    (D : ActualTubeDatum delta iota) (hD : D.IsAdmissible)
    (hdelta0 : delta ≤ delta0)
    (C : ENNReal) (k : Nat) [NeZero k]
    (hsource : IsKatzTao C D.family.bodyFamily)
    (hCfinite : C ≠ ∞)
    (hCscale : C.toReal / (k : Real) ≤ 1)
    (hdensityBudget :
      (delta : ENNReal) ^ eta * (2 * (k : ENNReal)) ≤
        D.shading.shadingDensity)
    (hcoefficient :
      ENNReal.ofReal (polynomialJohnTailParameter delta k) *
          johnCatalogueVolumeConstant ≤
        (delta : ENNReal) ^ (-eta)) :
    ∃ omega : iota → Fin k,
      ((zeroColorSample k omega).card : Real) ≤
          polynomialJohnTailParameter delta k *
            averageZeroColorCardinalCap iota k ∧
        (zeroColorActualDatum D k omega).shading.averageMultiplicity ≤
          katzTaoMultiplicityRHS delta
            (zeroColorSample k omega).card epsilon beta ∧
        D.shading.averageMultiplicity ≤
          ((2 * k : Nat) : ENNReal) *
            katzTaoMultiplicityRHS delta
              (zeroColorSample k omega).card epsilon beta := by
  obtain ⟨omega, hretained, hcard, hsampleKT⟩ :=
    exists_zeroColorActualDatum_polynomialJohn_isKatzTao
      D hD C k hsource hCfinite hCscale
  have hmass :=
    shadingMass_le_two_mul_k_of_toReal_retention D k omega hretained
  have hdensityLoss :=
    source_shadingDensity_div_loss_le_zeroColorActualDatum
      D k omega (2 * (k : ENNReal)) hmass
  have hkENN : (k : ENNReal) ≠ 0 := by
    simp [NeZero.ne k]
  have hloss0 : (2 * (k : ENNReal)) ≠ 0 := by
    exact mul_ne_zero (by norm_num) hkENN
  have hlossTop : (2 * (k : ENNReal)) ≠ ∞ :=
    ENNReal.mul_ne_top (by norm_num) (by simp)
  have hsampleDensity :
      (delta : ENNReal) ^ eta ≤
        (zeroColorActualDatum D k omega).shading.shadingDensity := by
    have hdiv :
        (delta : ENNReal) ^ eta ≤
          D.shading.shadingDensity / (2 * (k : ENNReal)) :=
      (ENNReal.le_div_iff_mul_le
        (Or.inl hloss0) (Or.inl hlossTop)).2 hdensityBudget
    exact hdiv.trans hdensityLoss
  have hsampleHyp :
      KatzTaoHypotheses (zeroColorActualDatum D k omega) eta := by
    refine ⟨hsampleDensity, ?_⟩
    rw [maximalConcentration_le_iff_isKatzTao]
    exact hsampleKT.mono hcoefficient
  have hsampleBound :=
    KatzTaoAtParameters.apply hKT
      (zeroColorActualDatum D k omega)
      (Family8GeneralizedKatzTaoMultiplicityV1.ActualTubeDatum.IsAdmissible.restrictTo
        hD (zeroColorSample k omega))
      hdelta0 hsampleHyp
  have hsourceBound :=
    source_averageMultiplicity_le_two_mul_k_mul_zeroColorActualDatum
      D k omega hretained
  refine ⟨omega, hcard, ?_, ?_⟩
  · simpa using hsampleBound
  · have hscaled :
        ((2 * k : Nat) : ENNReal) *
            (zeroColorActualDatum D k omega).shading.averageMultiplicity ≤
          ((2 * k : Nat) : ENNReal) *
            katzTaoMultiplicityRHS delta (zeroColorSample k omega).card epsilon beta :=
      mul_le_mul_right (by simpa using hsampleBound) (((2 * k : Nat) : ENNReal))
    exact hsourceBound.trans hscaled

/-- Automatic choice `k = ceil(C.toReal)`.  This closes the sampling-factor
interface while retaining the exact finite John tail and exact sampled
cardinality in the conclusion. -/
theorem exists_sampledCard_apply_katzTaoAtParameters_with_source_automatic
    {beta epsilon eta : Real} {delta0 delta : NNReal}
    {iota : Type} [Fintype iota] [DecidableEq iota]
    (hKT : KatzTaoAtParameters beta epsilon eta delta0)
    (D : ActualTubeDatum delta iota) (hD : D.IsAdmissible)
    (hdelta0 : delta ≤ delta0)
    (C : ENNReal) (hCpos : 0 < C) (hCfinite : C ≠ ∞)
    (hsource : IsKatzTao C D.family.bodyFamily)
    (hdensityBudget :
      (delta : ENNReal) ^ eta *
          (2 * (katzTaoSamplingMultiplicity C : ENNReal)) ≤
        D.shading.shadingDensity)
    (hcoefficient :
      ENNReal.ofReal (polynomialJohnTailParameter delta
          (katzTaoSamplingMultiplicity C)) *
          johnCatalogueVolumeConstant ≤
        (delta : ENNReal) ^ (-eta)) :
    ∃ sampledCard : Nat,
      (sampledCard : Real) ≤
          polynomialJohnTailParameter delta (katzTaoSamplingMultiplicity C) *
            averageZeroColorCardinalCap iota
              (katzTaoSamplingMultiplicity C) ∧
      D.shading.averageMultiplicity ≤
          ((2 * katzTaoSamplingMultiplicity C : Nat) : ENNReal) *
            katzTaoMultiplicityRHS delta sampledCard epsilon beta := by
  let k := katzTaoSamplingMultiplicity C
  have hk : 0 < k := katzTaoSamplingMultiplicity_pos hCpos hCfinite
  let _ : NeZero k := ⟨hk.ne'⟩
  obtain ⟨omega, hcard, _hsample, hsourceBound⟩ :=
    exists_zeroColorActualDatum_apply_katzTaoAtParameters_with_source
      hKT D hD hdelta0 C k hsource hCfinite
      (toReal_div_katzTaoSamplingMultiplicity_le_one hCpos hCfinite)
      hdensityBudget hcoefficient
  exact ⟨(zeroColorSample k omega).card, hcard, hsourceBound⟩

/-- The source-density formulation closes the full `2k` density budget
from an explicit concentration power bound. -/
theorem exists_sampledCard_apply_katzTaoAtParameters_with_source_automatic_of_sourceDensity
    {beta epsilon targetEta sourceEta : Real} {delta0 delta : NNReal}
    {iota : Type} [Fintype iota] [DecidableEq iota]
    (hKT : KatzTaoAtParameters beta epsilon targetEta delta0)
    (D : ActualTubeDatum delta iota) (hD : D.IsAdmissible)
    (hdelta0 : delta ≤ delta0)
    (hgap : 0 < targetEta - 2 * sourceEta)
    (hdeltaThreshold :
      delta ≤ katzTaoSamplingDensityThreshold targetEta sourceEta)
    (C : ENNReal) (hCone : 1 ≤ C) (hCfinite : C ≠ ∞)
    (hC : C ≤ (delta : ENNReal) ^ (-sourceEta))
    (hsource : IsKatzTao C D.family.bodyFamily)
    (hsourceDensity :
      (delta : ENNReal) ^ sourceEta ≤ D.shading.shadingDensity)
    (hcoefficient :
      ENNReal.ofReal (polynomialJohnTailParameter delta
          (katzTaoSamplingMultiplicity C)) *
          johnCatalogueVolumeConstant ≤
        (delta : ENNReal) ^ (-targetEta)) :
    ∃ sampledCard : Nat,
      (sampledCard : Real) ≤
          polynomialJohnTailParameter delta (katzTaoSamplingMultiplicity C) *
            averageZeroColorCardinalCap iota
              (katzTaoSamplingMultiplicity C) ∧
      D.shading.averageMultiplicity ≤
          ((2 * katzTaoSamplingMultiplicity C : Nat) : ENNReal) *
            katzTaoMultiplicityRHS delta sampledCard epsilon beta := by
  apply exists_sampledCard_apply_katzTaoAtParameters_with_source_automatic
    hKT D hD hdelta0 C (zero_lt_one.trans_le hCone) hCfinite hsource
  · exact samplingMultiplicity_densityBudget hD.delta_pos hgap
      hdeltaThreshold hCfinite hCone hC hsourceDensity
  · exact hcoefficient

/-- Fully automatic source-density form.  The John catalogue coefficient is
paid for by two explicit positive pieces of the target exponent, so no
coefficient callback remains in this statement. -/
theorem exists_sampledCard_apply_katzTaoAtParameters_with_source_fullyAutomatic
    {beta epsilon sourceEta tailEta constantEta : Real} {delta0 delta : NNReal}
    {iota : Type} [Fintype iota] [DecidableEq iota]
    (hKT : KatzTaoAtParameters beta epsilon (tailEta + constantEta) delta0)
    (D : ActualTubeDatum delta iota) (hD : D.IsAdmissible)
    (hdelta0 : delta ≤ delta0)
    (hsourceEta : 0 ≤ sourceEta)
    (htailEta : 0 < tailEta) (hconstantEta : 0 < constantEta)
    (hgap : 0 < tailEta + constantEta - 2 * sourceEta)
    (hdeltaDensityThreshold :
      delta ≤ katzTaoSamplingDensityThreshold
        (tailEta + constantEta) sourceEta)
    (hdeltaCoefficientThreshold :
      delta ≤ johnCoefficientThreshold johnCataloguePolynomialCostConstant
        (15 + sourceEta) tailEta constantEta)
    (C : ENNReal) (hCone : 1 ≤ C) (hCfinite : C ≠ ∞)
    (hC : C ≤ (delta : ENNReal) ^ (-sourceEta))
    (hsource : IsKatzTao C D.family.bodyFamily)
    (hsourceDensity :
      (delta : ENNReal) ^ sourceEta ≤ D.shading.shadingDensity) :
    ∃ sampledCard : Nat,
      (sampledCard : Real) ≤
          polynomialJohnTailParameter delta (katzTaoSamplingMultiplicity C) *
            averageZeroColorCardinalCap iota
              (katzTaoSamplingMultiplicity C) ∧
      D.shading.averageMultiplicity ≤
          ((2 * katzTaoSamplingMultiplicity C : Nat) : ENNReal) *
            katzTaoMultiplicityRHS delta sampledCard epsilon beta := by
  apply
    exists_sampledCard_apply_katzTaoAtParameters_with_source_automatic_of_sourceDensity
      hKT D hD hdelta0 hgap hdeltaDensityThreshold C hCone hCfinite hC
        hsource hsourceDensity
  exact automaticPolynomialJohn_coefficient_le_rpow
    hD.delta_pos (hD.delta_le_half.trans (by norm_num)) hsourceEta
      htailEta hconstantEta hCfinite hCone hC hdeltaCoefficientThreshold

/-- Actual-hypotheses specialization of the fully automatic sampling theorem.
The concentration constant is the literal power supplied by
`KatzTaoHypotheses`; hence the statement exposes neither `C` nor an
`IsKatzTao` callback. -/
theorem exists_sampledCard_apply_katzTaoAtParameters_with_source_of_hypotheses
    {beta epsilon sourceEta tailEta constantEta : Real} {delta0 delta : NNReal}
    {iota : Type} [Fintype iota] [DecidableEq iota]
    (hKT : KatzTaoAtParameters beta epsilon (tailEta + constantEta) delta0)
    (D : ActualTubeDatum delta iota) (hD : D.IsAdmissible)
    (hdelta0 : delta ≤ delta0)
    (hsourceEta : 0 ≤ sourceEta)
    (htailEta : 0 < tailEta) (hconstantEta : 0 < constantEta)
    (hgap : 0 < tailEta + constantEta - 2 * sourceEta)
    (hdeltaDensityThreshold :
      delta ≤ katzTaoSamplingDensityThreshold
        (tailEta + constantEta) sourceEta)
    (hdeltaCoefficientThreshold :
      delta ≤ johnCoefficientThreshold johnCataloguePolynomialCostConstant
        (15 + sourceEta) tailEta constantEta)
    (hHypotheses : KatzTaoHypotheses D sourceEta) :
    ∃ sampledCard : Nat,
      (sampledCard : Real) ≤
          polynomialJohnTailParameter delta
              (katzTaoSamplingMultiplicity
                ((delta : ENNReal) ^ (-sourceEta))) *
            averageZeroColorCardinalCap iota
              (katzTaoSamplingMultiplicity
                ((delta : ENNReal) ^ (-sourceEta))) ∧
      D.shading.averageMultiplicity ≤
          ((2 * katzTaoSamplingMultiplicity
            ((delta : ENNReal) ^ (-sourceEta)) : Nat) : ENNReal) *
            katzTaoMultiplicityRHS delta sampledCard epsilon beta := by
  let C : ENNReal := (delta : ENNReal) ^ (-sourceEta)
  have hCone : 1 ≤ C := by
    dsimp only [C]
    rw [← ENNReal.coe_rpow_of_ne_zero hD.delta_pos.ne' (-sourceEta)]
    exact_mod_cast NNReal.one_le_rpow_of_pos_of_le_one_of_nonpos
      hD.delta_pos (hD.delta_le_half.trans (by norm_num)) (by linarith)
  have hCfinite : C ≠ ∞ := by
    exact ENNReal.rpow_ne_top_of_ne_zero
      (ENNReal.coe_ne_zero.mpr hD.delta_pos.ne') ENNReal.coe_ne_top
  have hsource : IsKatzTao C D.family.bodyFamily := by
    exact (maximalConcentration_le_iff_isKatzTao).1 hHypotheses.2
  simpa only [C] using
    exists_sampledCard_apply_katzTaoAtParameters_with_source_fullyAutomatic
      hKT D hD hdelta0 hsourceEta htailEta hconstantEta hgap
        hdeltaDensityThreshold hdeltaCoefficientThreshold C hCone hCfinite
          le_rfl hsource hHypotheses.1

#print axioms exists_sampledCard_apply_katzTaoAtParameters_with_source_of_hypotheses

#print axioms exists_sampledCard_apply_katzTaoAtParameters_with_source_fullyAutomatic

#print axioms exists_sampledCard_apply_katzTaoAtParameters_with_source_automatic_of_sourceDensity

#print axioms exists_zeroColorActualDatum_apply_katzTaoAtParameters_with_source
#print axioms exists_sampledCard_apply_katzTaoAtParameters_with_source_automatic

end
end Family8GeneralizedKatzTaoPolynomialSamplingV1
