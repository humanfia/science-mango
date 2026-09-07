import Family8Grounding.Family8GeneralizedKatzTaoPolynomialSamplingV1
import Family8Grounding.Family8FrostmanOneFromPointwisePackingV1
import Mathlib.Tactic

open scoped ENNReal NNReal

namespace Family8GeneralizedKatzTaoSamplingNumericsV1

open Family8KatzTaoFrostmanPropertiesV1
open Family8GeneralizedKatzTaoMultiplicityV1
open Family8ZeroColorPolynomialJohnKatzTaoV1
open Family8KatzTaoSamplingMultiplicityV1
open Family8KatzTaoSamplingDensityBudgetV1
open Family8KatzTaoJohnCoefficientBudgetV1
open Family8PolynomialJohnFrameBoxVolumeV2
open Family8GeneralizedKatzTaoPolynomialSamplingV1
open Family8FrostmanOneFromPointwisePackingV1
open FamilyStickyScaleChainSmallDeltaExponentBudgetProducerV1

noncomputable section

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 2000000

/-!
# Numerical return from polynomial John sampling

This module converts the real sampled-cardinality estimate into the native
`ENNReal` scaling identity used by generalized Katz--Tao.  The nontrivial
sampling branch is kept separate from the small-family cardinality branch.
-/

/-- If the sampling multiplicity does not exceed the source cardinality,
the real `max 1 (#T/k)` cap gives the division-free native estimate
`k * #T_sample <= tail * #T`. -/
theorem samplingMultiplicity_mul_sampledCard_le_tail_mul_card
    {k sampledCard tubeCount : Nat} {tail : Real}
    (hk : 0 < k) (hkCard : k ≤ tubeCount) (htail : 0 ≤ tail)
    (hcard :
      (sampledCard : Real) ≤
        tail * max 1 ((tubeCount : Real) / (k : Real))) :
    (k : ENNReal) * (sampledCard : ENNReal) ≤
      ENNReal.ofReal tail * (tubeCount : ENNReal) := by
  have hkReal : 0 < (k : Real) := by exact_mod_cast hk
  have hkCardReal : (k : Real) ≤ (tubeCount : Real) := by exact_mod_cast hkCard
  have hratio : 1 ≤ (tubeCount : Real) / (k : Real) := by
    exact (le_div_iff₀ hkReal).2 (by simpa using hkCardReal)
  have hcard' :
      (sampledCard : Real) ≤ tail * ((tubeCount : Real) / (k : Real)) := by
    simpa [max_eq_right hratio] using hcard
  have hreal :
      (k : Real) * (sampledCard : Real) ≤ tail * (tubeCount : Real) := by
    calc
      (k : Real) * (sampledCard : Real) ≤
          (k : Real) * (tail * ((tubeCount : Real) / (k : Real))) := by
            exact mul_le_mul_of_nonneg_left hcard' hkReal.le
      _ = tail * (tubeCount : Real) := by
            field_simp [hkReal.ne']
  have hleftTop :
      (k : ENNReal) * (sampledCard : ENNReal) ≠ ∞ :=
    ENNReal.mul_ne_top ENNReal.coe_ne_top ENNReal.coe_ne_top
  have hrightTop :
      ENNReal.ofReal tail * (tubeCount : ENNReal) ≠ ∞ :=
    ENNReal.mul_ne_top ENNReal.ofReal_ne_top ENNReal.coe_ne_top
  apply (ENNReal.toReal_le_toReal hleftTop hrightTop).mp
  simpa [ENNReal.toReal_mul, ENNReal.toReal_ofReal htail] using hreal

/-- Native sampling-return algebra.  The hypothesis on `k * sampledCard` is
exactly the division-free conclusion of the preceding theorem.  The finite
factor four is absorbed below one explicit small-scale threshold. -/
theorem returnedSample_le_generalizedKatzTaoMultiplicityRHS
    {delta : NNReal} {C : ENNReal} {k sampledCard tubeCount : Nat}
    {epsilon eta absorbEta beta : Real}
    (hdelta : 0 < delta)
    (hk : 0 < k)
    (hbeta0 : 0 ≤ beta) (hbeta1 : beta ≤ 1)
    (habsorbEta : 0 < absorbEta)
    (hkC : (k : ENNReal) ≤ 2 * C)
    (hscaledCard :
      (k : ENNReal) * (sampledCard : ENNReal) ≤
        (delta : ENNReal) ^ (-eta) * (tubeCount : ENNReal))
    (hdeltaThreshold :
      delta ≤ finiteConstantSmallDeltaThreshold 4 absorbEta) :
    ((2 * k : Nat) : ENNReal) *
        katzTaoMultiplicityRHS delta sampledCard epsilon beta ≤
      generalizedKatzTaoMultiplicityRHS delta C tubeCount
        (epsilon + beta * eta + absorbEta) beta := by
  let d : ENNReal := (delta : ENNReal)
  let K : ENNReal := (k : ENNReal)
  let S : ENNReal := (sampledCard : ENNReal)
  let N : ENNReal := (tubeCount : ENNReal)
  have hd0 : d ≠ 0 := ENNReal.coe_ne_zero.mpr hdelta.ne'
  have hdTop : d ≠ ∞ := ENNReal.coe_ne_top
  have hK0 : K ≠ 0 := by simp [K, hk.ne']
  have hKTop : K ≠ ∞ := by simp [K]
  have hOneSub : 0 ≤ 1 - beta := by linarith
  have hKfactor :
      K * S ^ beta = K ^ (1 - beta) * (K * S) ^ beta := by
    symm
    calc
      K ^ (1 - beta) * (K * S) ^ beta =
          K ^ (1 - beta) * (K ^ beta * S ^ beta) := by
            rw [ENNReal.mul_rpow_of_nonneg _ _ hbeta0]
      _ = (K ^ (1 - beta) * K ^ beta) * S ^ beta := by
            rw [mul_assoc]
      _ = K ^ ((1 - beta) + beta) * S ^ beta := by
            rw [ENNReal.rpow_add (1 - beta) beta hK0 hKTop]
      _ = K * S ^ beta := by
            rw [show (1 - beta) + beta = (1 : Real) by ring, ENNReal.rpow_one]
  have hKpow :
      K ^ (1 - beta) ≤ (2 * C) ^ (1 - beta) :=
    ENNReal.rpow_le_rpow (by simpa only [K] using hkC) hOneSub
  have hscaledPow :
      (K * S) ^ beta ≤ (d ^ (-eta) * N) ^ beta :=
    ENNReal.rpow_le_rpow
      (by simpa only [K, S, d, N] using hscaledCard) hbeta0
  have htwoPow : (2 : ENNReal) ^ (1 - beta) ≤ 2 := by
    calc
      (2 : ENNReal) ^ (1 - beta) ≤ (2 : ENNReal) ^ (1 : Real) :=
        ENNReal.rpow_le_rpow_of_exponent_le (by norm_num) (by linarith)
      _ = 2 := by simp
  have htwoFactor :
      (2 : ENNReal) * (2 : ENNReal) ^ (1 - beta) ≤ 4 := by
    calc
      _ ≤ 2 * 2 := mul_le_mul_right htwoPow 2
      _ = 4 := by norm_num
  have hfour : (4 : ENNReal) ≤ d ^ (-absorbEta) := by
    simpa only [d] using finiteConstant_le_delta_negativePower
      (K := (4 : ENNReal)) (by norm_num) habsorbEta hdelta hdeltaThreshold
  have hdecomp :
      (2 * C) ^ (1 - beta) * (d ^ (-eta) * N) ^ beta =
        ((2 : ENNReal) ^ (1 - beta) * C ^ (1 - beta)) *
          (d ^ ((-eta) * beta) * N ^ beta) := by
    rw [ENNReal.mul_rpow_of_nonneg _ _ hOneSub,
      ENNReal.mul_rpow_of_nonneg _ _ hbeta0, ENNReal.rpow_mul]
  have hdpow :
      (d ^ (-absorbEta) * d ^ (-epsilon)) * d ^ ((-eta) * beta) =
        d ^ (-(epsilon + beta * eta + absorbEta)) := by
    rw [← ENNReal.rpow_add (-absorbEta) (-epsilon) hd0 hdTop,
      ← ENNReal.rpow_add ((-absorbEta) + (-epsilon))
        ((-eta) * beta) hd0 hdTop]
    congr 1
    ring
  unfold katzTaoMultiplicityRHS generalizedKatzTaoMultiplicityRHS
  rw [Nat.cast_mul]
  change (2 * K) * (d ^ (-epsilon) * S ^ beta) ≤
    d ^ (-(epsilon + beta * eta + absorbEta)) *
      C ^ (1 - beta) * N ^ beta
  calc
    (2 * K) * (d ^ (-epsilon) * S ^ beta) =
        2 * d ^ (-epsilon) * (K * S ^ beta) := by ac_rfl
    _ = 2 * d ^ (-epsilon) *
        (K ^ (1 - beta) * (K * S) ^ beta) := by rw [hKfactor]
    _ ≤ 2 * d ^ (-epsilon) *
        ((2 * C) ^ (1 - beta) * (d ^ (-eta) * N) ^ beta) := by
          gcongr
    _ = 2 * d ^ (-epsilon) *
        (((2 : ENNReal) ^ (1 - beta) * C ^ (1 - beta)) *
          (d ^ ((-eta) * beta) * N ^ beta)) := by rw [hdecomp]
    _ = (2 * (2 : ENNReal) ^ (1 - beta)) *
        (d ^ (-epsilon) * (C ^ (1 - beta) *
          (d ^ ((-eta) * beta) * N ^ beta))) := by ac_rfl
    _ ≤ 4 * d ^ (-epsilon) *
        (C ^ (1 - beta) * (d ^ ((-eta) * beta) * N ^ beta)) := by
          simpa only [mul_assoc] using (mul_le_mul_left htwoFactor
            (d ^ (-epsilon) * (C ^ (1 - beta) * (d ^ ((-eta) * beta) * N ^ beta))))
    _ ≤ d ^ (-absorbEta) * d ^ (-epsilon) *
        (C ^ (1 - beta) * (d ^ ((-eta) * beta) * N ^ beta)) := by
          gcongr
    _ = d ^ (-(epsilon + beta * eta + absorbEta)) *
        C ^ (1 - beta) * N ^ beta := by
          rw [← hdpow]
          ac_rfl

/-- The complete nontrivial sampling branch.  Every catalogue, density and
finite-constant loss is discharged by an explicit threshold; the only
branch hypothesis is the honest arithmetic condition `k ≤ #T`. -/
theorem averageMultiplicity_le_generalizedKatzTaoMultiplicityRHS_of_samplingBranch
    {beta epsilon sourceEta tailEta constantEta absorbEta : Real}
    {delta0 delta : NNReal}
    {iota : Type} [Fintype iota] [DecidableEq iota]
    (hKT : KatzTaoAtParameters beta epsilon (tailEta + constantEta) delta0)
    (D : ActualTubeDatum delta iota) (hD : D.IsAdmissible)
    (hdelta0 : delta ≤ delta0)
    (hsourceEta : 0 ≤ sourceEta)
    (htailEta : 0 < tailEta) (hconstantEta : 0 < constantEta)
    (hgap : 0 < tailEta + constantEta - 2 * sourceEta)
    (hbeta0 : 0 ≤ beta) (hbeta1 : beta ≤ 1)
    (habsorbEta : 0 < absorbEta)
    (hdeltaDensityThreshold :
      delta ≤ katzTaoSamplingDensityThreshold
        (tailEta + constantEta) sourceEta)
    (hdeltaCoefficientThreshold :
      delta ≤ johnCoefficientThreshold johnCataloguePolynomialCostConstant
        (15 + sourceEta) tailEta constantEta)
    (hdeltaFactorThreshold :
      delta ≤ finiteConstantSmallDeltaThreshold 4 absorbEta)
    (hHypotheses : KatzTaoHypotheses D sourceEta)
    (hkCard :
      katzTaoSamplingMultiplicity
          ((delta : ENNReal) ^ (-sourceEta)) ≤ Fintype.card iota) :
    D.shading.averageMultiplicity ≤
      generalizedKatzTaoMultiplicityRHS delta
        ((delta : ENNReal) ^ (-sourceEta)) (Fintype.card iota)
          (epsilon + beta * (tailEta + constantEta) + absorbEta) beta := by
  let C : ENNReal := (delta : ENNReal) ^ (-sourceEta)
  let k : Nat := katzTaoSamplingMultiplicity C
  have hCone : 1 ≤ C := by
    dsimp only [C]
    rw [← ENNReal.coe_rpow_of_ne_zero hD.delta_pos.ne' (-sourceEta)]
    exact_mod_cast NNReal.one_le_rpow_of_pos_of_le_one_of_nonpos
      hD.delta_pos (hD.delta_le_half.trans (by norm_num)) (by linarith)
  have hCfinite : C ≠ ∞ := by
    exact ENNReal.rpow_ne_top_of_ne_zero
      (ENNReal.coe_ne_zero.mpr hD.delta_pos.ne') ENNReal.coe_ne_top
  have hk : 0 < k :=
    katzTaoSamplingMultiplicity_pos (zero_lt_one.trans_le hCone) hCfinite
  obtain ⟨sampledCard, hcard, hsourceBound⟩ :=
    exists_sampledCard_apply_katzTaoAtParameters_with_source_of_hypotheses
      hKT D hD hdelta0 hsourceEta htailEta hconstantEta hgap
        hdeltaDensityThreshold hdeltaCoefficientThreshold hHypotheses
  have hscaledTail :
      (k : ENNReal) * (sampledCard : ENNReal) ≤
        ENNReal.ofReal (polynomialJohnTailParameter delta k) *
          (Fintype.card iota : ENNReal) := by
    apply samplingMultiplicity_mul_sampledCard_le_tail_mul_card
      hk (by simpa only [k, C] using hkCard)
      (zero_le_one.trans (one_le_polynomialJohnTailParameter delta k))
    simpa only [k, C, averageZeroColorCardinalCap] using hcard
  have hcoefficient :
      ENNReal.ofReal (polynomialJohnTailParameter delta k) *
          johnCatalogueVolumeConstant ≤
        (delta : ENNReal) ^ (-(tailEta + constantEta)) := by
    simpa only [k, C] using automaticPolynomialJohn_coefficient_le_rpow
      hD.delta_pos (hD.delta_le_half.trans (by norm_num)) hsourceEta
        htailEta hconstantEta hCfinite hCone le_rfl
          hdeltaCoefficientThreshold
  have hJohnOne : (1 : ENNReal) ≤ johnCatalogueVolumeConstant := by
    norm_num [johnCatalogueVolumeConstant]
  have htailBound :
      ENNReal.ofReal (polynomialJohnTailParameter delta k) ≤
        (delta : ENNReal) ^ (-(tailEta + constantEta)) := by
    calc
      ENNReal.ofReal (polynomialJohnTailParameter delta k) =
          ENNReal.ofReal (polynomialJohnTailParameter delta k) * 1 := by simp
      _ ≤ ENNReal.ofReal (polynomialJohnTailParameter delta k) *
          johnCatalogueVolumeConstant :=
        mul_le_mul_right hJohnOne _
      _ ≤ (delta : ENNReal) ^ (-(tailEta + constantEta)) := hcoefficient
  have hscaledCard :
      (k : ENNReal) * (sampledCard : ENNReal) ≤
        (delta : ENNReal) ^ (-(tailEta + constantEta)) *
          (Fintype.card iota : ENNReal) :=
    hscaledTail.trans (mul_le_mul_left htailBound _)
  have hkC : (k : ENNReal) ≤ 2 * C :=
    katzTaoSamplingMultiplicity_coe_le_two_mul hCone hCfinite
  exact hsourceBound.trans (by
    simpa only [k, C] using
      returnedSample_le_generalizedKatzTaoMultiplicityRHS
        hD.delta_pos hk hbeta0 hbeta1 habsorbEta hkC hscaledCard
          hdeltaFactorThreshold)

/-- Complementary small-family branch.  When `#T < ceil(C)`, ceiling
minimality gives `#T < C`; the pointwise cardinality cap is already stronger
than the generalized Katz--Tao interpolation target. -/
theorem averageMultiplicity_le_generalizedKatzTaoMultiplicityRHS_of_card_lt_samplingMultiplicity
    {beta epsilon sourceEta tailEta constantEta absorbEta : Real}
    {delta : NNReal}
    {iota : Type} [Fintype iota] [DecidableEq iota]
    (D : ActualTubeDatum delta iota) (hD : D.IsAdmissible)
    (hepsilon0 : 0 ≤ epsilon)
    (htailEta : 0 < tailEta) (hconstantEta : 0 < constantEta)
    (hbeta0 : 0 ≤ beta) (hbeta1 : beta ≤ 1)
    (habsorbEta : 0 < absorbEta)
    (hCard :
      Fintype.card iota < katzTaoSamplingMultiplicity
        ((delta : ENNReal) ^ (-sourceEta))) :
    D.shading.averageMultiplicity ≤
      generalizedKatzTaoMultiplicityRHS delta
        ((delta : ENNReal) ^ (-sourceEta)) (Fintype.card iota)
          (epsilon + beta * (tailEta + constantEta) + absorbEta) beta := by
  let d : ENNReal := (delta : ENNReal)
  let C : ENNReal := d ^ (-sourceEta)
  let N : ENNReal := (Fintype.card iota : ENNReal)
  have hd0 : d ≠ 0 := ENNReal.coe_ne_zero.mpr hD.delta_pos.ne'
  have hCfinite : C ≠ ∞ := by
    exact ENNReal.rpow_ne_top_of_ne_zero hd0 ENNReal.coe_ne_top
  have hNRealC : (Fintype.card iota : Real) < C.toReal := by
    have hceil :
        (Fintype.card iota : Real) < C.toReal := by
      exact Nat.lt_ceil.mp (by simpa only [katzTaoSamplingMultiplicity, C, d] using hCard)
    exact hceil
  have hNC : N ≤ C := by
    apply le_of_lt
    apply (ENNReal.toReal_lt_toReal ENNReal.coe_ne_top hCfinite).mp
    change (Fintype.card iota : Real) < C.toReal
    exact hNRealC
  have hOneSub : 0 ≤ 1 - beta := by linarith
  have hNpow : N ^ (1 - beta) ≤ C ^ (1 - beta) :=
    ENNReal.rpow_le_rpow hNC hOneSub
  have hNfactor : N = N ^ (1 - beta) * N ^ beta := by
    calc
      N = N ^ (1 : Real) := (ENNReal.rpow_one N).symm
      _ = N ^ ((1 - beta) + beta) := by congr 1; ring
      _ = N ^ (1 - beta) * N ^ beta :=
        ENNReal.rpow_add_of_nonneg (1 - beta) beta hOneSub hbeta0
  have hfinalNonneg :
      0 ≤ epsilon + beta * (tailEta + constantEta) + absorbEta := by
    have hsum : 0 < tailEta + constantEta := by linarith
    have hproduct : 0 ≤ beta * (tailEta + constantEta) := mul_nonneg hbeta0 hsum.le
    linarith
  have hlossOne :
      1 ≤ d ^ (-(epsilon + beta * (tailEta + constantEta) + absorbEta)) := by
    dsimp only [d]
    rw [← ENNReal.coe_rpow_of_ne_zero hD.delta_pos.ne'
      (-(epsilon + beta * (tailEta + constantEta) + absorbEta))]
    exact_mod_cast NNReal.one_le_rpow_of_pos_of_le_one_of_nonpos
      hD.delta_pos (hD.delta_le_half.trans (by norm_num))
        (neg_nonpos.mpr hfinalNonneg)
  have havg : D.shading.averageMultiplicity ≤ N := by
    simpa only [N] using averageMultiplicity_le_indexCard D.shading
  unfold generalizedKatzTaoMultiplicityRHS
  change D.shading.averageMultiplicity ≤
    d ^ (-(epsilon + beta * (tailEta + constantEta) + absorbEta)) *
      C ^ (1 - beta) * N ^ beta
  calc
    D.shading.averageMultiplicity ≤ N := havg
    _ = N ^ (1 - beta) * N ^ beta := hNfactor
    _ ≤ C ^ (1 - beta) * N ^ beta := mul_le_mul_left hNpow _
    _ = 1 * (C ^ (1 - beta) * N ^ beta) := by simp
    _ ≤ d ^ (-(epsilon + beta * (tailEta + constantEta) + absorbEta)) *
        (C ^ (1 - beta) * N ^ beta) := mul_le_mul_left hlossOne _
    _ = d ^ (-(epsilon + beta * (tailEta + constantEta) + absorbEta)) *
        C ^ (1 - beta) * N ^ beta := by rw [mul_assoc]

/-- Branch-free, paper-shaped generalized Katz--Tao source estimate.  The
proof decides the literal finite-cardinality comparison; neither branch is
exposed as an input and no multiplicity conclusion is assumed upstream. -/
theorem averageMultiplicity_le_generalizedKatzTaoMultiplicityRHS_of_katzTaoHypotheses
    {beta epsilon sourceEta tailEta constantEta absorbEta : Real}
    {delta0 delta : NNReal}
    {iota : Type} [Fintype iota] [DecidableEq iota]
    (hKT : KatzTaoAtParameters beta epsilon (tailEta + constantEta) delta0)
    (D : ActualTubeDatum delta iota) (hD : D.IsAdmissible)
    (hdelta0 : delta ≤ delta0)
    (hsourceEta : 0 ≤ sourceEta)
    (hepsilon0 : 0 ≤ epsilon)
    (htailEta : 0 < tailEta) (hconstantEta : 0 < constantEta)
    (hgap : 0 < tailEta + constantEta - 2 * sourceEta)
    (hbeta0 : 0 ≤ beta) (hbeta1 : beta ≤ 1)
    (habsorbEta : 0 < absorbEta)
    (hdeltaDensityThreshold :
      delta ≤ katzTaoSamplingDensityThreshold
        (tailEta + constantEta) sourceEta)
    (hdeltaCoefficientThreshold :
      delta ≤ johnCoefficientThreshold johnCataloguePolynomialCostConstant
        (15 + sourceEta) tailEta constantEta)
    (hdeltaFactorThreshold :
      delta ≤ finiteConstantSmallDeltaThreshold 4 absorbEta)
    (hHypotheses : KatzTaoHypotheses D sourceEta) :
    D.shading.averageMultiplicity ≤
      generalizedKatzTaoMultiplicityRHS delta
        ((delta : ENNReal) ^ (-sourceEta)) (Fintype.card iota)
          (epsilon + beta * (tailEta + constantEta) + absorbEta) beta := by
  by_cases hkCard :
      katzTaoSamplingMultiplicity
          ((delta : ENNReal) ^ (-sourceEta)) ≤ Fintype.card iota
  · exact
      averageMultiplicity_le_generalizedKatzTaoMultiplicityRHS_of_samplingBranch
        hKT D hD hdelta0 hsourceEta htailEta hconstantEta hgap
          hbeta0 hbeta1 habsorbEta hdeltaDensityThreshold
            hdeltaCoefficientThreshold hdeltaFactorThreshold hHypotheses hkCard
  · exact
      averageMultiplicity_le_generalizedKatzTaoMultiplicityRHS_of_card_lt_samplingMultiplicity
        D hD hepsilon0 htailEta hconstantEta hbeta0 hbeta1 habsorbEta
          (Nat.lt_of_not_ge hkCard)

#print axioms
  averageMultiplicity_le_generalizedKatzTaoMultiplicityRHS_of_katzTaoHypotheses

#print axioms
  averageMultiplicity_le_generalizedKatzTaoMultiplicityRHS_of_card_lt_samplingMultiplicity

#print axioms
  averageMultiplicity_le_generalizedKatzTaoMultiplicityRHS_of_samplingBranch

#print axioms returnedSample_le_generalizedKatzTaoMultiplicityRHS

#print axioms samplingMultiplicity_mul_sampledCard_le_tail_mul_card

end
end Family8GeneralizedKatzTaoSamplingNumericsV1
