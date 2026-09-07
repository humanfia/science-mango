import Family8Grounding.Family8ZeroColorPolynomialJohnScaleContainedV2
import Family8Grounding.Family8ZeroColorSampledDensityCardCancellationV1
import Family8Grounding.Family8ScaleContainedB2FreshKatzTaoEndpointV1
import Family8Grounding.Family8ZeroColorMultiplicityRetentionV1
import Family8Grounding.Family8KatzTaoSamplingMultiplicityV1
import Submission.Kakeya.ConvexFactoring.InducedShadingDensityAlgebra
import Mathlib.Tactic

open Set MeasureTheory
open scoped ENNReal NNReal BigOperators

namespace Family8ExplicitConcentrationSamplingFreshKatzTaoV1

open LeanEval.Analysis.WangZahlKakeya
open Submission.Kakeya.ConvexGeometry
open Submission.Kakeya.ConvexFactoring
open Submission.Kakeya.ConvexFactoring.InducedShadingDensityAlgebra
open Family8KatzTaoFrostmanPropertiesV1
open Family8GeneralizedKatzTaoMultiplicityV1
open Family8ZeroColorPolynomialJohnKatzTaoV1
open Family8ZeroColorPolynomialJohnScaleContainedV2
open Family8ZeroColorSampledDensityCardCancellationV1
open Family8ScaleContainedB2FreshKatzTaoEndpointV1
open Family8ZeroColorMultiplicityRetentionV1
open Family8KatzTaoSamplingMultiplicityV1
open Family8PolynomialJohnFrameBoxVolumeV2
open Family8FrozenCoarseB2DensityTransportScaleOnlyV1
open FamilyStickyCinematicL32Prop41FiniteRandomSamplingExtractionV1

noncomputable section

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 4000000

/-!
# Explicit-concentration generalized Katz--Tao sampling with fresh selection

The source is allowed to have coincident tubes.  Polynomial-John sampling
first reduces the source concentration from `C` to a logarithmic coefficient.
The sampled cardinality gain cancels the sampling multiplicity in density.
Only then does B2-normalized fresh selection manufacture an admissible datum
to which the actual fixed-parameter Katz--Tao theorem is applied.
-/

def explicitConcentrationSamplingMultiplicity (C : ENNReal) : Nat :=
  katzTaoSamplingMultiplicity C

def explicitConcentrationSamplingTail (delta : NNReal) (C : ENNReal) : Real :=
  polynomialJohnTailParameter delta
    (explicitConcentrationSamplingMultiplicity C)

def explicitConcentrationSampleKatzTaoConstant
    (delta : NNReal) (C : ENNReal) : ENNReal :=
  ENNReal.ofReal (explicitConcentrationSamplingTail delta C) *
    johnCatalogueVolumeConstant

theorem explicitConcentrationSamplingTail_pos
    (delta : NNReal) (C : ENNReal) :
    0 < explicitConcentrationSamplingTail delta C := by
  unfold explicitConcentrationSamplingTail
  exact zero_lt_one.trans_le
    (one_le_polynomialJohnTailParameter delta
      (explicitConcentrationSamplingMultiplicity C))

theorem explicitConcentrationSampleKatzTaoConstant_ne_top
    (delta : NNReal) (C : ENNReal) :
    explicitConcentrationSampleKatzTaoConstant delta C ≠ ∞ := by
  unfold explicitConcentrationSampleKatzTaoConstant
  exact ENNReal.mul_ne_top (by simp)
    (by norm_num [johnCatalogueVolumeConstant])

/-- Complete nontrivial sampling branch before the final pure-power
absorption.  Every object in the conclusion comes from the same zero-colour
sample and the same fresh selected subtype. -/
theorem exists_sample_and_fresh_katzTao_of_explicit_concentration
    {beta epsilon eta : Real} {delta0 delta : NNReal}
    {iota : Type} [Fintype iota] [Nonempty iota] [DecidableEq iota]
    (hKTP : KatzTaoAtParameters beta epsilon eta delta0)
    (D : ActualTubeDatum delta iota)
    (hdeltaPos : 0 < delta)
    (hdeltaHalf : delta <= (2 : NNReal)⁻¹)
    (hsupport : forall i,
      (D.family.tubes i).carrier ⊆ Metric.closedBall (0 : Space) 1)
    {C : ENNReal} (hCone : 1 <= C) (hCfinite : C ≠ ∞)
    (hKT : IsKatzTao C D.family.bodyFamily)
    (hkCard : explicitConcentrationSamplingMultiplicity C <=
      Fintype.card iota)
    (hdelta0 : delta / 8 <= delta0)
    (hdensityBudget :
      ((((delta / 8 : NNReal) : ENNReal) ^ eta) *
          (128 * (sourceKatzTaoFreshLoss
            (explicitConcentrationSampleKatzTaoConstant delta C) : ENNReal))) *
        (32 * ENNReal.ofReal
          (explicitConcentrationSamplingTail delta C)) <=
        D.shading.shadingDensity)
    (hcoefficient :
      128 * explicitConcentrationSampleKatzTaoConstant delta C <=
        ((delta / 8 : NNReal) : ENNReal) ^ (-eta)) :
    exists sampledCard selectedCard : Nat,
      (explicitConcentrationSamplingMultiplicity C : ENNReal) *
          (sampledCard : ENNReal) <=
        ENNReal.ofReal (explicitConcentrationSamplingTail delta C) *
          (Fintype.card iota : ENNReal) ∧
      selectedCard <= sampledCard ∧
      D.shading.averageMultiplicity <=
        ((2 * explicitConcentrationSamplingMultiplicity C : Nat) : ENNReal) *
          (sourceKatzTaoFreshLoss
            (explicitConcentrationSampleKatzTaoConstant delta C) : ENNReal) *
          katzTaoMultiplicityRHS (delta / 8) selectedCard epsilon beta := by
  let k := explicitConcentrationSamplingMultiplicity C
  let tail := explicitConcentrationSamplingTail delta C
  let Csample := explicitConcentrationSampleKatzTaoConstant delta C
  have hk : 0 < k := by
    exact katzTaoSamplingMultiplicity_pos (zero_lt_one.trans_le hCone) hCfinite
  let _ : NeZero k := ⟨hk.ne'⟩
  obtain ⟨omega, hretained, hcard, hsampleKT⟩ :=
    exists_zeroColorActualDatum_polynomialJohn_isKatzTao_of_scale_contained
      D hdeltaPos hdeltaHalf hsupport C k hKT hCfinite
        (toReal_div_katzTaoSamplingMultiplicity_le_one
          (zero_lt_one.trans_le hCone) hCfinite)
  let sampled := zeroColorActualDatum D k omega
  have htail0 : 0 <= tail :=
    (explicitConcentrationSamplingTail_pos delta C).le
  have hscaledCard :
      (k : ENNReal) * ((zeroColorSample k omega).card : ENNReal) <=
        ENNReal.ofReal tail * (Fintype.card iota : ENNReal) := by
    exact scaledCard_le_tail_mul_card_of_real_bound
      k (zeroColorSample k omega) tail htail0
        (by simpa only [k, explicitConcentrationSamplingMultiplicity] using hkCard)
        (by simpa only [tail, explicitConcentrationSamplingTail] using hcard)
  have hsourceToSampleDensity :
      D.shading.shadingDensity <=
        (32 * ENNReal.ofReal tail) * sampled.shading.shadingDensity := by
    exact source_shadingDensity_le_thirtyTwo_tail_mul_zeroColor
      D hdeltaHalf k omega tail hretained hscaledCard
  have htailFactorPos : 0 < (32 * ENNReal.ofReal tail : ENNReal) := by
    exact ENNReal.mul_pos (by norm_num)
      (ENNReal.ofReal_pos.mpr (explicitConcentrationSamplingTail_pos delta C)).ne'
  have htailFactor0 : (32 * ENNReal.ofReal tail : ENNReal) ≠ 0 :=
    htailFactorPos.ne'
  have htailFactorTop : (32 * ENNReal.ofReal tail : ENNReal) ≠ ∞ :=
    ENNReal.mul_ne_top (by norm_num) (by simp)
  have hsampleDensityBudget :
      (((delta / 8 : NNReal) : ENNReal) ^ eta) *
          (128 * (sourceKatzTaoFreshLoss Csample : ENNReal)) <=
        sampled.shading.shadingDensity := by
    apply (ENNReal.mul_le_mul_iff_right htailFactor0 htailFactorTop).mp
    calc
      (32 * ENNReal.ofReal tail) *
          ((((delta / 8 : NNReal) : ENNReal) ^ eta) *
            (128 * (sourceKatzTaoFreshLoss Csample : ENNReal))) =
        ((((delta / 8 : NNReal) : ENNReal) ^ eta) *
            (128 * (sourceKatzTaoFreshLoss Csample : ENNReal))) *
          (32 * ENNReal.ofReal tail) := by ac_rfl
      _ <= D.shading.shadingDensity := by
        simpa only [tail, Csample, explicitConcentrationSamplingTail,
          explicitConcentrationSampleKatzTaoConstant] using hdensityBudget
      _ <= (32 * ENNReal.ofReal tail) *
          sampled.shading.shadingDensity := hsourceToSampleDensity
  have hsourceDensityPos : 0 < D.shading.shadingDensity := by
    have hscalePos : 0 < (((delta / 8 : NNReal) : ENNReal)) :=
      ENNReal.coe_pos.mpr (div_pos hdeltaPos (by norm_num))
    have hrpowPos :
        0 < ((delta / 8 : NNReal) : ENNReal) ^ eta :=
      ENNReal.rpow_pos hscalePos ENNReal.coe_ne_top
    have hlossPos :
        0 < (sourceKatzTaoFreshLoss Csample : ENNReal) := by
      exact_mod_cast sourceKatzTaoFreshLoss_pos Csample
    have hnormalizedLossPos :
        0 < (128 * (sourceKatzTaoFreshLoss Csample : ENNReal) : ENNReal) :=
      ENNReal.mul_pos (by norm_num) hlossPos.ne'
    have hleftPos :
        0 < ((((delta / 8 : NNReal) : ENNReal) ^ eta) *
          (128 * (sourceKatzTaoFreshLoss Csample : ENNReal))) *
            (32 * ENNReal.ofReal tail) := by
      exact ENNReal.mul_pos
        (ENNReal.mul_pos hrpowPos.ne' hnormalizedLossPos.ne').ne'
        htailFactorPos.ne'
    exact hleftPos.trans_le (by
      simpa only [tail, Csample, explicitConcentrationSamplingTail,
        explicitConcentrationSampleKatzTaoConstant] using hdensityBudget)
  have hsourceVolumePos : 0 < familyVolume D.family.bodyFamily :=
    actualDatum_familyVolume_pos_of_scale D hdeltaPos
  have hsourceMassPos : 0 < D.shading.shadingMass := by
    rw [← shadingDensity_mul_familyVolume D.shading]
    exact ENNReal.mul_pos hsourceDensityPos.ne' hsourceVolumePos.ne'
  have hsourceMassRealPos : 0 < D.shading.shadingMass.toReal :=
    ENNReal.toReal_pos hsourceMassPos.ne' D.shading.shadingMass_lt_top.ne
  have hsampleMassRealPos : 0 < sampled.shading.shadingMass.toReal := by
    have hdenom : 0 < 2 * (k : Real) := by positivity
    exact (div_pos hsourceMassRealPos hdenom).trans_le
      (by simpa only [sampled] using hretained)
  have hsampleNonempty : (zeroColorSample k omega).Nonempty := by
    by_contra hempty
    rw [Finset.not_nonempty_iff_eq_empty] at hempty
    have hsampleMassZero : sampled.shading.shadingMass = 0 := by
      dsimp only [sampled]
      change (restrictActualTubeDatum D
        (zeroColorSample k omega)).shading.shadingMass = 0
      rw [restrictActualTubeDatum_shadingMass, hempty]
      simp
    rw [hsampleMassZero, ENNReal.toReal_zero] at hsampleMassRealPos
    exact lt_irrefl 0 hsampleMassRealPos
  let _ : Nonempty {i // i ∈ zeroColorSample k omega} :=
    Finset.nonempty_coe_sort.mpr hsampleNonempty
  have hsampleSupport : forall i,
      (sampled.family.tubes i).carrier ⊆ Metric.closedBall (0 : Space) 1 := by
    intro i
    exact hsupport i.1
  have hCsampleFinite : Csample ≠ ∞ := by
    simpa only [Csample] using
      explicitConcentrationSampleKatzTaoConstant_ne_top delta C
  obtain ⟨selected, hselected, hselectedCard, hsampleBound⟩ :=
    exists_fresh_apply_katzTaoAtParameters_of_scale_contained
      hKTP sampled hdeltaPos hdeltaHalf hsampleSupport hCsampleFinite
        (by simpa only [sampled, Csample, tail,
          explicitConcentrationSampleKatzTaoConstant,
          explicitConcentrationSamplingTail] using hsampleKT)
        hdelta0 hsampleDensityBudget
        (by simpa only [Csample] using hcoefficient)
  have hsourceAverage :=
    source_averageMultiplicity_le_two_mul_k_mul_zeroColorActualDatum
      D k omega hretained
  refine ⟨(zeroColorSample k omega).card, selected.card, ?_, ?_, ?_⟩
  · simpa only [k, tail] using hscaledCard
  · simpa using hselectedCard
  · calc
      D.shading.averageMultiplicity <=
          ((2 * k : Nat) : ENNReal) * sampled.shading.averageMultiplicity :=
        by simpa only [sampled] using hsourceAverage
      _ <= ((2 * k : Nat) : ENNReal) *
          ((sourceKatzTaoFreshLoss Csample : ENNReal) *
            katzTaoMultiplicityRHS (delta / 8) selected.card epsilon beta) := by
        gcongr
      _ = ((2 * k : Nat) : ENNReal) *
          (sourceKatzTaoFreshLoss Csample : ENNReal) *
            katzTaoMultiplicityRHS (delta / 8) selected.card epsilon beta := by
        ac_rfl
      _ = ((2 * explicitConcentrationSamplingMultiplicity C : Nat) : ENNReal) *
          (sourceKatzTaoFreshLoss
            (explicitConcentrationSampleKatzTaoConstant delta C) : ENNReal) *
            katzTaoMultiplicityRHS (delta / 8) selected.card epsilon beta := by
        rfl

#print axioms explicitConcentrationSamplingTail_pos
#print axioms explicitConcentrationSampleKatzTaoConstant_ne_top
#print axioms exists_sample_and_fresh_katzTao_of_explicit_concentration

end
end Family8ExplicitConcentrationSamplingFreshKatzTaoV1
