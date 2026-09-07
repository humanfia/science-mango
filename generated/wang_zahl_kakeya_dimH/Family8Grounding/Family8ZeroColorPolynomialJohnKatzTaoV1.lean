import Family8Grounding.Family8ZeroColorChernoffCardinalityConsumerV1
import Family8Grounding.Family8PolynomialJohnFrameBoxAllConvexV1
import Family8Grounding.Family8PolynomialJohnFrameBoxCardPowerV1
import Family8Grounding.Family8RestrictedActualDatumMassBridgeV1
import Family8Grounding.Family8RestrictedActualDatumDensityRetentionV1
import Mathlib.Tactic

open scoped ENNReal NNReal BigOperators
open MeasureTheory Set

namespace Family8ZeroColorPolynomialJohnKatzTaoV1

open LeanEval.Analysis.WangZahlKakeya
open Submission.Kakeya.ConvexGeometry
open Submission.Kakeya.ConvexFactoring
open Submission.Kakeya.Uniformity
open Family8KatzTaoFrostmanPropertiesV1
open Family8GeneralizedKatzTaoMultiplicityV1
open Family8ZeroColorChernoffCardinalityConsumerV1
open FamilyStickyCinematicL32Prop41FiniteRandomSamplingExtractionV1
open Family8RestrictedActualDatumMassBridgeV1
open Family8PolynomialJohnFrameBoxTestNetV1
open Family8RestrictedActualDatumDensityRetentionV1
open Family8PolynomialJohnFrameBoxVolumeV2
open Family8PolynomialJohnFrameBoxAllConvexV1
open Family8PolynomialJohnFrameBoxCardPowerV1

noncomputable section

set_option autoImplicit false
set_option warningAsError true
set_option linter.unusedSectionVars false
set_option maxHeartbeats 2000000

/-!
# One actual zero-colour sample controlled by the polynomial John catalogue

The same literal colouring controls the sampled cardinality, retains shaded
mass, and satisfies every occupied John-box test.  The polynomial all-convex
adapter then upgrades those finitely many estimates to a genuine IsKatzTao
statement for the actual restricted tube datum.
-/

/-- Real weight contributed by one source tube to one John catalogue test. -/
def polynomialJohnTestWeight
    {delta : NNReal} {iota : Type} [Fintype iota] [DecidableEq iota]
    (D : ActualTubeDatum delta iota) (hdelta : 0 < delta)
    (q : CatalogueIndex delta hdelta) (i : iota) : Real :=
  containedBodyRealWeight D.family.bodyFamily
    (representativeTestBody delta hdelta q) i

/-- Finite positive volume scale used to normalize one catalogue test. -/
def polynomialJohnTestCap
    {delta : NNReal} (hdelta : 0 < delta)
    (q : CatalogueIndex delta hdelta) : Real :=
  (volume (representativeTestBody delta hdelta q : Set Space)).toReal

theorem polynomialJohnTestCap_pos
    {delta : NNReal} (hdelta : 0 < delta)
    (q : CatalogueIndex delta hdelta) :
    0 < polynomialJohnTestCap hdelta q := by
  unfold polynomialJohnTestCap representativeTestBody
  apply ENNReal.toReal_pos
  · apply ne_of_gt
    apply FrameBox.volume_body_pos
    intro i
    rw [representativeTestBox, FrameBox.rescale_side,
      congrFun (representativeParameter delta hdelta q).certificate.side_eq i]
    have hside :=
      (representativeParameter delta hdelta q).two_mul_delta_le_side i
    have hsourceSide :
        0 < (representativeParameter delta hdelta q).side i :=
      lt_of_lt_of_le (mul_pos (by norm_num) hdelta) hside
    exact mul_pos (by norm_num) hsourceSide
  · exact (representativeTestBox delta hdelta q).body.isCompact.measure_lt_top.ne

theorem polynomialJohnTestWeight_nonneg
    {delta : NNReal} {iota : Type} [Fintype iota] [DecidableEq iota]
    (D : ActualTubeDatum delta iota) (hdelta : 0 < delta)
    (q : CatalogueIndex delta hdelta) (i : iota) :
    0 ≤ polynomialJohnTestWeight D hdelta q i := by
  unfold polynomialJohnTestWeight containedBodyRealWeight
  split_ifs <;> positivity

theorem polynomialJohnTestWeight_le_cap
    {delta : NNReal} {iota : Type} [Fintype iota] [DecidableEq iota]
    (D : ActualTubeDatum delta iota) (hdelta : 0 < delta)
    (q : CatalogueIndex delta hdelta) (i : iota) :
    polynomialJohnTestWeight D hdelta q i ≤
      polynomialJohnTestCap hdelta q := by
  unfold polynomialJohnTestWeight polynomialJohnTestCap
  unfold containedBodyRealWeight
  split_ifs with hi
  · apply ENNReal.toReal_mono
    · exact (representativeTestBody delta hdelta q).isCompact.measure_lt_top.ne
    · exact measure_mono hi
  · positivity

/-- A source Katz--Tao coefficient of average size at most one after the
one-over-k sampling factor supplies every catalogue mean hypothesis. -/
theorem polynomialJohnTest_mean_le_cap
    {delta : NNReal} {iota : Type} [Fintype iota] [DecidableEq iota]
    (D : ActualTubeDatum delta iota) (hdelta : 0 < delta)
    (C : ENNReal) (k : Nat) [NeZero k]
    (hsource : IsKatzTao C D.family.bodyFamily)
    (hCfinite : C ≠ ∞)
    (hCscale : C.toReal / (k : Real) ≤ 1)
    (q : CatalogueIndex delta hdelta) :
    (∑ i : iota, polynomialJohnTestWeight D hdelta q i) /
        (k : Real) ≤ polynomialJohnTestCap hdelta q := by
  have htest := hsource (representativeTestBody delta hdelta q)
  have htestReal :
      (containedMass D.family.bodyFamily
        (representativeTestBody delta hdelta q)).toReal ≤
      C.toReal * polynomialJohnTestCap hdelta q := by
    have hrightTop :
        C * volume (representativeTestBody delta hdelta q : Set Space) ≠ ∞ :=
      ENNReal.mul_ne_top hCfinite
        (representativeTestBody delta hdelta q).isCompact.measure_lt_top.ne
    have h := (ENNReal.toReal_le_toReal
      (containedMass_lt_top _ _).ne hrightTop).2 htest
    simpa [polynomialJohnTestCap, ENNReal.toReal_mul] using h
  change (∑ i : iota, containedBodyRealWeight D.family.bodyFamily
    (representativeTestBody delta hdelta q) i) / (k : Real) ≤ _
  rw [← containedMass_toReal_eq_sum_containedBodyRealWeight]
  calc
    (containedMass D.family.bodyFamily
        (representativeTestBody delta hdelta q)).toReal / (k : Real) ≤
      (C.toReal * polynomialJohnTestCap hdelta q) / (k : Real) := by
        gcongr
    _ = (C.toReal / (k : Real)) * polynomialJohnTestCap hdelta q := by ring
    _ ≤ 1 * polynomialJohnTestCap hdelta q := by
      exact mul_le_mul_of_nonneg_right hCscale (polynomialJohnTestCap_pos hdelta q).le
    _ = polynomialJohnTestCap hdelta q := one_mul _

def polynomialJohnCatalogueUpperCost
    (delta : NNReal) (k : Nat) : Real :=
  (2 * (k : Real)) *
    (((46082 / (delta : Real)) ^ 15 + 1) *
      Real.exp (Real.exp 1 - 1))

def polynomialJohnTailParameter
    (delta : NNReal) (k : Nat) : Real :=
  max 1 (Real.log (polynomialJohnCatalogueUpperCost delta k + 1))

theorem one_le_polynomialJohnTailParameter
    (delta : NNReal) (k : Nat) :
    1 ≤ polynomialJohnTailParameter delta k :=
  le_max_left _ _

/-- The floor catalogue is absorbed into one explicit logarithmic tail
parameter.  This is the promised polynomial, rather than exponential,
simultaneous-test cost. -/
theorem polynomialJohnTailRoom
    (delta : NNReal) (hdelta : 0 < delta)
    (hdeltaUpper : delta ≤ (1 / 2 : NNReal))
    (k : Nat) [NeZero k] :
    (2 * (k : Real)) *
        (((Fintype.card (CatalogueIndex delta hdelta) + 1 : Nat) : Real) *
          Real.exp (Real.exp 1 - 1)) <
      Real.exp (polynomialJohnTailParameter delta k) := by
  have hcard := card_catalogueIndex_real_le_div_pow
    delta hdelta hdeltaUpper
  have hcardPlus :
      ((Fintype.card (CatalogueIndex delta hdelta) + 1 : Nat) : Real) ≤
        (46082 / (delta : Real)) ^ 15 + 1 := by
    norm_num only [Nat.cast_add, Nat.cast_one]
    linarith
  have hactualUpper :
      (2 * (k : Real)) *
          (((Fintype.card (CatalogueIndex delta hdelta) + 1 : Nat) : Real) *
            Real.exp (Real.exp 1 - 1)) ≤
        polynomialJohnCatalogueUpperCost delta k := by
    unfold polynomialJohnCatalogueUpperCost
    apply mul_le_mul_of_nonneg_left
    · apply mul_le_mul_of_nonneg_right
      · simpa using hcardPlus
      · exact (Real.exp_pos _).le
    · positivity
  have hcost0 : 0 ≤ polynomialJohnCatalogueUpperCost delta k := by
    unfold polynomialJohnCatalogueUpperCost
    positivity
  have hcostOne :
      0 < polynomialJohnCatalogueUpperCost delta k + 1 := by
    linarith
  have hcostLt :
      polynomialJohnCatalogueUpperCost delta k <
        Real.exp (Real.log
          (polynomialJohnCatalogueUpperCost delta k + 1)) := by
    rw [Real.exp_log hcostOne]
    linarith
  calc
    (2 * (k : Real)) *
        (((Fintype.card (CatalogueIndex delta hdelta) + 1 : Nat) : Real) *
          Real.exp (Real.exp 1 - 1)) ≤
      polynomialJohnCatalogueUpperCost delta k := hactualUpper
    _ < Real.exp (Real.log
        (polynomialJohnCatalogueUpperCost delta k + 1)) := hcostLt
    _ ≤ Real.exp (polynomialJohnTailParameter delta k) := by
      apply Real.exp_le_exp.mpr
      exact le_max_right _ _

def averageZeroColorCardinalCap
    (iota : Type) [Fintype iota] (k : Nat) : Real :=
  max 1 ((Fintype.card iota : Real) / (k : Real))

theorem averageZeroColorCardinalCap_pos
    (iota : Type) [Fintype iota] (k : Nat) :
    0 < averageZeroColorCardinalCap iota k :=
  lt_of_lt_of_le zero_lt_one (le_max_left _ _)

theorem one_le_averageZeroColorCardinalCap
    (iota : Type) [Fintype iota] (k : Nat) :
    1 ≤ averageZeroColorCardinalCap iota k :=
  le_max_left _ _

theorem average_card_le_averageZeroColorCardinalCap
    (iota : Type) [Fintype iota] (k : Nat) :
    (Fintype.card iota : Real) / (k : Real) ≤
      averageZeroColorCardinalCap iota k :=
  le_max_right _ _

theorem zeroColorSampleRealWeight_shading_eq
    {delta : NNReal} {iota : Type} [Fintype iota] [DecidableEq iota]
    (D : ActualTubeDatum delta iota) (k : Nat) [NeZero k]
    (omega : iota → Fin k) :
    zeroColorSampleRealWeight k (shadingPieceRealWeight D.shading) omega =
      (zeroColorActualDatum D k omega).shading.shadingMass.toReal := by
  symm
  change (restrictActualTubeDatum D
    (zeroColorSample k omega)).shading.shadingMass.toReal = _
  rw [restrictActualTubeDatum_shadingMass, ENNReal.toReal_sum]
  · rfl
  · intro i hi
    exact (shadingPiece_volume_lt_top D.shading i).ne

/-- One colouring simultaneously gives actual shaded-mass retention, an
actual sampled-cardinality bound, and every polynomial John test bound. -/
theorem exists_zeroColorActualDatum_polynomialJohnTests
    {delta : NNReal} {iota : Type} [Fintype iota] [DecidableEq iota]
    (D : ActualTubeDatum delta iota)
    (hdelta : 0 < delta) (hdeltaUpper : delta ≤ (1 / 2 : NNReal))
    (C : ENNReal) (k : Nat) [NeZero k]
    (hsource : IsKatzTao C D.family.bodyFamily)
    (hCfinite : C ≠ ∞)
    (hCscale : C.toReal / (k : Real) ≤ 1) :
    ∃ omega : iota → Fin k,
      D.shading.shadingMass.toReal / (2 * (k : Real)) ≤
          (zeroColorActualDatum D k omega).shading.shadingMass.toReal ∧
        ((zeroColorSample k omega).card : Real) ≤
          polynomialJohnTailParameter delta k *
            averageZeroColorCardinalCap iota k ∧
        ∀ q : CatalogueIndex delta hdelta,
          zeroColorSampleRealWeight k
              (polynomialJohnTestWeight D hdelta q) omega ≤
            polynomialJohnTailParameter delta k *
              polynomialJohnTestCap hdelta q := by
  classical
  let tests : Finset (CatalogueIndex delta hdelta) := Finset.univ
  obtain ⟨omega, hretained, hcard, htests⟩ :=
    exists_zeroColorSample_retention_card_and_all_weightedLoads_le
      tests k (shadingPieceRealWeight D.shading)
      (polynomialJohnTestWeight D hdelta)
      (averageZeroColorCardinalCap iota k)
      (polynomialJohnTestCap hdelta)
      (polynomialJohnTailParameter delta k)
      (fun i => by
        unfold shadingPieceRealWeight shadingWeight
        exact NNReal.zero_le_coe)
      (averageZeroColorCardinalCap_pos iota k)
      (one_le_averageZeroColorCardinalCap iota k)
      (average_card_le_averageZeroColorCardinalCap iota k)
      (fun q _hq => polynomialJohnTestCap_pos hdelta q)
      (fun q _hq i => polynomialJohnTestWeight_nonneg D hdelta q i)
      (fun q _hq i => polynomialJohnTestWeight_le_cap D hdelta q i)
      (fun q _hq =>
        polynomialJohnTest_mean_le_cap D hdelta C k
          hsource hCfinite hCscale q)
      (by simpa [tests] using
        polynomialJohnTailRoom delta hdelta hdeltaUpper k)
  refine ⟨omega, ?_, hcard, ?_⟩
  · simpa [shadingMass_toReal_eq_sum_shadingPieceRealWeight,
      zeroColorSampleRealWeight_shading_eq] using hretained
  · intro q
    exact htests q (Finset.mem_univ q)

#print axioms one_le_polynomialJohnTailParameter
#print axioms polynomialJohnTailRoom
#print axioms zeroColorSampleRealWeight_shading_eq
#print axioms exists_zeroColorActualDatum_polynomialJohnTests


/-- The finite catalogue estimates are upgraded to a genuine all-convex
Katz--Tao bound for the same actual sampled datum. -/
theorem exists_zeroColorActualDatum_polynomialJohn_isKatzTao
    {delta : NNReal} {iota : Type} [Fintype iota] [DecidableEq iota]
    (D : ActualTubeDatum delta iota) (hD : D.IsAdmissible)
    (C : ENNReal) (k : Nat) [NeZero k]
    (hsource : IsKatzTao C D.family.bodyFamily)
    (hCfinite : C ≠ ∞)
    (hCscale : C.toReal / (k : Real) ≤ 1) :
    ∃ omega : iota → Fin k,
      D.shading.shadingMass.toReal / (2 * (k : Real)) ≤
          (zeroColorActualDatum D k omega).shading.shadingMass.toReal ∧
        ((zeroColorSample k omega).card : Real) ≤
          polynomialJohnTailParameter delta k *
            averageZeroColorCardinalCap iota k ∧
        IsKatzTao
          ((ENNReal.ofReal (polynomialJohnTailParameter delta k)) *
            johnCatalogueVolumeConstant)
          (zeroColorActualDatum D k omega).family.bodyFamily := by
  classical
  obtain ⟨omega, hretained, hcard, htests⟩ :=
    exists_zeroColorActualDatum_polynomialJohnTests D
      hD.delta_pos (by simpa [div_eq_mul_inv] using hD.delta_le_half)
      C k hsource hCfinite hCscale
  refine ⟨omega, hretained, hcard, ?_⟩
  have htail0 : 0 ≤ polynomialJohnTailParameter delta k :=
    zero_le_one.trans (one_le_polynomialJohnTailParameter delta k)
  have hcatalogue :
      ∀ q : CatalogueIndex delta hD.delta_pos,
        IsKatzTaoAt
          (ENNReal.ofReal (polynomialJohnTailParameter delta k))
          (tubeBodyFamily
            (zeroColorActualDatum D k omega).family.tubes)
          (representativeTestBody delta hD.delta_pos q) := by
    intro q
    have hreal :
        (containedMass (zeroColorActualDatum D k omega).family.bodyFamily
          (representativeTestBody delta hD.delta_pos q)).toReal ≤
        polynomialJohnTailParameter delta k *
          polynomialJohnTestCap hD.delta_pos q := by
      rw [zeroColorActualDatum_containedMass,
        containedMassOn_toReal_eq_sum_containedBodyRealWeight]
      simpa [zeroColorSampleRealWeight, polynomialJohnTestWeight] using
        htests q
    change containedMass
        (zeroColorActualDatum D k omega).family.bodyFamily
        (representativeTestBody delta hD.delta_pos q) ≤
      ENNReal.ofReal (polynomialJohnTailParameter delta k) *
        volume (representativeTestBody delta hD.delta_pos q : Set Space)
    apply (ENNReal.toReal_le_toReal
      (containedMass_lt_top _ _).ne
      (ENNReal.mul_ne_top (by simp)
        (representativeTestBody delta hD.delta_pos q).isCompact.measure_lt_top.ne)).mp
    simpa [ENNReal.toReal_mul, ENNReal.toReal_ofReal htail0,
      polynomialJohnTestCap] using hreal
  have hall :=
    isKatzTao_of_polynomialJohnCatalogue hD.delta_pos
      (zeroColorActualDatum D k omega).family.tubes
      (fun i => by
        change (D.family.tubes i.1).carrier ⊆ Metric.closedBall 0 1
        exact hD.contained_in_unit_ball i.1)
      (ENNReal.ofReal (polynomialJohnTailParameter delta k))
      hcatalogue
  change IsKatzTao
    (ENNReal.ofReal (polynomialJohnTailParameter delta k) * johnCatalogueVolumeConstant)
    (tubeBodyFamily (zeroColorActualDatum D k omega).family.tubes)
  exact hall

#print axioms exists_zeroColorActualDatum_polynomialJohn_isKatzTao


/-- Convert the real-valued retention supplied by the Chernoff argument into
the division-free ENNReal retention consumed by the density bridge. -/
theorem shadingMass_le_two_mul_k_of_toReal_retention
    {delta : NNReal} {iota : Type} [Fintype iota] [DecidableEq iota]
    (D : ActualTubeDatum delta iota) (k : Nat) [NeZero k]
    (omega : iota → Fin k)
    (hretained :
      D.shading.shadingMass.toReal / (2 * (k : Real)) ≤
        (zeroColorActualDatum D k omega).shading.shadingMass.toReal) :
    D.shading.shadingMass ≤
      (2 * (k : ENNReal)) *
        (zeroColorActualDatum D k omega).shading.shadingMass := by
  have hk : 0 < (k : Real) := by
    exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne k)
  have hcross :
      D.shading.shadingMass.toReal ≤
        (2 * (k : Real)) *
          (zeroColorActualDatum D k omega).shading.shadingMass.toReal :=
    by
      simpa [mul_comm] using
        (div_le_iff₀ (mul_pos zero_lt_two hk)).mp hretained
  have hlossTop : (2 * (k : ENNReal)) ≠ ∞ :=
    ENNReal.mul_ne_top (by norm_num) (by simp)
  apply (ENNReal.toReal_le_toReal D.shading.shadingMass_lt_top.ne
    (ENNReal.mul_ne_top hlossTop
      (zeroColorActualDatum D k omega).shading.shadingMass_lt_top.ne)).mp
  simpa [ENNReal.toReal_mul] using hcross

/-- Apply an actual fixed-parameter Katz--Tao property to the same sampled
datum.  The only residual assumptions are explicit numerical absorption
inequalities: source density pays the factor 2k, and the logarithmic John
coefficient fits below the target concentration power. -/
theorem exists_zeroColorActualDatum_apply_katzTaoAtParameters
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
  have hbound :=
    KatzTaoAtParameters.apply hKT
      (zeroColorActualDatum D k omega)
      (Family8GeneralizedKatzTaoMultiplicityV1.ActualTubeDatum.IsAdmissible.restrictTo
        hD (zeroColorSample k omega))
      hdelta0 hsampleHyp
  refine ⟨omega, hcard, ?_⟩
  simpa using hbound

#print axioms shadingMass_le_two_mul_k_of_toReal_retention
#print axioms exists_zeroColorActualDatum_apply_katzTaoAtParameters


#print axioms polynomialJohnTestCap_pos
#print axioms polynomialJohnTestWeight_le_cap
#print axioms polynomialJohnTest_mean_le_cap

end
end Family8ZeroColorPolynomialJohnKatzTaoV1
