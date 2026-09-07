import Family8Grounding.Family8FiniteRigidMotionOrthogonalTranslationScaleOnlyConflictMeanV1
import Family8Grounding.Family8FiniteRigidMotionNormalizedBodyLoadCapScaleOnlyV1
import FamilyStickyGrounding.FamilyStickyRandomTwoFamilyChernoffV1
import Mathlib.Tactic

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 6000000
set_option linter.unusedSectionVars false
set_option linter.unnecessarySimpa false

open Set MeasureTheory
open scoped ENNReal NNReal BigOperators InnerProductSpace

namespace Family8FiniteRigidMotionOrthogonalTranslationScaleOnlyJointSelectorV1

open LeanEval.Analysis.WangZahlKakeya
open Submission.Kakeya.ConvexGeometry
open Family8KatzTaoFrostmanPropertiesV1
open Family8FiniteRandomRigidMotionB2NormalizationCoreV1
open Family8FiniteRigidMotionOrthogonalHundredCatalogueV2
open Family8FiniteRigidMotionOrthogonalPatternCatalogueV3
open Family8FiniteRigidMotionOrthogonalTranslationScaleOnlyProductLawV1
open Family8FiniteRigidMotionOrthogonalTranslationScaleOnlyConflictMeanV1
open Family8FiniteRigidMotionOrthogonalScaleOnlyCatalogueScaleV1
open Family8FiniteRigidMotionNormalizedBodyLoadCapScaleOnlyV1
open FamilyStickyRandomFiniteChernoffV3

noncomputable section

/-!
# A scale-only joint fixed-John/conflict selector

Both event families below live on the literal same automatic-scale
orthogonal--translation outcome type.  The analytic inputs are the two
division-free product means and the normalized Katz--Tao half-square cap;
no admissibility, `B2`, endpoint, or Family 7 conclusion is used.
-/

/-- The single automatic-scale outcome type shared by both event families. -/
abbrev ScaleOnlyJointChoice
    {delta : NNReal} {iota : Type}
    [Fintype iota] [DecidableEq iota]
    (D : ActualTubeDatum delta iota) (hdelta : 0 < delta) :=
  ScaleOnlyFixedJohnOrthogonalTranslationChoice D hdelta
    (scaleOnlyOrthogonalCatalogueScale D hdelta)

/-- The exact tube-volume floor used by every normalized pointwise load. -/
def scaleOnlyJointHalfSq (delta : NNReal) : ENNReal :=
  ((delta / 8 : NNReal) : ENNReal) ^ 2 / 2

/-- The fixed normalized translation-ball volume. -/
def scaleOnlyJointMotionBallVolume : ENNReal :=
  volume (Metric.closedBall (0 : Space) (((1 / 8 : NNReal) : Real)))

/-- The body-independent coefficient in the fixed-John product mean. -/
def scaleOnlyJointJohnMeanCoefficient
    (iota : Type) [Fintype iota] : ENNReal :=
  729 * (Fintype.card iota : ENNReal)

/-- The body-independent coefficient in the elongated conflict product mean. -/
def scaleOnlyJointConflictMeanCoefficient
    (delta : NNReal) (iota : Type) [Fintype iota] : ENNReal :=
  (11 * (enlargedHundredDirectionCap (delta / 8) : ENNReal) ^ 2) *
    729 * (Fintype.card iota : ENNReal)

def scaleOnlyJointJohnLoad
    {delta : NNReal} {iota : Type}
    [Fintype iota] [DecidableEq iota]
    (D : ActualTubeDatum delta iota) (hdelta : 0 < delta)
    (K : ScaleOnlyFixedJohnTest delta hdelta)
    (g : ScaleOnlyJointChoice D hdelta) : Real :=
  (normalizedRigidBodyLoadNat
    (scaleOnlyFixedJohnSampledOrthogonalTranslationMotion D hdelta
      (scaleOnlyOrthogonalCatalogueScale D hdelta)) D
    (scaleOnlyFixedJohnCatalogueBody hdelta) K g : Real)

def scaleOnlyJointConflictLoad
    {delta : NNReal} {iota : Type}
    [Fintype iota] [DecidableEq iota]
    (D : ActualTubeDatum delta iota) (hdelta : 0 < delta)
    (K : ScaleOnlyFixedJohnElongatedTest D hdelta
      (scaleOnlyOrthogonalCatalogueScale D hdelta))
    (g : ScaleOnlyJointChoice D hdelta) : Real :=
  (normalizedRigidBodyLoadNat
    (scaleOnlyFixedJohnSampledOrthogonalTranslationMotion D hdelta
      (scaleOnlyOrthogonalCatalogueScale D hdelta)) D
    (scaleOnlyFixedJohnOrthogonalTranslationElongatedBody D hdelta
      (scaleOnlyOrthogonalCatalogueScale D hdelta)) K g : Real)

/-- Generic normalized Katz--Tao cap for one fixed-John catalogue body. -/
def scaleOnlyJointJohnCap
    {delta : NNReal} {iota : Type}
    [Fintype iota] [DecidableEq iota]
    (C : ENNReal) (D : ActualTubeDatum delta iota) (hdelta : 0 < delta)
    (K : ScaleOnlyFixedJohnTest delta hdelta) : Real :=
  (C * volume (scaleOnlyFixedJohnCatalogueBody hdelta K : Set Space) /
    scaleOnlyJointHalfSq delta).toReal

/-- Generic normalized Katz--Tao cap for one elongated candidate body. -/
def scaleOnlyJointConflictCap
    {delta : NNReal} {iota : Type}
    [Fintype iota] [DecidableEq iota]
    (C : ENNReal) (D : ActualTubeDatum delta iota) (hdelta : 0 < delta)
    (K : ScaleOnlyFixedJohnElongatedTest D hdelta
      (scaleOnlyOrthogonalCatalogueScale D hdelta)) : Real :=
  (C * volume
      (scaleOnlyFixedJohnOrthogonalTranslationElongatedBody D hdelta
        (scaleOnlyOrthogonalCatalogueScale D hdelta) K : Set Space) /
    scaleOnlyJointHalfSq delta).toReal

/-- Real wrapper around the division-free fixed-John product mean. -/
def scaleOnlyJointJohnMean
    {delta : NNReal} {iota : Type}
    [Fintype iota] [DecidableEq iota]
    (D : ActualTubeDatum delta iota) (hdelta : 0 < delta)
    (K : ScaleOnlyFixedJohnTest delta hdelta) : Real :=
  (scaleOnlyJointJohnMeanCoefficient iota *
      volume (scaleOnlyFixedJohnCatalogueBody hdelta K : Set Space) /
    scaleOnlyJointMotionBallVolume).toReal

/-- Real wrapper around the division-free elongated product mean. -/
def scaleOnlyJointConflictMean
    {delta : NNReal} {iota : Type}
    [Fintype iota] [DecidableEq iota]
    (D : ActualTubeDatum delta iota) (hdelta : 0 < delta)
    (K : ScaleOnlyFixedJohnElongatedTest D hdelta
      (scaleOnlyOrthogonalCatalogueScale D hdelta)) : Real :=
  (scaleOnlyJointConflictMeanCoefficient delta iota *
      volume
        (scaleOnlyFixedJohnOrthogonalTranslationElongatedBody D hdelta
          (scaleOnlyOrthogonalCatalogueScale D hdelta) K : Set Space) /
    scaleOnlyJointMotionBallVolume).toReal

private theorem scaleOnlyJointHalfSq_ne_zero
    {delta : NNReal} (hdelta : 0 < delta) :
    scaleOnlyJointHalfSq delta ≠ 0 := by
  unfold scaleOnlyJointHalfSq
  positivity

private theorem scaleOnlyJointHalfSq_ne_top (delta : NNReal) :
    scaleOnlyJointHalfSq delta ≠ ∞ := by
  unfold scaleOnlyJointHalfSq
  simp

private theorem scaleOnlyJointMotionBallVolume_ne_zero :
    scaleOnlyJointMotionBallVolume ≠ 0 := by
  unfold scaleOnlyJointMotionBallVolume
  exact ne_of_gt
    (Metric.measure_closedBall_pos volume (0 : Space) (by norm_num))

private theorem scaleOnlyJointMotionBallVolume_ne_top :
    scaleOnlyJointMotionBallVolume ≠ ∞ := by
  unfold scaleOnlyJointMotionBallVolume
  exact Metric.isCompact_closedBall.measure_lt_top.ne

private theorem natCast_le_div_toReal
    (m : Nat) {lower total : ENNReal}
    (hlower0 : lower ≠ 0) (hlowerTop : lower ≠ ∞)
    (htotalTop : total ≠ ∞)
    (hcross : (m : ENNReal) * lower ≤ total) :
    (m : Real) ≤ (total / lower).toReal := by
  have hreal := ENNReal.toReal_mono htotalTop hcross
  have hlowerReal : 0 < lower.toReal :=
    ENNReal.toReal_pos hlower0 hlowerTop
  rw [ENNReal.toReal_div]
  apply (le_div_iff₀ hlowerReal).2
  simpa only [ENNReal.toReal_mul, ENNReal.toReal_natCast] using hreal

private theorem sum_natCast_le_card_mul_div_toReal
    {choice : Type} [Fintype choice]
    (load : choice → Nat) {ball rhs : ENNReal}
    (hball0 : ball ≠ 0) (hballTop : ball ≠ ∞)
    (hrhsTop : rhs ≠ ∞)
    (hcross :
      (∑ g : choice, (load g : ENNReal)) * ball ≤
        (Fintype.card choice : ENNReal) * rhs) :
    (∑ g : choice, (load g : Real)) ≤
      (Fintype.card choice : Real) * (rhs / ball).toReal := by
  have hrightTop :
      (Fintype.card choice : ENNReal) * rhs ≠ ∞ :=
    ENNReal.mul_ne_top (by simp) hrhsTop
  have hreal := ENNReal.toReal_mono hrightTop hcross
  have hballReal : 0 < ball.toReal :=
    ENNReal.toReal_pos hball0 hballTop
  have hsum :
      (∑ g : choice, (load g : ENNReal)).toReal =
        ∑ g : choice, (load g : Real) := by
    rw [ENNReal.toReal_sum]
    simp only [ENNReal.toReal_natCast]
  calc
    (∑ g : choice, (load g : Real)) =
        (∑ g : choice, (load g : ENNReal)).toReal := hsum.symm
    _ ≤ ((Fintype.card choice : Real) * rhs.toReal) / ball.toReal := by
      apply (le_div_iff₀ hballReal).2
      simpa only [ENNReal.toReal_mul, ENNReal.toReal_natCast] using hreal
    _ = (Fintype.card choice : Real) * (rhs / ball).toReal := by
      rw [ENNReal.toReal_div]
      ring

private theorem natCast_mul_bodyMean_le_bodyCap
    (repetitions : Nat) {coefficient bodyVolume ball lower C : ENNReal}
    (hball0 : ball ≠ 0) (hballTop : ball ≠ ∞)
    (hlower0 : lower ≠ 0) (hlowerTop : lower ≠ ∞)
    (hCTop : C ≠ ∞)
    (hscale :
      (repetitions : ENNReal) * coefficient * lower ≤ C * ball) :
    (repetitions : Real) *
        (coefficient * bodyVolume / ball).toReal ≤
      (C * bodyVolume / lower).toReal := by
  have hscaleReal := ENNReal.toReal_mono
    (ENNReal.mul_ne_top hCTop hballTop) hscale
  have hballReal : 0 < ball.toReal :=
    ENNReal.toReal_pos hball0 hballTop
  have hlowerReal : 0 < lower.toReal :=
    ENNReal.toReal_pos hlower0 hlowerTop
  have hfactor : 0 ≤
      bodyVolume.toReal / (ball.toReal * lower.toReal) := by positivity
  have hscaleReal' :
      (repetitions : Real) * coefficient.toReal * lower.toReal ≤
        C.toReal * ball.toReal := by
    simpa only [ENNReal.toReal_mul, ENNReal.toReal_natCast] using hscaleReal
  rw [ENNReal.toReal_div, ENNReal.toReal_div]
  simp only [ENNReal.toReal_mul]
  calc
    (repetitions : Real) *
          (coefficient.toReal * bodyVolume.toReal / ball.toReal) =
        ((repetitions : Real) * coefficient.toReal * lower.toReal) *
          (bodyVolume.toReal / (ball.toReal * lower.toReal)) := by
            field_simp [ne_of_gt hballReal, ne_of_gt hlowerReal]
            ring
    _ ≤ (C.toReal * ball.toReal) *
          (bodyVolume.toReal / (ball.toReal * lower.toReal)) :=
      mul_le_mul_of_nonneg_right hscaleReal' hfactor
    _ = C.toReal * bodyVolume.toReal / lower.toReal := by
      field_simp [ne_of_gt hballReal, ne_of_gt hlowerReal]
      ring

private theorem scaleOnlyJointChoice_nonempty
    {delta : NNReal} {iota : Type}
    [Fintype iota] [DecidableEq iota]
    (D : ActualTubeDatum delta iota) (hdelta : 0 < delta) :
    Nonempty (ScaleOnlyJointChoice D hdelta) := by
  let n := scaleOnlyOrthogonalCatalogueScale D hdelta
  have hn : 0 < n := scaleOnlyOrthogonalCatalogueScale_pos D hdelta
  have hnReal : 0 < (n : Real) := by exact_mod_cast hn
  have hsampleReal :
      0 < (Fintype.card (ScaleOnlyFixedJohnOrthogonalSample D hdelta n) : Real) :=
    hnReal.trans_le
      (scale_le_card_orthogonalPatternSample
        (sourceTubeDirection (normalizedSourceTube D))
        (hundredNetDirection (delta / 8)
          (scaleOnlyNormalizedRadiusPos hdelta))
        (enlargedHundredDirectionCap (delta / 8)) n)
  have hsample :
      0 < Fintype.card (ScaleOnlyFixedJohnOrthogonalSample D hdelta n) := by
    exact_mod_cast hsampleReal
  letI : Nonempty (ScaleOnlyFixedJohnOrthogonalSample D hdelta n) :=
    Fintype.card_pos_iff.mp hsample
  exact inferInstance

private theorem scaleOnlyJoint_load_le_cap
    {delta : NNReal} {iota test : Type}
    [Fintype iota] [DecidableEq iota]
    (C : ENNReal) (hCTop : C ≠ ∞)
    (D : ActualTubeDatum delta iota) (hdelta : 0 < delta)
    (hdeltaHalf : delta ≤ (2 : NNReal)⁻¹)
    (hKT : IsKatzTao C (eighthNormalizedDatum D).family.bodyFamily)
    (testBody : test → ConvexBody Space) (K : test)
    (g : ScaleOnlyJointChoice D hdelta) :
    (normalizedRigidBodyLoadNat
      (scaleOnlyFixedJohnSampledOrthogonalTranslationMotion D hdelta
        (scaleOnlyOrthogonalCatalogueScale D hdelta)) D testBody K g : Real) ≤
      (C * volume (testBody K : Set Space) /
        scaleOnlyJointHalfSq delta).toReal := by
  have hcross := normalizedOrthogonalTranslationBodyLoadNat_mul_halfSq_le
    (fun u : ScaleOnlyJointChoice D hdelta ↦
      sampledHundredOrthogonal (normalizedSourceTube D)
        (scaleOnlyNormalizedRadiusPos hdelta) u.2)
    (fun u : ScaleOnlyJointChoice D hdelta ↦
      scaleOnlyFixedJohnPackingGridVector hdelta u.1)
    D hdeltaHalf hKT testBody K g
  apply natCast_le_div_toReal
    (normalizedRigidBodyLoadNat
      (scaleOnlyFixedJohnSampledOrthogonalTranslationMotion D hdelta
        (scaleOnlyOrthogonalCatalogueScale D hdelta)) D testBody K g)
    (scaleOnlyJointHalfSq_ne_zero hdelta)
    (scaleOnlyJointHalfSq_ne_top delta)
    (ENNReal.mul_ne_top hCTop (testBody K).isCompact.measure_lt_top.ne)
  simpa only [scaleOnlyJointHalfSq,
    scaleOnlyFixedJohnSampledOrthogonalTranslationMotion] using hcross

/-- Internal two-family selector.  The elongated catalogue is quantified
only here; the public conflict endpoint below projects it to actual anchors. -/
theorem exists_scaleOnlyJointChoice_two_bodyLoad_bounds
    {delta : NNReal} {iota : Type}
    [Fintype iota] [DecidableEq iota]
    (D : ActualTubeDatum delta iota) (hdelta : 0 < delta)
    (hdeltaHalf : delta ≤ (2 : NNReal)⁻¹)
    {C : ENNReal} (hCTop : C ≠ ∞)
    (hKT : IsKatzTao C (eighthNormalizedDatum D).family.bodyFamily)
    (repetitions : Nat) (AJohn AConflict : Real)
    (hscaleJ :
      (repetitions : ENNReal) * scaleOnlyJointJohnMeanCoefficient iota *
          scaleOnlyJointHalfSq delta ≤
        C * scaleOnlyJointMotionBallVolume)
    (hscaleE :
      (repetitions : ENNReal) *
          scaleOnlyJointConflictMeanCoefficient delta iota *
          scaleOnlyJointHalfSq delta ≤
        C * scaleOnlyJointMotionBallVolume)
    (htailRoom :
      (Fintype.card (ScaleOnlyFixedJohnTest delta hdelta) : Real) *
            Real.exp (Real.exp 1 - 1) * Real.exp AConflict +
          (Fintype.card
            (ScaleOnlyFixedJohnElongatedTest D hdelta
              (scaleOnlyOrthogonalCatalogueScale D hdelta)) : Real) *
            Real.exp (Real.exp 1 - 1) * Real.exp AJohn <
        Real.exp AJohn * Real.exp AConflict) :
    exists omega : Fin repetitions → ScaleOnlyJointChoice D hdelta,
      (forall K : ScaleOnlyFixedJohnTest delta hdelta,
        (∑ j, scaleOnlyJointJohnLoad D hdelta K (omega j)) ≤
          AJohn * scaleOnlyJointJohnCap C D hdelta K) /\
      (forall K : ScaleOnlyFixedJohnElongatedTest D hdelta
          (scaleOnlyOrthogonalCatalogueScale D hdelta),
        (∑ j, scaleOnlyJointConflictLoad D hdelta K (omega j)) ≤
          AConflict * scaleOnlyJointConflictCap C D hdelta K) := by
  classical
  letI : Nonempty (ScaleOnlyJointChoice D hdelta) :=
    scaleOnlyJointChoice_nonempty D hdelta
  let johnTests : Finset (ScaleOnlyFixedJohnTest delta hdelta) := Finset.univ
  let conflictTests : Finset
      (ScaleOnlyFixedJohnElongatedTest D hdelta
        (scaleOnlyOrthogonalCatalogueScale D hdelta)) := Finset.univ
  have hjohnSum (K : ScaleOnlyFixedJohnTest delta hdelta) :
      (∑ g : ScaleOnlyJointChoice D hdelta,
        scaleOnlyJointJohnLoad D hdelta K g) ≤
        (Fintype.card (ScaleOnlyJointChoice D hdelta) : Real) *
          scaleOnlyJointJohnMean D hdelta K := by
    apply sum_natCast_le_card_mul_div_toReal
      (fun g : ScaleOnlyJointChoice D hdelta ↦
        normalizedRigidBodyLoadNat
          (scaleOnlyFixedJohnSampledOrthogonalTranslationMotion D hdelta
            (scaleOnlyOrthogonalCatalogueScale D hdelta)) D
          (scaleOnlyFixedJohnCatalogueBody hdelta) K g)
      scaleOnlyJointMotionBallVolume_ne_zero
      scaleOnlyJointMotionBallVolume_ne_top
      (ENNReal.mul_ne_top (by simp)
        (scaleOnlyFixedJohnCatalogueBody hdelta K).isCompact.measure_lt_top.ne)
    have h :=
      sum_scaleOnlyFixedJohnOrthogonalTranslationBodyLoadNat_mul_motionBallVolume_le
        D hdelta (scaleOnlyOrthogonalCatalogueScale D hdelta) K
    simpa only [scaleOnlyJointMotionBallVolume,
      scaleOnlyJointJohnMeanCoefficient, scaleOnlyJointJohnLoad,
      scaleOnlyJointJohnMean, ScaleOnlyJointChoice, mul_assoc] using h
  have hconflictSum
      (K : ScaleOnlyFixedJohnElongatedTest D hdelta
        (scaleOnlyOrthogonalCatalogueScale D hdelta)) :
      (∑ g : ScaleOnlyJointChoice D hdelta,
        scaleOnlyJointConflictLoad D hdelta K g) ≤
        (Fintype.card (ScaleOnlyJointChoice D hdelta) : Real) *
          scaleOnlyJointConflictMean D hdelta K := by
    apply sum_natCast_le_card_mul_div_toReal
      (fun g : ScaleOnlyJointChoice D hdelta ↦
        normalizedRigidBodyLoadNat
          (scaleOnlyFixedJohnSampledOrthogonalTranslationMotion D hdelta
            (scaleOnlyOrthogonalCatalogueScale D hdelta)) D
          (scaleOnlyFixedJohnOrthogonalTranslationElongatedBody D hdelta
            (scaleOnlyOrthogonalCatalogueScale D hdelta)) K g)
      scaleOnlyJointMotionBallVolume_ne_zero
      scaleOnlyJointMotionBallVolume_ne_top
      (ENNReal.mul_ne_top (by simp)
        (scaleOnlyFixedJohnOrthogonalTranslationElongatedBody D hdelta
          (scaleOnlyOrthogonalCatalogueScale D hdelta) K).isCompact.measure_lt_top.ne)
    have h :=
      sum_scaleOnlyNormalizedOrthogonalTranslationElongatedBodyLoad_mul_motionBallVolume_le
        D hdelta (by simpa using hdeltaHalf)
        (scaleOnlyOrthogonalCatalogueScale D hdelta) K
        (scaleOnlyOrthogonalCatalogueScale_rounding D hdelta)
    simpa only [scaleOnlyJointMotionBallVolume,
      scaleOnlyJointConflictMeanCoefficient, scaleOnlyJointConflictLoad,
      scaleOnlyJointConflictMean, ScaleOnlyJointChoice, mul_assoc] using h
  obtain ⟨omega, homegaJ, homegaE⟩ :=
    FamilyStickyRandomTwoFamilyChernoffV1.exists_product_choice_two_load_bounds
      johnTests conflictTests repetitions
      (scaleOnlyJointJohnLoad D hdelta)
      (scaleOnlyJointJohnCap C D hdelta)
      (scaleOnlyJointJohnMean D hdelta)
      (scaleOnlyJointConflictLoad D hdelta)
      (scaleOnlyJointConflictCap C D hdelta)
      (scaleOnlyJointConflictMean D hdelta)
      AJohn AConflict
      (fun _K _hK ↦ ENNReal.toReal_nonneg)
      (fun _K _hK ↦ ENNReal.toReal_nonneg)
      (fun _K _hK _g ↦ Nat.cast_nonneg _)
      (fun K _hK g ↦ by
        exact scaleOnlyJoint_load_le_cap C hCTop D hdelta hdeltaHalf hKT
          (scaleOnlyFixedJohnCatalogueBody hdelta) K g)
      (fun K _hK ↦ hjohnSum K)
      (fun K _hK ↦ by
        exact natCast_mul_bodyMean_le_bodyCap repetitions
          scaleOnlyJointMotionBallVolume_ne_zero
          scaleOnlyJointMotionBallVolume_ne_top
          (scaleOnlyJointHalfSq_ne_zero hdelta)
          (scaleOnlyJointHalfSq_ne_top delta) hCTop hscaleJ)
      (fun _K _hK ↦ ENNReal.toReal_nonneg)
      (fun _K _hK ↦ ENNReal.toReal_nonneg)
      (fun _K _hK _g ↦ Nat.cast_nonneg _)
      (fun K _hK g ↦ by
        exact scaleOnlyJoint_load_le_cap C hCTop D hdelta hdeltaHalf hKT
          (scaleOnlyFixedJohnOrthogonalTranslationElongatedBody D hdelta
            (scaleOnlyOrthogonalCatalogueScale D hdelta)) K g)
      (fun K _hK ↦ hconflictSum K)
      (fun K _hK ↦ by
        exact natCast_mul_bodyMean_le_bodyCap repetitions
          scaleOnlyJointMotionBallVolume_ne_zero
          scaleOnlyJointMotionBallVolume_ne_top
          (scaleOnlyJointHalfSq_ne_zero hdelta)
          (scaleOnlyJointHalfSq_ne_top delta) hCTop hscaleE)
      (by simpa only [johnTests, conflictTests, Finset.card_univ] using htailRoom)
  refine ⟨omega, ?_, ?_⟩
  · intro K
    simpa only [johnTests, Finset.mem_univ,
      FamilyStickyRandomFiniteChernoffV3.productLoad] using
        homegaJ K (Finset.mem_univ K)
  · intro K
    simpa only [conflictTests, Finset.mem_univ,
      FamilyStickyRandomFiniteChernoffV3.productLoad] using
        homegaE K (Finset.mem_univ K)

#print axioms exists_scaleOnlyJointChoice_two_bodyLoad_bounds

end
end Family8FiniteRigidMotionOrthogonalTranslationScaleOnlyJointSelectorV1
