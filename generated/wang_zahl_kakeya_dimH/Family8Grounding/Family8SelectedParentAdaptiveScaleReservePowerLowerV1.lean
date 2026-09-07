import Family8Grounding.Family8CanonicalBufferedGlobalAbsoluteScaleGainV1
import Family8Grounding.Family8SelectedParentPlankCenteredAdaptiveScaleHullFlatnessProducerV1
import FamilyStickyGrounding.FamilyStickyScaleChainSmallDeltaExponentBudgetProducerV1
import Mathlib.Tactic

/-!
# Delta-power lower envelope for the adaptive scale reserve

In the non-hull-thin branch at paper parameter `tau = 1`, the actual bucket
has `a <= 286654464 * rho`.  Together with `a <= b`, the aspect part of the
adaptive inner reserve loses only the displayed finite constant.  The
canonical-buffered absolute bound supplies the remaining
`rho^(-epsilon/2)` delta gain, and a standard finite-constant threshold
absorbs that sole geometric constant.
-/

open Set MeasureTheory
open scoped BigOperators ENNReal NNReal InnerProductSpace

namespace Family8SelectedParentAdaptiveScaleReservePowerLowerV1

open LeanEval.Analysis.WangZahlKakeya
open Submission.Kakeya.ConvexGeometry
open Submission.Kakeya.ConvexFactoring
open Submission.Kakeya.ConvexFactoring.FullConvexMaximalDensity
open Submission.Kakeya.ConvexFactoring.GreedyOccurrenceFactorization
open Submission.Kakeya.Uniformity
open Family8CanonicalBufferedGlobalAbsoluteScaleGainV1
open Family8IdentifiedDividingWitnessCanonicalBufferedCoverV5.Witness
open Family8SelectedParentCertifiedPlankCordobaConnectorV3
open Family8SelectedParentJohnFrameNormalizationV9
open Family8SelectedParentJohnPlankSideWidthBridgeV5
open Family8SelectedParentJohnPlankSideWidthBridgeV7
open Family8SelectedParentPlankCenteredAdaptiveScaleHullFlatnessGeometryV1
open Family8SelectedParentPlankCenteredAdaptiveScaleHullFlatnessProducerV1
open Family8StickySelectedParentGreedyBlockFrostmanV3
open FamilyStickyAtEveryScaleCoreV1
open FamilyStickyDividingScalesFiniteStoppingV1
open FamilyStickyScaleChainCoherentIntervalProducerV1
open FamilyStickyScaleChainIdentifiedFrostmanDividingWitnessV4
open FamilyStickyScaleChainSmallDeltaExponentBudgetProducerV1

noncomputable section

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 5000000

/-- The sole finite geometric constant in the non-hull-thin scale reserve. -/
def adaptiveScaleReserveFlatConstant (beta : Real) : ENNReal :=
  (286654464 : ENNReal) ^ (2 - 3 * beta)

def adaptiveScaleReserveFlatConstantThreshold
    (beta absorbExponent : Real) : NNReal :=
  finiteConstantSmallDeltaThreshold
    (adaptiveScaleReserveFlatConstant beta) absorbExponent

theorem adaptiveScaleReserveFlatConstant_ne_top
    {beta : Real} (hbetaTwoThirds : beta ≤ 2 / 3) :
    adaptiveScaleReserveFlatConstant beta ≠ ∞ := by
  unfold adaptiveScaleReserveFlatConstant
  exact ENNReal.rpow_ne_top_of_nonneg (by linarith) (by norm_num)

theorem adaptiveScaleReserveFlatConstantThreshold_pos
    (beta absorbExponent : Real) :
    0 < adaptiveScaleReserveFlatConstantThreshold beta absorbExponent :=
  finiteConstantSmallDeltaThreshold_pos _ _

/-- Pure scalar core: an upper bound `rho <= delta^alpha` and the actual
flat-branch side bound imply the exact delta-power lower reserve. -/
theorem delta_rpow_absorb_sub_radiusGain_le_scaleReserve
    {delta rho a b : NNReal}
    {alpha innerEpsilon beta absorbExponent : Real}
    (hdelta : 0 < delta) (hrho : 0 < rho)
    (hinnerEpsilon : 0 ≤ innerEpsilon)
    (hbetaTwoThirds : beta ≤ 2 / 3)
    (ha : 0 < a) (hab : a ≤ b)
    (hrhoUpper : rho ≤ delta ^ alpha)
    (haUpper : a ≤ 286654464 * rho)
    (habsorbExponent : 0 < absorbExponent)
    (hsmall : delta ≤
      adaptiveScaleReserveFlatConstantThreshold beta absorbExponent) :
    (delta : ENNReal) ^
        (absorbExponent - alpha * (innerEpsilon / 2)) ≤
      (rho : ENNReal) ^ (-innerEpsilon / 2) *
        ((b : ENNReal) / (a : ENNReal)) *
        (((rho : ENNReal) / (a : ENNReal)) ^ (2 - 3 * beta)) := by
  let d : ENNReal := delta
  let R : ENNReal := rho
  let A : ENNReal := a
  let B : ENNReal := b
  let K : ENNReal := 286654464
  let q : Real := 2 - 3 * beta
  let u : Real := innerEpsilon / 2
  have hq : 0 ≤ q := by dsimp only [q]; linarith
  have hu : 0 ≤ u := by dsimp only [u]; linarith
  have hd0 : d ≠ 0 := ENNReal.coe_ne_zero.mpr hdelta.ne'
  have hdTop : d ≠ ∞ := ENNReal.coe_ne_top
  have hR0 : R ≠ 0 := ENNReal.coe_ne_zero.mpr hrho.ne'
  have hRTop : R ≠ ∞ := ENNReal.coe_ne_top
  have hA0 : A ≠ 0 := ENNReal.coe_ne_zero.mpr ha.ne'
  have hATop : A ≠ ∞ := ENNReal.coe_ne_top
  have hK0 : K ≠ 0 := by norm_num [K]
  have hKTop : K ≠ ∞ := by norm_num [K]
  have hRhoPower : R ^ u ≤ (d ^ alpha) ^ u := by
    apply ENNReal.rpow_le_rpow
    · rw [← ENNReal.coe_rpow_of_ne_zero hdelta.ne' alpha,
        ENNReal.coe_le_coe]
      exact hrhoUpper
    · exact hu
  have hRadiusGain : d ^ (-(alpha * u)) ≤ R ^ (-u) := by
    have hinv := ENNReal.inv_le_inv' hRhoPower
    calc
      d ^ (-(alpha * u)) = (d ^ (alpha * u))⁻¹ := by
        rw [ENNReal.rpow_neg]
      _ = ((d ^ alpha) ^ u)⁻¹ := by rw [ENNReal.rpow_mul]
      _ ≤ (R ^ u)⁻¹ := hinv
      _ = R ^ (-u) := by rw [ENNReal.rpow_neg]
  have haUpperE : A ≤ K * R := by
    dsimp only [A, K, R]
    exact_mod_cast haUpper
  have hratio : K⁻¹ ≤ R / A := by
    apply (ENNReal.le_div_iff_mul_le (Or.inl hA0) (Or.inl hATop)).2
    calc
      K⁻¹ * A ≤ K⁻¹ * (K * R) := mul_le_mul' le_rfl haUpperE
      _ = R := by
        rw [← mul_assoc, ENNReal.inv_mul_cancel hK0 hKTop, one_mul]
  have hratioPower : K ^ (-q) ≤ (R / A) ^ q := by
    have h := ENNReal.rpow_le_rpow hratio hq
    simpa only [ENNReal.inv_rpow, ← ENNReal.rpow_neg] using h
  have hbone : (1 : ENNReal) ≤ B / A := by
    apply (ENNReal.le_div_iff_mul_le (Or.inl hA0) (Or.inl hATop)).2
    simpa only [one_mul, B, A, ENNReal.coe_le_coe] using hab
  have hconstant0 : adaptiveScaleReserveFlatConstant beta ≤
      (delta : ENNReal) ^ (-absorbExponent) :=
    finiteConstant_le_delta_negativePower
      (adaptiveScaleReserveFlatConstant_ne_top hbetaTwoThirds)
      habsorbExponent hdelta hsmall
  have hconstant : K ^ q ≤ d ^ (-absorbExponent) := by
    simpa only [adaptiveScaleReserveFlatConstant, K, q, d] using hconstant0
  have habsorb : d ^ absorbExponent ≤ K ^ (-q) := by
    have hinv := ENNReal.inv_le_inv' hconstant
    simpa only [ENNReal.rpow_neg, inv_inv] using hinv
  calc
    (delta : ENNReal) ^
          (absorbExponent - alpha * (innerEpsilon / 2)) =
        d ^ absorbExponent * d ^ (-(alpha * u)) := by
      change d ^ (absorbExponent - alpha * (innerEpsilon / 2)) = _
      rw [show absorbExponent - alpha * (innerEpsilon / 2) =
        absorbExponent + (-(alpha * u)) by dsimp only [u]; ring]
      rw [ENNReal.rpow_add absorbExponent (-(alpha * u)) hd0 hdTop]
    _ ≤ K ^ (-q) * R ^ (-u) := mul_le_mul' habsorb hRadiusGain
    _ ≤ (R / A) ^ q * R ^ (-u) :=
      mul_le_mul' hratioPower le_rfl
    _ = R ^ (-u) * (R / A) ^ q := by ac_rfl
    _ ≤ R ^ (-u) * (B / A) * (R / A) ^ q := by
      calc
        R ^ (-u) * (R / A) ^ q =
            R ^ (-u) * 1 * (R / A) ^ q := by simp
        _ ≤ R ^ (-u) * (B / A) * (R / A) ^ q :=
          mul_le_mul' (mul_le_mul' le_rfl hbone) le_rfl
    _ = (rho : ENNReal) ^ (-innerEpsilon / 2) *
        ((b : ENNReal) / (a : ENNReal)) *
        (((rho : ENNReal) / (a : ENNReal)) ^ (2 - 3 * beta)) := by
      simp only [R, A, B, q, u]
      rw [show -(innerEpsilon / 2) = -innerEpsilon / 2 by ring]

variable {delta : NNReal} {index : Type}
  [Fintype index] [DecidableEq index]
  {fine : UniformTubeFamily delta index}
  {Cmulti : CoherentStickyMultiscaleCover fine}
  {depth N : Nat} {stoppingEpsilon : Real} {eta : Nat → Real}
  {scaleSequence : FiniteScaleSequence delta depth}

/-- Actual canonical-buffered specialization.  The only branch input is the
literal failure of the paper hull-thin alternative at `tau = 1`; the side
bound and radius power are constructed from the existing geometry. -/
theorem selectedParent_canonicalBuffered_nonHullThin_scaleReservePowerLower
    (D : IdentifiedFrostmanDividingWitness
      fine Cmulti N stoppingEpsilon eta scaleSequence)
    (hfineContained : ∀ i, (fine.tubes i).carrier ⊆
      Metric.closedBall (0 : Space) 1)
    (hdelta : 0 < delta) (hstoppingEpsilon : 0 ≤ stoppingEpsilon)
    (hstoppingEpsilonHalf : stoppingEpsilon ≤ 1 / 2)
    (G : StickyScaleCover fine (canonicalBufferedRadius D))
    (P : GreedyDensityPartition G.activeCoarseFamily
      (hullCandidates (Finset.univ : Finset (ActiveParentIndex G)))
      (hullContainer G.activeCoarseFamily) Finset.univ)
    (k : Fin (blocks G.activeCoarseFamily P).length)
    (r : NNReal) (hr : 0 < r) (label : Fin 3 → Int)
    (W : {p // p ∈ selectedParentPlankBucketIndices
      (contractedJohnAffineEquiv
        (selectedParentGreedyBlockJohnFrame G
          (canonicalBufferedRadius_pos D hdelta hstoppingEpsilon) P k) r hr)
      G (blockAt G.activeCoarseFamily P k).fiber
        (canonicalBufferedRadius_pos D hdelta hstoppingEpsilon) label})
    (hnotHullThin : ¬ hullShortestSide
      (selectedParentGreedyBlockJohnFrame G
        (canonicalBufferedRadius_pos D hdelta hstoppingEpsilon) P k) ≤ 1)
    (innerEpsilon beta absorbExponent : Real)
    (hinnerEpsilon : 0 ≤ innerEpsilon)
    (hbetaTwoThirds : beta ≤ 2 / 3)
    (habsorbExponent : 0 < absorbExponent)
    (hsmall : delta ≤
      adaptiveScaleReserveFlatConstantThreshold beta absorbExponent) :
    (delta : ENNReal) ^
        (absorbExponent -
          (stoppingEpsilon * (1 - stoppingEpsilon)) *
            (innerEpsilon / 2)) ≤
      (canonicalBufferedRadius D : ENNReal) ^ (-innerEpsilon / 2) *
        ((bucketShortB label : ENNReal) /
          (bucketShortA label : ENNReal)) *
        (((canonicalBufferedRadius D : ENNReal) /
          (bucketShortA label : ENNReal)) ^ (2 - 3 * beta)) := by
  let hrho : 0 < canonicalBufferedRadius D :=
    canonicalBufferedRadius_pos D hdelta hstoppingEpsilon
  have hrhoOne : canonicalBufferedRadius D ≤ 1 :=
    canonicalBufferedRadius_le_one D hdelta hstoppingEpsilon
      hstoppingEpsilonHalf
  have hflatBranch := selectedParent_paperHullThin_or_bucketFlat
    hfineContained G hrho hrhoOne P k r hr label W 1
  have hflat : bucketShortA label ≤
      286654464 * canonicalBufferedRadius D := by
    rcases hflatBranch with hthin | hflat
    · exfalso
      apply hnotHullThin
      simpa only [sub_self, NNReal.rpow_zero] using hthin
    · simpa only [NNReal.rpow_one] using hflat
  apply delta_rpow_absorb_sub_radiusGain_le_scaleReserve
    hdelta hrho hinnerEpsilon hbetaTwoThirds (bucketShortA_pos label)
      (bucketShortA_le_bucketShortB label)
  · exact canonicalBufferedRadius_le_delta_rpow_mul_one_sub
      D hdelta hstoppingEpsilon hstoppingEpsilonHalf
  · exact hflat
  · exact habsorbExponent
  · exact hsmall

#print axioms adaptiveScaleReserveFlatConstant_ne_top
#print axioms delta_rpow_absorb_sub_radiusGain_le_scaleReserve
#print axioms
  selectedParent_canonicalBuffered_nonHullThin_scaleReservePowerLower

end
end Family8SelectedParentAdaptiveScaleReservePowerLowerV1
