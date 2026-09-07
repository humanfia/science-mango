import Family8Grounding.Family8SelectedParentAdaptiveScaleReservePowerLowerV1
import Mathlib.Tactic

/-!
# Arbitrary-paper-parameter delta envelope for the adaptive scale reserve

This is the thin successor of the `tau = 1` specialization.  On the
non-hull-thin branch, the actual side bound is
`a <= 286654464 * rho^tau`.  Consequently the complete radius exponent in
the scale reserve is

`-innerEpsilon / 2 + (1 - tau) * (2 - 3 * beta)`.

Keeping `tau` free is essential: it records the genuine paper flatness gain
instead of replacing it by a conclusion-valued hypothesis.
-/

open Set MeasureTheory
open scoped BigOperators ENNReal NNReal InnerProductSpace

namespace Family8SelectedParentAdaptiveScaleReservePowerLowerV2

open LeanEval.Analysis.WangZahlKakeya
open Submission.Kakeya.ConvexGeometry
open Submission.Kakeya.ConvexFactoring
open Submission.Kakeya.ConvexFactoring.FullConvexMaximalDensity
open Submission.Kakeya.ConvexFactoring.GreedyOccurrenceFactorization
open Submission.Kakeya.Uniformity
open Family8CanonicalBufferedGlobalAbsoluteScaleGainV1
open Family8IdentifiedDividingWitnessCanonicalBufferedCoverV5.Witness
open Family8SelectedParentAdaptiveScaleReservePowerLowerV1
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

/-- Pure scalar core with the full paper flatness exponent retained. -/
theorem delta_rpow_absorb_add_flatRadiusExponent_le_scaleReserve
    {delta rho a b : NNReal}
    {alpha tau innerEpsilon beta absorbExponent : Real}
    (hdelta : 0 < delta) (hrho : 0 < rho)
    (hbetaTwoThirds : beta ≤ 2 / 3)
    (ha : 0 < a) (hab : a ≤ b)
    (hrhoUpper : rho ≤ delta ^ alpha)
    (haUpper : a ≤ 286654464 * rho ^ tau)
    (hflatRadiusExponent :
      -innerEpsilon / 2 + (1 - tau) * (2 - 3 * beta) ≤ 0)
    (habsorbExponent : 0 < absorbExponent)
    (hsmall : delta ≤
      adaptiveScaleReserveFlatConstantThreshold beta absorbExponent) :
    (delta : ENNReal) ^
        (absorbExponent + alpha *
          (-innerEpsilon / 2 + (1 - tau) * (2 - 3 * beta))) ≤
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
  let e : Real := -u + (1 - tau) * q
  have hq : 0 ≤ q := by dsimp only [q]; linarith
  have he : e ≤ 0 := by
    dsimp only [e, u, q]
    convert hflatRadiusExponent using 1; ring
  have hd0 : d ≠ 0 := ENNReal.coe_ne_zero.mpr hdelta.ne'
  have hdTop : d ≠ ∞ := ENNReal.coe_ne_top
  have hR0 : R ≠ 0 := ENNReal.coe_ne_zero.mpr hrho.ne'
  have hRTop : R ≠ ∞ := ENNReal.coe_ne_top
  have hA0 : A ≠ 0 := ENNReal.coe_ne_zero.mpr ha.ne'
  have hATop : A ≠ ∞ := ENNReal.coe_ne_top
  have hK0 : K ≠ 0 := by norm_num [K]
  have hKTop : K ≠ ∞ := by norm_num [K]
  have hRadiusGainNN : delta ^ (alpha * e) ≤ rho ^ e := by
    calc
      delta ^ (alpha * e) = (delta ^ alpha) ^ e :=
        NNReal.rpow_mul delta alpha e
      _ ≤ rho ^ e :=
        NNReal.rpow_le_rpow_of_nonpos hrho hrhoUpper he
  have hRadiusGain : d ^ (alpha * e) ≤ R ^ e := by
    rw [← ENNReal.coe_rpow_of_ne_zero hdelta.ne' (alpha * e),
      ← ENNReal.coe_rpow_of_ne_zero hrho.ne' e,
      ENNReal.coe_le_coe]
    exact hRadiusGainNN
  have haUpperE : A ≤ K * R ^ tau := by
    dsimp only [A, K, R]
    rw [← ENNReal.coe_rpow_of_ne_zero hrho.ne' tau]
    exact_mod_cast haUpper
  have hratio : K⁻¹ * R ^ (1 - tau) ≤ R / A := by
    apply (ENNReal.le_div_iff_mul_le (Or.inl hA0) (Or.inl hATop)).2
    calc
      (K⁻¹ * R ^ (1 - tau)) * A ≤
          (K⁻¹ * R ^ (1 - tau)) * (K * R ^ tau) :=
        mul_le_mul' le_rfl haUpperE
      _ = (K⁻¹ * K) * (R ^ (1 - tau) * R ^ tau) := by ac_rfl
      _ = R := by
        rw [ENNReal.inv_mul_cancel hK0 hKTop, one_mul,
          ← ENNReal.rpow_add (1 - tau) tau hR0 hRTop]
        convert ENNReal.rpow_one R using 1; ring
  have hratioPower : K ^ (-q) * R ^ ((1 - tau) * q) ≤
      (R / A) ^ q := by
    calc
      K ^ (-q) * R ^ ((1 - tau) * q) =
          (K⁻¹ * R ^ (1 - tau)) ^ q := by
        rw [ENNReal.mul_rpow_of_nonneg _ _ hq, ENNReal.inv_rpow,
          ← ENNReal.rpow_neg, ENNReal.rpow_mul]
      _ ≤ (R / A) ^ q := ENNReal.rpow_le_rpow hratio hq
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
          (absorbExponent + alpha *
            (-innerEpsilon / 2 + (1 - tau) * (2 - 3 * beta))) =
        d ^ absorbExponent * d ^ (alpha * e) := by
      change d ^
        (absorbExponent + alpha *
          (-innerEpsilon / 2 + (1 - tau) * (2 - 3 * beta))) = _
      rw [show absorbExponent + alpha *
          (-innerEpsilon / 2 + (1 - tau) * (2 - 3 * beta)) =
          absorbExponent + alpha * e by dsimp only [e, u, q]; ring]
      rw [ENNReal.rpow_add absorbExponent (alpha * e) hd0 hdTop]
    _ ≤ K ^ (-q) * R ^ e := mul_le_mul' habsorb hRadiusGain
    _ = R ^ (-u) * (K ^ (-q) * R ^ ((1 - tau) * q)) := by
      rw [show e = -u + (1 - tau) * q by rfl,
        ENNReal.rpow_add (-u) ((1 - tau) * q) hR0 hRTop]
      ac_rfl
    _ ≤ R ^ (-u) * (R / A) ^ q := mul_le_mul' le_rfl hratioPower
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
      congr 3; ring

variable {delta : NNReal} {index : Type}
  [Fintype index] [DecidableEq index]
  {fine : UniformTubeFamily delta index}
  {Cmulti : CoherentStickyMultiscaleCover fine}
  {depth N : Nat} {stoppingEpsilon : Real} {eta : Nat → Real}
  {scaleSequence : FiniteScaleSequence delta depth}

/-- Actual canonical-buffered specialization for an arbitrary paper
flatness parameter `tau`. -/
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
    (tau innerEpsilon beta absorbExponent : Real)
    (hnotHullThin : ¬ hullShortestSide
      (selectedParentGreedyBlockJohnFrame G
        (canonicalBufferedRadius_pos D hdelta hstoppingEpsilon) P k) ≤
          canonicalBufferedRadius D ^ (1 - tau))
    (hbetaTwoThirds : beta ≤ 2 / 3)
    (hflatRadiusExponent :
      -innerEpsilon / 2 + (1 - tau) * (2 - 3 * beta) ≤ 0)
    (habsorbExponent : 0 < absorbExponent)
    (hsmall : delta ≤
      adaptiveScaleReserveFlatConstantThreshold beta absorbExponent) :
    (delta : ENNReal) ^
        (absorbExponent +
          (stoppingEpsilon * (1 - stoppingEpsilon)) *
            (-innerEpsilon / 2 + (1 - tau) * (2 - 3 * beta))) ≤
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
    hfineContained G hrho hrhoOne P k r hr label W tau
  have hflat : bucketShortA label ≤
      286654464 * canonicalBufferedRadius D ^ tau := by
    rcases hflatBranch with hthin | hflat
    · exact False.elim (hnotHullThin hthin)
    · exact hflat
  apply delta_rpow_absorb_add_flatRadiusExponent_le_scaleReserve
    hdelta hrho hbetaTwoThirds (bucketShortA_pos label)
      (bucketShortA_le_bucketShortB label)
  · exact canonicalBufferedRadius_le_delta_rpow_mul_one_sub
      D hdelta hstoppingEpsilon hstoppingEpsilonHalf
  · exact hflat
  · exact hflatRadiusExponent
  · exact habsorbExponent
  · exact hsmall

#print axioms delta_rpow_absorb_add_flatRadiusExponent_le_scaleReserve
#print axioms
  selectedParent_canonicalBuffered_nonHullThin_scaleReservePowerLower

end
end Family8SelectedParentAdaptiveScaleReservePowerLowerV2
