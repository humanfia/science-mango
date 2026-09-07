import Family8Grounding.Family8SelectedParentCanonicalBufferedAdaptiveInnerPowerLowerV2
import Mathlib.Tactic

/-!
# Canonical paper flatness parameter and the actual power residual

The fixed quadratic loss in the card-weighted Equation (46) residual cannot
be absorbed at `tau = 1`.  Here `tau` is chosen canonically from the displayed
loss budget.  The non-hull-thin branch then has exactly enough negative
radius exponent to absorb that loss.  The endpoint invokes the actual
selected-bucket inner lower bound; the residual inequality is not assumed.
-/

open Set MeasureTheory
open scoped BigOperators ENNReal NNReal InnerProductSpace

namespace Family8SelectedParentCanonicalBufferedAdaptivePowerResidualV1

open LeanEval.Analysis.WangZahlKakeya
open Submission.Kakeya.ConvexGeometry
open Submission.Kakeya.ConvexFactoring
open Submission.Kakeya.ConvexFactoring.FullConvexMaximalDensity
open Submission.Kakeya.ConvexFactoring.GreedyOccurrenceFactorization
open Submission.Kakeya.Uniformity
open Family8IdentifiedDividingWitnessCanonicalBufferedCoverV5.Witness
open Family8Prop66AOuterInnerProductAlgebraV1
open Family8SelectedParentAdaptiveScaleReservePowerLowerV1
open Family8SelectedParentCanonicalBufferedAdaptiveInnerPowerLowerV2
open Family8SelectedParentCertifiedPlankCordobaConnectorV3
open Family8SelectedParentJohnFrameNormalizationV9
open Family8SelectedParentJohnPlankSideWidthBridgeV5
open Family8SelectedParentJohnPlankSideWidthBridgeV7
open Family8SelectedParentPlankCenteredAdaptiveScaleHullFlatnessGeometryV1
open Family8SelectedParentPlankCenteredAdaptiveThinCountGlobalEq46CountV2
open Family8SelectedParentPlankCenteredAdaptiveThinCountGlobalMassPopularEndpointV3
open Family8SelectedParentPlankCenteredHalfPostAdaptiveScalePackingV1
open Family8StickySelectedParentGreedyBlockFrostmanV3
open FamilyStickyAtEveryScaleCoreV1
open FamilyStickyCinematicL32FiniteWeightedBucketV1
open FamilyStickyDividingScalesFiniteStoppingV1
open FamilyStickyScaleChainCoherentIntervalProducerV1
open FamilyStickyScaleChainIdentifiedFrostmanDividingWitnessV4

noncomputable section

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 6000000

/-- The canonical paper flatness parameter.  `reserveBudget` is all power
that must be paid beyond the radius reserve. -/
def canonicalEq46PaperFlatnessTau
    (alpha q u reserveBudget : Real) : Real :=
  1 + (reserveBudget / alpha + u) / q

theorem canonicalEq46PaperFlatnessTau_flatExponent_eq
    {alpha q u reserveBudget : Real}
    (halpha : 0 < alpha) (hq : 0 < q) :
    -u + (1 - canonicalEq46PaperFlatnessTau alpha q u reserveBudget) * q =
      -(reserveBudget / alpha) - 2 * u := by
  unfold canonicalEq46PaperFlatnessTau
  field_simp [halpha.ne', hq.ne']
  ring

/-- The canonical choice makes the flat exponent nonpositive and pays the
complete quadratic/card-weighted power budget. -/
theorem canonicalEq46PaperFlatnessTau_exponent_budget
    {alpha q u p absorbExponent coefficientExponent etaF : Real}
    (halpha : 0 < alpha) (hq : 0 < q) (hu : 0 ≤ u)
    (hreserve : 0 ≤
      p + absorbExponent + coefficientExponent + 2 + 2 * etaF) :
    let reserveBudget :=
      p + absorbExponent + coefficientExponent + 2 + 2 * etaF
    let tau := canonicalEq46PaperFlatnessTau alpha q u reserveBudget
    (-u + (1 - tau) * q ≤ 0) ∧
      (2 + 2 * etaF +
        (p + absorbExponent + alpha * (-u + (1 - tau) * q)) ≤
          -coefficientExponent) := by
  dsimp only
  let reserveBudget : Real :=
    p + absorbExponent + coefficientExponent + 2 + 2 * etaF
  let tau := canonicalEq46PaperFlatnessTau alpha q u reserveBudget
  have heq : -u + (1 - tau) * q =
      -(reserveBudget / alpha) - 2 * u := by
    simpa only [tau] using
      canonicalEq46PaperFlatnessTau_flatExponent_eq
        (reserveBudget := reserveBudget) halpha hq
  have hdiv : 0 ≤ reserveBudget / alpha :=
    div_nonneg (by simpa only [reserveBudget] using hreserve) halpha.le
  have hcancel : alpha * (reserveBudget / alpha) = reserveBudget := by
    field_simp [halpha.ne']
  constructor
  · rw [heq]
    linarith
  · rw [heq]
    have hau : 0 ≤ alpha * u := mul_nonneg halpha.le hu
    dsimp only [reserveBudget] at hcancel ⊢
    nlinarith

/-- Base-at-most-one power algebra used by the actual endpoint. -/
theorem delta_negativePower_le_quadratic_mul_inner_of_powerLower
    {delta : NNReal} {coefficientExponent etaF innerExponent : Real}
    {inner : ENNReal}
    (hdelta : 0 < delta) (hdeltaOne : delta ≤ 1)
    (hexponent :
      2 + 2 * etaF + innerExponent ≤ -coefficientExponent)
    (hinner : (delta : ENNReal) ^ innerExponent ≤ inner) :
    (delta : ENNReal) ^ (-coefficientExponent) ≤
      (delta : ENNReal) ^ 2 *
        ((delta : ENNReal) ^ (2 * etaF) * inner) := by
  let d : ENNReal := delta
  have hd0 : d ≠ 0 := ENNReal.coe_ne_zero.mpr hdelta.ne'
  have hdTop : d ≠ ∞ := ENNReal.coe_ne_top
  have hdOne0 : (delta : ENNReal) ≤ 1 := by exact_mod_cast hdeltaOne
  have hdOne : d ≤ 1 := by simpa only [d] using hdOne0
  have hpower : d ^ (-coefficientExponent) ≤
      d ^ (2 + 2 * etaF + innerExponent) :=
    ENNReal.rpow_le_rpow_of_exponent_ge hdOne hexponent
  calc
    (delta : ENNReal) ^ (-coefficientExponent) ≤
        d ^ (2 + 2 * etaF + innerExponent) := hpower
    _ = d ^ 2 * (d ^ (2 * etaF) * d ^ innerExponent) := by
      rw [show 2 + 2 * etaF + innerExponent =
          2 + (2 * etaF + innerExponent) by ring,
        ENNReal.rpow_add 2 (2 * etaF + innerExponent) hd0 hdTop,
        ENNReal.rpow_add (2 * etaF) innerExponent hd0 hdTop]
      exact congrArg (fun x : ENNReal =>
        x * (d ^ (2 * etaF) * d ^ innerExponent))
          (ENNReal.rpow_natCast d 2)
    _ ≤ d ^ 2 * (d ^ (2 * etaF) * inner) :=
      mul_le_mul' le_rfl (mul_le_mul' le_rfl hinner)
    _ = (delta : ENNReal) ^ 2 *
        ((delta : ENNReal) ^ (2 * etaF) * inner) := rfl

/-- Canonical parameter used by the selected-parent actual endpoint. -/
def selectedParentCanonicalEq46PaperTau
    (stoppingEpsilon innerEpsilon beta coarseExponent absorbExponent
      coefficientExponent etaF : Real) : Real :=
  canonicalEq46PaperFlatnessTau
    (stoppingEpsilon * (1 - stoppingEpsilon))
    (2 - 3 * beta) (innerEpsilon / 2)
    (coarseExponent * (beta / 2) + absorbExponent +
      coefficientExponent + 2 + 2 * etaF)

variable {delta : NNReal} {index : Type}
  [Fintype index] [DecidableEq index]
  {fine : UniformTubeFamily delta index}
  {Cmulti : CoherentStickyMultiscaleCover fine}
  {depth N : Nat} {stoppingEpsilon : Real} {eta : Nat → Real}
  {scaleSequence : FiniteScaleSequence delta depth}

/-- Callback-free actual residual on the selected canonical-buffered bucket.
The only branch premise is failure of the geometric hull-thin alternative at
the explicitly displayed canonical paper parameter. -/
theorem selectedParent_canonicalBuffered_nonHullThin_powerResidual
    (D : IdentifiedFrostmanDividingWitness
      fine Cmulti N stoppingEpsilon eta scaleSequence)
    (hfineContained : ∀ i, (fine.tubes i).carrier ⊆
      Metric.closedBall (0 : Space) 1)
    (hdelta : 0 < delta) (hdeltaHalf : delta ≤ (2 : NNReal)⁻¹)
    (hstoppingEpsilon : 0 < stoppingEpsilon)
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
          (canonicalBufferedRadius_pos D hdelta hstoppingEpsilon.le) P k) r hr)
      G (blockAt G.activeCoarseFamily P k).fiber
        (canonicalBufferedRadius_pos D hdelta hstoppingEpsilon.le) label})
    (hsmallPacking : selectedParentCenteredHalfPostAdaptiveProxyScale
      delta (canonicalBufferedRadius D) r label / 8 ≤
        (1 / 100 : NNReal))
    (C : ENNReal) (coarseExponent innerEpsilon beta absorbExponent
      coefficientExponent etaF : Real)
    (hKT : IsKatzTao C G.activeCoarseFamily)
    (hCpower : C ≤ (delta : ENNReal) ^ (-coarseExponent))
    (hinnerEpsilon : 0 ≤ innerEpsilon)
    (hbeta : 0 ≤ beta) (hbetaStrict : beta < 2 / 3)
    (habsorbExponent : 0 < absorbExponent)
    (hreserve : 0 ≤
      coarseExponent * (beta / 2) + absorbExponent +
        coefficientExponent + 2 + 2 * etaF)
    (hsmall : delta ≤
      adaptiveScaleReserveFlatConstantThreshold beta absorbExponent)
    (hnotHullThin : ¬ hullShortestSide
      (selectedParentGreedyBlockJohnFrame G
        (canonicalBufferedRadius_pos D hdelta hstoppingEpsilon.le) P k) ≤
      canonicalBufferedRadius D ^
        (1 - selectedParentCanonicalEq46PaperTau stoppingEpsilon
          innerEpsilon beta coarseExponent absorbExponent
          coefficientExponent etaF)) :
    (delta : ENNReal) ^ (-coefficientExponent) ≤
      (delta : ENNReal) ^ 2 *
        ((delta : ENNReal) ^ (2 * etaF) *
          proposition66AInnerFactor (canonicalBufferedRadius D)
            (bucketShortA label) (bucketShortB label)
            (centeredAdaptiveActualBucketFullFiberNatCap G
              (canonicalBufferedRadius_pos D hdelta hstoppingEpsilon.le)
              P k r hr label C) innerEpsilon beta) := by
  let alpha : Real := stoppingEpsilon * (1 - stoppingEpsilon)
  let q : Real := 2 - 3 * beta
  let u : Real := innerEpsilon / 2
  let p : Real := coarseExponent * (beta / 2)
  let reserveBudget : Real :=
    p + absorbExponent + coefficientExponent + 2 + 2 * etaF
  let tau : Real := canonicalEq46PaperFlatnessTau alpha q u reserveBudget
  let g : Real := p + absorbExponent +
    alpha * (-u + (1 - tau) * q)
  have halpha : 0 < alpha := by
    dsimp only [alpha]
    exact mul_pos hstoppingEpsilon (sub_pos.mpr
      (hstoppingEpsilonHalf.trans_lt (by norm_num)))
  have hq : 0 < q := by dsimp only [q]; linarith
  have hu : 0 ≤ u := by dsimp only [u]; linarith
  have hbudget := canonicalEq46PaperFlatnessTau_exponent_budget
    (alpha := alpha) (q := q) (u := u) (p := p)
    (absorbExponent := absorbExponent)
    (coefficientExponent := coefficientExponent) (etaF := etaF)
    halpha hq hu (by simpa only [reserveBudget, p] using hreserve)
  have hflatExponent : -innerEpsilon / 2 +
      (1 - tau) * (2 - 3 * beta) ≤ 0 := by
    simpa only [tau, reserveBudget, alpha, q, u, p, neg_div,
      selectedParentCanonicalEq46PaperTau] using hbudget.1
  have hexponent : 2 + 2 * etaF + g ≤ -coefficientExponent := by
    simpa only [g, tau, reserveBudget, alpha, q, u, p,
      selectedParentCanonicalEq46PaperTau] using hbudget.2
  have hinner : (delta : ENNReal) ^ g ≤
      proposition66AInnerFactor (canonicalBufferedRadius D)
        (bucketShortA label) (bucketShortB label)
        (centeredAdaptiveActualBucketFullFiberNatCap G
          (canonicalBufferedRadius_pos D hdelta hstoppingEpsilon.le)
          P k r hr label C) innerEpsilon beta := by
    simpa only [g, tau, reserveBudget, alpha, q, u, p, neg_div,
      selectedParentCanonicalEq46PaperTau] using
      selectedParent_canonicalBuffered_nonHullThin_deltaPower_le_adaptiveActualInnerFactor
        D hfineContained hdelta hdeltaHalf hstoppingEpsilon.le
        hstoppingEpsilonHalf G P k r hr label W
        (selectedParentCanonicalEq46PaperTau stoppingEpsilon
          innerEpsilon beta coarseExponent absorbExponent
          coefficientExponent etaF)
        hnotHullThin hsmallPacking C coarseExponent innerEpsilon beta
        absorbExponent hKT hCpower hbeta hbetaStrict.le hflatExponent
        habsorbExponent hsmall
  exact delta_negativePower_le_quadratic_mul_inner_of_powerLower
    hdelta (hdeltaHalf.trans (by norm_num)) hexponent hinner

#print axioms canonicalEq46PaperFlatnessTau_flatExponent_eq
#print axioms canonicalEq46PaperFlatnessTau_exponent_budget
#print axioms delta_negativePower_le_quadratic_mul_inner_of_powerLower
#print axioms selectedParent_canonicalBuffered_nonHullThin_powerResidual

end
end Family8SelectedParentCanonicalBufferedAdaptivePowerResidualV1
