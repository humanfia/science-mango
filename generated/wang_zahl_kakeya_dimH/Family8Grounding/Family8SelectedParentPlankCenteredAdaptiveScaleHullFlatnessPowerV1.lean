import Family8Grounding.Family8SelectedParentPlankCenteredAdaptiveScaleHullFlatnessAdaptiveBoundV2
import FamilyStickyGrounding.FamilyStickyScaleChainSmallDeltaExponentBudgetProducerV1
import Mathlib.Tactic

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 5000000

open Set MeasureTheory
open scoped ENNReal NNReal BigOperators InnerProductSpace

namespace Family8SelectedParentPlankCenteredAdaptiveScaleHullFlatnessPowerV1

open LeanEval.Analysis.WangZahlKakeya
open Submission.Kakeya.ConvexGeometry
open Submission.Kakeya.ConvexFactoring
open Submission.Kakeya.ConvexFactoring.FullConvexMaximalDensity
open Submission.Kakeya.ConvexFactoring.GreedyOccurrenceFactorization
open Submission.Kakeya.Uniformity
open Family8SelectedParentCertifiedPlankCordobaConnectorV3
open Family8SelectedParentJohnFrameNormalizationV9
open Family8SelectedParentJohnPlankSideWidthBridgeV5
open Family8SelectedParentJohnPlankSideWidthBridgeV7
open Family8SelectedParentPlankCenteredAdaptiveScaleHullFlatnessGeometryV1
open Family8SelectedParentPlankCenteredAdaptiveScaleHullFlatnessAdaptiveBoundV2
open Family8SelectedParentPlankCenteredHalfPostAdaptiveScalePackingV1
open Family8StickySelectedParentGreedyBlockFrostmanV3
open FamilyStickyAtEveryScaleCoreV1
open FamilyStickyDividingScalesFiniteStoppingV1
open FamilyStickyScaleChainCoherentIntervalProducerV1
open FamilyStickyScaleChainIdentifiedFrostmanDividingWitnessV4
open FamilyStickyScaleChainSmallDeltaExponentBudgetProducerV1
open Family8IdentifiedDividingWitnessCanonicalBufferedCoverV5.Witness

noncomputable section

theorem max_mul_rpow_power_le_self
    {d s K₁ K₂ : NNReal} {alpha beta q : Real}
    (hd : 0 < d) (hdOne : d ≤ 1) (hq : 0 ≤ q)
    (hs : s ≤ max (K₁ * d ^ alpha) (K₂ * d ^ beta))
    (hgap : 0 < min alpha beta * q - 1)
    (hdSmall : d ≤ finiteConstantSmallDeltaThreshold
      ((((max K₁ K₂ : NNReal) : ENNReal) ^ q))
      (min alpha beta * q - 1)) :
    (s : ENNReal) ^ q ≤ (d : ENNReal) := by
  let m : Real := min alpha beta
  let K : NNReal := max K₁ K₂
  have hmAlpha : m ≤ alpha := min_le_left _ _
  have hmBeta : m ≤ beta := min_le_right _ _
  have hdAlpha : d ^ alpha ≤ d ^ m :=
    NNReal.rpow_le_rpow_of_exponent_ge hd hdOne hmAlpha
  have hdBeta : d ^ beta ≤ d ^ m :=
    NNReal.rpow_le_rpow_of_exponent_ge hd hdOne hmBeta
  have hK₁ : K₁ ≤ K := le_max_left _ _
  have hK₂ : K₂ ≤ K := le_max_right _ _
  have hsK : s ≤ K * d ^ m := by
    calc
      s ≤ max (K₁ * d ^ alpha) (K₂ * d ^ beta) := hs
      _ ≤ max (K * d ^ m) (K * d ^ m) := by
        exact max_le_max (by gcongr) (by gcongr)
      _ = K * d ^ m := max_self _
  have hsENN : (s : ENNReal) ≤
      (K : ENNReal) * (d : ENNReal) ^ m := by
    rw [← ENNReal.coe_rpow_of_ne_zero hd.ne' m,
      ← ENNReal.coe_mul, ENNReal.coe_le_coe]
    exact hsK
  have hKTop : (K : ENNReal) ^ q ≠ ∞ :=
    ENNReal.rpow_ne_top_of_nonneg hq ENNReal.coe_ne_top
  have hKAbsorb : (K : ENNReal) ^ q ≤
      (d : ENNReal) ^ (-(m * q - 1)) := by
    exact finiteConstant_le_delta_negativePower hKTop
      (by simpa only [m] using hgap) hd (by
        simpa only [K, m] using hdSmall)
  have hd0 : (d : ENNReal) ≠ 0 := ENNReal.coe_ne_zero.mpr hd.ne'
  have hdTop : (d : ENNReal) ≠ ∞ := ENNReal.coe_ne_top
  calc
    (s : ENNReal) ^ q ≤
        ((K : ENNReal) * (d : ENNReal) ^ m) ^ q :=
      ENNReal.rpow_le_rpow hsENN hq
    _ = (K : ENNReal) ^ q * (((d : ENNReal) ^ m) ^ q) := by
      rw [ENNReal.mul_rpow_of_nonneg _ _ hq]
    _ = (K : ENNReal) ^ q * (d : ENNReal) ^ (m * q) := by
      rw [ENNReal.rpow_mul]
    _ ≤ (d : ENNReal) ^ (-(m * q - 1)) *
        (d : ENNReal) ^ (m * q) := by
      simpa only [mul_comm] using
        (mul_le_mul_right hKAbsorb ((d : ENNReal) ^ (m * q)))
    _ = (d : ENNReal) ^ (-(m * q - 1) + (m * q)) := by
      rw [ENNReal.rpow_add (-(m * q - 1)) (m * q) hd0 hdTop]
    _ = (d : ENNReal) := by
      rw [show -(m * q - 1) + (m * q) = (1 : Real) by ring,
        ENNReal.rpow_one]

variable {delta : NNReal} {index : Type}
  [Fintype index] [DecidableEq index]
  {fine : UniformTubeFamily delta index}
  {C : CoherentStickyMultiscaleCover fine}
  {depth N : Nat} {epsilon : Real} {eta : Nat → Real}
  {scaleSequence : FiniteScaleSequence delta depth}

theorem selectedParent_canonicalBuffered_paperHullThin_or_adaptivePower
    (hfineContained : ∀ i, (fine.tubes i).carrier ⊆
      Metric.closedBall (0 : Space) 1)
    (D : IdentifiedFrostmanDividingWitness
      fine C N epsilon eta scaleSequence)
    (hdelta : 0 < delta) (hepsilon : 0 ≤ epsilon)
    (hepsilonHalf : epsilon ≤ 1 / 2)
    (G : StickyScaleCover fine (canonicalBufferedRadius D))
    (P : GreedyDensityPartition G.activeCoarseFamily
      (hullCandidates (Finset.univ : Finset (ActiveParentIndex G)))
      (hullContainer G.activeCoarseFamily) Finset.univ)
    (k : Fin (blocks G.activeCoarseFamily P).length)
    (r : NNReal) (hr : 0 < r) (label : Fin 3 → Int)
    (W : {p // p ∈ selectedParentPlankBucketIndices
      (contractedJohnAffineEquiv
        (selectedParentGreedyBlockJohnFrame G
          (canonicalBufferedRadius_pos D hdelta hepsilon) P k) r hr)
      G (blockAt G.activeCoarseFamily P k).fiber
        (canonicalBufferedRadius_pos D hdelta hepsilon) label})
    (tau scaleExponent : Real) (htau : 0 ≤ tau)
    (hscaleExponent : 0 ≤ scaleExponent)
    (hgap : 0 <
      min ((epsilon * (1 - epsilon)) * tau) (epsilon ^ 2) *
        scaleExponent - 1)
    (hdeltaSmall : delta ≤ finiteConstantSmallDeltaThreshold
      ((((max (191102976 * 286654464) 31104 : NNReal) : ENNReal) ^
        scaleExponent))
      (min ((epsilon * (1 - epsilon)) * tau) (epsilon ^ 2) *
        scaleExponent - 1)) :
    let rho := canonicalBufferedRadius D
    let J := selectedParentGreedyBlockJohnFrame G
      (canonicalBufferedRadius_pos D hdelta hepsilon) P k
    hullShortestSide J ≤ rho ^ (1 - tau) ∨
      ((selectedParentCenteredHalfPostAdaptiveProxyScale
        delta rho r label : NNReal) : ENNReal) ^ scaleExponent ≤
        (delta : ENNReal) := by
  dsimp only
  let rho := canonicalBufferedRadius D
  rcases selectedParent_canonicalBuffered_paperHullThin_or_adaptiveDeltaPower
      hfineContained D hdelta hepsilon hepsilonHalf G P k r hr label W
        tau htau with hthin | hflat
  · exact Or.inl hthin
  · right
    have hdeltaOne : delta ≤ 1 :=
      (scaleSequence.delta_le_tau D.m).trans
        ((scaleSequence.tau_le_theta D.m).trans
          (scaleSequence.theta_le_one D.m))
    apply max_mul_rpow_power_le_self hdelta hdeltaOne hscaleExponent
      (K₁ := 191102976 * 286654464) (K₂ := 31104)
      (alpha := (epsilon * (1 - epsilon)) * tau)
      (beta := epsilon ^ 2)
    · simpa only [mul_assoc] using hflat
    · exact hgap
    · exact hdeltaSmall

#print axioms max_mul_rpow_power_le_self
#print axioms selectedParent_canonicalBuffered_paperHullThin_or_adaptivePower

end
end Family8SelectedParentPlankCenteredAdaptiveScaleHullFlatnessPowerV1
