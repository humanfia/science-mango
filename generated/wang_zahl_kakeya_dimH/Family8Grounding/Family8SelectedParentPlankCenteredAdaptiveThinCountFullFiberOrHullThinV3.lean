import Family8Grounding.Family8SelectedParentPlankCenteredAdaptiveThinCountOrHullThinV2
import Family8Grounding.Family8SelectedParentPlankCenteredAdaptiveScaleHullFlatnessPowerV1
import Family8Grounding.Family8SelectedParentPlankCenteredAdaptiveScaleThinGeometryV1
import Family8Grounding.Family8SelectedParentPlankCenteredMassFreshAdaptiveSourcePowerThinCountV1
import Mathlib.Tactic

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 5000000

open Set MeasureTheory
open scoped ENNReal NNReal BigOperators

namespace Family8SelectedParentPlankCenteredAdaptiveThinCountFullFiberOrHullThinV3

open LeanEval.Analysis.WangZahlKakeya
open Submission.Kakeya.ConvexGeometry
open Submission.Kakeya.ConvexFactoring
open Submission.Kakeya.ConvexFactoring.FullConvexMaximalDensity
open Submission.Kakeya.ConvexFactoring.GreedyOccurrenceFactorization
open Submission.Kakeya.Uniformity
open Family4GlobalExtremalUpstream
open Family8ContractedJohnActualTubeProxyV1
open Family8FiniteRandomRigidMotionB2NormalizedDatumV1
open Family8GeneralizedKatzTaoMultiplicityV1
open Family8KatzTaoFrostmanPropertiesV1
open Family8SelectedParentCertifiedPlankCordobaConnectorV3
open Family8SelectedParentJohnFrameNormalizationV9
open Family8SelectedParentJohnPlankSideWidthBridgeV5
open Family8SelectedParentJohnPlankSideWidthBridgeV7
open Family8SelectedParentJohnPlankSideWidthBridgeV8
open Family8SelectedParentPlankCanonicalThinCountV5
open Family8SelectedParentPlankCenteredAdaptiveScaleHullFlatnessPowerV1
open Family8SelectedParentPlankCenteredAdaptiveScaleHullFlatnessGeometryV1
open FamilyStickyDividingScalesFiniteStoppingV1
open FamilyStickyScaleChainCoherentIntervalProducerV1
open FamilyStickyScaleChainIdentifiedFrostmanDividingWitnessV4
open FamilyStickyScaleChainSmallDeltaExponentBudgetProducerV1
open Family8SelectedParentPlankCenteredAdaptiveScaleThinGeometryV1
open Family8SelectedParentPlankCenteredAdaptiveThinCountOrHullThinV2
open Family8SelectedParentPlankCenteredHalfPostAdaptiveScalePackingV1
open Family8SelectedParentPlankCenteredHalfPostCarrierV1
open Family8SelectedParentPlankCenteredHalfPostKatzTaoV1
open Family8SelectedParentPlankCenteredHalfPostMassDatumV2
open Family8SelectedParentPlankCenteredHalfPostStructuredRadiusV1
open Family8SelectedParentPlankCenteredMassFreshAdaptiveSourcePowerThinCountV1
open Family8SelectedParentPlankCenteredMassFreshKatzTaoEndpointV6
open Family8SelectedParentPlankCenteredSourcePowerBudgetsV3
open Family8SelectedParentPlankCenteredSourcePowerEnvelopesV4
open Family8SelectedParentPlankFineAxisCoordinateV2
open Family8SelectedParentPlankFineMassProxyDatumV2
open Family8SelectedParentPlankFineProxyCarrierV3
open Family8StickySelectedParentGreedyBlockFrostmanV3
open Family8ThinPlankFiveParameterPackingV2
open FamilyStickyAtEveryScaleCoreV1
open Family8IdentifiedDividingWitnessCanonicalBufferedCoverV5.Witness

noncomputable section

/-!
# Same-selected adaptive thin-count or paper hull-thin branch

On the flat-scale side of the actual hull dichotomy, the proved adaptive
power is inverted at one explicit positive threshold.  This generates all
four small-scale premises of the existing source-power thin-count consumer,
including its literal aspect-dependent quadratic inequality.  The other
side is the unchanged shortest-axis paper branch for the same `G,P,k,r,label,W`.
-/

/-- The literal natural Eq. (46) fibre parameter: fresh loss times the
five-parameter packing cap for the same actual selected plank. -/
def adaptiveThinCountFullFiberNatCap
    (Cproxy : ENNReal) (label : Fin 3 → Int) : Nat :=
  (Nat.ceil ((480000 * (128 * Cproxy) : ENNReal).toReal) + 1) *
    thinPlankFivePackingNatCap
      (3 * selectedPlankFineCanonicalAspect label)

variable {delta : NNReal} {index : Type}
  [Fintype index] [DecidableEq index]
  {fine : UniformTubeFamily delta index}
  {Cmulti : CoherentStickyMultiscaleCover fine}
  {depth N : Nat} {stoppingEpsilon : Real}
  {stoppingEta : Nat → Real}
  {scaleSequence : FiniteScaleSequence delta depth}

theorem exists_adaptiveThinCount_fullFiberCap_or_paperHullThin_of_sourcePowers
    {beta epsilon eta sourceEta geometricEta globalEta freshAbsorbEta
      densityAbsorbEta coefficientAbsorbEta : Real}
    {delta0 : NNReal}
    (hKTP : KatzTaoAtParameters beta epsilon eta delta0)
    (hdelta0Pos : 0 < delta0)
    (Y : Shading fine.bodyFamily)
    (hfineContained : ∀ i, (fine.tubes i).carrier ⊆
      Metric.closedBall (0 : Space) 1)
    (D : IdentifiedFrostmanDividingWitness
      fine Cmulti N stoppingEpsilon stoppingEta scaleSequence)
    (hdeltaPos : 0 < delta)
    (hstoppingEpsilon : 0 ≤ stoppingEpsilon)
    (hstoppingEpsilonHalf : stoppingEpsilon ≤ 1 / 2)
    (G : StickyScaleCover fine (canonicalBufferedRadius D))
    (P : GreedyDensityPartition G.activeCoarseFamily
      (hullCandidates (Finset.univ : Finset (ActiveParentIndex G)))
      (hullContainer G.activeCoarseFamily) Finset.univ)
    (k : Fin (blocks G.activeCoarseFamily P).length)
    (r : NNReal) (hr : 0 < r) (label : Fin 3 → Int)
    (hplank : ∀ W : {p // p ∈ selectedParentPlankBucketIndices
      (contractedJohnAffineEquiv
        (selectedParentGreedyBlockJohnFrame G
          (canonicalBufferedRadius_pos D hdeltaPos hstoppingEpsilon) P k)
          r hr)
      G (blockAt G.activeCoarseFamily P k).fiber
        (canonicalBufferedRadius_pos D hdeltaPos hstoppingEpsilon) label},
      IsPlank 576 (bucketShortA label) (bucketShortB label)
        (selectedParentPlankBucketFamily
          (contractedJohnAffineEquiv
            (selectedParentGreedyBlockJohnFrame G
              (canonicalBufferedRadius_pos D hdeltaPos
                hstoppingEpsilon) P k) r hr)
          G (blockAt G.activeCoarseFamily P k).fiber
            (canonicalBufferedRadius_pos D hdeltaPos
              hstoppingEpsilon) label W))
    (W : {p // p ∈ selectedParentPlankBucketIndices
      (contractedJohnAffineEquiv
        (selectedParentGreedyBlockJohnFrame G
          (canonicalBufferedRadius_pos D hdeltaPos hstoppingEpsilon) P k)
          r hr)
      G (blockAt G.activeCoarseFamily P k).fiber
        (canonicalBufferedRadius_pos D hdeltaPos hstoppingEpsilon) label})
    (tau scaleExponent : Real) (htau : 0 ≤ tau)
    (hscaleExponent : 0 < scaleExponent)
    (hgap : 0 <
      min ((stoppingEpsilon * (1 - stoppingEpsilon)) * tau)
          (stoppingEpsilon ^ 2) * scaleExponent - 1)
    (hdeltaPowerSmall : delta ≤ finiteConstantSmallDeltaThreshold
      ((((max (191102976 * 286654464) 31104 : NNReal) : ENNReal) ^
        scaleExponent))
      (min ((stoppingEpsilon * (1 - stoppingEpsilon)) * tau)
          (stoppingEpsilon ^ 2) * scaleExponent - 1))
    (hdeltaThinSmall : delta ≤
      (adaptiveThinCountScaleThreshold delta0 freshAbsorbEta
        densityAbsorbEta coefficientAbsorbEta label) ^ scaleExponent)
    (hdeltaHalf : delta ≤ (2 : NNReal)⁻¹)
    {CKT : ENNReal} (hCKTfinite : CKT ≠ ∞)
    (hglobalKT : IsKatzTao CKT fine.bodyFamily)
    (heta : 0 ≤ eta)
    (hsourcePower :
      let rho := canonicalBufferedRadius D
      let hrho := canonicalBufferedRadius_pos D hdeltaPos hstoppingEpsilon
      let e := contractedJohnAffineEquiv
        (selectedParentGreedyBlockJohnFrame G hrho P k) r hr
      let B := (blockAt G.activeCoarseFamily P k).fiber
      let s := selectedParentCenteredHalfPostAdaptiveProxyScale
        delta rho r label
      (s : ENNReal) ^ sourceEta ≤
        (selectedPlankFineSourceShading
          Y e G B hrho label W).shadingDensity)
    (hgeometricPower :
      let rho := canonicalBufferedRadius D
      let hrho := canonicalBufferedRadius_pos D hdeltaPos hstoppingEpsilon
      let e := contractedJohnAffineEquiv
        (selectedParentGreedyBlockJohnFrame G hrho P k) r hr
      let B := (blockAt G.activeCoarseFamily P k).fiber
      let s := selectedParentCenteredHalfPostAdaptiveProxyScale
        delta rho r label
      centeredHalfPostSelectedPlankFineProxyGeometricLoss
          s e G B hrho label hplank W ≤
        (s : ENNReal) ^ (-geometricEta))
    (hglobalPower :
      CKT ≤ (selectedParentCenteredHalfPostAdaptiveProxyScale
        delta (canonicalBufferedRadius D) r label : ENNReal) ^ (-globalEta))
    (hgeometricEta : 0 ≤ geometricEta) (hglobalEta : 0 ≤ globalEta)
    (hfreshAbsorbEta : 0 < freshAbsorbEta)
    (hdensityAbsorbEta : 0 < densityAbsorbEta)
    (hcoefficientAbsorbEta : 0 < coefficientAbsorbEta)
    (hdensityExponent :
      (sourceEta + geometricEta) +
          (geometricEta + globalEta + freshAbsorbEta) +
            densityAbsorbEta ≤ eta)
    (hcoefficientExponent :
      (geometricEta + globalEta) + coefficientAbsorbEta ≤ eta) :
    let rho := canonicalBufferedRadius D
    let hrho := canonicalBufferedRadius_pos D hdeltaPos hstoppingEpsilon
    let J := selectedParentGreedyBlockJohnFrame G hrho P k
    let e := contractedJohnAffineEquiv J r hr
    let B := (blockAt G.activeCoarseFamily P k).fiber
    let s := selectedParentCenteredHalfPostAdaptiveProxyScale
      delta rho r label
    let R := selectedPlankFineCanonicalAspect label
    let hscalar := selectedParent_centeredHalfPost_adaptive_radius_scalar
      (delta := delta) hrho r label
    let hradius := selectedParent_centeredHalfPost_radius_budget
      G hrho P k r hr label B hplank W s hscalar
    let M := centeredHalfPostSelectedPlankFineMassDatum
      s Y e G B hrho label hplank W hradius
    let Cproxy := centeredHalfPostSelectedPlankFineProxyKatzTaoConstant
      s e G B hrho label hplank W CKT
    let threshold := Nat.ceil ((480000 * (128 * Cproxy) : ENNReal).toReal)
    let loss := threshold + 1
    (∃ selected : Finset (SelectedPlankFineIndex G W),
      selected.Nonempty ∧
      (restrictActualTubeDatum
        (eighthNormalizedDatum M) selected).IsAdmissible ∧
      (Fintype.card (SelectedPlankFineIndex G W) : ENNReal) ≤
        (loss : ENNReal) * (selected.card : ENNReal) ∧
      (eighthNormalizedDatum M).shading.shadingMass ≤
        (loss : ENNReal) *
          (restrictActualTubeDatum
            (eighthNormalizedDatum M) selected).shading.shadingMass ∧
      IsKatzTao (128 * Cproxy)
        (restrictActualTubeDatum
          (eighthNormalizedDatum M) selected).family.bodyFamily ∧
      KatzTaoHypotheses
        (restrictActualTubeDatum (eighthNormalizedDatum M) selected) eta ∧
      (restrictActualTubeDatum
        (eighthNormalizedDatum M) selected).shading.averageMultiplicity ≤
          katzTaoMultiplicityRHS (s / 8) selected.card epsilon beta ∧
      (selectedPlankFineSourceShading
        Y e G B hrho label W).averageMultiplicity ≤
          (loss : ENNReal) *
            katzTaoMultiplicityRHS (s / 8) selected.card epsilon beta ∧
      selected.card ≤ thinPlankFivePackingNatCap (3 * R) ∧
      Fintype.card (SelectedPlankFineIndex G W) ≤
        adaptiveThinCountFullFiberNatCap Cproxy label) ∨
      hullShortestSide J ≤ rho ^ (1 - tau) := by
  dsimp only
  have hbranch :=
    Family8SelectedParentPlankCenteredAdaptiveThinCountOrHullThinV2.exists_adaptiveThinCount_or_paperHullThin_of_sourcePowers
        hKTP hdelta0Pos Y hfineContained D hdeltaPos hstoppingEpsilon
          hstoppingEpsilonHalf G P k r hr label hplank W tau scaleExponent
            htau hscaleExponent hgap hdeltaPowerSmall hdeltaThinSmall
              hdeltaHalf hCKTfinite hglobalKT heta hsourcePower
                hgeometricPower hglobalPower hgeometricEta hglobalEta
                  hfreshAbsorbEta hdensityAbsorbEta hcoefficientAbsorbEta
                    hdensityExponent hcoefficientExponent
  dsimp only at hbranch
  rcases hbranch with hThin | hHull
  · left
    obtain ⟨selected, hselected, hadmissible, hcard, hmass, hKT,
      hKTHypotheses, havg, hsourceAvg, hcap⟩ := hThin
    refine ⟨selected, hselected, hadmissible, hcard, hmass, hKT,
      hKTHypotheses, havg, hsourceAvg, hcap, ?_⟩
    let rho := canonicalBufferedRadius D
    let hrho : 0 < rho :=
      canonicalBufferedRadius_pos D hdeltaPos hstoppingEpsilon
    let J := selectedParentGreedyBlockJohnFrame G hrho P k
    let e := contractedJohnAffineEquiv J r hr
    let B := (blockAt G.activeCoarseFamily P k).fiber
    let s := selectedParentCenteredHalfPostAdaptiveProxyScale
      delta rho r label
    let Cproxy := centeredHalfPostSelectedPlankFineProxyKatzTaoConstant
      s e G B hrho label hplank W CKT
    let loss := Nat.ceil ((480000 * (128 * Cproxy) : ENNReal).toReal) + 1
    let thinCap := thinPlankFivePackingNatCap
      (3 * selectedPlankFineCanonicalAspect label)
    have hcard' : (Fintype.card (SelectedPlankFineIndex G W) : ENNReal) ≤
        (loss : ENNReal) * (selected.card : ENNReal) := by
      simpa only [rho, hrho, J, e, B, s, Cproxy, loss] using hcard
    have hcapENN : (selected.card : ENNReal) ≤ (thinCap : Nat) := by
      exact_mod_cast hcap
    have hfullENN :
        (Fintype.card (SelectedPlankFineIndex G W) : ENNReal) ≤
          ((loss * thinCap : Nat) : ENNReal) := by
      calc
        (Fintype.card (SelectedPlankFineIndex G W) : ENNReal) ≤
            (loss : ENNReal) * (selected.card : ENNReal) := hcard'
        _ ≤ (loss : ENNReal) * (thinCap : Nat) :=
          mul_le_mul' le_rfl hcapENN
        _ = ((loss * thinCap : Nat) : ENNReal) := by norm_num
    have hfullNat :
        Fintype.card (SelectedPlankFineIndex G W) ≤ loss * thinCap := by
      exact_mod_cast hfullENN
    simpa only [adaptiveThinCountFullFiberNatCap, rho, hrho, J, e, B, s,
      Cproxy, loss, thinCap] using hfullNat
  · exact Or.inr hHull

#print axioms
  exists_adaptiveThinCount_fullFiberCap_or_paperHullThin_of_sourcePowers

end
end Family8SelectedParentPlankCenteredAdaptiveThinCountFullFiberOrHullThinV3
