import Family8Grounding.Family8EndpointLongCoreIdentityFirstFieldsV3
import Family8Grounding.Family8AdmissibleCommonPointGlobalKatzTaoV1
import Family8Grounding.Family8EndpointIdentityTauActiveParentAdmissibilityV1
import Family8Grounding.Family8EndpointLongCoreSourceTauIdentityTransportV5
import Family8Grounding.Family8GreedyHighPrefixSameOccurrenceProp66AInnerBridgeV1
import Family8Grounding.Family8IdentitySourceFrostmanKatzTaoCardScaleCancellationV2
import Family8Grounding.Family8NormalizedLongCoreCanonicalTauCoarseDatumV2
import Family8Grounding.Family8SourceKatzTaoHypothesesFromFrostmanPackingV1
import Mathlib.Tactic

/-!
# Endpoint identity source-tau Katz--Tao power budget for the same occurrence

On the automatic endpoint identity cover the selected source-to-`tau` scale
is literally `delta`.  Thus the concrete Katz--Tao coefficient used by the
same-occurrence Cordoba branch is

`identitySourceFrostmanKatzTaoConstant D delta outputEta`.

The identity-radius loss is then the fixed number sixteen, rather than a
relative-scale power.  Common-point packing and the fixed John/angle envelope
are absorbed together in one positive exponent.  The only remaining scalar
seam is displayed as a pure power comparison against the unchanged
Proposition 6.6(A) inner factor.
-/

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 4000000

open Set MeasureTheory
open scoped BigOperators ENNReal NNReal

namespace Family8EndpointIdentitySourceTauSameOccurrenceProp66APowerBudgetV1

open LeanEval.Analysis.WangZahlKakeya
open Submission.Kakeya.ConvexGeometry
open Submission.Kakeya.ConvexFactoring
open Submission.Kakeya.ConvexFactoring.FullConvexMaximalDensity
open Submission.Kakeya.ConvexFactoring.GreedyOccurrenceFactorization
open Submission.Kakeya.ConvexFactoring.HeavyParentSelection
open Submission.Kakeya.Uniformity
open Family6AffineConvexVolumeCoreV1
open Family8EndpointLongCoreIdentityFirstFieldsV3
open Family8AdmissibleCommonPointGlobalKatzTaoV1
open Family8AmbientFamilyVolumeDensityV2
open Family8CommonPointTubePackingV1
open Family8EndpointIdentityTauActiveParentAdmissibilityV1
open Family8EndpointLongCoreSourceTauIdentityTransportV5
open Family8FullRefinementActualDatumV1
open Family8GreedyHighOccurrenceSelectedParentJohnPlankConnectorV1
open Family8GreedyHighPrefixSameOccurrenceProp66AInnerBridgeV1
open Family8IdentityRadiusSourceKatzTaoTransportV1
open Family8IdentitySourceFrostmanKatzTaoCardScaleCancellationV2
open Family8KatzTaoFrostmanPropertiesV1
open Family8NormalizedLongCoreCanonicalTauCoarseDatumV2
open Family8NormalizedLongIntervalCoreConsumerV1
open Family8ParameterLadderV1
open Family8Prop66AOuterInnerProductAlgebraV1
open Family8QuantitativeCarrierPopularityRestrictionV3
open Family8SelectedParentArbitraryBlockPlankBucketV4
open Family8SelectedParentCertifiedPlankCordobaThresholdedAngleV6
open Family8SelectedParentGreedyBlockFiberIdentityV2
open Family8SelectedParentJohnFrameNormalizationV9
open Family8SelectedParentJohnPlankSideWidthBridgeV5
open Family8SelectedParentJohnPlankSideWidthBridgeV7
open Family8SelectedParentJohnPlankSideWidthBridgeV8
open Family8SourceKatzTaoHypothesesFromFrostmanPackingV1
open Family8StickySelectedParentGreedyBlockFrostmanV3
open FamilyStickyAtEveryScaleCoreV1
open FamilyStickyDividingScalesFiniteStoppingV1
open FamilyStickyHierarchyEndpointPrefixShadingTransportV1.StickyScaleCover
open FamilyStickyScaleChainCappedSeedSequenceV2
open FamilyStickyScaleChainCoherentIntervalProducerV1
open FamilyStickyScaleChainSelectedCanonicalCoverCoordinatesProducerV1
open FamilyStickyScaleChainSmallDeltaExponentBudgetProducerV1

noncomputable section

variable {delta : NNReal} {index : Type}
  [Fintype index] [DecidableEq index]

/-- All fixed factors appearing between the exact endpoint identity source
Katz--Tao coefficient and the fixed same-bucket John envelope. -/
def endpointIdentitySourceTauCordobaFixedCoefficient : ENNReal :=
  (16 * commonPointTubePackingConstant) *
    (certifiedPlankThresholdedAngleScaleCap 576 * (2304 : ENNReal) ^ 3)

theorem endpointIdentitySourceTauCordobaFixedCoefficient_ne_top :
    endpointIdentitySourceTauCordobaFixedCoefficient ≠ ∞ := by
  unfold endpointIdentitySourceTauCordobaFixedCoefficient
  apply ENNReal.mul_ne_top
  · exact ENNReal.mul_ne_top (by norm_num)
      commonPointTubePackingConstant_ne_top
  · apply ENNReal.mul_ne_top
    · unfold certifiedPlankThresholdedAngleScaleCap
      exact max_ne_top (by norm_num) (by finiteness)
    · exact ENNReal.pow_ne_top ENNReal.coe_ne_top

/-- Terminal scale for common-point packing and a single absorption of all
fixed identity-radius, packing, angle, and John-box constants. -/
def endpointIdentitySourceTauCordobaPowerThreshold
    (absorbEta : Real) : NNReal :=
  min (1 / 100 : NNReal)
    (finiteConstantSmallDeltaThreshold
      endpointIdentitySourceTauCordobaFixedCoefficient absorbEta)

theorem endpointIdentitySourceTauCordobaPowerThreshold_pos
    (absorbEta : Real) :
    0 < endpointIdentitySourceTauCordobaPowerThreshold absorbEta := by
  rw [endpointIdentitySourceTauCordobaPowerThreshold, lt_min_iff]
  exact ⟨by positivity,
    finiteConstantSmallDeltaThreshold_pos _ _⟩

/-- The identity-radius transport ratio at the unchanged endpoint radius is
the fixed number sixteen. -/
theorem identityRadiusKatzTaoVolumeRatio_self
    (hdelta : 0 < delta) :
    identityRadiusKatzTaoVolumeRatio delta delta = 16 := by
  have hNN :
      (8 * delta ^ (2 : Nat)) / (delta ^ (2 : Nat) / 2) =
        (16 : NNReal) := by
    field_simp [hdelta.ne']
    ring
  have hdenNN : delta ^ (2 : Nat) / 2 ≠ 0 :=
    div_ne_zero (pow_ne_zero 2 hdelta.ne') (by norm_num)
  have hcast := congrArg (fun x : NNReal => (x : ENNReal)) hNN
  simpa only [identityRadiusKatzTaoVolumeRatio, ENNReal.coe_mul,
    ENNReal.coe_div hdenNN,
    ENNReal.coe_div (by norm_num : (2 : NNReal) ≠ 0),
    ENNReal.coe_pow, ENNReal.coe_ofNat] using hcast

/-- At the endpoint source scale, the concrete identity-source Katz--Tao
coefficient and the entire fixed Cordoba/John factor cost exactly the source
Frostman exponent, the geometric packing exponent two, and one chosen
absorption reserve. -/
theorem identitySourceFrostmanKatzTaoConstant_delta_mul_cordobaFixed_le_power
    (D : ActualTubeDatum delta index) (hD : D.IsAdmissible)
    {outputEta absorbEta : Real}
    (habsorbEta : 0 < absorbEta)
    (hsmall : delta <=
      endpointIdentitySourceTauCordobaPowerThreshold absorbEta) :
    identitySourceFrostmanKatzTaoConstant D delta outputEta *
        (certifiedPlankThresholdedAngleScaleCap 576 *
          (2304 : ENNReal) ^ 3) <=
      (delta : ENNReal) ^ (-(outputEta + 2 + absorbEta)) := by
  let E := fullRefinementDatum D
  have hd0 : (delta : ENNReal) ≠ 0 :=
    ENNReal.coe_ne_zero.mpr hD.delta_pos.ne'
  have hdTop : (delta : ENNReal) ≠ ∞ := ENNReal.coe_ne_top
  have hgeometric : delta <= (1 / 100 : NNReal) :=
    hsmall.trans (min_le_left _ _)
  have habsorbSmall : delta <=
      finiteConstantSmallDeltaThreshold
        endpointIdentitySourceTauCordobaFixedCoefficient absorbEta :=
    hsmall.trans (min_le_right _ _)
  have hconstant : endpointIdentitySourceTauCordobaFixedCoefficient <=
      (delta : ENNReal) ^ (-absorbEta) :=
    finiteConstant_le_delta_negativePower
      endpointIdentitySourceTauCordobaFixedCoefficient_ne_top
      habsorbEta hD.delta_pos habsorbSmall
  have hdensity :
      ambientFamilyVolumeDensity E.family.bodyFamily unitBallBody <=
        commonPointTubePackingConstant *
          (delta : ENNReal) ^ (-2 : Real) :=
    ambientFamilyVolumeDensity_le_commonPointPacking
      E (fullRefinementDatum_isAdmissible hD) hgeometric
  have hratio := identityRadiusKatzTaoVolumeRatio_self hD.delta_pos
  unfold identitySourceFrostmanKatzTaoConstant
  rw [hratio]
  calc
    (16 * ((delta : ENNReal) ^ (-outputEta) *
          ambientFamilyVolumeDensity E.family.bodyFamily unitBallBody)) *
        (certifiedPlankThresholdedAngleScaleCap 576 *
          (2304 : ENNReal) ^ 3) <=
      endpointIdentitySourceTauCordobaFixedCoefficient *
        ((delta : ENNReal) ^ (-outputEta) *
          (delta : ENNReal) ^ (-2 : Real)) := by
            unfold endpointIdentitySourceTauCordobaFixedCoefficient
            calc
              (16 * ((delta : ENNReal) ^ (-outputEta) *
                    ambientFamilyVolumeDensity E.family.bodyFamily
                      unitBallBody)) *
                  (certifiedPlankThresholdedAngleScaleCap 576 *
                    (2304 : ENNReal) ^ 3) <=
                (16 * ((delta : ENNReal) ^ (-outputEta) *
                    (commonPointTubePackingConstant *
                      (delta : ENNReal) ^ (-2 : Real)))) *
                  (certifiedPlankThresholdedAngleScaleCap 576 *
                    (2304 : ENNReal) ^ 3) := by
                      exact mul_le_mul'
                        (mul_le_mul' le_rfl
                          (mul_le_mul' le_rfl hdensity)) le_rfl
              _ = ((16 * commonPointTubePackingConstant) *
                    (certifiedPlankThresholdedAngleScaleCap 576 *
                      (2304 : ENNReal) ^ 3)) *
                  ((delta : ENNReal) ^ (-outputEta) *
                    (delta : ENNReal) ^ (-2 : Real)) := by ac_rfl
    _ <= (delta : ENNReal) ^ (-absorbEta) *
        ((delta : ENNReal) ^ (-outputEta) *
          (delta : ENNReal) ^ (-2 : Real)) :=
      mul_le_mul' hconstant le_rfl
    _ = (delta : ENNReal) ^ (-(outputEta + 2 + absorbEta)) := by
      rw [<- ENNReal.rpow_add (-outputEta) (-2 : Real) hd0 hdTop,
        <- ENNReal.rpow_add (-absorbEta)
          (-outputEta + (-2 : Real)) hd0 hdTop]
      congr 1
      ring

/-- The exact endpoint identity source-to-`tau` coefficient is simultaneously
the native coefficient on the literal `tauScaleCover` active-coarse family
and bounded by the one-reserve power envelope above. -/
theorem endpointIdentity_sourceTau_concreteKT_and_cordobaFixed_le_power
    {epsilon0 beta gamma : Real}
    (D : ActualTubeDatum delta index) (hD : D.IsAdmissible)
    (P : ParameterLadder epsilon0 beta gamma)
    (W : NormalizedLongIntervalCoreWitness
      (fullRefinementDatum D).family
      (identityRadiusCoherentCover (fullRefinementDatum D).family)
      P.N P.epsilon P.eta
      (endpointScaleSequence delta
        (hD.delta_le_half.trans (by norm_num))))
    {outputEta absorbEta : Real}
    (hF : FrostmanHypotheses D outputEta)
    (habsorbEta : 0 < absorbEta)
    (hsmall : delta <=
      endpointIdentitySourceTauCordobaPowerThreshold absorbEta) :
    let E := fullRefinementDatum D
    let C := identityRadiusCoherentCover E.family
    let Sseq := endpointScaleSequence delta
      (hD.delta_le_half.trans (by norm_num))
    let S := tauScaleCover E C Sseq W
    let KT := identitySourceFrostmanKatzTaoConstant D
      (Sseq.tau W.m) outputEta
    IsKatzTao KT S.activeCoarseFamily /\
      KT * (certifiedPlankThresholdedAngleScaleCap 576 *
        (2304 : ENNReal) ^ 3) <=
        (delta : ENNReal) ^ (-(outputEta + 2 + absorbEta)) := by
  dsimp only
  let E := fullRefinementDatum D
  let C := identityRadiusCoherentCover E.family
  let Sseq := endpointScaleSequence delta
    (hD.delta_le_half.trans (by norm_num))
  have htau : Sseq.tau W.m = delta :=
    endpointLongCore_tau_eq_delta
      (hD.delta_le_half.trans (by norm_num)) C W
  have hcoverKT :=
    identityRadiusScaleCover_isKatzTaoAtScale_of_sourceFrostman
      D hD (Sseq.tau W.m) (Sseq.delta_le_tau W.m)
        (by simpa only [htau] using hD.delta_le_half) hF
  have hcoverEq : tauScaleCover E C Sseq W =
      identityRadiusScaleCover E.family (Sseq.tau W.m)
        (Sseq.delta_le_tau W.m) := by
    rfl
  constructor
  · change IsKatzTao
      (identitySourceFrostmanKatzTaoConstant D (Sseq.tau W.m) outputEta)
      (tauScaleCover E C Sseq W).activeCoarseFamily
    apply isKatzTao_iff_concentration_le.mpr
    intro K
    rw [hcoverEq]
    exact hcoverKT K
  · rw [htau]
    exact
      identitySourceFrostmanKatzTaoConstant_delta_mul_cordobaFixed_le_power
        D hD habsorbEta hsmall

/-! ## Stronger automatic common-point coefficient -/

/-- The concrete source-to-`tau` coefficient obtained without a Frostman
loss: common-point packing on the source, followed by the literal identity
radius transport. -/
def endpointIdentitySourceTauPackingKatzTaoConstant
    (delta rho : NNReal) : ENNReal :=
  identityRadiusKatzTaoVolumeRatio delta rho *
    (commonPointTubePackingConstant *
      (delta : ENNReal) ^ (-2 : Real))

/-- After multiplication by the unchanged fixed Cordoba/John factor, the
automatic packing coefficient costs only exponent two and one absorption
reserve.  In particular it pays no `outputEta` loss. -/
theorem endpointIdentitySourceTauPackingKatzTaoConstant_self_mul_fixed_le_power
    (hdelta : 0 < delta) {absorbEta : Real}
    (habsorbEta : 0 < absorbEta)
    (hsmall : delta <=
      endpointIdentitySourceTauCordobaPowerThreshold absorbEta) :
    endpointIdentitySourceTauPackingKatzTaoConstant delta delta *
        (certifiedPlankThresholdedAngleScaleCap 576 *
          (2304 : ENNReal) ^ 3) <=
      (delta : ENNReal) ^ (-(2 + absorbEta)) := by
  have hd0 : (delta : ENNReal) ≠ 0 :=
    ENNReal.coe_ne_zero.mpr hdelta.ne'
  have hdTop : (delta : ENNReal) ≠ ∞ := ENNReal.coe_ne_top
  have habsorbSmall : delta <=
      finiteConstantSmallDeltaThreshold
        endpointIdentitySourceTauCordobaFixedCoefficient absorbEta :=
    hsmall.trans (min_le_right _ _)
  have hconstant : endpointIdentitySourceTauCordobaFixedCoefficient <=
      (delta : ENNReal) ^ (-absorbEta) :=
    finiteConstant_le_delta_negativePower
      endpointIdentitySourceTauCordobaFixedCoefficient_ne_top
      habsorbEta hdelta habsorbSmall
  rw [endpointIdentitySourceTauPackingKatzTaoConstant,
    identityRadiusKatzTaoVolumeRatio_self hdelta]
  calc
    (16 * (commonPointTubePackingConstant *
          (delta : ENNReal) ^ (-2 : Real))) *
        (certifiedPlankThresholdedAngleScaleCap 576 *
          (2304 : ENNReal) ^ 3) =
      endpointIdentitySourceTauCordobaFixedCoefficient *
        (delta : ENNReal) ^ (-2 : Real) := by
          unfold endpointIdentitySourceTauCordobaFixedCoefficient
          ac_rfl
    _ <= (delta : ENNReal) ^ (-absorbEta) *
        (delta : ENNReal) ^ (-2 : Real) :=
      mul_le_mul' hconstant le_rfl
    _ = (delta : ENNReal) ^ (-(2 + absorbEta)) := by
      rw [<- ENNReal.rpow_add (-absorbEta) (-2 : Real) hd0 hdTop]
      congr 1
      ring

/-- Callback-free automatic endpoint bundle for the direct same-occurrence
consumer.  Geometry and the source-average identity are both constructed by
their exact endpoint theorems.  The same concrete `KT` is certified on the
literal `tauScaleCover` active-coarse family and receives the strongest
available exponent-two power envelope. -/
theorem endpointIdentity_directSameOccurrenceAutomaticInputs
    {epsilon0 beta gamma : Real}
    (D : ActualTubeDatum delta index) (hD : D.IsAdmissible)
    (P : ParameterLadder epsilon0 beta gamma)
    (W : NormalizedLongIntervalCoreWitness
      (fullRefinementDatum D).family
      (identityRadiusCoherentCover (fullRefinementDatum D).family)
      P.N P.epsilon P.eta
      (endpointScaleSequence delta
        (hD.delta_le_half.trans (by norm_num))))
    {absorbEta : Real}
    (habsorbEta : 0 < absorbEta)
    (hsmall : delta <=
      endpointIdentitySourceTauCordobaPowerThreshold absorbEta) :
    let E := fullRefinementDatum D
    let C := identityRadiusCoherentCover E.family
    let Sseq := endpointScaleSequence delta
      (hD.delta_le_half.trans (by norm_num))
    let S := tauScaleCover E C Sseq W
    let KT := endpointIdentitySourceTauPackingKatzTaoConstant
      delta (Sseq.tau W.m)
    TauActiveCoarseAdmissibility E C Sseq W /\
      (tauActiveCoarseDatum E C Sseq W).shading.averageMultiplicity =
        D.shading.averageMultiplicity /\
      IsKatzTao KT S.activeCoarseFamily /\
      KT * (certifiedPlankThresholdedAngleScaleCap 576 *
        (2304 : ENNReal) ^ 3) <=
        (delta : ENNReal) ^ (-(2 + absorbEta)) := by
  dsimp only
  let E := fullRefinementDatum D
  let C := identityRadiusCoherentCover E.family
  let Sseq := endpointScaleSequence delta
    (hD.delta_le_half.trans (by norm_num))
  have htau : Sseq.tau W.m = delta :=
    endpointLongCore_tau_eq_delta
      (hD.delta_le_half.trans (by norm_num)) C W
  have hgeometry :=
    endpointIdentity_tauActiveCoarseAdmissibility D hD P W
  have havg := endpointLongCore_tauActive_averageMultiplicity_eq_source
    D hD P W
  have hsourceKT : IsKatzTao
      (commonPointTubePackingConstant *
        (delta : ENNReal) ^ (-2 : Real)) E.family.bodyFamily := by
    exact isKatzTao_commonPointTubePacking_rpow E
      (fullRefinementDatum_isAdmissible hD)
      (hsmall.trans (min_le_left _ _))
  have hcoverKT :=
    identityRadiusScaleCover_isKatzTaoAtScale_of_sourceKatzTao
      E.family (Sseq.tau W.m) (Sseq.delta_le_tau W.m)
        hD.delta_pos hD.delta_le_half
        (by simpa only [htau] using hD.delta_le_half) hsourceKT
  have hcoverEq : tauScaleCover E C Sseq W =
      identityRadiusScaleCover E.family (Sseq.tau W.m)
        (Sseq.delta_le_tau W.m) := by
    rfl
  refine ⟨hgeometry, havg, ?_, ?_⟩
  · change IsKatzTao
      (endpointIdentitySourceTauPackingKatzTaoConstant
        delta (Sseq.tau W.m))
      (tauScaleCover E C Sseq W).activeCoarseFamily
    apply isKatzTao_iff_concentration_le.mpr
    intro K
    rw [hcoverEq]
    exact hcoverKT K
  · rw [htau]
    exact
      endpointIdentitySourceTauPackingKatzTaoConstant_self_mul_fixed_le_power
        hD.delta_pos habsorbEta hsmall

/-- Exact scalar residual for the strongest automatic coefficient.  The
premise mentions the already chosen `a`, `b`, and tube count, so it remains a
local residual rather than a global fixed-envelope hypothesis. -/
theorem endpointIdentitySourceTauPackingKatzTaoConstant_fixedResidual_of_power
    (hdelta : 0 < delta) {outputEta absorbEta epsilon beta : Real}
    (habsorbEta : 0 < absorbEta)
    (hsmall : delta <=
      endpointIdentitySourceTauCordobaPowerThreshold absorbEta)
    (rho a b : NNReal) (tubesPerPlank : Nat)
    (hpower :
      (delta : ENNReal) ^ (-(2 + absorbEta)) <=
        (delta : ENNReal) ^ (2 * outputEta) *
          proposition66AInnerFactor rho a b tubesPerPlank epsilon beta) :
    endpointIdentitySourceTauPackingKatzTaoConstant delta delta *
        (certifiedPlankThresholdedAngleScaleCap 576 *
          (2304 : ENNReal) ^ 3) <=
      (delta : ENNReal) ^ (2 * outputEta) *
        proposition66AInnerFactor rho a b tubesPerPlank epsilon beta :=
  (endpointIdentitySourceTauPackingKatzTaoConstant_self_mul_fixed_le_power
    hdelta habsorbEta hsmall).trans hpower

/-- Actual same-object consumer after the occurrence, block, zero-extended
shading, and side label have already been selected.  Its scalar premise is
local to that exact label and tube count.  The theorem invokes the exact
carrier-floor consumer unchanged; it neither reselects nor asserts a fixed
envelope for any other bucket. -/
theorem sameScale_packingKT_sourceDensity_mul_thresholdedCordobaScale_le_prop66AInner_of_localPower
    (D : ActualTubeDatum delta index) (hD : D.IsAdmissible)
    (S : StickyScaleCover (fullRefinementDatum D).family delta)
    (P : GreedyDensityPartition S.activeCoarseFamily
      (hullCandidates (Finset.univ : Finset (ActiveParentIndex S)))
      (hullContainer S.activeCoarseFamily) Finset.univ)
    (k : Fin (blocks S.activeCoarseFamily P).length)
    (sourceDensity loss : ENNReal)
    (r : NNReal) (hr : 0 < r) (label : Fin 3 -> Int)
    (Z : Shading (selectedCoarseFamily S.activeCoarseFamily
      (blockAt S.activeCoarseFamily P k).fiber))
    (tubesPerPlank : Nat)
    {outputEta absorbEta epsilon beta : Real}
    (habsorbEta : 0 < absorbEta)
    (hsmall : delta <=
      endpointIdentitySourceTauCordobaPowerThreshold absorbEta)
    (hfloor :
      let B := (blockAt S.activeCoarseFamily P k).fiber
      let e := contractedJohnAffineEquiv
        (selectedParentGreedyBlockJohnFrame S hD.delta_pos P k) r hr
      let Ybucket := selectedParentArbitraryPlankBucketShading
        e S B hD.delta_pos label Z
      affineJacobian (bucketNormalizedAffineEquiv e label) *
          (sourceDensity * ((delta : ENNReal) ^ 2 / 2)) <=
        loss * quantitativeCarrierFloor Ybucket)
    (hpower :
      (delta : ENNReal) ^ (-(2 + absorbEta)) <=
        (delta : ENNReal) ^ (2 * outputEta) *
          proposition66AInnerFactor delta
            (bucketShortA label) (bucketShortB label)
            tubesPerPlank epsilon beta) :
    let B := (blockAt S.activeCoarseFamily P k).fiber
    let e := contractedJohnAffineEquiv
      (selectedParentGreedyBlockJohnFrame S hD.delta_pos P k) r hr
    let Ybucket := selectedParentArbitraryPlankBucketShading
      e S B hD.delta_pos label Z
    (affineJacobian (bucketNormalizedAffineEquiv e label) *
        (sourceDensity * ((delta : ENNReal) ^ 2 / 2))) *
        (endpointIdentitySourceTauPackingKatzTaoConstant delta delta *
          (certifiedPlankThresholdedAngleScaleCap 576 *
            (((((sideShapeUpper label 2)⁻¹ * r : NNReal) : ENNReal) ^ 3) /
              quantitativeCarrierFloor Ybucket))) <=
      loss *
        (affineJacobian (bucketNormalizedAffineEquiv e label) *
          ((delta : ENNReal) ^ (2 * outputEta) *
            proposition66AInnerFactor delta
              (bucketShortA label) (bucketShortB label)
              tubesPerPlank epsilon beta)) := by
  apply
    sourceDensity_mul_thresholdedCordobaScale_le_prop66AInner_of_fixedResidual
      (fine := (fullRefinementDatum D).family)
      (rho := delta)
      (by
        intro i
        exact hD.contained_in_unit_ball i)
      S hD.delta_pos (hD.delta_le_half.trans (by norm_num)) P k
      sourceDensity loss
      (endpointIdentitySourceTauPackingKatzTaoConstant delta delta)
      ((delta : ENNReal) ^ (2 * outputEta))
      r hr label Z tubesPerPlank epsilon beta hfloor
  exact
    endpointIdentitySourceTauPackingKatzTaoConstant_fixedResidual_of_power
      hD.delta_pos habsorbEta hsmall delta
      (bucketShortA label) (bucketShortB label) tubesPerPlank hpower

/-- Pure scalar handoff to the unchanged Proposition 6.6(A) inner factor.
The source power is the literal Frostman floor power `delta^(2*outputEta)`
used by the existing source-cap cancellation.  No selected object occurs in
the premise, and no stronger inner-factor target is requested. -/
theorem identitySourceFrostmanKatzTaoConstant_delta_fixedResidual_of_power
    (D : ActualTubeDatum delta index) (hD : D.IsAdmissible)
    {outputEta absorbEta epsilon beta : Real}
    (habsorbEta : 0 < absorbEta)
    (hsmall : delta <=
      endpointIdentitySourceTauCordobaPowerThreshold absorbEta)
    (rho a b : NNReal) (tubesPerPlank : Nat)
    (hpower :
      (delta : ENNReal) ^ (-(outputEta + 2 + absorbEta)) <=
        (delta : ENNReal) ^ (2 * outputEta) *
          proposition66AInnerFactor rho a b tubesPerPlank epsilon beta) :
    identitySourceFrostmanKatzTaoConstant D delta outputEta *
        (certifiedPlankThresholdedAngleScaleCap 576 *
          (2304 : ENNReal) ^ 3) <=
      (delta : ENNReal) ^ (2 * outputEta) *
        proposition66AInnerFactor rho a b tubesPerPlank epsilon beta :=
  (identitySourceFrostmanKatzTaoConstant_delta_mul_cordobaFixed_le_power
    D hD habsorbEta hsmall).trans hpower

#print axioms endpointIdentitySourceTauCordobaFixedCoefficient_ne_top
#print axioms endpointIdentitySourceTauCordobaPowerThreshold_pos
#print axioms
  identitySourceFrostmanKatzTaoConstant_delta_mul_cordobaFixed_le_power
#print axioms endpointIdentity_sourceTau_concreteKT_and_cordobaFixed_le_power
#print axioms
  identitySourceFrostmanKatzTaoConstant_delta_fixedResidual_of_power
#print axioms identityRadiusKatzTaoVolumeRatio_self
#print axioms
  endpointIdentitySourceTauPackingKatzTaoConstant_self_mul_fixed_le_power
#print axioms endpointIdentity_directSameOccurrenceAutomaticInputs
#print axioms
  endpointIdentitySourceTauPackingKatzTaoConstant_fixedResidual_of_power
#print axioms
  sameScale_packingKT_sourceDensity_mul_thresholdedCordobaScale_le_prop66AInner_of_localPower

end
end Family8EndpointIdentitySourceTauSameOccurrenceProp66APowerBudgetV1
