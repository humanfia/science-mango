import Family8Grounding.Family8EndpointIdentitySourceTauSameOccurrenceProp66APowerBudgetV1
import Family8Grounding.Family8SelectedParentAdaptiveInnerSourceReserveV1
import Mathlib.Tactic

/-!
# Endpoint identity high-gamma reserve for the Proposition 6.6(A) inner factor

The automatic endpoint coefficient is literally

`16 * commonPointTubePackingConstant * delta^(-2)`.

Consequently its power `1 - gamma / 2` retains the exact geometric reserve
`delta^(-(2 - gamma))` whenever `gamma <= 2`.  Combining this with the
same selected bucket's scale/aspect reserve closes the local scalar premise
used by the direct same-occurrence Proposition 6.6(A) consumer.  No
low-`gamma` sign hypothesis is used, and `gamma` is passed unchanged as the
Proposition 6.6(A) exponent.
-/

open Set MeasureTheory
open scoped BigOperators ENNReal NNReal

namespace Family8EndpointIdentitySourceTauHighGammaInnerReserveV1

open LeanEval.Analysis.WangZahlKakeya
open Submission.Kakeya.ConvexGeometry
open Submission.Kakeya.ConvexFactoring
open Submission.Kakeya.ConvexFactoring.FullConvexMaximalDensity
open Submission.Kakeya.ConvexFactoring.GreedyOccurrenceFactorization
open Submission.Kakeya.Uniformity
open Family8CommonPointTubePackingV1
open Family8EndpointIdentitySourceTauSameOccurrenceProp66APowerBudgetV1
open Family8Prop66AOuterInnerProductAlgebraV1
open Family8SelectedParentAdaptiveInnerSourceReserveV1
open Family8SelectedParentCertifiedPlankCordobaConnectorV3
open Family8SelectedParentJohnFrameNormalizationV9
open Family8SelectedParentJohnPlankSideWidthBridgeV5
open Family8SelectedParentJohnPlankSideWidthBridgeV7
open Family8SelectedParentPlankCenteredAdaptiveThinCountGlobalEq46CountV2
open Family8SelectedParentPlankCenteredAdaptiveThinCountGlobalMassPopularEndpointV3
open Family8SelectedParentPlankCenteredHalfPostAdaptiveScalePackingV1
open Family8StickySelectedParentGreedyBlockFrostmanV3
open FamilyStickyAtEveryScaleCoreV1
open FamilyStickyCinematicL32FiniteWeightedBucketV1

noncomputable section

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 5000000

variable {delta : NNReal} {index : Type}
  [Fintype index] [DecidableEq index]
  {fine : UniformTubeFamily delta index}

/-- At the unchanged endpoint radius, the concrete automatic Katz--Tao
coefficient contains at least the full geometric `delta^(-2)` factor. -/
theorem delta_negativeTwo_le_endpointIdentitySourceTauPackingKatzTaoConstant_self
    (hdelta : 0 < delta) :
    (delta : ENNReal) ^ (-2 : Real) <=
      endpointIdentitySourceTauPackingKatzTaoConstant delta delta := by
  have hconstant : (1 : ENNReal) <=
      16 * commonPointTubePackingConstant := by
    norm_num [commonPointTubePackingConstant, commonPointPositionCodeLoss]
  rw [endpointIdentitySourceTauPackingKatzTaoConstant,
    identityRadiusKatzTaoVolumeRatio_self hdelta]
  calc
    (delta : ENNReal) ^ (-2 : Real) =
        1 * (delta : ENNReal) ^ (-2 : Real) := by simp
    _ <= (16 * commonPointTubePackingConstant) *
        (delta : ENNReal) ^ (-2 : Real) :=
      mul_le_mul' hconstant le_rfl
    _ = 16 * (commonPointTubePackingConstant *
        (delta : ENNReal) ^ (-2 : Real)) := by ac_rfl

/-- Raising the exact endpoint packing coefficient to the actual
Proposition 6.6(A) exponent retains `delta^(-(2-gamma))`.  This only uses
the natural upper bound `gamma <= 2`; in particular it is valid on the high
branch where the older `gamma <= 2/3` scale lemmas do not apply. -/
theorem delta_negative_two_sub_gamma_le_endpointPacking_one_sub_gamma_half
    (hdelta : 0 < delta) {gamma : Real} (hgammaTwo : gamma <= 2) :
    (delta : ENNReal) ^ (-(2 - gamma)) <=
      (endpointIdentitySourceTauPackingKatzTaoConstant delta delta) ^
        (1 - gamma / 2) := by
  have hp : 0 <= 1 - gamma / 2 := by linarith
  have hbase :=
    delta_negativeTwo_le_endpointIdentitySourceTauPackingKatzTaoConstant_self
      (delta := delta) hdelta
  calc
    (delta : ENNReal) ^ (-(2 - gamma)) =
        (delta : ENNReal) ^ ((-2 : Real) * (1 - gamma / 2)) := by
      congr 1
      ring
    _ = ((delta : ENNReal) ^ (-2 : Real)) ^ (1 - gamma / 2) :=
      ENNReal.rpow_mul (delta : ENNReal) (-2 : Real) (1 - gamma / 2)
    _ <= (endpointIdentitySourceTauPackingKatzTaoConstant delta delta) ^
        (1 - gamma / 2) := ENNReal.rpow_le_rpow hbase hp

/-- The weakest local high-branch seam furnished by the current adaptive
cap.  It stays on the exact selected bucket and uses `gamma` itself as the
Proposition 6.6(A) exponent.  The sole geometric premise asks for the
remaining scale/aspect reserve; the concrete endpoint coefficient supplies
the complementary `2-gamma` power automatically. -/
theorem sameBucket_localScaleReserve_implies_prop66AInner_fixedResidual
    (S : StickyScaleCover fine delta)
    (P : GreedyDensityPartition S.activeCoarseFamily
      (hullCandidates (Finset.univ : Finset (ActiveParentIndex S)))
      (hullContainer S.activeCoarseFamily) Finset.univ)
    (k : Fin (blocks S.activeCoarseFamily P).length)
    (r : NNReal) (hr : 0 < r) (label : Fin 3 -> Int)
    (hdelta : 0 < delta)
    (hoccupied : SelectedBucketOccupied S hdelta P k r hr label)
    (hdeltaHalf : delta <= (2 : NNReal)⁻¹)
    (hsmallPacking : selectedParentCenteredHalfPostAdaptiveProxyScale
      delta delta r label / 8 <= (1 / 100 : NNReal))
    {outputEta absorbEta innerEpsilon gamma : Real}
    (hgammaTwo : gamma <= 2)
    (hscaleReserve :
      (delta : ENNReal) ^ (-(gamma + absorbEta + 2 * outputEta)) <=
        (delta : ENNReal) ^ (-innerEpsilon / 2) *
          ((bucketShortB label : ENNReal) /
            (bucketShortA label : ENNReal)) *
          (((delta : ENNReal) / (bucketShortA label : ENNReal)) ^
            (2 - 3 * gamma))) :
    (delta : ENNReal) ^ (-(2 + absorbEta)) <=
      (delta : ENNReal) ^ (2 * outputEta) *
        proposition66AInnerFactor delta
          (bucketShortA label) (bucketShortB label)
          (centeredAdaptiveActualBucketFullFiberNatCap
            S hdelta P k r hr label
              (endpointIdentitySourceTauPackingKatzTaoConstant delta delta))
          innerEpsilon gamma := by
  let C := endpointIdentitySourceTauPackingKatzTaoConstant delta delta
  let R : ENNReal :=
    (delta : ENNReal) ^ (-innerEpsilon / 2) *
      ((bucketShortB label : ENNReal) /
        (bucketShortA label : ENNReal)) *
      (((delta : ENNReal) / (bucketShortA label : ENNReal)) ^
        (2 - 3 * gamma))
  let inner : ENNReal := proposition66AInnerFactor delta
    (bucketShortA label) (bucketShortB label)
    (centeredAdaptiveActualBucketFullFiberNatCap
      S hdelta P k r hr label C) innerEpsilon gamma
  have hd0 : (delta : ENNReal) ≠ 0 :=
    ENNReal.coe_ne_zero.mpr hdelta.ne'
  have hdTop : (delta : ENNReal) ≠ ∞ := ENNReal.coe_ne_top
  have hCfinite : C ≠ ∞ := by
    dsimp only [C]
    rw [endpointIdentitySourceTauPackingKatzTaoConstant,
      identityRadiusKatzTaoVolumeRatio_self hdelta]
    exact ENNReal.mul_ne_top (by norm_num)
      (ENNReal.mul_ne_top commonPointTubePackingConstant_ne_top
        (ENNReal.rpow_ne_top_of_ne_zero hd0 hdTop))
  have hcoefficient :
      (delta : ENNReal) ^ (-(2 - gamma)) <= C ^ (1 - gamma / 2) := by
    simpa only [C] using
      delta_negative_two_sub_gamma_le_endpointPacking_one_sub_gamma_half
        (delta := delta) hdelta hgammaTwo
  have hinner : R * C ^ (1 - gamma / 2) <= inner := by
    simpa only [C, R, inner] using
      selectedParent_sourceScaleReserve_le_adaptiveActualInnerFactor
        S hdelta P k r hr label hoccupied hdelta hdeltaHalf hsmallPacking
          C hCfinite innerEpsilon gamma hgammaTwo
  have hscale :
      (delta : ENNReal) ^ (-(gamma + absorbEta + 2 * outputEta)) <= R := by
    simpa only [R] using hscaleReserve
  have hinnerPower :
      (delta : ENNReal) ^ (-(2 + absorbEta + 2 * outputEta)) <= inner := by
    calc
      (delta : ENNReal) ^ (-(2 + absorbEta + 2 * outputEta)) =
          (delta : ENNReal) ^
              (-(gamma + absorbEta + 2 * outputEta)) *
            (delta : ENNReal) ^ (-(2 - gamma)) := by
        rw [← ENNReal.rpow_add _ _ hd0 hdTop]
        congr 1
        ring
      _ <= R * C ^ (1 - gamma / 2) :=
        mul_le_mul' hscale hcoefficient
      _ <= inner := hinner
  calc
    (delta : ENNReal) ^ (-(2 + absorbEta)) =
        (delta : ENNReal) ^ (2 * outputEta) *
          (delta : ENNReal) ^ (-(2 + absorbEta + 2 * outputEta)) := by
      rw [← ENNReal.rpow_add _ _ hd0 hdTop]
      congr 1
      ring
    _ <= (delta : ENNReal) ^ (2 * outputEta) * inner :=
      mul_le_mul' le_rfl hinnerPower
    _ = (delta : ENNReal) ^ (2 * outputEta) *
        proposition66AInnerFactor delta
          (bucketShortA label) (bucketShortB label)
          (centeredAdaptiveActualBucketFullFiberNatCap
            S hdelta P k r hr label
              (endpointIdentitySourceTauPackingKatzTaoConstant delta delta))
          innerEpsilon gamma := rfl

#print axioms
  delta_negativeTwo_le_endpointIdentitySourceTauPackingKatzTaoConstant_self
#print axioms
  delta_negative_two_sub_gamma_le_endpointPacking_one_sub_gamma_half
#print axioms
  sameBucket_localScaleReserve_implies_prop66AInner_fixedResidual

end
end Family8EndpointIdentitySourceTauHighGammaInnerReserveV1
