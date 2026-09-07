import Family8Grounding.Family8SelectedParentJohnPlankQuantitativeLossV10
import Family8Grounding.Family8SelectedParentMassPopularCoreJacobianCancellationV2
import Mathlib.Tactic

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 5000000

open Set MeasureTheory
open scoped ENNReal NNReal BigOperators

namespace Family8SelectedParentMassPopularFixedEnvelopeLogAbsorptionCoreV3

open LeanEval.Analysis.WangZahlKakeya
open Submission.Kakeya.ConvexGeometry
open Submission.Kakeya.ConvexFactoring
open Submission.Kakeya.ConvexFactoring.FactoringMultiplicityAssembly
open Submission.Kakeya.ConvexFactoring.FullConvexMaximalDensity
open Submission.Kakeya.ConvexFactoring.GreedyOccurrenceFactorization
open Submission.Kakeya.ConvexFactoring.HeavyParentSelection
open Submission.Kakeya.Uniformity
open Family6AffineConvexVolumeCoreV1
open Family8KatzTaoFrostmanPropertiesV1
open Family8Prop66AOuterInnerProductAlgebraV1
open Family8SelectedParentAffineShadingTransportV4
open Family8SelectedParentBucketContainerJacobianEnvelopeV3
open Family8SelectedParentCertifiedPlankCordobaActualJohnContainerV7
open Family8SelectedParentCertifiedPlankCordobaConnectorV3
open Family8SelectedParentGreedyBlockFiberIdentityV2
open Family8SelectedParentJohnFrameNormalizationV9
open Family8SelectedParentJohnPlankQuantitativeLossV9
open Family8SelectedParentJohnPlankQuantitativeLossV10
open Family8SelectedParentJohnPlankSideWidthBridgeV5
open Family8SelectedParentJohnPlankSideWidthBridgeV7
open Family8SelectedParentJohnPlankSideWidthBridgeV8
open Family8SelectedParentMassPopularCordobaCoreV2
open Family8SelectedParentMassPopularCoreJacobianCancellationV2
open Family8StickySelectedParentGreedyBlockFrostmanV3
open FamilyStickyAtEveryScaleCoreV1
open FamilyStickyCinematicL32FiniteWeightedBucketV1
open FamilyStickyHierarchyEndpointPrefixShadingTransportV1.StickyScaleCover

noncomputable section

/-!
# Removing the selected-parent side logarithm from the Equation (46) envelope

V1/CoreV1 and CoreV2 are failed drafts and intentionally not imported.  This
successor absorbs precisely the literal `sideLog * 2 * 2304^3`, leaving all
data-dependent counts visible.
-/

variable {delta rho : NNReal} {index : Type}
  [Fintype index] [DecidableEq index]

theorem selectedParentMassPopularCordobaFixedEnvelope_le_rpow_residual
    (D : ActualTubeDatum delta index)
    (S : StickyScaleCover D.family rho) (hrho : 0 < rho)
    (P : GreedyDensityPartition S.activeCoarseFamily
      (hullCandidates (Finset.univ : Finset (ActiveParentIndex S)))
      (hullContainer S.activeCoarseFamily) Finset.univ)
    (k : Fin (blocks S.activeCoarseFamily P).length)
    (r : NNReal) (hr : 0 < r) {loss : Nat}
    (A : FactoringMultiplicityAssembly.ExactAssembly
      (greedyParentFactorization S P)
      (parentAggregatedShading S D.shading) loss)
    (label : Fin 3 -> Int) (KT : ENNReal)
    {absorbEta : Real} (habsorbEta : 0 < absorbEta)
    (hrhoThreshold :
      rho ≤ selectedParentLogarithmicSideBucketAbsorptionThreshold
        ((2 : ENNReal) * (2304 : ENNReal) ^ 3) absorbEta) :
    selectedParentMassPopularCordobaFixedEnvelope
        D S hrho P k r hr A label KT ≤
      (rho : ENNReal) ^ (-absorbEta) *
        ((loss : ENNReal) * (P.length : ENNReal) *
          (selectedParentPlankBucketIndices
            (contractedJohnAffineEquiv
              (selectedParentGreedyBlockJohnFrame S hrho P k) r hr)
            S (blockAt S.activeCoarseFamily P k).fiber hrho label).card * KT) := by
  let e := contractedJohnAffineEquiv
    (selectedParentGreedyBlockJohnFrame S hrho P k) r hr
  let B := (blockAt S.activeCoarseFamily P k).fiber
  let residual : ENNReal :=
    (loss : ENNReal) * (P.length : ENNReal) *
      (selectedParentPlankBucketIndices e S B hrho label).card * KT
  have hfinite :
      ((2 : ENNReal) * (2304 : ENNReal) ^ 3) ≠ ∞ :=
    ENNReal.mul_ne_top ENNReal.coe_ne_top
      (ENNReal.pow_ne_top ENNReal.coe_ne_top)
  have hlog :
      ((2 : ENNReal) * (2304 : ENNReal) ^ 3) *
          (selectedParentLogarithmicSideBucketLoss rho : ENNReal) ≤
        (rho : ENNReal) ^ (-absorbEta) := by
    exact fixedConstant_mul_selectedParentLogarithmicSideBucketLoss_le_rpow
      (rho := rho)
      (fixedConstant := (2 : ENNReal) * (2304 : ENNReal) ^ 3)
      (lossEta := absorbEta) hfinite habsorbEta hrho hrhoThreshold
  change
    ((loss : ENNReal) * (P.length : ENNReal) *
        (selectedParentLogarithmicSideBucketLoss rho : ENNReal)) *
      (((selectedParentPlankBucketIndices e S B hrho label).card : ENNReal) * 2) *
        (KT * (2304 : ENNReal) ^ 3) ≤
      (rho : ENNReal) ^ (-absorbEta) * residual
  calc
    ((loss : ENNReal) * (P.length : ENNReal) *
        (selectedParentLogarithmicSideBucketLoss rho : ENNReal)) *
      (((selectedParentPlankBucketIndices e S B hrho label).card : ENNReal) * 2) *
        (KT * (2304 : ENNReal) ^ 3) =
      residual *
        (((2 : ENNReal) * (2304 : ENNReal) ^ 3) *
          (selectedParentLogarithmicSideBucketLoss rho : ENNReal)) := by
            dsimp only [residual]
            ac_rfl
    _ ≤ residual * (rho : ENNReal) ^ (-absorbEta) :=
      mul_le_mul' le_rfl hlog
    _ = (rho : ENNReal) ^ (-absorbEta) * residual := by ac_rfl

#print axioms selectedParentMassPopularCordobaFixedEnvelope_le_rpow_residual

end
end Family8SelectedParentMassPopularFixedEnvelopeLogAbsorptionCoreV3
