import Family8Grounding.Family8SelectedParentMassPopularFixedEnvelopeLogAbsorptionCoreV3
import Mathlib.Tactic

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 5000000

open Set MeasureTheory
open scoped ENNReal NNReal BigOperators

namespace Family8SelectedParentMassPopularFixedEnvelopeLogAbsorptionV2

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
open Family8SelectedParentMassPopularFixedEnvelopeLogAbsorptionCoreV3
open Family8StickySelectedParentGreedyBlockFrostmanV3
open FamilyStickyAtEveryScaleCoreV1
open FamilyStickyCinematicL32FiniteWeightedBucketV1
open FamilyStickyHierarchyEndpointPrefixShadingTransportV1.StickyScaleCover

noncomputable section

/-!
# Actual Equation (46) connector after fixed-log absorption

V1 is a failed draft and intentionally not imported.  This theorem applies
the audited container/Jacobian envelope and the CoreV3 logarithmic absorption
to the actual mass-popular Cordoba core in one step.
-/

variable {delta rho : NNReal} {index : Type}
  [Fintype index] [DecidableEq index]

theorem relativeScaled_massPopularCordobaCore_le_of_residualEnvelope
    (D : ActualTubeDatum delta index) (hD : D.IsAdmissible)
    (S : StickyScaleCover D.family rho) (hrho : 0 < rho)
    (hrhoOne : rho ≤ 1)
    (P : GreedyDensityPartition S.activeCoarseFamily
      (hullCandidates (Finset.univ : Finset (ActiveParentIndex S)))
      (hullContainer S.activeCoarseFamily) Finset.univ)
    (k : Fin (blocks S.activeCoarseFamily P).length)
    (r : NNReal) (hr : 0 < r) {loss : Nat}
    (A : FactoringMultiplicityAssembly.ExactAssembly
      (greedyParentFactorization S P)
      (parentAggregatedShading S D.shading) loss)
    (label : Fin 3 -> Int) (KT : ENNReal)
    (tubesPerPlank : Nat)
    {capBound relativeSquare sourcePower : ENNReal}
    {lossEta absorbEta epsilon beta : Real}
    (habsorbEta : 0 < absorbEta)
    (hrhoThreshold :
      rho ≤ selectedParentLogarithmicSideBucketAbsorptionThreshold
        ((2 : ENNReal) * (2304 : ENNReal) ^ 3) absorbEta)
    (hscalar :
      capBound *
          ((rho : ENNReal) ^ (-(lossEta + absorbEta)) *
            ((loss : ENNReal) * (P.length : ENNReal) *
              (selectedParentPlankBucketIndices
                (contractedJohnAffineEquiv
                  (selectedParentGreedyBlockJohnFrame S hrho P k) r hr)
                S (blockAt S.activeCoarseFamily P k).fiber hrho label).card *
              KT)) ≤
        relativeSquare *
          (sourcePower *
            proposition66AInnerFactor rho
              (bucketShortA label) (bucketShortB label)
              tubesPerPlank epsilon beta)) :
    capBound *
        ((rho : ENNReal) ^ (-lossEta) *
          selectedParentMassPopularCordobaCoreBudget
            D S hrho P k r hr A label KT) ≤
      relativeSquare *
        ((affineJacobian
            (bucketNormalizedAffineEquiv
              (contractedJohnAffineEquiv
                (selectedParentGreedyBlockJohnFrame S hrho P k) r hr)
              label) * sourcePower) *
          proposition66AInnerFactor rho
            (bucketShortA label) (bucketShortB label)
            tubesPerPlank epsilon beta) := by
  apply relativeScaled_massPopularCordobaCore_le_of_fixedEnvelope
    D hD S hrho hrhoOne P k r hr A label KT tubesPerPlank
  have hfixed :=
    selectedParentMassPopularCordobaFixedEnvelope_le_rpow_residual
      D S hrho P k r hr A label KT habsorbEta hrhoThreshold
  have hpow :
      (rho : ENNReal) ^ (-lossEta) * (rho : ENNReal) ^ (-absorbEta) =
        (rho : ENNReal) ^ (-(lossEta + absorbEta)) := by
    rw [← ENNReal.rpow_add _ _ (by exact_mod_cast hrho.ne') (by simp)]
    congr 1
    ring
  calc
    capBound * ((rho : ENNReal) ^ (-lossEta) *
        selectedParentMassPopularCordobaFixedEnvelope
          D S hrho P k r hr A label KT) ≤
      capBound * ((rho : ENNReal) ^ (-lossEta) *
        ((rho : ENNReal) ^ (-absorbEta) *
          ((loss : ENNReal) * (P.length : ENNReal) *
            (selectedParentPlankBucketIndices
              (contractedJohnAffineEquiv
                (selectedParentGreedyBlockJohnFrame S hrho P k) r hr)
              S (blockAt S.activeCoarseFamily P k).fiber hrho label).card *
            KT))) := by
              exact mul_le_mul' le_rfl (mul_le_mul' le_rfl hfixed)
    _ = capBound *
        (((rho : ENNReal) ^ (-lossEta) *
            (rho : ENNReal) ^ (-absorbEta)) *
          ((loss : ENNReal) * (P.length : ENNReal) *
            (selectedParentPlankBucketIndices
              (contractedJohnAffineEquiv
                (selectedParentGreedyBlockJohnFrame S hrho P k) r hr)
              S (blockAt S.activeCoarseFamily P k).fiber hrho label).card *
            KT)) := by ac_rfl
    _ = capBound *
        ((rho : ENNReal) ^ (-(lossEta + absorbEta)) *
          ((loss : ENNReal) * (P.length : ENNReal) *
            (selectedParentPlankBucketIndices
              (contractedJohnAffineEquiv
                (selectedParentGreedyBlockJohnFrame S hrho P k) r hr)
              S (blockAt S.activeCoarseFamily P k).fiber hrho label).card *
            KT)) := by rw [hpow]
    _ ≤ relativeSquare *
        (sourcePower * proposition66AInnerFactor rho
          (bucketShortA label) (bucketShortB label)
          tubesPerPlank epsilon beta) := hscalar

#print axioms relativeScaled_massPopularCordobaCore_le_of_residualEnvelope

end
end Family8SelectedParentMassPopularFixedEnvelopeLogAbsorptionV2
