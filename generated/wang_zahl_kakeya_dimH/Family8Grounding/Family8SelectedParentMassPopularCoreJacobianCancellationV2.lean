import Family8Grounding.Family8SelectedParentBucketContainerJacobianEnvelopeV3
import Family8Grounding.Family8SelectedParentMassPopularCordobaCoreV2
import Family8Grounding.Family8Prop66AOuterInnerProductAlgebraV1
import Mathlib.Tactic

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 5000000

open Set MeasureTheory
open scoped ENNReal NNReal BigOperators

namespace Family8SelectedParentMassPopularCoreJacobianCancellationV2

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
open Family8SelectedParentJohnPlankSideWidthBridgeV5
open Family8SelectedParentJohnPlankSideWidthBridgeV7
open Family8SelectedParentJohnPlankSideWidthBridgeV8
open Family8SelectedParentMassPopularCordobaCoreV2
open Family8StickySelectedParentGreedyBlockFrostmanV3
open FamilyStickyAtEveryScaleCoreV1
open FamilyStickyCinematicL32FiniteWeightedBucketV1
open FamilyStickyHierarchyEndpointPrefixShadingTransportV1.StickyScaleCover

noncomputable section

/-!
# Removing the actual normalized-container Jacobian from Equation (46)

V1 was an unbuilt namespace draft and is intentionally not imported.  The
division-free mass-popular core contains the volume of the actual common
bucket-normalized John container.  Its actual image/Jacobian envelope leaves
only the literal count/log/Katz--Tao scalar below.
-/

variable {delta rho : NNReal} {index : Type}
  [Fintype index] [DecidableEq index]

noncomputable def selectedParentMassPopularCordobaFixedEnvelope
    (D : ActualTubeDatum delta index)
    (S : StickyScaleCover D.family rho) (hrho : 0 < rho)
    (P : GreedyDensityPartition S.activeCoarseFamily
      (hullCandidates (Finset.univ : Finset (ActiveParentIndex S)))
      (hullContainer S.activeCoarseFamily) Finset.univ)
    (k : Fin (blocks S.activeCoarseFamily P).length)
    (r : NNReal) (hr : 0 < r) {loss : Nat}
    (_A : FactoringMultiplicityAssembly.ExactAssembly
      (greedyParentFactorization S P)
      (parentAggregatedShading S D.shading) loss)
    (label : Fin 3 -> Int) (KT : ENNReal) : ENNReal :=
  let e := contractedJohnAffineEquiv
    (selectedParentGreedyBlockJohnFrame S hrho P k) r hr
  let B := (blockAt S.activeCoarseFamily P k).fiber
  ((loss : ENNReal) * (P.length : ENNReal) *
      (selectedParentLogarithmicSideBucketLoss rho : ENNReal)) *
    (((selectedParentPlankBucketIndices e S B hrho label).card : ENNReal) * 2) *
      (KT * (2304 : ENNReal) ^ 3)

theorem selectedParentMassPopularCordobaCoreBudget_le_jacobian_fixedEnvelope
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
    (label : Fin 3 -> Int) (KT : ENNReal) :
    selectedParentMassPopularCordobaCoreBudget
        D S hrho P k r hr A label KT ≤
      affineJacobian
          (bucketNormalizedAffineEquiv
            (contractedJohnAffineEquiv
              (selectedParentGreedyBlockJohnFrame S hrho P k) r hr)
            label) *
        selectedParentMassPopularCordobaFixedEnvelope
          D S hrho P k r hr A label KT := by
  let e := contractedJohnAffineEquiv
    (selectedParentGreedyBlockJohnFrame S hrho P k) r hr
  let B := (blockAt S.activeCoarseFamily P k).fiber
  let coefficient : ENNReal :=
    ((loss : ENNReal) * (P.length : ENNReal) *
      (selectedParentLogarithmicSideBucketLoss rho : ENNReal)) *
      (((selectedParentPlankBucketIndices e S B hrho label).card : ENNReal) * 2)
  let J : ENNReal := affineJacobian (bucketNormalizedAffineEquiv e label)
  have hvolume :=
    selectedParentBucketNormalizedJohnContainer_volume_le_jacobian_fixed
      hD.contained_in_unit_ball S hrho hrhoOne P k r hr label
  change coefficient *
      (KT * volume (selectedParentBucketNormalizedJohnContainer
        S hrho P k r label : Set Space)) ≤
    J * (coefficient * (KT * (2304 : ENNReal) ^ 3))
  calc
    coefficient *
        (KT * volume (selectedParentBucketNormalizedJohnContainer
          S hrho P k r label : Set Space)) ≤
      coefficient * (KT * (J * (2304 : ENNReal) ^ 3)) := by
        exact mul_le_mul' le_rfl (mul_le_mul' le_rfl hvolume)
    _ = J * (coefficient * (KT * (2304 : ENNReal) ^ 3)) := by ac_rfl

theorem relativeScaled_massPopularCordobaCore_le_of_fixedEnvelope
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
    {lossEta epsilon beta : Real}
    (hscalar :
      capBound *
          ((rho : ENNReal) ^ (-lossEta) *
            selectedParentMassPopularCordobaFixedEnvelope
              D S hrho P k r hr A label KT) ≤
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
  let J : ENNReal := affineJacobian
    (bucketNormalizedAffineEquiv
      (contractedJohnAffineEquiv
        (selectedParentGreedyBlockJohnFrame S hrho P k) r hr)
      label)
  let fixed := selectedParentMassPopularCordobaFixedEnvelope
    D S hrho P k r hr A label KT
  have hcore :=
    selectedParentMassPopularCordobaCoreBudget_le_jacobian_fixedEnvelope
      D hD S hrho hrhoOne P k r hr A label KT
  calc
    capBound * ((rho : ENNReal) ^ (-lossEta) *
        selectedParentMassPopularCordobaCoreBudget
          D S hrho P k r hr A label KT) ≤
      capBound * ((rho : ENNReal) ^ (-lossEta) * (J * fixed)) := by
        exact mul_le_mul' le_rfl (mul_le_mul' le_rfl hcore)
    _ = J * (capBound * ((rho : ENNReal) ^ (-lossEta) * fixed)) := by ac_rfl
    _ ≤ J * (relativeSquare *
        (sourcePower * proposition66AInnerFactor rho
          (bucketShortA label) (bucketShortB label)
          tubesPerPlank epsilon beta)) := by
      exact mul_le_mul' le_rfl (by simpa only [fixed] using hscalar)
    _ = relativeSquare * ((J * sourcePower) *
        proposition66AInnerFactor rho
          (bucketShortA label) (bucketShortB label)
          tubesPerPlank epsilon beta) := by ac_rfl

#print axioms selectedParentMassPopularCordobaFixedEnvelope
#print axioms
  selectedParentMassPopularCordobaCoreBudget_le_jacobian_fixedEnvelope
#print axioms
  relativeScaled_massPopularCordobaCore_le_of_fixedEnvelope

end
end Family8SelectedParentMassPopularCoreJacobianCancellationV2
