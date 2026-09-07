import Family8Grounding.Family8SelectedOccurrenceFrozenFinalFiberBlockAverageBridgeV1
import Family8Grounding.Family8SelectedParentArbitraryBlockQuantitativeCordobaV2
import Family8Grounding.Family8SelectedParentExactAssemblyCordobaExpandedV5
import Mathlib.Tactic

/-!
# Fixed-occurrence frozen fibre to the local Eq. (46) scalar

For an occurrence `q` already returned by the frozen exact-outer producer,
reindex its actual final fibre on the literal block at that same `q`, apply the
automatic arbitrary-block plank bucket theorem, and expand the certified
dyadic factor to its explicit local scalar.

The occurrence is never reselected.  The carrier floor in the scalar is the
literal floor of the bucket constructed inside this fixed block; no additional
global cap is assumed or introduced.
-/

open Set MeasureTheory
open scoped BigOperators ENNReal NNReal

namespace Family8SelectedOccurrenceFrozenSameQEq46ScalarSeamV1

open LeanEval.Analysis.WangZahlKakeya
open Submission.Kakeya.ConvexGeometry
open Submission.Kakeya.ConvexFactoring
open Submission.Kakeya.ConvexFactoring.FullConvexMaximalDensity
open Submission.Kakeya.ConvexFactoring.GreedyOccurrenceFactorization
open Submission.Kakeya.ConvexFactoring.HeavyParentSelection
open Submission.Kakeya.Uniformity
open Family8CertifiedPlankDyadicCordobaV2
open Family8FrozenComparableActualAverageMassDensityV1
open Family8FrozenNeighborhoodAssemblyV1
open Family8KatzTaoFrostmanPropertiesV1
open Family8QuantitativeCarrierPopularityRestrictionV3
open Family8SelectedOccurrenceDensityFrostmanV1
open Family8SelectedOccurrenceFrozenFinalFiberBlockAverageBridgeV1
open Family8SelectedParentAffineShadingTransportV4
open Family8SelectedParentArbitraryBlockPlankBucketV4
open Family8SelectedParentArbitraryBlockQuantitativeCordobaV2
open Family8SelectedParentCertifiedPlankCordobaConnectorV3
open Family8SelectedParentCertifiedPlankCordobaThresholdedAngleV6
open Family8SelectedParentExactAssemblyCordobaExpandedV5
open Family8SelectedParentJohnFrameNormalizationV9
open Family8SelectedParentJohnPlankQuantitativeLossV9
open Family8SelectedParentJohnPlankSideWidthBridgeV4
open Family8SelectedParentJohnPlankSideWidthBridgeV5
open Family8SelectedParentJohnPlankSideWidthBridgeV7
open Family8SelectedParentJohnPlankSideWidthBridgeV8
open Family8StickySelectedParentGreedyBlockFrostmanV3
open FamilyStickyAtEveryScaleCoreV1
open FamilyStickyCinematicL32FiniteWeightedBucketV1
open FamilyStickyHierarchyEndpointPrefixShadingTransportV1.StickyScaleCover

noncomputable section

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 7000000

local instance (p : Prop) : Decidable p := Classical.propDecidable p

variable {delta rho : NNReal} {index : Type}
  [Fintype index] [DecidableEq index]
  {fine : UniformTubeFamily delta index}

/-- The explicit certificate-free local Córdoba scalar for one fixed block,
one occupied side label, and the literal bucket carrier floor. -/
noncomputable def selectedOccurrenceFrozenSameQExpandedCordobaRHS
    (S : StickyScaleCover fine rho) (hrho : 0 < rho)
    (P : GreedyDensityPartition S.activeCoarseFamily
      (hullCandidates (Finset.univ : Finset (ActiveParentIndex S)))
      (hullContainer S.activeCoarseFamily) Finset.univ)
    (q : Fin (blocks S.activeCoarseFamily P).length)
    (r : NNReal) (hr : 0 < r)
    (Z : Shading (selectedCoarseFamily S.activeCoarseFamily
      (blockAt S.activeCoarseFamily P q).fiber))
    (label : Fin 3 -> Int) (KT : ENNReal) : ENNReal :=
  let B := (blockAt S.activeCoarseFamily P q).fiber
  let e := contractedJohnAffineEquiv
    (selectedParentGreedyBlockJohnFrame S hrho P q) r hr
  let Ybucket := selectedParentArbitraryPlankBucketShading
    e S B hrho label Z
  (selectedParentLogarithmicSideBucketLoss rho : ENNReal) *
    (2 *
      (((certifiedPlankThresholdedAngleBucketLoss
            (bucketShortA label) (bucketShortB label) : Nat) : ENNReal) *
          KT *
          (certifiedPlankThresholdedAngleScaleCap 576 *
            (((((sideShapeUpper label 2)⁻¹ * r : NNReal) : ENNReal) ^ 3) /
              quantitativeCarrierFloor Ybucket))))

/-- The actual frozen final fibre at a fixed selected occurrence is bounded by
one explicit local Eq. (46) Córdoba scalar from a side label chosen inside that
same occurrence. -/
theorem exists_selectedOccurrenceFrozenSameQ_expandedCordobaScalar
    (D : ActualTubeDatum delta index) (hD : D.IsAdmissible)
    (S : StickyScaleCover D.family rho) (hrho : 0 < rho)
    (hrhoOne : rho <= 1)
    (P : GreedyDensityPartition S.activeCoarseFamily
      (hullCandidates (Finset.univ : Finset (ActiveParentIndex S)))
      (hullContainer S.activeCoarseFamily) Finset.univ)
    (R : Finset (Fin (blocks S.activeCoarseFamily P).length))
    {Y : Shading S.activeCoarseFamily} {rFrozen : Real}
    (A : Family8FrozenNeighborhoodAssemblyV1.Assembly
      (selectedOccurrenceFactorization P R) Y rFrozen)
    (q : Fin (blocks S.activeCoarseFamily P).length) (hq : q ∈ R)
    (r : NNReal) (hr : 0 < r)
    (KT : ENNReal) (hKT : IsKatzTao KT S.activeCoarseFamily) :
    let B := (blockAt S.activeCoarseFamily P q).fiber
    let e := contractedJohnAffineEquiv
      (selectedParentGreedyBlockJohnFrame S hrho P q) r hr
    let parent := {p // p ∈ B}
    let side : parent -> Fin 3 -> NNReal := fun p =>
      selectedParentLongRelabeledSide e S B hrho p
    ∃ label : Fin 3 -> Int,
      label ∈ occupiedWeightBuckets (Finset.univ : Finset parent)
        (fun p => sideShapeLabel (side p)) ∧
      0 < bucketShortA label ∧
      bucketShortA label <= bucketShortB label ∧
      bucketShortB label <= 1 ∧
      (Family8FrozenComparableActualAverageMassDensityV1.Assembly.finalFiberShading
          A (some q)).averageMultiplicity <=
        selectedOccurrenceFrozenSameQExpandedCordobaRHS
          S hrho P q r hr
            (selectedOccurrenceFrozenFinalFiberBlockShading P R A q)
              label KT := by
  dsimp only
  let B := (blockAt S.activeCoarseFamily P q).fiber
  let e := contractedJohnAffineEquiv
    (selectedParentGreedyBlockJohnFrame S hrho P q) r hr
  let Z := selectedOccurrenceFrozenFinalFiberBlockShading P R A q
  have hcordoba :=
    exists_selectedParentArbitraryPlankBucket_averageMultiplicity_le
      D hD S hrho hrhoOne P q r hr Z KT hKT
  dsimp only at hcordoba
  obtain ⟨label, hoccupied, ha, hab, hb, hplank, hbound⟩ := hcordoba
  refine ⟨label, hoccupied, ha, hab, hb, ?_⟩
  let Ybucket := selectedParentArbitraryPlankBucketShading
    e S B hrho label Z
  let hplankPos : forall t,
      IsPlank 576 (bucketShortA label) (bucketShortB label)
        (quantitativePositiveCarrierFamily Ybucket t) := fun t =>
    selectedParentPlankBucket_isPlank e S B hrho label hplank t.1
  let cert := chosenPlankCertificate hplankPos
  let scale : ENNReal :=
    certifiedPlankThresholdedAngleScaleCap 576 *
      (((((sideShapeUpper label 2)⁻¹ * r : NNReal) : ENNReal) ^ 3) /
        quantitativeCarrierFloor Ybucket)
  have hbound' : Z.averageMultiplicity <=
      (selectedParentLogarithmicSideBucketLoss rho : ENNReal) *
        (2 * certifiedPlankDyadicFactor
          (certifiedPlankThresholdedLevels cert) KT scale) := by
    simpa only [Z, e, B, Ybucket, hplankPos, cert, scale] using hbound
  have hexpand :
      (selectedParentLogarithmicSideBucketLoss rho : ENNReal) *
          (2 * certifiedPlankDyadicFactor
            (certifiedPlankThresholdedLevels cert) KT scale) <=
        selectedOccurrenceFrozenSameQExpandedCordobaRHS
          S hrho P q r hr Z label KT := by
    have h := loss_mul_two_mul_certifiedPlankDyadicFactor_le_explicit
      cert (selectedParentLogarithmicSideBucketLoss rho : ENNReal) KT scale
    simpa only [selectedOccurrenceFrozenSameQExpandedCordobaRHS,
      Z, e, B, Ybucket, scale] using h
  calc
    (Family8FrozenComparableActualAverageMassDensityV1.Assembly.finalFiberShading
        A (some q)).averageMultiplicity = Z.averageMultiplicity := by
      symm
      simpa only [Z] using
        (selectedOccurrenceFrozenFinalFiberBlockShading_averageMultiplicity_eq
          P R A q hq)
    _ <= (selectedParentLogarithmicSideBucketLoss rho : ENNReal) *
        (2 * certifiedPlankDyadicFactor
          (certifiedPlankThresholdedLevels cert) KT scale) := hbound'
    _ <= selectedOccurrenceFrozenSameQExpandedCordobaRHS
        S hrho P q r hr Z label KT := hexpand

#print axioms selectedOccurrenceFrozenSameQExpandedCordobaRHS
#print axioms exists_selectedOccurrenceFrozenSameQ_expandedCordobaScalar

end

end Family8SelectedOccurrenceFrozenSameQEq46ScalarSeamV1
