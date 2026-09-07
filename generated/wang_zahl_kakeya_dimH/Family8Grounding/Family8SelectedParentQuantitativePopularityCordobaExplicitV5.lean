import Family8Grounding.Family8SelectedParentQuantitativePopularityCordobaV3

/-!
# Explicit selected-parent quantitative-popularity Córdoba dichotomy, V5

The zero-mass branch has zero average multiplicity.  In the nonzero branch,
the popularity floor is the actual bucket mass divided by twice its literal
cardinality.
-/

open Set MeasureTheory
open scoped BigOperators ENNReal NNReal

namespace Family8SelectedParentQuantitativePopularityCordobaExplicitV5

open LeanEval.Analysis.WangZahlKakeya
open Submission.Kakeya.ConvexGeometry
open Submission.Kakeya.ConvexFactoring
open Submission.Kakeya.ConvexFactoring.FullConvexMaximalDensity
open Submission.Kakeya.ConvexFactoring.GreedyOccurrenceFactorization
open Submission.Kakeya.ConvexFactoring.HeavyParentSelection
open Submission.Kakeya.Uniformity
open Family8CertifiedPlankDyadicCordobaV2
open Family8QuantitativeCarrierPopularityRestrictionV3
open Family8SelectedParentAffineShadingTransportV4
open Family8SelectedParentCertifiedPlankCordobaConnectorV3
open Family8SelectedParentCertifiedPlankCordobaThresholdedAngleV6
open Family8SelectedParentJohnFrameNormalizationV9
open Family8SelectedParentJohnPlankSideWidthBridgeV4
open Family8SelectedParentJohnPlankSideWidthBridgeV5
open Family8SelectedParentJohnPlankSideWidthBridgeV7
open Family8SelectedParentJohnPlankSideWidthBridgeV8
open Family8SelectedParentQuantitativePopularityCordobaV3
open Family8StickySelectedParentGreedyBlockFrostmanV3
open FamilyStickyAtEveryScaleCoreV1

noncomputable section

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 5000000

variable {delta rho : NNReal} {index : Type}
  [Fintype index] [DecidableEq index]
  {fine : UniformTubeFamily delta index}

theorem selectedParentPlankBucket_averageMultiplicity_eq_zero_or_le_explicit
    (S : StickyScaleCover fine rho) (hrho : 0 < rho)
    (Y : Shading fine.bodyFamily)
    (P : GreedyDensityPartition S.activeCoarseFamily
      (hullCandidates (Finset.univ : Finset (ActiveParentIndex S)))
      (hullContainer S.activeCoarseFamily) Finset.univ)
    (k : Fin (blocks S.activeCoarseFamily P).length)
    (r : NNReal) (hr : 0 < r) (label : Fin 3 -> Int)
    (hplank : forall p : {p // p ∈ (blockAt S.activeCoarseFamily P k).fiber},
      p ∈ selectedParentPlankBucketIndices
          (contractedJohnAffineEquiv
            (selectedParentGreedyBlockJohnFrame S hrho P k) r hr)
          S (blockAt S.activeCoarseFamily P k).fiber hrho label ->
        IsPlank 576 (bucketShortA label) (bucketShortB label)
          (selectedParentAffineFamily
            (bucketNormalizedAffineEquiv
              (contractedJohnAffineEquiv
                (selectedParentGreedyBlockJohnFrame S hrho P k) r hr)
              label)
            S (blockAt S.activeCoarseFamily P k).fiber p))
    (KT : ENNReal) (hKT : IsKatzTao KT S.activeCoarseFamily) :
    let e := contractedJohnAffineEquiv
      (selectedParentGreedyBlockJohnFrame S hrho P k) r hr
    let B := (blockAt S.activeCoarseFamily P k).fiber
    let Ybucket := selectedParentPlankBucketShading e S Y B hrho label
    let hplankPos : forall q,
        IsPlank 576 (bucketShortA label) (bucketShortB label)
          (quantitativePositiveCarrierFamily Ybucket q) := fun q =>
      selectedParentPlankBucket_isPlank e S B hrho label hplank q.1
    let cert := chosenPlankCertificate hplankPos
    Ybucket.averageMultiplicity = 0 ∨
      Ybucket.averageMultiplicity ≤
        2 * certifiedPlankDyadicFactor
          (certifiedPlankThresholdedLevels cert) KT
            (certifiedPlankThresholdedAngleScaleCap 576 *
              (((((sideShapeUpper label 2)⁻¹ * r : NNReal) : ENNReal) ^ 3) /
                (Ybucket.shadingMass /
                  (((selectedParentPlankBucketIndices e S B hrho label).card :
                    ENNReal) * 2)))) := by
  dsimp only
  let e := contractedJohnAffineEquiv
    (selectedParentGreedyBlockJohnFrame S hrho P k) r hr
  let B := (blockAt S.activeCoarseFamily P k).fiber
  let Ybucket := selectedParentPlankBucketShading e S Y B hrho label
  by_cases hmass : Ybucket.shadingMass = 0
  · left
    change Ybucket.shadingMass / volume Ybucket.shadedUnion = 0
    rw [hmass, ENNReal.zero_div]
  · right
    have hresult :=
      selectedParentPlankBucket_averageMultiplicity_le_quantitativePopularityJohn
        S hrho Y P k r hr label hplank KT hKT
    dsimp only at hresult
    rw [quantitativeCarrierFloor_eq_mass_div_card_mul_two Ybucket hmass] at hresult
    simpa only [Fintype.card_coe] using hresult

#print axioms
  selectedParentPlankBucket_averageMultiplicity_eq_zero_or_le_explicit

end

end Family8SelectedParentQuantitativePopularityCordobaExplicitV5
