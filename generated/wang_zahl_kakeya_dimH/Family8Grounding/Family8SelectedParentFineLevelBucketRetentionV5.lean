import Family8Grounding.Family8SelectedParentFineLevelBucketRetentionV3

/-!
# Transport actual fine-level bucket retention through V9 normalization, V5

The selected V9 plank bucket is the common affine image of the literal
pre-affine restriction.  We prove its exact shading-mass Jacobian formula,
lift the V3 real retention to `ENNReal`, and transport the estimate to the
very affine bucket shading consumed by certified plank Córdoba.
-/

open Set MeasureTheory
open scoped BigOperators ENNReal NNReal

namespace Family8SelectedParentFineLevelBucketRetentionV5

open LeanEval.Analysis.WangZahlKakeya
open Submission.Kakeya.ConvexGeometry
open Submission.Kakeya.ConvexFactoring
open Submission.Kakeya.ConvexFactoring.FactoringMultiplicityAssembly
open Submission.Kakeya.ConvexFactoring.FullConvexMaximalDensity
open Submission.Kakeya.ConvexFactoring.GreedyOccurrenceFactorization
open Submission.Kakeya.ConvexFactoring.HeavyParentSelection
open Submission.Kakeya.Uniformity
open Family6AffineConvexVolumeCoreV1
open Family8ExactAssemblyActualAverageBridgeV1
open Family8ExactAssemblyActualAverageBridgeV1.ExactAssembly
open Family8GeneralizedKatzTaoMultiplicityV1
open Family8KatzTaoFrostmanPropertiesV1
open Family8SelectedParentAffineShadingTransportV4
open Family8SelectedParentCertifiedPlankCordobaConnectorV3
open Family8SelectedParentFineLevelBucketRetentionV3
open Family8SelectedParentFineLevelLiftV2
open Family8SelectedParentGreedyBlockFiberIdentityV2
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
set_option maxHeartbeats 4000000

variable {delta rho : NNReal} {index : Type}
  [Fintype index] [DecidableEq index]
  {fine : UniformTubeFamily delta index}

/-- Restriction to the chosen parent subtype commutes exactly with the common
affine normalization at the level of multiplicity-counted shading mass. -/
theorem selectedParentPlankBucketShading_shadingMass_eq_jacobian_mul_preAffine
    (e : Space ≃ᵃ[Real] Space) (S : StickyScaleCover fine rho)
    (Y : Shading fine.bodyFamily)
    (B : Finset (ActiveParentIndex S)) (hrho : 0 < rho)
    (label : Fin 3 -> Int) :
    (selectedParentPlankBucketShading e S Y B hrho label).shadingMass =
      affineJacobian (bucketNormalizedAffineEquiv e label) *
        (selectedParentPreAffinePlankBucketShading
          e S Y B hrho label).shadingMass := by
  rw [selectedParentPlankBucketShading,
    selectedParentPreAffinePlankBucketShading,
    selectedCoarseShading_mass, selectedCoarseShading_mass]
  simp_rw [selectedParentAffineShading_carrier, volume_image_affineEquiv]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro p _hp
  rfl

/-- The source fine-level mass, after the same V9 affine normalization, is
retained by the actual affine plank-bucket shading. -/
theorem exists_selectedParentFineLevelPlankBucket_affineShadingMassRetention
    (D : ActualTubeDatum delta index) (hD : D.IsAdmissible)
    (S : StickyScaleCover D.family rho) (hrho : 0 < rho) (hrhoOne : rho <= 1)
    (P : GreedyDensityPartition S.activeCoarseFamily
      (hullCandidates (Finset.univ : Finset (ActiveParentIndex S)))
      (hullContainer S.activeCoarseFamily) Finset.univ)
    (k : Fin (blocks S.activeCoarseFamily P).length)
    (r : NNReal) (hr : 0 < r) {loss : Nat}
    (A : FactoringMultiplicityAssembly.ExactAssembly
      (greedyParentFactorization S P)
      (parentAggregatedShading S D.shading) loss) :
    let B := (blockAt S.activeCoarseFamily P k).fiber
    let Ylevel :=
      fineShadingAtGreedyBlockLevel S D.shading P k A.fineLevel
    let e := contractedJohnAffineEquiv
      (selectedParentGreedyBlockJohnFrame S hrho P k) r hr
    let parent := {p // p ∈ B}
    let side : parent -> Fin 3 -> NNReal := fun p =>
      selectedParentLongRelabeledSide e S B hrho p
    exists label : Fin 3 -> Int,
      label ∈ occupiedWeightBuckets (Finset.univ : Finset parent)
        (fun p => sideShapeLabel (side p)) ∧
      affineJacobian (bucketNormalizedAffineEquiv e label) *
          (sourceFineLevelShading A (some k)).shadingMass <=
        (selectedParentLogarithmicSideBucketLoss rho : ENNReal) *
          (selectedParentPlankBucketShading
            e S Ylevel B hrho label).shadingMass ∧
      0 < bucketShortA label ∧
      bucketShortA label <= bucketShortB label ∧
      bucketShortB label <= 1 ∧
      forall p, p ∈ sideShapeBucket Finset.univ side label ->
        IsPlank 576 (bucketShortA label) (bucketShortB label)
          (selectedParentAffineFamily
            (bucketNormalizedAffineEquiv e label) S B p) := by
  dsimp only
  have hbucket :=
    exists_selectedParentFineLevelPlankBucket_shadingMassRetention
      D hD S hrho hrhoOne P k r hr A
  dsimp only at hbucket
  obtain ⟨label, hoccupied, hretained, ha, hab, hb, hplank⟩ := hbucket
  refine ⟨label, hoccupied, ?_, ha, hab, hb, hplank⟩
  let e := contractedJohnAffineEquiv
    (selectedParentGreedyBlockJohnFrame S hrho P k) r hr
  let Ylevel := fineShadingAtGreedyBlockLevel
    S D.shading P k A.fineLevel
  let B := (blockAt S.activeCoarseFamily P k).fiber
  have hpre :
      (sourceFineLevelShading A (some k)).shadingMass <=
        (selectedParentLogarithmicSideBucketLoss rho : ENNReal) *
          (selectedParentPreAffinePlankBucketShading
            e S Ylevel B hrho label).shadingMass := by
    apply (ENNReal.toReal_le_toReal
      (sourceFineLevelShading A (some k)).shadingMass_lt_top.ne
      (ENNReal.mul_ne_top (by simp)
        (selectedParentPreAffinePlankBucketShading
          e S Ylevel B hrho label).shadingMass_lt_top.ne)).mp
    simpa only [ENNReal.toReal_mul, ENNReal.toReal_natCast] using hretained
  calc
    affineJacobian (bucketNormalizedAffineEquiv e label) *
        (sourceFineLevelShading A (some k)).shadingMass <=
      affineJacobian (bucketNormalizedAffineEquiv e label) *
        ((selectedParentLogarithmicSideBucketLoss rho : ENNReal) *
          (selectedParentPreAffinePlankBucketShading
            e S Ylevel B hrho label).shadingMass) := by
      simpa only [mul_comm] using
        (mul_le_mul_left hpre
          (affineJacobian (bucketNormalizedAffineEquiv e label)))
    _ = (selectedParentLogarithmicSideBucketLoss rho : ENNReal) *
        (selectedParentPlankBucketShading
          e S Ylevel B hrho label).shadingMass := by
      rw [selectedParentPlankBucketShading_shadingMass_eq_jacobian_mul_preAffine]
      ac_rfl

#print axioms
  selectedParentPlankBucketShading_shadingMass_eq_jacobian_mul_preAffine
#print axioms
  exists_selectedParentFineLevelPlankBucket_affineShadingMassRetention

end

end Family8SelectedParentFineLevelBucketRetentionV5
