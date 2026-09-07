import Family8Grounding.Family8SelectedParentFineLevelBucketRetentionV5

/-!
# Transport a selected affine bucket bound back to the actual fine level, V3

V1 omitted namespace opens and V2 used the wrong explicit argument order for
`ENNReal.mul_div_mul_left`.  This canonical successor proves the quotient
comparison directly from the actual carrier identity.
-/

open Set MeasureTheory
open scoped BigOperators ENNReal NNReal

namespace Family8SelectedParentFineLevelAverageTransportV3

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
open Family8KatzTaoFrostmanPropertiesV1
open Family8SelectedParentAffineShadingTransportV4
open Family8SelectedParentCertifiedPlankCordobaConnectorV3
open Family8SelectedParentFineLevelLiftV2
open Family8SelectedParentGreedyBlockFiberIdentityV2
open Family8SelectedParentJohnFrameNormalizationV9
open Family8SelectedParentJohnPlankSideWidthBridgeV4
open Family8SelectedParentJohnPlankSideWidthBridgeV5
open Family8SelectedParentJohnPlankSideWidthBridgeV7
open Family8SelectedParentJohnPlankSideWidthBridgeV8
open Family8StickySelectedParentGreedyBlockFrostmanV3
open FamilyStickyAtEveryScaleCoreV1
open FamilyStickyHierarchyEndpointPrefixShadingTransportV1.StickyScaleCover

noncomputable section

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 4000000

variable {delta rho : NNReal} {index : Type}
  [Fintype index] [DecidableEq index]

/-- A Jacobian-weighted mass-retention estimate for the literal selected
bucket implies the quotient comparison required by the actual-average
assembly.  No positivity of either shaded union is needed. -/
theorem sourceFineLevelShading_averageMultiplicity_le_bucketLoss_mul
    (D : ActualTubeDatum delta index)
    (S : StickyScaleCover D.family rho)
    (P : GreedyDensityPartition S.activeCoarseFamily
      (hullCandidates (Finset.univ : Finset (ActiveParentIndex S)))
      (hullContainer S.activeCoarseFamily) Finset.univ)
    (k : Fin (blocks S.activeCoarseFamily P).length)
    {loss : Nat}
    (A : FactoringMultiplicityAssembly.ExactAssembly
      (greedyParentFactorization S P)
      (parentAggregatedShading S D.shading) loss)
    (e : Space ≃ᵃ[Real] Space) (hrho : 0 < rho)
    (label : Fin 3 -> Int) (bucketLoss : ENNReal)
    (hretained :
      affineJacobian (bucketNormalizedAffineEquiv e label) *
          (sourceFineLevelShading A (some k)).shadingMass ≤
        bucketLoss *
          (selectedParentPlankBucketShading e S
            (fineShadingAtGreedyBlockLevel S D.shading P k A.fineLevel)
            (blockAt S.activeCoarseFamily P k).fiber hrho label).shadingMass) :
    (sourceFineLevelShading A (some k)).averageMultiplicity ≤
      bucketLoss *
        (selectedParentPlankBucketShading e S
          (fineShadingAtGreedyBlockLevel S D.shading P k A.fineLevel)
          (blockAt S.activeCoarseFamily P k).fiber hrho label).averageMultiplicity := by
  let f := bucketNormalizedAffineEquiv e label
  let Z := sourceFineLevelShading A (some k)
  let Ybucket := selectedParentPlankBucketShading e S
    (fineShadingAtGreedyBlockLevel S D.shading P k A.fineLevel)
    (blockAt S.activeCoarseFamily P k).fiber hrho label
  have hunion : Ybucket.shadedUnion ⊆ f '' Z.shadedUnion := by
    intro x hx
    obtain ⟨q, hxq⟩ := Set.mem_iUnion.mp hx
    rw [exactAssembly_fineLevelPlankBucket_carrier] at hxq
    obtain ⟨y, hy, rfl⟩ := hxq
    exact ⟨y, Set.mem_iUnion.mpr ⟨q.1.1, hy⟩, rfl⟩
  have hvolume : volume Ybucket.shadedUnion ≤
      affineJacobian f * volume Z.shadedUnion := by
    calc
      volume Ybucket.shadedUnion ≤ volume (f '' Z.shadedUnion) :=
        measure_mono hunion
      _ = affineJacobian f * volume Z.shadedUnion :=
        volume_image_affineEquiv f Z.shadedUnion
  have hJ0 : affineJacobian f ≠ 0 := (affineJacobian_pos f).ne'
  have hJtop : affineJacobian f ≠ ∞ := affineJacobian_ne_top f
  unfold Shading.averageMultiplicity
  change Z.shadingMass / volume Z.shadedUnion ≤
    bucketLoss * (Ybucket.shadingMass / volume Ybucket.shadedUnion)
  calc
    Z.shadingMass / volume Z.shadedUnion =
        (affineJacobian f * Z.shadingMass) /
          (affineJacobian f * volume Z.shadedUnion) := by
      exact (ENNReal.mul_div_mul_left Z.shadingMass
        (volume Z.shadedUnion) hJ0 hJtop).symm
    _ ≤ (bucketLoss * Ybucket.shadingMass) /
          (affineJacobian f * volume Z.shadedUnion) :=
      ENNReal.div_le_div_right hretained _
    _ ≤ (bucketLoss * Ybucket.shadingMass) /
          volume Ybucket.shadedUnion :=
      ENNReal.div_le_div_left hvolume _
    _ = bucketLoss *
          (Ybucket.shadingMass / volume Ybucket.shadedUnion) := by
      simp only [div_eq_mul_inv]
      ac_rfl

#print axioms sourceFineLevelShading_averageMultiplicity_le_bucketLoss_mul

end

end Family8SelectedParentFineLevelAverageTransportV3
