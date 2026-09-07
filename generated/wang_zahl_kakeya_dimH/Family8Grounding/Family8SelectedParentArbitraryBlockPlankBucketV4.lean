import Family8Grounding.Family8SelectedParentFineLevelBucketRetentionV5

/-!
# A logarithmic plank bucket for an arbitrary selected-parent block shading

The V9 side-shape pigeonhole is genuinely weighted: it applies to the actual
carrier volumes of any shading on one selected greedy block.  The earlier
fine-level endpoint used only the special shading coming from an
`ExactAssembly`.  This module records the stronger data-level statement.

It is the bridge needed for the paper-strength frozen route: a surviving
fibre of the polylogarithmic frozen assembly can first be reindexed on its
literal greedy block and then fed here, without introducing the coarse-card
averaging loss `P.length`.
-/

open Set MeasureTheory
open scoped BigOperators ENNReal NNReal

namespace Family8SelectedParentArbitraryBlockPlankBucketV4

open LeanEval.Analysis.WangZahlKakeya
open Submission.Kakeya.ConvexGeometry
open Submission.Kakeya.ConvexFactoring
open Submission.Kakeya.ConvexFactoring.FullConvexMaximalDensity
open Submission.Kakeya.ConvexFactoring.GreedyOccurrenceFactorization
open Submission.Kakeya.ConvexFactoring.HeavyParentSelection
open Submission.Kakeya.Uniformity
open Family6AffineConvexVolumeCoreV1
open Family8GeneralizedKatzTaoMultiplicityV1
open Family8KatzTaoFrostmanPropertiesV1
open Family8SelectedParentAffineShadingTransportV4
open Family8SelectedParentCertifiedPlankCordobaConnectorV3
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
set_option maxHeartbeats 8000000

variable {delta rho : NNReal} {index : Type}
  [Fintype index] [DecidableEq index]
  {fine : UniformTubeFamily delta index}

/-- Restrict an arbitrary actual block shading to one side-shape bucket before
the common affine normalization. -/
def selectedParentArbitraryPreAffinePlankBucketShading
    (e : Space ≃ᵃ[Real] Space) (S : StickyScaleCover fine rho)
    (B : Finset (ActiveParentIndex S)) (hrho : 0 < rho)
    (label : Fin 3 -> Int)
    (Z : Shading (selectedCoarseFamily S.activeCoarseFamily B)) :
    Shading (selectedCoarseFamily
      (selectedCoarseFamily S.activeCoarseFamily B)
      (selectedParentPlankBucketIndices e S B hrho label)) :=
  selectedCoarseShading Z
    (selectedParentPlankBucketIndices e S B hrho label)

/-- Affinely normalize the literal bucket of an arbitrary actual block
shading.  Its family is the same V9 plank family used by the certified
Cordoba endpoint. -/
def selectedParentArbitraryPlankBucketShading
    (e : Space ≃ᵃ[Real] Space) (S : StickyScaleCover fine rho)
    (B : Finset (ActiveParentIndex S)) (hrho : 0 < rho)
    (label : Fin 3 -> Int)
    (Z : Shading (selectedCoarseFamily S.activeCoarseFamily B)) :
    Shading (selectedParentPlankBucketFamily e S B hrho label) :=
  selectedCoarseShading
    (affineImageShading (bucketNormalizedAffineEquiv e label) Z)
    (selectedParentPlankBucketIndices e S B hrho label)

/-- The pre-affine bucket mass is the literal filtered sum of its actual
carrier-volume weights. -/
theorem selectedParentArbitraryPreAffinePlankBucketShading_mass_toReal
    (e : Space ≃ᵃ[Real] Space) (S : StickyScaleCover fine rho)
    (B : Finset (ActiveParentIndex S)) (hrho : 0 < rho)
    (label : Fin 3 -> Int)
    (Z : Shading (selectedCoarseFamily S.activeCoarseFamily B)) :
    (selectedParentArbitraryPreAffinePlankBucketShading
      e S B hrho label Z).shadingMass.toReal =
      ∑ p ∈ selectedParentPlankBucketIndices e S B hrho label,
        shadingPieceRealWeight Z p := by
  rw [shadingMass_toReal_eq_sum_shadingPieceRealWeight]
  rw [← Finset.attach_eq_univ]
  calc
    (∑ p ∈ (selectedParentPlankBucketIndices e S B hrho label).attach,
        shadingPieceRealWeight
          (selectedParentArbitraryPreAffinePlankBucketShading
            e S B hrho label Z) p) =
      ∑ p ∈ (selectedParentPlankBucketIndices e S B hrho label).attach,
        shadingPieceRealWeight Z p.1 := by rfl
    _ = ∑ p ∈ selectedParentPlankBucketIndices e S B hrho label,
        shadingPieceRealWeight Z p := Finset.sum_attach _ _

/-- Affine normalization multiplies the arbitrary bucket mass by the honest
Jacobian. -/
theorem selectedParentArbitraryPlankBucketShading_shadingMass
    (e : Space ≃ᵃ[Real] Space) (S : StickyScaleCover fine rho)
    (B : Finset (ActiveParentIndex S)) (hrho : 0 < rho)
    (label : Fin 3 -> Int)
    (Z : Shading (selectedCoarseFamily S.activeCoarseFamily B)) :
    (selectedParentArbitraryPlankBucketShading
      e S B hrho label Z).shadingMass =
      affineJacobian (bucketNormalizedAffineEquiv e label) *
        (selectedParentArbitraryPreAffinePlankBucketShading
          e S B hrho label Z).shadingMass := by
  rw [selectedParentArbitraryPlankBucketShading,
    selectedParentArbitraryPreAffinePlankBucketShading,
    selectedCoarseShading_mass, selectedCoarseShading_mass]
  simp_rw [affineImageShading_carrier, volume_image_affineEquiv]
  rw [Finset.mul_sum]

/-- Every actual shading on one selected greedy block has a logarithmically
retained affine plank bucket.  Both the mass comparison and the plank
certificate are outputs of the construction. -/
theorem exists_selectedParentArbitraryPlankBucket_affineShadingMassRetention
    (D : ActualTubeDatum delta index) (hD : D.IsAdmissible)
    (S : StickyScaleCover D.family rho) (hrho : 0 < rho)
    (hrhoOne : rho <= 1)
    (P : GreedyDensityPartition S.activeCoarseFamily
      (hullCandidates (Finset.univ : Finset (ActiveParentIndex S)))
      (hullContainer S.activeCoarseFamily) Finset.univ)
    (k : Fin (blocks S.activeCoarseFamily P).length)
    (r : NNReal) (hr : 0 < r)
    (Z : Shading (selectedCoarseFamily S.activeCoarseFamily
      (blockAt S.activeCoarseFamily P k).fiber)) :
    let B := (blockAt S.activeCoarseFamily P k).fiber
    let e := contractedJohnAffineEquiv
      (selectedParentGreedyBlockJohnFrame S hrho P k) r hr
    let parent := {p // p ∈ B}
    let side : parent -> Fin 3 -> NNReal := fun p =>
      selectedParentLongRelabeledSide e S B hrho p
    exists label : Fin 3 -> Int,
      label ∈ occupiedWeightBuckets (Finset.univ : Finset parent)
        (fun p => sideShapeLabel (side p)) ∧
      affineJacobian (bucketNormalizedAffineEquiv e label) *
          Z.shadingMass <=
        (selectedParentLogarithmicSideBucketLoss rho : ENNReal) *
          (selectedParentArbitraryPlankBucketShading
            e S B hrho label Z).shadingMass ∧
      0 < bucketShortA label ∧
      bucketShortA label <= bucketShortB label ∧
      bucketShortB label <= 1 ∧
      forall p, p ∈ sideShapeBucket Finset.univ side label ->
        IsPlank 576 (bucketShortA label) (bucketShortB label)
          (selectedParentAffineFamily
            (bucketNormalizedAffineEquiv e label) S B p) := by
  dsimp only
  let B := (blockAt S.activeCoarseFamily P k).fiber
  let e := contractedJohnAffineEquiv
    (selectedParentGreedyBlockJohnFrame S hrho P k) r hr
  let weight : {p // p ∈ B} -> Real :=
    fun p => shadingPieceRealWeight Z p
  have hweightNonneg : forall p, 0 <= weight p := by
    intro p
    dsimp only [weight, shadingPieceRealWeight]
    positivity
  have hbucket :=
    exists_selectedParentActualIsPlankBucket_logarithmicLoss_of_admissible
      D hD S hrho hrhoOne P k r hr weight hweightNonneg
  dsimp only at hbucket
  obtain ⟨label, hoccupied, hretained, ha, hab, hb, hplank⟩ := hbucket
  refine ⟨label, hoccupied, ?_, ha, hab, hb, hplank⟩
  have hreal : Z.shadingMass.toReal <=
      selectedParentLogarithmicSideBucketLoss rho *
        (selectedParentArbitraryPreAffinePlankBucketShading
          e S B hrho label Z).shadingMass.toReal := by
    calc
      Z.shadingMass.toReal = ∑ p, weight p := by
        exact shadingMass_toReal_eq_sum_shadingPieceRealWeight Z
      _ <= selectedParentLogarithmicSideBucketLoss rho *
          (∑ p ∈ sideShapeBucket Finset.univ
            (fun p => selectedParentLongRelabeledSide e S B hrho p) label,
            weight p) := hretained
      _ = selectedParentLogarithmicSideBucketLoss rho *
          (selectedParentArbitraryPreAffinePlankBucketShading
            e S B hrho label Z).shadingMass.toReal := by
        rw [selectedParentArbitraryPreAffinePlankBucketShading_mass_toReal]
        rfl
  have hpre : Z.shadingMass <=
      (selectedParentLogarithmicSideBucketLoss rho : ENNReal) *
        (selectedParentArbitraryPreAffinePlankBucketShading
          e S B hrho label Z).shadingMass := by
    apply (ENNReal.toReal_le_toReal Z.shadingMass_lt_top.ne
      (ENNReal.mul_ne_top (by simp)
        (selectedParentArbitraryPreAffinePlankBucketShading
          e S B hrho label Z).shadingMass_lt_top.ne)).mp
    simpa only [ENNReal.toReal_mul, ENNReal.toReal_natCast] using hreal
  calc
    affineJacobian (bucketNormalizedAffineEquiv e label) * Z.shadingMass <=
      affineJacobian (bucketNormalizedAffineEquiv e label) *
        ((selectedParentLogarithmicSideBucketLoss rho : ENNReal) *
          (selectedParentArbitraryPreAffinePlankBucketShading
            e S B hrho label Z).shadingMass) :=
      mul_le_mul' le_rfl hpre
    _ = (selectedParentLogarithmicSideBucketLoss rho : ENNReal) *
        (selectedParentArbitraryPlankBucketShading
          e S B hrho label Z).shadingMass := by
      rw [selectedParentArbitraryPlankBucketShading_shadingMass]
      ac_rfl

#print axioms selectedParentArbitraryPreAffinePlankBucketShading_mass_toReal
#print axioms selectedParentArbitraryPlankBucketShading_shadingMass
#print axioms
  exists_selectedParentArbitraryPlankBucket_affineShadingMassRetention

end

end Family8SelectedParentArbitraryBlockPlankBucketV4
