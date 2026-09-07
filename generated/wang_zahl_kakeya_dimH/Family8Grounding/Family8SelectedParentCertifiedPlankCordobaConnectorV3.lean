import Family8Grounding.Family8SelectedParentJohnPlankQuantitativeLossV9
import Family8Grounding.Family8CertifiedPlankDyadicCordobaV2
import Family8Grounding.Family8GreedyOccurrenceCanonicalFrostmanBridgeV2
import FamilyStickyGrounding.Family6AffineKatzTaoTransportV3

/-!
# Actual selected-parent plank bucket to certified Cordoba, V3

This canonical connector forms the literal V9 shape-bucket subtype and its
actual affine-image shading. Memberwise `IsPlank 576 a b` supplies all frame
certificates, while source Katz--Tao control passes through the block
restriction, common affine map, and bucket restriction.

The repository still has no actual dyadic angle/container producer for this
bucket. The endpoint therefore leaves exactly the finite angle assignment,
inverse-sine control, container containment, and container-scale inequality
as direct premises, with no overlap or multiplicity callback.
-/

open scoped ENNReal NNReal BigOperators
open MeasureTheory Set

namespace Family8SelectedParentCertifiedPlankCordobaConnectorV3

open LeanEval.Analysis.WangZahlKakeya
open Submission.Kakeya.ConvexGeometry
open Submission.Kakeya.ConvexFactoring
open Submission.Kakeya.ConvexFactoring.FullConvexMaximalDensity
open Submission.Kakeya.ConvexFactoring.GreedyOccurrenceFactorization
open Submission.Kakeya.ConvexFactoring.HeavyParentSelection
open Submission.Kakeya.Uniformity
open Family6AffineKatzTaoTransportV3
open Family8CertifiedPlankPairOverlapV2
open Family8CertifiedPlankDyadicCordobaV2
open Family8GreedyOccurrenceCanonicalFrostmanBridgeV2
open Family8SelectedParentAffineShadingTransportV4
open Family8SelectedParentJohnPlankQuantitativeLossV9
open Family8SelectedParentJohnPlankSideWidthBridgeV4
open Family8SelectedParentJohnPlankSideWidthBridgeV5
open Family8SelectedParentJohnPlankSideWidthBridgeV7
open Family8SelectedParentJohnPlankSideWidthBridgeV8
open Family8StickySelectedParentGreedyBlockFrostmanV3
open FamilyStickyAtEveryScaleCoreV1

noncomputable section

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 4000000

universe u v

/-- Canonical data certificate chosen from a proved `IsPlank`. -/
noncomputable def chosenPlankCertificate
    {iota : Type u} {F : ConvexFamily iota} {C a b : NNReal}
    (hplank : forall i, IsPlank C a b (F i))
    (i : iota) : PlankDimensionsCertificate C a b (F i) :=
  Classical.choice
    (Family8CertifiedPlankPairOverlapV2.IsPlank.nonempty_plankDimensionsCertificate
      (hplank i))

/-- Generic certificate-eliminating endpoint. -/
theorem certifiedPlankDyadic_averageMultiplicity_le_of_isPlank
    {iota : Type u} {kappa : Type v}
    [Fintype iota] [DecidableEq kappa]
    {F : ConvexFamily iota} {Y : Shading F} {C a b : NNReal}
    (hplank : forall i, IsPlank C a b (F i))
    (levels : Finset kappa)
    (level : iota -> iota -> Option kappa)
    (inverseSineWeight : kappa -> ENNReal)
    (container : iota -> Option kappa -> ConvexBody Space)
    (D A : ENNReal)
    (hlevel : forall i j, level i j ∈ plankAngleLevels levels)
    (htransverse : forall i j k, level i j = some k ->
      0 < certifiedPlankPairSine (chosenPlankCertificate hplank) i j)
    (hinverse : forall i j k, level i j = some k ->
      ENNReal.ofReal
          ((certifiedPlankPairSine
            (chosenPlankCertificate hplank) i j)⁻¹) <=
        inverseSineWeight k)
    (hcontained : forall i j,
      (F j : Set Space) ⊆ (container i (level i j) : Set Space))
    (hKT : IsKatzTao D F)
    (hscale : forall i k, k ∈ plankAngleLevels levels ->
      certifiedPlankAngleScale C a b inverseSineWeight k *
          volume (container i k : Set Space) <=
        A * volume (Y.carrier i)) :
    Y.averageMultiplicity <= certifiedPlankDyadicFactor levels D A := by
  exact certifiedPlankDyadic_averageMultiplicity_le
    (chosenPlankCertificate hplank) levels level inverseSineWeight
    container D A hlevel htransverse hinverse hcontained hKT hscale

variable {delta rho : NNReal} {index : Type}
  [Fintype index] [DecidableEq index]
  {fine : UniformTubeFamily delta index}

/-- Actual V9 side-shape bucket indices. -/
def selectedParentPlankBucketIndices
    (e : Space ≃ᵃ[Real] Space) (S : StickyScaleCover fine rho)
    (B : Finset (ActiveParentIndex S)) (hrho : 0 < rho)
    (label : Fin 3 -> Int) : Finset {p // p ∈ B} :=
  sideShapeBucket Finset.univ
    (fun p => selectedParentLongRelabeledSide e S B hrho p) label

/-- Literal affine family on the actual bucket subtype. -/
abbrev selectedParentPlankBucketFamily
    (e : Space ≃ᵃ[Real] Space) (S : StickyScaleCover fine rho)
    (B : Finset (ActiveParentIndex S)) (hrho : 0 < rho)
    (label : Fin 3 -> Int) :
    ConvexFamily
      {p // p ∈ selectedParentPlankBucketIndices e S B hrho label} :=
  selectedCoarseFamily
    (selectedParentAffineFamily (bucketNormalizedAffineEquiv e label) S B)
    (selectedParentPlankBucketIndices e S B hrho label)

/-- Actual transported shading on exactly the same subtype. -/
def selectedParentPlankBucketShading
    (e : Space ≃ᵃ[Real] Space) (S : StickyScaleCover fine rho)
    (Y : Shading fine.bodyFamily)
    (B : Finset (ActiveParentIndex S)) (hrho : 0 < rho)
    (label : Fin 3 -> Int) :
    Shading (selectedParentPlankBucketFamily e S B hrho label) :=
  selectedCoarseShading
    (selectedParentAffineShading
      (bucketNormalizedAffineEquiv e label) S Y B)
    (selectedParentPlankBucketIndices e S B hrho label)

/-- V9's memberwise plank theorem becomes a full-bucket theorem. -/
theorem selectedParentPlankBucket_isPlank
    (e : Space ≃ᵃ[Real] Space) (S : StickyScaleCover fine rho)
    (B : Finset (ActiveParentIndex S)) (hrho : 0 < rho)
    (label : Fin 3 -> Int)
    (hplank : forall p : {p // p ∈ B},
      p ∈ selectedParentPlankBucketIndices e S B hrho label ->
        IsPlank 576 (bucketShortA label) (bucketShortB label)
          (selectedParentAffineFamily
            (bucketNormalizedAffineEquiv e label) S B p)) :
    forall q :
      {p // p ∈ selectedParentPlankBucketIndices e S B hrho label},
      IsPlank 576 (bucketShortA label) (bucketShortB label)
        (selectedParentPlankBucketFamily e S B hrho label q) := by
  intro q
  exact hplank q.1 q.2

/-- Source KT is inherited by the actual affine bucket. -/
theorem selectedParentPlankBucket_isKatzTao
    (e : Space ≃ᵃ[Real] Space) (S : StickyScaleCover fine rho)
    (B : Finset (ActiveParentIndex S)) (hrho : 0 < rho)
    (label : Fin 3 -> Int) (D : ENNReal)
    (hKT : IsKatzTao D S.activeCoarseFamily) :
    IsKatzTao D (selectedParentPlankBucketFamily e S B hrho label) := by
  have hblock : IsKatzTao D
      (selectedCoarseFamily S.activeCoarseFamily B) :=
    isKatzTao_selectedCoarseFamily_of_isKatzTaoOn (hKT.on B)
  have haffine : IsKatzTao D
      (selectedParentAffineFamily
        (bucketNormalizedAffineEquiv e label) S B) := by
    exact isKatzTao_affineImageFamily
      (bucketNormalizedAffineEquiv e label)
      (selectedCoarseFamily S.activeCoarseFamily B) hblock
  exact isKatzTao_selectedCoarseFamily_of_isKatzTaoOn
    (haffine.on (selectedParentPlankBucketIndices e S B hrho label))

/-- Actual selected-parent Córdoba endpoint with automatic certificates and
automatic KT transport. -/
theorem selectedParentPlankBucket_averageMultiplicity_le
    {kappa : Type v} [DecidableEq kappa]
    (e : Space ≃ᵃ[Real] Space) (S : StickyScaleCover fine rho)
    (Y : Shading fine.bodyFamily)
    (B : Finset (ActiveParentIndex S)) (hrho : 0 < rho)
    (label : Fin 3 -> Int)
    (hplank : forall p : {p // p ∈ B},
      p ∈ selectedParentPlankBucketIndices e S B hrho label ->
        IsPlank 576 (bucketShortA label) (bucketShortB label)
          (selectedParentAffineFamily
            (bucketNormalizedAffineEquiv e label) S B p))
    (levels : Finset kappa)
    (level :
      {p // p ∈ selectedParentPlankBucketIndices e S B hrho label} ->
      {p // p ∈ selectedParentPlankBucketIndices e S B hrho label} ->
        Option kappa)
    (inverseSineWeight : kappa -> ENNReal)
    (container :
      {p // p ∈ selectedParentPlankBucketIndices e S B hrho label} ->
      Option kappa -> ConvexBody Space)
    (D A : ENNReal)
    (hlevel : forall i j, level i j ∈ plankAngleLevels levels)
    (htransverse : forall i j k, level i j = some k ->
      0 < certifiedPlankPairSine
        (chosenPlankCertificate
          (selectedParentPlankBucket_isPlank e S B hrho label hplank)) i j)
    (hinverse : forall i j k, level i j = some k ->
      ENNReal.ofReal
          ((certifiedPlankPairSine
            (chosenPlankCertificate
              (selectedParentPlankBucket_isPlank
                e S B hrho label hplank)) i j)⁻¹) <=
        inverseSineWeight k)
    (hcontained : forall i j,
      (selectedParentPlankBucketFamily e S B hrho label j : Set Space) ⊆
        (container i (level i j) : Set Space))
    (hKT : IsKatzTao D S.activeCoarseFamily)
    (hscale : forall i k, k ∈ plankAngleLevels levels ->
      certifiedPlankAngleScale 576 (bucketShortA label)
          (bucketShortB label) inverseSineWeight k *
          volume (container i k : Set Space) <=
        A * volume
          ((selectedParentPlankBucketShading e S Y B hrho label).carrier i)) :
    (selectedParentPlankBucketShading e S Y B hrho label).averageMultiplicity <=
      certifiedPlankDyadicFactor levels D A := by
  apply certifiedPlankDyadic_averageMultiplicity_le_of_isPlank
    (selectedParentPlankBucket_isPlank e S B hrho label hplank)
    levels level inverseSineWeight container D A hlevel htransverse
    hinverse hcontained
  · exact selectedParentPlankBucket_isKatzTao e S B hrho label D hKT
  · exact hscale

#print axioms chosenPlankCertificate
#print axioms certifiedPlankDyadic_averageMultiplicity_le_of_isPlank
#print axioms selectedParentPlankBucket_isPlank
#print axioms selectedParentPlankBucket_isKatzTao
#print axioms selectedParentPlankBucket_averageMultiplicity_le

end

end Family8SelectedParentCertifiedPlankCordobaConnectorV3
