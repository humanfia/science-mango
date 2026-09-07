import Family8Grounding.Family8SelectedParentCertifiedPlankCordobaThresholdedAngleV6
import Submission.Kakeya.ConvexFactoring.FrameBoxVolume

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 4000000

open Set MeasureTheory
open scoped ENNReal NNReal BigOperators

namespace Family8SelectedParentCertifiedPlankCordobaActualJohnContainerV7

open LeanEval.Analysis.WangZahlKakeya
open Submission.Kakeya.ConvexGeometry
open Submission.Kakeya.ConvexFactoring
open Submission.Kakeya.ConvexFactoring.FullConvexMaximalDensity
open Submission.Kakeya.ConvexFactoring.GreedyOccurrenceFactorization
open Submission.Kakeya.ConvexFactoring.HeavyParentSelection
open Submission.Kakeya.Uniformity
open Family8CertifiedPlankDyadicCordobaV2
open Family8SelectedParentCertifiedPlankCordobaConnectorV3
open Family8SelectedParentCertifiedPlankCordobaThresholdedAngleV6
open Family8SelectedParentAffineShadingTransportV4
open Family8SelectedParentJohnFrameNormalizationV9
open Family8SelectedParentJohnPlankSideWidthBridgeV4
open Family8SelectedParentJohnPlankSideWidthBridgeV5
open Family8SelectedParentJohnPlankSideWidthBridgeV7
open Family8SelectedParentJohnPlankSideWidthBridgeV8
open Family8StickySelectedParentGreedyBlockFrostmanV3
open FamilyStickyAtEveryScaleCoreV1
open Family8SelectedParentJohnBoxAffineTransportV16

noncomputable section

/-!
# Actual common John container for the thresholded Córdoba rows

For a literal V9 side bucket, the contracted winning-hull John box contains
every parent before bucket normalization.  Transporting that same box by the
actual scalar part of `bucketNormalizedAffineEquiv` produces one common
container of side `r / sideShapeUpper label 2`; its volume is exactly the
cube of that side.  Combining this with V6 removes the row-scale callback
from the actual selected-parent Córdoba endpoint.
-/

variable {delta rho : NNReal} {index : Type}
  [Fintype index] [DecidableEq index]
  {fine : UniformTubeFamily delta index}

/-- The actual common container after the side-bucket scalar normalization. -/
noncomputable def selectedParentBucketNormalizedJohnContainer
    (S : StickyScaleCover fine rho) (hrho : 0 < rho)
    (P : GreedyDensityPartition S.activeCoarseFamily
      (hullCandidates (Finset.univ : Finset (ActiveParentIndex S)))
      (hullContainer S.activeCoarseFamily) Finset.univ)
    (k : Fin (blocks S.activeCoarseFamily P).length)
    (r : NNReal) (label : Fin 3 → Int) : ConvexBody Space :=
  (normalizedJohnBox (selectedParentGreedyBlockJohnFrame S hrho P k)
    ((sideShapeUpper label 2)⁻¹ * r)).body

theorem volume_selectedParentBucketNormalizedJohnContainer
    (S : StickyScaleCover fine rho) (hrho : 0 < rho)
    (P : GreedyDensityPartition S.activeCoarseFamily
      (hullCandidates (Finset.univ : Finset (ActiveParentIndex S)))
      (hullContainer S.activeCoarseFamily) Finset.univ)
    (k : Fin (blocks S.activeCoarseFamily P).length)
    (r : NNReal) (label : Fin 3 → Int) :
    volume (selectedParentBucketNormalizedJohnContainer
      S hrho P k r label : Set Space) =
      ((((sideShapeUpper label 2)⁻¹ * r : NNReal) : ENNReal) ^ 3) := by
  unfold selectedParentBucketNormalizedJohnContainer
  rw [FrameBox.volume_body]
  simp only [Fin.prod_univ_three,
    Family8SelectedParentJohnBoxAffineTransportV16.normalizedJohnBox_side,
    ENNReal.coe_mul]
  ring

/-- Every actual member of the literal plank bucket lies in that one
transported winning-hull John box. -/
theorem selectedParentPlankBucketFamily_subset_normalizedJohnContainer
    (S : StickyScaleCover fine rho) (hrho : 0 < rho)
    (P : GreedyDensityPartition S.activeCoarseFamily
      (hullCandidates (Finset.univ : Finset (ActiveParentIndex S)))
      (hullContainer S.activeCoarseFamily) Finset.univ)
    (k : Fin (blocks S.activeCoarseFamily P).length)
    (r : NNReal) (hr : 0 < r) (label : Fin 3 → Int)
    (q : {p // p ∈ selectedParentPlankBucketIndices
      (contractedJohnAffineEquiv
        (selectedParentGreedyBlockJohnFrame S hrho P k) r hr)
      S (blockAt S.activeCoarseFamily P k).fiber hrho label}) :
    (selectedParentPlankBucketFamily
        (contractedJohnAffineEquiv
          (selectedParentGreedyBlockJohnFrame S hrho P k) r hr)
        S (blockAt S.activeCoarseFamily P k).fiber hrho label q : Set Space) ⊆
      (selectedParentBucketNormalizedJohnContainer
        S hrho P k r label : Set Space) := by
  let J := selectedParentGreedyBlockJohnFrame S hrho P k
  let e := contractedJohnAffineEquiv J r hr
  let B := (blockAt S.activeCoarseFamily P k).fiber
  let t := (sideShapeUpper label 2)⁻¹
  let d := scalarDilationAffineEquiv t
    (inv_pos.mpr (sideShapeUpper_pos label 2))
  intro x hx
  change x ∈ (selectedParentAffineFamily
    (bucketNormalizedAffineEquiv e label) S B q.1 : Set Space) at hx
  rw [selectedParentAffineFamily_apply] at hx
  rcases hx with ⟨y, hy, rfl⟩
  have hey : e y ∈ (normalizedJohnBox J r).carrier :=
    selectedParentContracted_subset_normalizedJohnBox
      S hrho P k r hr q.1 ⟨y, hy, rfl⟩
  have hdy : d (e y) ∈ d '' (normalizedJohnBox J r).carrier :=
    ⟨e y, hey, rfl⟩
  have himage := scalarDilation_image_normalizedJohnBox J t
    (inv_pos.mpr (sideShapeUpper_pos label 2)) r
  rw [himage] at hdy
  change (bucketNormalizedAffineEquiv e label) y ∈
    ((normalizedJohnBox J (t * r)).body : Set Space)
  rw [FrameBox.coe_body]
  simpa [bucketNormalizedAffineEquiv, e, d, t] using hdy

/-- Actual selected-parent endpoint with the common John container and all
angle data automatic.  The only row-density input is the primitive carrier
floor that a subsequent popularity restriction must supply. -/
theorem selectedParentPlankBucket_averageMultiplicity_le_thresholdedJohn
    (S : StickyScaleCover fine rho) (hrho : 0 < rho)
    (Y : Shading fine.bodyFamily)
    (P : GreedyDensityPartition S.activeCoarseFamily
      (hullCandidates (Finset.univ : Finset (ActiveParentIndex S)))
      (hullContainer S.activeCoarseFamily) Finset.univ)
    (k : Fin (blocks S.activeCoarseFamily P).length)
    (r : NNReal) (hr : 0 < r) (label : Fin 3 → Int)
    (hplank : ∀ p : {p // p ∈ (blockAt S.activeCoarseFamily P k).fiber},
      p ∈ selectedParentPlankBucketIndices
          (contractedJohnAffineEquiv
            (selectedParentGreedyBlockJohnFrame S hrho P k) r hr)
          S (blockAt S.activeCoarseFamily P k).fiber hrho label →
        IsPlank 576 (bucketShortA label) (bucketShortB label)
          (selectedParentAffineFamily
            (bucketNormalizedAffineEquiv
              (contractedJohnAffineEquiv
                (selectedParentGreedyBlockJohnFrame S hrho P k) r hr)
              label)
            S (blockAt S.activeCoarseFamily P k).fiber p))
    (lower : ENNReal) (hlower0 : lower ≠ 0) (hlowerTop : lower ≠ ∞)
    (hfloor : ∀ q, lower ≤ volume
      ((selectedParentPlankBucketShading
        (contractedJohnAffineEquiv
          (selectedParentGreedyBlockJohnFrame S hrho P k) r hr)
        S Y (blockAt S.activeCoarseFamily P k).fiber hrho label).carrier q))
    (D : ENNReal) (hKT : IsKatzTao D S.activeCoarseFamily) :
    (selectedParentPlankBucketShading
      (contractedJohnAffineEquiv
        (selectedParentGreedyBlockJohnFrame S hrho P k) r hr)
      S Y (blockAt S.activeCoarseFamily P k).fiber hrho label).averageMultiplicity ≤
      let cert := chosenPlankCertificate
        (selectedParentPlankBucket_isPlank
          (contractedJohnAffineEquiv
            (selectedParentGreedyBlockJohnFrame S hrho P k) r hr)
          S (blockAt S.activeCoarseFamily P k).fiber hrho label hplank)
      certifiedPlankDyadicFactor (certifiedPlankThresholdedLevels cert) D
        (certifiedPlankThresholdedAngleScaleCap 576 *
          (((((sideShapeUpper label 2)⁻¹ * r : NNReal) : ENNReal) ^ 3) /
            lower)) := by
  dsimp only
  let e := contractedJohnAffineEquiv
    (selectedParentGreedyBlockJohnFrame S hrho P k) r hr
  let B := (blockAt S.activeCoarseFamily P k).fiber

  let Y' := selectedParentPlankBucketShading e S Y B hrho label
  let cert := chosenPlankCertificate
    (selectedParentPlankBucket_isPlank e S B hrho label hplank)
  have hfloor' : ∀ q, lower ≤ volume (Y'.carrier q) := by
    intro q
    change lower ≤ volume
      ((selectedParentPlankBucketShading
        (contractedJohnAffineEquiv
          (selectedParentGreedyBlockJohnFrame S hrho P k) r hr)
        S Y (blockAt S.activeCoarseFamily P k).fiber hrho label).carrier q)
    exact hfloor q
  have hresult := certifiedPlankThresholded_averageMultiplicity_le_globalContainer
    cert Y' (selectedParentBucketNormalizedJohnContainer S hrho P k r label)
    (selectedParentPlankBucketFamily_subset_normalizedJohnContainer
      S hrho P k r hr label)
    lower hlower0 hlowerTop hfloor' D
    (selectedParentPlankBucket_isKatzTao e S B hrho label D hKT)
  rw [volume_selectedParentBucketNormalizedJohnContainer] at hresult
  simpa [e, B, Y', cert] using hresult

#print axioms volume_selectedParentBucketNormalizedJohnContainer
#print axioms selectedParentPlankBucketFamily_subset_normalizedJohnContainer
#print axioms selectedParentPlankBucket_averageMultiplicity_le_thresholdedJohn

end
end Family8SelectedParentCertifiedPlankCordobaActualJohnContainerV7
