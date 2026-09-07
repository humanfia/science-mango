import Family8Grounding.Family8SelectedOccurrenceMaxOwnerHullJohnPlankProducerV1
import Family8Grounding.Family8SelectedOccurrenceMaxOwnerHullFrostmanProducerV3
import Family8Grounding.Family8SelectedParentAffineShadingTransportV4
import Family6Grounding.Family6AffinePlankAnalyticHypothesesStableV1
import Mathlib.Tactic

/-!
# The common-scale max-owner hull datum

This file upgrades the memberwise conclusion of the John/plank producer to
one actual finite family.  A literal side-label fibre is pulled back to an
occurrence-position finset.  Every retained body and shaded carrier is then
sent through the same scalar affine equivalence.  Consequently overlap and
average multiplicity are transported on one common coordinate space.

The generic affine Frostman lemma below is exact: both contained masses and
both test-body volumes acquire the same Jacobian factors.  It is included so
that the normalized family can be used by the paper input without accepting
a new Frostman callback.
-/

open Set MeasureTheory
open scoped BigOperators ENNReal NNReal InnerProductSpace

namespace Family8SelectedOccurrenceMaxOwnerHullCommonScaleDatumV1

open LeanEval.Analysis.WangZahlKakeya
open Submission.Kakeya.ConvexGeometry
open Submission.Kakeya.ConvexFactoring
open Submission.Kakeya.ConvexFactoring.FullConvexMaximalDensity
open Submission.Kakeya.ConvexFactoring.GreedyOccurrenceFactorization
open Submission.Kakeya.Uniformity
open Family6AffineConvexVolumeCoreV1
open Family6AffinePlankAnalyticHypothesesStableV1
open Family8SelectedOccurrenceActiveParentOwnerV7
open Family8SelectedOccurrenceDensityFrostmanV1
open Family8SelectedOccurrenceMaxOwnerHullAggregateV2
open Family8SelectedOccurrenceMaxOwnerHullCommonScaleDatumV1
open Family8SelectedOccurrenceMaxOwnerHullJohnPlankProducerV1
open Family8SelectedOccurrenceMaxOwnerHullQualityV3
open Family8SelectedParentAffineShadingTransportV4
open Family8SelectedParentJohnPlankSideWidthBridgeV5
open Family8SelectedParentJohnPlankSideWidthBridgeV7
open FamilyStickyAtEveryScaleCoreV1
open FamilyStickyCinematicL32FiniteWeightedBucketV1

noncomputable section

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 5000000

local instance (p : Prop) : Decidable p := Classical.propDecidable p

universe u

/-! ## Generic exact affine transport of contained mass and Frostman data -/

theorem containedIndices_affineImageFamily_eq
    {iota : Type u} [Fintype iota]
    (e : Space ≃ᵃ[Real] Space) (F : ConvexFamily iota)
    (K : ConvexBody Space) :
    containedIndices (affineImageFamily e F) K =
      containedIndices F (affinePreimageConvexBody e K) := by
  classical
  ext i
  rw [mem_containedIndices, mem_containedIndices]
  exact affineImage_subset_iff_subset_preimage e
    (F i : Set Space) (K : Set Space)

/-- Every member volume and the containment predicate transport exactly. -/
theorem containedMass_affineImageFamily
    {iota : Type u} [Fintype iota]
    (e : Space ≃ᵃ[Real] Space) (F : ConvexFamily iota)
    (K : ConvexBody Space) :
    containedMass (affineImageFamily e F) K =
      affineJacobian e *
        containedMass F (affinePreimageConvexBody e K) := by
  classical
  unfold containedMass
  rw [containedIndices_affineImageFamily_eq]
  simp_rw [affineImageFamily_apply, volume_affineImageConvexBody]
  rw [Finset.mul_sum]

theorem affinePreimageConvexBody_affineImageConvexBody
    (e : Space ≃ᵃ[Real] Space) (K : ConvexBody Space) :
    affinePreimageConvexBody e (affineImageConvexBody e K) = K := by
  apply ConvexBody.ext
  ext x
  constructor
  · rintro ⟨y, ⟨z, hz, rfl⟩, hzx⟩
    have : z = x := by
      apply e.injective
      simpa using hzx
    simpa [this] using hz
  · intro hx
    exact ⟨e x, ⟨x, hx, rfl⟩, e.symm_apply_apply x⟩

/-- Frostman nonconcentration is invariant when a family and its ambient
body are transported by one affine equivalence. -/
theorem IsFrostmanIn.affineImage
    {iota : Type u} [Fintype iota]
    {CF : ENNReal} {F : ConvexFamily iota} {ambient : ConvexBody Space}
    (e : Space ≃ᵃ[Real] Space)
    (hF : IsFrostmanIn CF F ambient) :
    IsFrostmanIn CF (affineImageFamily e F)
      (affineImageConvexBody e ambient) := by
  refine ⟨?_, ?_⟩
  · intro i
    exact Set.image_mono (hF.1 i)
  · intro K hK
    let Kpre := affinePreimageConvexBody e K
    have hKpre : (Kpre : Set Space) ⊆ (ambient : Set Space) := by
      intro x hx
      have hex : e x ∈ (K : Set Space) := by
        rw [← image_affinePreimageConvexBody e K]
        exact ⟨x, hx, rfl⟩
      have himage := hK hex
      rcases himage with ⟨y, hy, hey⟩
      have hyx : y = x := by
        apply e.injective
        simpa using hey
      simpa [hyx] using hy
    have hsource := hF.2 Kpre hKpre
    let J := affineJacobian e
    calc
      containedMass (affineImageFamily e F) K *
          volume (affineImageConvexBody e ambient : Set Space) =
        (J * containedMass F Kpre) *
          (J * volume (ambient : Set Space)) := by
            rw [containedMass_affineImageFamily,
              volume_affineImageConvexBody]
      _ = (J * J) *
          (containedMass F Kpre * volume (ambient : Set Space)) := by
            ac_rfl
      _ ≤ (J * J) *
          (CF * containedMass F ambient * volume (Kpre : Set Space)) := by
            exact mul_le_mul_of_nonneg_left hsource bot_le
      _ = CF *
          (J * containedMass F ambient) *
            (J * volume (Kpre : Set Space)) := by ac_rfl
      _ = CF * containedMass (affineImageFamily e F)
          (affineImageConvexBody e ambient) * volume (K : Set Space) := by
            rw [containedMass_affineImageFamily,
              affinePreimageConvexBody_affineImageConvexBody,
              volume_eq_affineJacobian_mul_preimage e K]

/-! ## The actual common-label occurrence refinement -/

variable {delta rho : NNReal} {index : Type}
  [Fintype index] [DecidableEq index]
  {fine : UniformTubeFamily delta index}
  (C : StickyScaleCover fine rho)
  (P : GreedyDensityPartition fine.bodyFamily
    (hullCandidates C.activeFine) (hullContainer fine.bodyFamily)
    C.activeFine)
  (Y : Shading fine.bodyFamily)

/-- Occurrence positions lying in one literal John-side label fibre. -/
def occurrenceMaxOwnerHullSideBucketPositions
    (hdelta : 0 < delta)
    (R : Finset (Fin (blocks fine.bodyFamily P).length))
    (label : Fin 3 → Int) :
    Finset (Fin (blocks fine.bodyFamily P).length) :=
  R.filter fun k ↦
    sideShapeLabel (occurrenceMaxOwnerHullLongSide C P Y hdelta k) = label

@[simp] theorem mem_occurrenceMaxOwnerHullSideBucketPositions
    (hdelta : 0 < delta)
    (R : Finset (Fin (blocks fine.bodyFamily P).length))
    (label : Fin 3 → Int)
    (k : Fin (blocks fine.bodyFamily P).length) :
    k ∈ occurrenceMaxOwnerHullSideBucketPositions C P Y hdelta R label ↔
      k ∈ R ∧
        sideShapeLabel (occurrenceMaxOwnerHullLongSide C P Y hdelta k) =
          label := by
  simp [occurrenceMaxOwnerHullSideBucketPositions]

theorem occurrenceMaxOwnerHullSideBucketPositions_nonempty
    (hdelta : 0 < delta)
    (R : Finset (Fin (blocks fine.bodyFamily P).length))
    (label : Fin 3 → Int)
    (hlabel : label ∈ occupiedWeightBuckets
      (Finset.univ : Finset {k // k ∈ R})
      (fun k ↦ sideShapeLabel
        (selectedOccurrenceMaxOwnerHullLongSide C P Y hdelta R k))) :
    (occurrenceMaxOwnerHullSideBucketPositions C P Y hdelta R label).Nonempty := by
  rcases mem_occupiedWeightBuckets_iff.mp hlabel with ⟨k, _hk, hkLabel⟩
  exact ⟨k.1, (mem_occurrenceMaxOwnerHullSideBucketPositions
    C P Y hdelta R label k.1).2 ⟨k.2, hkLabel⟩⟩

/-- The one affine equivalence shared by every member of this bucket. -/
def occurrenceMaxOwnerHullCommonScaleEquiv (label : Fin 3 → Int) :
    Space ≃ᵃ[Real] Space :=
  scalarDilationAffineEquiv
    (sideShapeUpper label 2)⁻¹
    (inv_pos.mpr (sideShapeUpper_pos label 2))

/-- Actual retained max-owner hulls in the common normalized coordinates. -/
abbrev selectedOccurrenceMaxOwnerHullCommonScaleFamily
    (label : Fin 3 → Int)
    (S : Finset (Fin (blocks fine.bodyFamily P).length)) :
    ConvexFamily {q // q ∈ selectedOccurrenceIndices P S} :=
  affineImageFamily (occurrenceMaxOwnerHullCommonScaleEquiv label)
    (selectedOccurrenceMaxOwnerHullFamily C P Y S)

/-- Literal image of the actual max-owner shading under the same map. -/
def selectedOccurrenceMaxOwnerHullCommonScaleShading
    (label : Fin 3 → Int)
    (S : Finset (Fin (blocks fine.bodyFamily P).length)) :
    Shading (selectedOccurrenceMaxOwnerHullCommonScaleFamily C P Y label S) :=
  affineImageShading (occurrenceMaxOwnerHullCommonScaleEquiv label)
    (selectedOccurrenceMaxOwnerHullShading C P Y S)

@[simp] theorem selectedOccurrenceMaxOwnerHullCommonScaleFamily_apply
    (label : Fin 3 → Int)
    (S : Finset (Fin (blocks fine.bodyFamily P).length))
    (q : {q // q ∈ selectedOccurrenceIndices P S}) :
    selectedOccurrenceMaxOwnerHullCommonScaleFamily C P Y label S q =
      occurrenceMaxOwnerHullBucketNormalized C P Y label
        (selectedOccurrencePosition C S q) := rfl

@[simp] theorem selectedOccurrenceMaxOwnerHullCommonScaleShading_carrier
    (label : Fin 3 → Int)
    (S : Finset (Fin (blocks fine.bodyFamily P).length))
    (q : {q // q ∈ selectedOccurrenceIndices P S}) :
    (selectedOccurrenceMaxOwnerHullCommonScaleShading C P Y label S).carrier q =
      occurrenceMaxOwnerHullCommonScaleEquiv label ''
        (selectedOccurrenceMaxOwnerHullShading C P Y S).carrier q := rfl

/-- A literal common-label position set produces the uniform plank field on
the same common-coordinate family. -/
theorem selectedOccurrenceMaxOwnerHullCommonScale_all_isPlank
    (hdelta : 0 < delta)
    (label : Fin 3 → Int)
    (S : Finset (Fin (blocks fine.bodyFamily P).length))
    (hlabel : ∀ k ∈ S,
      sideShapeLabel (occurrenceMaxOwnerHullLongSide C P Y hdelta k) = label)
    (q : {q // q ∈ selectedOccurrenceIndices P S}) :
    IsPlank 576 (bucketShortA label) (bucketShortB label)
      (selectedOccurrenceMaxOwnerHullCommonScaleFamily C P Y label S q) := by
  let k := selectedOccurrencePosition C S q
  have hk := selectedOccurrencePosition_mem C S q
  have hkLabel := hlabel k hk
  have hpos : ∀ i, 0 < occurrenceMaxOwnerHullLongSide C P Y hdelta k i :=
    fun i ↦ occurrenceMaxOwnerHullLongSide_pos C P Y hdelta k i
  have h02 := sideShapeUpper_le_of_side_le hpos
    (occurrenceMaxOwnerHullLongSide_le_two C P Y hdelta k 0)
  have h12 := sideShapeUpper_le_of_side_le hpos
    (occurrenceMaxOwnerHullLongSide_le_two C P Y hdelta k 1)
  rw [hkLabel] at h02 h12
  have hband0 := sideShapeUpper_half_lt_and_le hpos
  have hband : ∀ i,
      sideShapeUpper label i / 2 <
          occurrenceMaxOwnerHullLongSide C P Y hdelta k i ∧
        occurrenceMaxOwnerHullLongSide C P Y hdelta k i ≤
          sideShapeUpper label i := by
    intro i
    simpa only [hkLabel] using hband0 i
  rw [selectedOccurrenceMaxOwnerHullCommonScaleFamily_apply]
  exact occurrenceMaxOwnerHullBucketNormalized_isPlank C P Y hdelta label k
    (bucketShortB_le_one label h02 h12) hband

theorem selectedOccurrenceMaxOwnerHullSideBucketCommonScale_all_isPlank
    (hdelta : 0 < delta)
    (R : Finset (Fin (blocks fine.bodyFamily P).length))
    (label : Fin 3 → Int)
    (q : {q // q ∈ selectedOccurrenceIndices P
      (occurrenceMaxOwnerHullSideBucketPositions C P Y hdelta R label)}) :
    IsPlank 576 (bucketShortA label) (bucketShortB label)
      (selectedOccurrenceMaxOwnerHullCommonScaleFamily C P Y label
        (occurrenceMaxOwnerHullSideBucketPositions C P Y hdelta R label) q) := by
  apply selectedOccurrenceMaxOwnerHullCommonScale_all_isPlank C P Y hdelta
  intro k hk
  exact (mem_occurrenceMaxOwnerHullSideBucketPositions
    C P Y hdelta R label k).1 hk |>.2

/-- Common affine transport preserves the selected actual average exactly. -/
theorem selectedOccurrenceMaxOwnerHullCommonScale_averageMultiplicity
    (label : Fin 3 → Int)
    (S : Finset (Fin (blocks fine.bodyFamily P).length)) :
    (selectedOccurrenceMaxOwnerHullCommonScaleShading C P Y label S).averageMultiplicity =
      (selectedOccurrenceMaxOwnerHullShading C P Y S).averageMultiplicity :=
  affineImageShading_averageMultiplicity
    (occurrenceMaxOwnerHullCommonScaleEquiv label)
    (selectedOccurrenceMaxOwnerHullShading C P Y S)

/-- The existing actual max-owner Frostman theorem transports without any
change of constant when the ambient is sent through the same common map. -/
theorem selectedOccurrenceMaxOwnerHullCommonScale_isFrostmanIn
    {CF : ENNReal}
    (label : Fin 3 → Int)
    (S : Finset (Fin (blocks fine.bodyFamily P).length))
    (ambient : ConvexBody Space)
    (hF : IsFrostmanIn CF
      (selectedOccurrenceMaxOwnerHullFamily C P Y S) ambient) :
    IsFrostmanIn CF
      (selectedOccurrenceMaxOwnerHullCommonScaleFamily C P Y label S)
      (affineImageConvexBody
        (occurrenceMaxOwnerHullCommonScaleEquiv label) ambient) :=
  IsFrostmanIn.affineImage
    (occurrenceMaxOwnerHullCommonScaleEquiv label) hF

/-- The normalized actual family as a Family 6 datum.  Its memberwise plank
field is produced above; only the ambient normalization is supplied by the
caller because the ambient chosen upstream is independent of the side
bucket. -/
def selectedOccurrenceMaxOwnerHullCommonScaleDatum
    (hdelta : 0 < delta)
    (label : Fin 3 → Int)
    (S : Finset (Fin (blocks fine.bodyFamily P).length))
    (hlabel : ∀ k ∈ S,
      sideShapeLabel (occurrenceMaxOwnerHullLongSide C P Y hdelta k) = label)
    (ambient : ConvexBody Space) (ambientComparisonConstant : NNReal)
    (ambient_is_unit_scale : IsPlank ambientComparisonConstant 1 1
      (affineImageConvexBody
        (occurrenceMaxOwnerHullCommonScaleEquiv label) ambient))
    (contained_in_ambient : ∀ q,
      (selectedOccurrenceMaxOwnerHullFamily C P Y S q : Set Space) ⊆
        (ambient : Set Space)) :
    ShadedConvexPlankFamily
      {q // q ∈ selectedOccurrenceIndices P S}
      (bucketShortA label) (bucketShortB label) where
  family := selectedOccurrenceMaxOwnerHullCommonScaleFamily C P Y label S
  shading := selectedOccurrenceMaxOwnerHullCommonScaleShading C P Y label S
  comparisonConstant := 576
  all_isPlank := selectedOccurrenceMaxOwnerHullCommonScale_all_isPlank
    C P Y hdelta label S hlabel
  ambient := affineImageConvexBody
    (occurrenceMaxOwnerHullCommonScaleEquiv label) ambient
  ambientComparisonConstant := ambientComparisonConstant
  ambient_is_unit_scale := ambient_is_unit_scale
  contained_in_ambient q := Set.image_mono (contained_in_ambient q)

#print axioms containedIndices_affineImageFamily_eq
#print axioms containedMass_affineImageFamily
#print axioms affinePreimageConvexBody_affineImageConvexBody
#print axioms IsFrostmanIn.affineImage
#print axioms occurrenceMaxOwnerHullSideBucketPositions_nonempty
#print axioms selectedOccurrenceMaxOwnerHullCommonScale_all_isPlank
#print axioms selectedOccurrenceMaxOwnerHullSideBucketCommonScale_all_isPlank
#print axioms selectedOccurrenceMaxOwnerHullCommonScale_averageMultiplicity
#print axioms selectedOccurrenceMaxOwnerHullCommonScale_isFrostmanIn
#print axioms selectedOccurrenceMaxOwnerHullCommonScaleDatum

end
end Family8SelectedOccurrenceMaxOwnerHullCommonScaleDatumV1
