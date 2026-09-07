import Family8Grounding.Family8SelectedParentCertifiedPlankCordobaConnectorV3
import FamilyStickyCinematicL32Lemma57DyadicCeilBucketV1
import Submission.Kakeya.ConvexFactoring.FullConvexMaximalDensity
import Mathlib.Tactic

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 4000000

open Set MeasureTheory
open scoped ENNReal NNReal BigOperators

namespace Family8SelectedParentCertifiedPlankCordobaConnectorV4

open LeanEval.Analysis.WangZahlKakeya
open Submission.Kakeya.ConvexGeometry
open Submission.Kakeya.ConvexFactoring
open Submission.Kakeya.ConvexFactoring.FullConvexMaximalDensity
open Submission.Kakeya.Uniformity
open Submission.Kakeya.ConvexFactoring.GreedyOccurrenceFactorization
open Submission.Kakeya.ConvexFactoring.HeavyParentSelection
open Family8CertifiedPlankDyadicCordobaV2
open Family8CertifiedPlankPairOverlapV2
open Family8SelectedParentCertifiedPlankCordobaConnectorV3
open Family8SelectedParentJohnPlankSideWidthBridgeV4
open Family8SelectedParentAffineShadingTransportV4
open Family8StickySelectedParentGreedyBlockFrostmanV3
open Family8SelectedParentJohnPlankSideWidthBridgeV5
open Family8SelectedParentJohnPlankSideWidthBridgeV7
open Family8SelectedParentJohnPlankSideWidthBridgeV8
open FamilyStickyAtEveryScaleCoreV1
open FamilyStickyCinematicL32Lemma57DyadicCeilBucketV1

noncomputable section

/-!
# Canonical dyadic angles and row hulls for the actual plank bucket

For every positive certified pair sine, take the literal
`ceil (log_2 (sin(angle)⁻¹))` label and its dyadic upper endpoint.  Nonpositive
pairs form the exceptional level.  For a fixed row and level, the container
is the closed convex hull of exactly the full bodies assigned to that level.
Thus angle assignment, transversality, inverse-sine domination, and body
containment are all produced from the actual certificates.

The only quantitative geometry left is one scalar: the finite supremum of
`angleScale * rowHullVolume / rowShadingVolume`.  A finite upper bound for
this explicit scalar automatically rules out zero-volume rows and supplies
the rowwise scale premise.  This is strictly narrower than V3's five
function-valued premises and is the paper-faithful remaining container seam.
-/

universe u

variable {iota : Type u} [Fintype iota]
variable {F : ConvexFamily iota} {Y : Shading F}
variable {C a b : NNReal}

/-- Literal exceptional-or-dyadic assignment from the certified pair sine. -/
noncomputable def certifiedPlankDyadicPairLevel
    (cert : ∀ i, PlankDimensionsCertificate C a b (F i))
    (i j : iota) : Option Int :=
  if 0 < certifiedPlankPairSine cert i j then
    some (dyadicCeilBucket ((certifiedPlankPairSine cert i j)⁻¹))
  else none

/-- The finite set of all pair-generated integer labels.  Labels belonging
to exceptional pairs may be present but are harmless empty row levels. -/
noncomputable def certifiedPlankDyadicLevels
    (cert : ∀ i, PlankDimensionsCertificate C a b (F i)) : Finset Int := by
  classical
  exact (Finset.univ : Finset (iota × iota)).image fun ij ↦
    dyadicCeilBucket ((certifiedPlankPairSine cert ij.1 ij.2)⁻¹)

/-- Dyadic upper endpoint used as the genuine-level inverse-sine weight. -/
def certifiedPlankDyadicInverseSineWeight (k : Int) : ENNReal :=
  ENNReal.ofReal (dyadicCeilUpper k)

/-- Members assigned to one literal row-angle level. -/
noncomputable def certifiedPlankDyadicRowIndices
    (cert : ∀ i, PlankDimensionsCertificate C a b (F i))
    (i : iota) (k : Option Int) : Finset iota := by
  classical
  exact Finset.univ.filter fun j ↦ certifiedPlankDyadicPairLevel cert i j = k

@[simp]
theorem mem_certifiedPlankDyadicRowIndices
    (cert : ∀ i, PlankDimensionsCertificate C a b (F i))
    (i j : iota) (k : Option Int) :
    j ∈ certifiedPlankDyadicRowIndices cert i k ↔
      certifiedPlankDyadicPairLevel cert i j = k := by
  classical
  simp [certifiedPlankDyadicRowIndices]

/-- Closed convex hull of the full bodies in one actual row-angle class. -/
noncomputable def certifiedPlankDyadicHullContainer
    (cert : ∀ i, PlankDimensionsCertificate C a b (F i))
    (i : iota) (k : Option Int) : ConvexBody Space :=
  hullContainer F (certifiedPlankDyadicRowIndices cert i k)

theorem certifiedPlankDyadicPairLevel_mem
    (cert : ∀ i, PlankDimensionsCertificate C a b (F i))
    (i j : iota) :
    certifiedPlankDyadicPairLevel cert i j ∈
      plankAngleLevels (certifiedPlankDyadicLevels cert) := by
  classical
  by_cases hsin : 0 < certifiedPlankPairSine cert i j
  · simp [certifiedPlankDyadicPairLevel, hsin, plankAngleLevels,
      certifiedPlankDyadicLevels]
  · simp [certifiedPlankDyadicPairLevel, hsin, plankAngleLevels]

omit [Fintype iota] in
theorem certifiedPlankPairSine_pos_of_dyadicPairLevel_eq_some
    (cert : ∀ i, PlankDimensionsCertificate C a b (F i))
    (i j : iota) (k : Int)
    (hlevel : certifiedPlankDyadicPairLevel cert i j = some k) :
    0 < certifiedPlankPairSine cert i j := by
  unfold certifiedPlankDyadicPairLevel at hlevel
  split_ifs at hlevel with hsin
  · exact hsin

omit [Fintype iota] in
theorem certifiedPlankDyadic_inverseSine_le
    (cert : ∀ i, PlankDimensionsCertificate C a b (F i))
    (i j : iota) (k : Int)
    (hlevel : certifiedPlankDyadicPairLevel cert i j = some k) :
    ENNReal.ofReal ((certifiedPlankPairSine cert i j)⁻¹) ≤
      certifiedPlankDyadicInverseSineWeight k := by
  have hsin := certifiedPlankPairSine_pos_of_dyadicPairLevel_eq_some
    cert i j k hlevel
  unfold certifiedPlankDyadicPairLevel at hlevel
  rw [if_pos hsin] at hlevel
  injection hlevel with hk
  subst k
  unfold certifiedPlankDyadicInverseSineWeight
  exact ENNReal.ofReal_le_ofReal
    (dyadicCeilUpper_half_lt_and_le (inv_pos.mpr hsin)).2

theorem certifiedPlankDyadic_body_subset_hullContainer
    (cert : ∀ i, PlankDimensionsCertificate C a b (F i))
    (i j : iota) :
    (F j : Set Space) ⊆
      (certifiedPlankDyadicHullContainer cert i
        (certifiedPlankDyadicPairLevel cert i j) : Set Space) := by
  classical
  have hj : j ∈ certifiedPlankDyadicRowIndices cert i
      (certifiedPlankDyadicPairLevel cert i j) := by simp
  exact body_subset_hullContainer F hj ⟨j, hj⟩

omit [Fintype iota] in
theorem certifiedPlankDyadicPairLevel_self
    (cert : ∀ i, PlankDimensionsCertificate C a b (F i)) (i : iota) :
    certifiedPlankDyadicPairLevel cert i i = none := by
  have hframe : (cert i).box.frame 0 ≠ 0 := by
    intro hzero
    have hone := (cert i).box.frame.norm_eq_one 0
    rw [hzero, norm_zero] at hone
    norm_num at hone
  have hsine : certifiedPlankPairSine cert i i = 0 := by
    unfold certifiedPlankPairSine
    rw [InnerProductGeometry.angle_self hframe]
    simp
  simp [certifiedPlankDyadicPairLevel, hsine]

/-- The explicit finite row-angle scale factor. -/
noncomputable def canonicalCertifiedPlankAngleContainerScaleFactor
    (cert : ∀ i, PlankDimensionsCertificate C a b (F i))
    (Y : Shading F) : ENNReal :=
  ⨆ i : iota,
    ⨆ k : {k // k ∈ plankAngleLevels (certifiedPlankDyadicLevels cert)},
      certifiedPlankAngleScale C a b
          certifiedPlankDyadicInverseSineWeight k.1 *
        volume (certifiedPlankDyadicHullContainer cert i k.1 : Set Space) /
          volume (Y.carrier i)

theorem certifiedPlankAngleContainer_ratio_le_canonical
    (cert : ∀ i, PlankDimensionsCertificate C a b (F i))
    (Y : Shading F) (i : iota)
    (k : Option Int)
    (hk : k ∈ plankAngleLevels (certifiedPlankDyadicLevels cert)) :
    certifiedPlankAngleScale C a b
        certifiedPlankDyadicInverseSineWeight k *
      volume (certifiedPlankDyadicHullContainer cert i k : Set Space) /
        volume (Y.carrier i) ≤
      canonicalCertifiedPlankAngleContainerScaleFactor cert Y := by
  exact (le_iSup (fun j : iota ↦
    ⨆ l : {l // l ∈ plankAngleLevels (certifiedPlankDyadicLevels cert)},
      certifiedPlankAngleScale C a b
          certifiedPlankDyadicInverseSineWeight l.1 *
        volume (certifiedPlankDyadicHullContainer cert j l.1 : Set Space) /
          volume (Y.carrier j)) i).trans'
    (le_iSup (fun l : {l // l ∈
      plankAngleLevels (certifiedPlankDyadicLevels cert)} ↦
        certifiedPlankAngleScale C a b
            certifiedPlankDyadicInverseSineWeight l.1 *
          volume (certifiedPlankDyadicHullContainer cert i l.1 : Set Space) /
            volume (Y.carrier i)) ⟨k, hk⟩)

/-- A finite scalar upper bound automatically gives every V3 row-scale
inequality.  Finiteness also forces every row shading volume to be nonzero,
because the exceptional self-class contains the row's positive-volume full
plank body. -/
theorem certifiedPlankAngleContainer_scale_le_of_canonical_le
    (cert : ∀ i, PlankDimensionsCertificate C a b (F i))
    (Y : Shading F) (A : ENNReal) (hAfinite : A ≠ ∞)
    (hcanonical : canonicalCertifiedPlankAngleContainerScaleFactor cert Y ≤ A)
    (i : iota) (k : Option Int)
    (hk : k ∈ plankAngleLevels (certifiedPlankDyadicLevels cert)) :
    certifiedPlankAngleScale C a b
        certifiedPlankDyadicInverseSineWeight k *
      volume (certifiedPlankDyadicHullContainer cert i k : Set Space) ≤
        A * volume (Y.carrier i) := by
  have hcarrier : volume (Y.carrier i) ≠ 0 := by
    intro hzero
    have hi : i ∈ certifiedPlankDyadicRowIndices cert i none := by
      rw [mem_certifiedPlankDyadicRowIndices,
        certifiedPlankDyadicPairLevel_self]
    have hbody : (F i : Set Space) ⊆
        (certifiedPlankDyadicHullContainer cert i none : Set Space) :=
      body_subset_hullContainer F hi ⟨i, hi⟩
    have hcontainerPos : 0 <
        volume (certifiedPlankDyadicHullContainer cert i none : Set Space) :=
      (cert i).isPlank.volume_pos.trans_le (measure_mono hbody)
    have hnone : none ∈ plankAngleLevels (certifiedPlankDyadicLevels cert) := by
      simp [plankAngleLevels]
    have hratio := certifiedPlankAngleContainer_ratio_le_canonical
      cert Y i none hnone
    have hratioTop :
        certifiedPlankAngleScale C a b
            certifiedPlankDyadicInverseSineWeight none *
          volume (certifiedPlankDyadicHullContainer cert i none : Set Space) /
            volume (Y.carrier i) = ∞ := by
      rw [hzero]
      simpa only [certifiedPlankAngleScale, one_mul] using
        ENNReal.div_eq_top.mpr
          (Or.inl ⟨ne_of_gt hcontainerPos, rfl⟩)
    rw [hratioTop] at hratio
    have hfactorTop :
        canonicalCertifiedPlankAngleContainerScaleFactor cert Y = ∞ :=
      top_unique hratio
    have hAtop : A = ∞ := top_unique (hfactorTop ▸ hcanonical)
    exact hAfinite hAtop
  have hcarrierTop : volume (Y.carrier i) ≠ ∞ :=
    ((measure_mono (Y.carrier_subset i)).trans_lt
      (F i).isCompact.measure_lt_top).ne
  have hratio := certifiedPlankAngleContainer_ratio_le_canonical
    cert Y i k hk
  calc
    certifiedPlankAngleScale C a b
          certifiedPlankDyadicInverseSineWeight k *
        volume (certifiedPlankDyadicHullContainer cert i k : Set Space) =
        (certifiedPlankAngleScale C a b
            certifiedPlankDyadicInverseSineWeight k *
          volume (certifiedPlankDyadicHullContainer cert i k : Set Space) /
            volume (Y.carrier i)) * volume (Y.carrier i) :=
      (ENNReal.div_mul_cancel hcarrier hcarrierTop).symm
    _ ≤ canonicalCertifiedPlankAngleContainerScaleFactor cert Y *
        volume (Y.carrier i) := by gcongr
    _ ≤ A * volume (Y.carrier i) := by gcongr

variable {delta rho : NNReal} {index : Type}
  [Fintype index] [DecidableEq index]
  {fine : UniformTubeFamily delta index}

/-- V3 with all angle functions and containers instantiated canonically.
The sole remaining geometric premise is a finite scalar upper bound for the
literal row-angle hull ratio. -/
theorem selectedParentPlankBucket_averageMultiplicity_le_of_canonicalAngleScale
    (e : Space ≃ᵃ[Real] Space) (S : StickyScaleCover fine rho)
    (Y : Shading fine.bodyFamily)
    (B : Finset (ActiveParentIndex S)) (hrho : 0 < rho)
    (label : Fin 3 → Int)
    (hplank : ∀ p : {p // p ∈ B},
      p ∈ selectedParentPlankBucketIndices e S B hrho label →
        IsPlank 576 (bucketShortA label) (bucketShortB label)
          (selectedParentAffineFamily
            (bucketNormalizedAffineEquiv e label) S B p))
    (D A : ENNReal) (hAfinite : A ≠ ∞)
    (hcanonical :
      canonicalCertifiedPlankAngleContainerScaleFactor
        (chosenPlankCertificate
          (selectedParentPlankBucket_isPlank e S B hrho label hplank))
        (selectedParentPlankBucketShading e S Y B hrho label) ≤ A)
    (hKT : IsKatzTao D S.activeCoarseFamily) :
    (selectedParentPlankBucketShading e S Y B hrho label).averageMultiplicity ≤
      certifiedPlankDyadicFactor
        (certifiedPlankDyadicLevels
          (chosenPlankCertificate
            (selectedParentPlankBucket_isPlank e S B hrho label hplank))) D A := by
  let cert := chosenPlankCertificate
    (selectedParentPlankBucket_isPlank e S B hrho label hplank)
  apply selectedParentPlankBucket_averageMultiplicity_le
    (kappa := Int) e S Y B hrho label hplank
    (certifiedPlankDyadicLevels cert)
    (certifiedPlankDyadicPairLevel cert)
    certifiedPlankDyadicInverseSineWeight
    (certifiedPlankDyadicHullContainer cert) D A
  · exact certifiedPlankDyadicPairLevel_mem cert
  · exact certifiedPlankPairSine_pos_of_dyadicPairLevel_eq_some cert
  · exact certifiedPlankDyadic_inverseSine_le cert
  · exact certifiedPlankDyadic_body_subset_hullContainer cert
  · exact hKT
  · intro i k hk
    exact certifiedPlankAngleContainer_scale_le_of_canonical_le
      cert (selectedParentPlankBucketShading e S Y B hrho label)
      A hAfinite (by simpa [cert] using hcanonical) i k hk

#print axioms certifiedPlankDyadicPairLevel_mem
#print axioms certifiedPlankDyadic_inverseSine_le
#print axioms certifiedPlankDyadic_body_subset_hullContainer
#print axioms certifiedPlankAngleContainer_scale_le_of_canonical_le
#print axioms selectedParentPlankBucket_averageMultiplicity_le_of_canonicalAngleScale

end
end Family8SelectedParentCertifiedPlankCordobaConnectorV4
