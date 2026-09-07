import Family6Grounding.Family6Lemma69DeltaBCPlankGeometryV1
import Family8Grounding.Family8SelectedParentCertifiedPlankCordobaThresholdedAngleV6
import FamilyStickyGrounding.Family6AffineKatzTaoTransportV3

/-!
# Lemma 6.9: automatic thresholded rows for normalized `delta x b x c` bodies

This file specializes the existing paper-faithful `a / b` angle cutoff to
the honest scalar normalization of a `delta x b x c` family.  The angle
assignment, inverse-sine weights, and row hull containers are all canonical.
The only analytic family input is the existing Katz--Tao condition; the
remaining row geometry is recorded by one explicit scalar absorption
condition for the canonical row-scale supremum.
-/

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 4000000

open Set MeasureTheory
open scoped ENNReal NNReal BigOperators

namespace Family6Lemma69DeltaBCThresholdedBudgetV1

open LeanEval.Analysis.WangZahlKakeya
open Submission.Kakeya.ConvexGeometry
open Submission.Kakeya.ConvexFactoring
open Submission.Kakeya.ConvexFactoring.FullConvexMaximalDensity
open Family6AffineConvexVolumeCoreV1
open Family6AffineKatzTaoTransportV3
open Family6Lemma69DeltaBCPlankGeometryV1
open Family8CertifiedPlankPairOverlapV2
open Family8CertifiedPlankDyadicCordobaV2
open Family8SelectedParentAffineShadingTransportV4
open Family8SelectedParentCertifiedPlankCordobaConnectorV4
open Family8SelectedParentCertifiedPlankCordobaThresholdedAngleV6
open Family8SelectedParentJohnPlankSideWidthBridgeV5

noncomputable section

/-- The exact common scalar normalization by the long side `c`. -/
abbrev deltaBCNormalizationEquiv (c : NNReal) (hc : 0 < c) :
    Space ≃ᵃ[Real] Space :=
  scalarDilationAffineEquiv c⁻¹ (inv_pos.mpr hc)

/-- The actual normalized family, not a slab proxy. -/
abbrev deltaBCNormalizedFamily
    {iota : Type*} (c : NNReal) (hc : 0 < c)
    (F : ConvexFamily iota) : ConvexFamily iota :=
  affineImageFamily (deltaBCNormalizationEquiv c hc) F

/-- Literal affine-image shading on the normalized family. -/
noncomputable def deltaBCNormalizedShading
    {iota : Type*} {F : ConvexFamily iota}
    (c : NNReal) (hc : 0 < c) (Y : Shading F) :
    Shading (deltaBCNormalizedFamily c hc F) :=
  affineImageShading (deltaBCNormalizationEquiv c hc) Y

/-- Every canonical thresholded row ratio is below the double supremum that
defines the exact row-scale factor. -/
theorem thresholdedAngleContainer_ratio_le_canonical
    {iota : Type*} [Fintype iota]
    {F : ConvexFamily iota} {C a b : NNReal}
    (cert : ∀ i, PlankDimensionsCertificate C a b (F i))
    (Y : Shading F) (i : iota) (k : Option Int)
    (hk : k ∈ plankAngleLevels (certifiedPlankThresholdedLevels cert)) :
    certifiedPlankAngleScale C a b
          certifiedPlankDyadicInverseSineWeight k *
        volume (certifiedPlankThresholdedHullContainer cert i k : Set Space) /
          volume (Y.carrier i) ≤
      canonicalCertifiedPlankThresholdedAngleContainerScaleFactor cert Y := by
  exact (le_iSup (fun j : iota ↦
    ⨆ l : {l // l ∈ plankAngleLevels
        (certifiedPlankThresholdedLevels cert)},
      certifiedPlankAngleScale C a b
          certifiedPlankDyadicInverseSineWeight l.1 *
        volume (certifiedPlankThresholdedHullContainer cert j l.1 : Set Space) /
          volume (Y.carrier j)) i).trans'
    (le_iSup (fun l : {l // l ∈ plankAngleLevels
        (certifiedPlankThresholdedLevels cert)} ↦
      certifiedPlankAngleScale C a b
          certifiedPlankDyadicInverseSineWeight l.1 *
        volume (certifiedPlankThresholdedHullContainer cert i l.1 : Set Space) /
          volume (Y.carrier i)) ⟨k, hk⟩)

/-- Finiteness of the exact thresholded canonical factor produces the
rowwise `hscale` inequality.  It also rules out zero shaded rows: the
exceptional self bucket contains the positive-volume full plank. -/
theorem thresholdedAngleContainer_scale_le_of_canonical_finite
    {iota : Type*} [Fintype iota]
    {F : ConvexFamily iota} {C a b : NNReal}
    (cert : ∀ i, PlankDimensionsCertificate C a b (F i))
    (Y : Shading F)
    (hfinite :
      canonicalCertifiedPlankThresholdedAngleContainerScaleFactor cert Y ≠ ∞)
    (i : iota) (k : Option Int)
    (hk : k ∈ plankAngleLevels (certifiedPlankThresholdedLevels cert)) :
    certifiedPlankAngleScale C a b
          certifiedPlankDyadicInverseSineWeight k *
        volume (certifiedPlankThresholdedHullContainer cert i k : Set Space) ≤
      canonicalCertifiedPlankThresholdedAngleContainerScaleFactor cert Y *
        volume (Y.carrier i) := by
  have hcarrier : volume (Y.carrier i) ≠ 0 := by
    intro hzero
    have hi : i ∈ certifiedPlankThresholdedRowIndices cert i none := by
      rw [mem_certifiedPlankThresholdedRowIndices,
        certifiedPlankThresholdedPairLevel_self]
    have hbody : (F i : Set Space) ⊆
        (certifiedPlankThresholdedHullContainer cert i none : Set Space) :=
      body_subset_hullContainer F hi ⟨i, hi⟩
    have hcontainerPos : 0 <
        volume (certifiedPlankThresholdedHullContainer cert i none : Set Space) :=
      (cert i).isPlank.volume_pos.trans_le (measure_mono hbody)
    have hnone : none ∈
        plankAngleLevels (certifiedPlankThresholdedLevels cert) := by
      simp [plankAngleLevels]
    have hratio := thresholdedAngleContainer_ratio_le_canonical
      cert Y i none hnone
    have hratioTop :
        certifiedPlankAngleScale C a b
              certifiedPlankDyadicInverseSineWeight none *
            volume (certifiedPlankThresholdedHullContainer cert i none : Set Space) /
              volume (Y.carrier i) = ∞ := by
      rw [hzero]
      simpa only [certifiedPlankAngleScale, one_mul] using
        ENNReal.div_eq_top.mpr (Or.inl ⟨ne_of_gt hcontainerPos, rfl⟩)
    rw [hratioTop] at hratio
    exact hfinite (top_unique hratio)
  have hcarrierTop : volume (Y.carrier i) ≠ ∞ :=
    ((measure_mono (Y.carrier_subset i)).trans_lt
      (F i).isCompact.measure_lt_top).ne
  have hratio := thresholdedAngleContainer_ratio_le_canonical
    cert Y i k hk
  calc
    certifiedPlankAngleScale C a b
          certifiedPlankDyadicInverseSineWeight k *
        volume (certifiedPlankThresholdedHullContainer cert i k : Set Space) =
        (certifiedPlankAngleScale C a b
            certifiedPlankDyadicInverseSineWeight k *
          volume (certifiedPlankThresholdedHullContainer cert i k : Set Space) /
            volume (Y.carrier i)) * volume (Y.carrier i) :=
      (ENNReal.div_mul_cancel hcarrier hcarrierTop).symm
    _ ≤ canonicalCertifiedPlankThresholdedAngleContainerScaleFactor cert Y *
        volume (Y.carrier i) := by gcongr

/-- The occupied genuine angle labels for the normalized family. -/
noncomputable def deltaBCThresholdedLevels
    {iota : Type*} [Fintype iota] {F : ConvexFamily iota}
    {C delta b c : NNReal}
    (cert : ∀ i, DeltaBCDimensionsCertificate C delta b c (F i))
    (hc : 0 < c) : Finset Int :=
  certifiedPlankThresholdedLevels
    (deltaBCNormalizedPlankCertificate cert hc)

/-- Exact thresholded row-scale supremum for the normalized image shading. -/
noncomputable def deltaBCThresholdedCanonicalScale
    {iota : Type*} [Fintype iota] {F : ConvexFamily iota}
    {C delta b c : NNReal}
    (cert : ∀ i, DeltaBCDimensionsCertificate C delta b c (F i))
    (hc : 0 < c) (Y : Shading F) : ENNReal :=
  canonicalCertifiedPlankThresholdedAngleContainerScaleFactor
    (deltaBCNormalizedPlankCertificate cert hc)
    (deltaBCNormalizedShading c hc Y)

/-- The sole scalar seam after canonical angle rows and hull containers are
chosen.  Its first conjunct is the cancellation side condition for row
ratios; its second conjunct is exactly the Lemma 6.9 absorption inequality. -/
def DeltaBCThresholdedScalarAbsorption
    {iota : Type*} [Fintype iota] {F : ConvexFamily iota}
    {C delta b c : NNReal}
    (cert : ∀ i, DeltaBCDimensionsCertificate C delta b c (F i))
    (hc : 0 < c) (Y : Shading F) (D L : ENNReal) : Prop :=
  deltaBCThresholdedCanonicalScale cert hc Y ≠ ∞ ∧
    L * (((plankAngleLevels (deltaBCThresholdedLevels cert hc)).card : ENNReal) *
      D * deltaBCThresholdedCanonicalScale cert hc Y) ≤
        (deltaBCNormalizedShading c hc Y).shadingMass

/-- End-to-end normalized `hBudget` producer.  All thresholded angle data,
pairwise overlap estimates, row hull containers, and `hscale` inequalities
are generated internally.  Apart from the genuine `delta x b x c`
certificates, the remaining inputs are the existing source Katz--Tao bound
and the single scalar absorption predicate above. -/
theorem lemma69_normalized_overlapBudget_of_deltaBCThresholded
    {iota : Type*} [Fintype iota]
    {F : ConvexFamily iota} (Y : Shading F)
    {C delta b c : NNReal}
    (cert : ∀ i, DeltaBCDimensionsCertificate C delta b c (F i))
    (hc : 0 < c) (D L : ENNReal)
    (hKT : IsKatzTao D F)
    (hscalar : DeltaBCThresholdedScalarAbsorption cert hc Y D L) :
    L * (∑ i, ∑ j,
      volume
        ((deltaBCNormalizedShading c hc Y).carrier i ∩
          (deltaBCNormalizedShading c hc Y).carrier j)) ≤
      (deltaBCNormalizedShading c hc Y).shadingMass ^ 2 := by
  let Yn := deltaBCNormalizedShading c hc Y
  let certn := deltaBCNormalizedPlankCertificate cert hc
  let levels := deltaBCThresholdedLevels cert hc
  let A := deltaBCThresholdedCanonicalScale cert hc Y
  have hAfinite : A ≠ ∞ := by
    exact hscalar.1
  have hKTn : IsKatzTao D (deltaBCNormalizedFamily c hc F) := by
    exact isKatzTao_affineImageFamily (deltaBCNormalizationEquiv c hc) F hKT
  apply lemma69_overlapBudget_of_dyadicPairwiseFrostman
    Yn (plankAngleLevels levels)
      (certifiedPlankThresholdedPairLevel certn)
      (certifiedPlankThresholdedHullContainer certn)
      (fun _ k ↦ certifiedPlankAngleScale C (delta / c) (b / c)
        certifiedPlankDyadicInverseSineWeight k)
      D A L
  · exact certifiedPlankThresholdedPairLevel_mem certn
  · intro i j
    exact certifiedPlank_pairwiseOverlap_le_angleScale certn
      (certifiedPlankThresholdedPairLevel certn)
      certifiedPlankDyadicInverseSineWeight
      (certifiedPlankThresholdedPairSine_pos_of_level_eq_some certn)
      (certifiedPlankThresholded_inverseSine_le certn) i j
  · exact certifiedPlankThresholded_body_subset_hullContainer certn
  · exact hKTn
  · exact thresholdedAngleContainer_scale_le_of_canonical_finite
      certn Yn hAfinite
  · exact hscalar.2

#print axioms thresholdedAngleContainer_scale_le_of_canonical_finite
#print axioms lemma69_normalized_overlapBudget_of_deltaBCThresholded

end

end Family6Lemma69DeltaBCThresholdedBudgetV1
