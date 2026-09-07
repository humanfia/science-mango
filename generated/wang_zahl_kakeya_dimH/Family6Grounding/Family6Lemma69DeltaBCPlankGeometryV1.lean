import Family6Grounding.Family6Lemma69OverlapBudgetProducerV1
import Family8Grounding.Family8CertifiedPlankDyadicCordobaV2
import Family8Grounding.Family8SelectedParentAffineShadingTransportV4
import Family8Grounding.Family8SelectedParentJohnPlankSideWidthBridgeV8
import Mathlib.Tactic

/-!
# Lemma 6.9: honest `delta x b x c` normalization and pair overlap

The manuscript's large-`b` geometry first divides all three side lengths by
the common long scale `c`.  Thus a genuine `delta x b x c` box certificate
becomes an actual `(delta / c) x (b / c) x 1` `IsPlank` certificate.  This
file implements that scalar normalization and transports the certified plank
pair-overlap estimate back through the affine equivalence.

No `delta x b x c` body is treated as a `theta x 1 x 1` slab.  In particular,
the pair majorant retains the normalized aspect ratio
`(delta / c) / (b / c)` through `certifiedPlankAngleScale`.
-/

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 4000000

open Set MeasureTheory
open scoped ENNReal NNReal Pointwise InnerProductSpace Matrix

namespace Family6Lemma69DeltaBCPlankGeometryV1

open LeanEval.Analysis.WangZahlKakeya
open Submission.Kakeya.ConvexGeometry
open Submission.Kakeya.ConvexFactoring
open Family6AffineConvexVolumeCoreV1
open Family8CertifiedPlankPairOverlapV2
open Family8CertifiedPlankDyadicCordobaV2
open Family8SelectedParentAffineShadingTransportV4
open Family8SelectedParentJohnPlankSideWidthBridgeV5
open Family8SelectedParentJohnPlankSideWidthBridgeV8

noncomputable section

/-- Literal side pattern used before division by the common long scale. -/
def deltaBCSides (delta b c : NNReal) : Fin 3 → NNReal :=
  ![delta, b, c]

/-- Data-bearing, comparison-controlled form of a genuine
`delta x b x c` body.  The scalar ordering is precisely what is needed to
obtain an `IsPlank` after division by `c`. -/
structure DeltaBCDimensionsCertificate (C delta b c : NNReal)
    (K : ConvexBody Space) extends
    BoxDimensionsCertificate C (deltaBCSides delta b c) K where
  delta_pos : 0 < delta
  delta_le_b : delta ≤ b
  b_le_c : b ≤ c

/-- Positive scalar dilation by `c⁻¹` turns the literal three-scale box
certificate into the project's genuine normalized plank certificate. -/
noncomputable def DeltaBCDimensionsCertificate.normalizedPlankCertificate
    {C delta b c : NNReal} {K : ConvexBody Space}
    (cert : DeltaBCDimensionsCertificate C delta b c K)
    (hc : 0 < c) :
    PlankDimensionsCertificate C (delta / c) (b / c)
      (affineImageConvexBody
        (scalarDilationAffineEquiv c⁻¹ (inv_pos.mpr hc)) K) := by
  let boxCert := scalarDilationBoxDimensionsCertificate
    cert.toBoxDimensionsCertificate c⁻¹ (inv_pos.mpr hc)
  have hcne : c ≠ 0 := ne_of_gt hc
  have hside :
      (fun i ↦ c⁻¹ * deltaBCSides delta b c i) =
        plankSides (delta / c) (b / c) := by
    funext i
    fin_cases i <;>
      simp [deltaBCSides, plankSides, div_eq_mul_inv, hcne, mul_comm]
  have normalizedBox :
      BoxDimensionsCertificate C (plankSides (delta / c) (b / c))
        (affineImageConvexBody
          (scalarDilationAffineEquiv c⁻¹ (inv_pos.mpr hc)) K) := by
    exact hside ▸ boxCert
  exact
    { toBoxDimensionsCertificate := normalizedBox
      a_pos := div_pos cert.delta_pos hc
      a_le_b := by
        gcongr
        exact cert.delta_le_b
      b_le_one := by
        rw [div_le_one hc]
        exact cert.b_le_c }

/-- Proposition-level form of the same exact normalization. -/
theorem DeltaBCDimensionsCertificate.normalized_isPlank
    {C delta b c : NNReal} {K : ConvexBody Space}
    (cert : DeltaBCDimensionsCertificate C delta b c K)
    (hc : 0 < c) :
    IsPlank C (delta / c) (b / c)
      (affineImageConvexBody
        (scalarDilationAffineEquiv c⁻¹ (inv_pos.mpr hc)) K) :=
  (cert.normalizedPlankCertificate hc).isPlank

/-- Memberwise normalized certificates for a family of genuine
`delta x b x c` bodies. -/
noncomputable def deltaBCNormalizedPlankCertificate
    {iota : Type*} {F : ConvexFamily iota}
    {C delta b c : NNReal}
    (cert : ∀ i, DeltaBCDimensionsCertificate C delta b c (F i))
    (hc : 0 < c) (i : iota) :
    PlankDimensionsCertificate C (delta / c) (b / c)
      (affineImageFamily
        (scalarDilationAffineEquiv c⁻¹ (inv_pos.mpr hc)) F i) := by
  change PlankDimensionsCertificate C (delta / c) (b / c)
    (affineImageConvexBody
      (scalarDilationAffineEquiv c⁻¹ (inv_pos.mpr hc)) (F i))
  exact (cert i).normalizedPlankCertificate hc

/-- Pairwise shaded overlap acquires exactly the common affine Jacobian.
This is the cancellation bridge used to return the normalized plank estimate
to the original `delta x b x c` coordinates. -/
theorem affineImageShading_pairOverlap_volume
    {iota : Type*} {F : ConvexFamily iota}
    (e : Space ≃ᵃ[Real] Space) (Y : Shading F) (i j : iota) :
    volume
        ((affineImageShading e Y).carrier i ∩
          (affineImageShading e Y).carrier j) =
      affineJacobian e * volume (Y.carrier i ∩ Y.carrier j) := by
  rw [affineImageShading_carrier, affineImageShading_carrier,
    ← Set.image_inter e.injective, volume_image_affineEquiv]

/-- The actual `delta x b x c` certificate supplies the pairwise majorant
after honest normalization.  Both overlap and member volume have the same
Jacobian, so the resulting bound is stated back in the original coordinates
without a determinant loss. -/
theorem deltaBC_pairwiseOverlap_le_normalizedAngleScale
    {iota kappa : Type*} {F : ConvexFamily iota} {Y : Shading F}
    {C delta b c : NNReal}
    (cert : ∀ i, DeltaBCDimensionsCertificate C delta b c (F i))
    (hc : 0 < c)
    (level : iota → iota → Option kappa)
    (inverseSineWeight : kappa → ENNReal)
    (htransverse : ∀ i j k, level i j = some k →
      0 < certifiedPlankPairSine
        (deltaBCNormalizedPlankCertificate cert hc) i j)
    (hinverse : ∀ i j k, level i j = some k →
      ENNReal.ofReal
          ((certifiedPlankPairSine
            (deltaBCNormalizedPlankCertificate cert hc) i j)⁻¹) ≤
        inverseSineWeight k)
    (i j : iota) :
    volume (Y.carrier i ∩ Y.carrier j) ≤
      certifiedPlankAngleScale C (delta / c) (b / c)
          inverseSineWeight (level i j) *
        volume (F j : Set Space) := by
  let e : Space ≃ᵃ[Real] Space :=
    scalarDilationAffineEquiv c⁻¹ (inv_pos.mpr hc)
  let J : ENNReal := affineJacobian e
  have hnormalized :=
    certifiedPlank_pairwiseOverlap_le_angleScale
      (F := affineImageFamily e F) (Y := affineImageShading e Y)
      (deltaBCNormalizedPlankCertificate cert hc)
      level inverseSineWeight htransverse hinverse i j
  have hpairVolume :
      volume
          ((affineImageShading e Y).carrier i ∩
            (affineImageShading e Y).carrier j) =
        J * volume (Y.carrier i ∩ Y.carrier j) := by
    simpa [J] using affineImageShading_pairOverlap_volume e Y i j
  have hbodyVolume :
      volume (affineImageFamily e F j : Set Space) =
        J * volume (F j : Set Space) := by
    simpa [J, affineImageFamily] using
      volume_affineImageConvexBody e (F j)
  rw [hpairVolume, hbodyVolume] at hnormalized
  apply (ENNReal.mul_le_mul_iff_left
    (affineJacobian_pos e).ne' (affineJacobian_ne_top e)).mp
  simpa [J, mul_assoc, mul_left_comm, mul_comm] using hnormalized

/-- Concrete large-`b` overlap-budget producer.  The pairwise inequality is
now derived from genuine `delta x b x c` geometry; only the dyadic angle
assignment, its row containers/Frostman control, and the final scalar
absorption remain as explicit inputs. -/
theorem lemma69_overlapBudget_of_deltaBCPairwiseFrostman
    {iota kappa : Type*} [Fintype iota] [DecidableEq kappa]
    {F : ConvexFamily iota} (Y : Shading F)
    {C delta b c : NNReal}
    (cert : ∀ i, DeltaBCDimensionsCertificate C delta b c (F i))
    (hc : 0 < c)
    (levels : Finset kappa)
    (level : iota → iota → Option kappa)
    (inverseSineWeight : kappa → ENNReal)
    (container : iota → Option kappa → ConvexBody Space)
    (D A L : ENNReal)
    (hlevel : ∀ i j, level i j ∈ plankAngleLevels levels)
    (htransverse : ∀ i j k, level i j = some k →
      0 < certifiedPlankPairSine
        (deltaBCNormalizedPlankCertificate cert hc) i j)
    (hinverse : ∀ i j k, level i j = some k →
      ENNReal.ofReal
          ((certifiedPlankPairSine
            (deltaBCNormalizedPlankCertificate cert hc) i j)⁻¹) ≤
        inverseSineWeight k)
    (hcontained : ∀ i j,
      (F j : Set Space) ⊆ (container i (level i j) : Set Space))
    (hKT : IsKatzTao D F)
    (hscale : ∀ i k, k ∈ plankAngleLevels levels →
      certifiedPlankAngleScale C (delta / c) (b / c)
          inverseSineWeight k *
          volume (container i k : Set Space) ≤
        A * volume (Y.carrier i))
    (habsorb :
      L * (((plankAngleLevels levels).card : ENNReal) * D * A) ≤
        Y.shadingMass) :
    L * (∑ i, ∑ j, volume (Y.carrier i ∩ Y.carrier j)) ≤
      Y.shadingMass ^ 2 := by
  apply lemma69_overlapBudget_of_dyadicPairwiseFrostman
    Y (plankAngleLevels levels) level container
      (fun _ k ↦ certifiedPlankAngleScale C (delta / c) (b / c)
        inverseSineWeight k) D A L
  · exact hlevel
  · intro i j
    exact deltaBC_pairwiseOverlap_le_normalizedAngleScale
      cert hc level inverseSineWeight htransverse hinverse i j
  · exact hcontained
  · exact hKT
  · exact hscale
  · exact habsorb

#print axioms DeltaBCDimensionsCertificate.normalizedPlankCertificate
#print axioms affineImageShading_pairOverlap_volume
#print axioms deltaBC_pairwiseOverlap_le_normalizedAngleScale
#print axioms lemma69_overlapBudget_of_deltaBCPairwiseFrostman

end

end Family6Lemma69DeltaBCPlankGeometryV1
