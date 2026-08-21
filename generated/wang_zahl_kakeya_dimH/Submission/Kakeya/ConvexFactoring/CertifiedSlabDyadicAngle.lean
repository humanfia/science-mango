import Submission.Kakeya.ConvexFactoring.TransverseUnit
import Submission.Kakeya.ConvexFactoring.DeterminantAngleBridge
import Submission.Kakeya.ConvexFactoring.DyadicOverlapSummation
import Submission.Kakeya.ConvexFactoring.BoxDimensionsMeasure

/-!
# Dyadic sine buckets for certified slab overlap

The exceptional level handles diagonal or nontransverse pairs by the trivial
body-volume bound. At a genuine angle level, certified slab geometry supplies
the pairwise overlap estimate; no overlap inequality is assumed by the API.
-/

open scoped ENNReal NNReal Pointwise InnerProductSpace Matrix
open MeasureTheory Set

namespace Submission.Kakeya.ConvexFactoring

open LeanEval.Analysis.WangZahlKakeya
open Submission.Kakeya.ConvexGeometry
open Submission.Kakeya.ConvexGeometry.TransverseCoordinateOverlap

noncomputable section

variable {ι κ : Type*} [Fintype ι] [DecidableEq κ]
variable {F : ConvexFamily ι} {Y : Shading F}
variable {C θ : ℝ≥0}

/-- Sine of the angle between the certified short normals. -/
def certifiedSlabPairSine
    (cert : ∀ i, SlabDimensionsCertificate C θ (F i)) (i j : ι) : ℝ :=
  Real.sin (InnerProductGeometry.angle
    ((cert i).box.frame 0) ((cert j).box.frame 0))

/-- Adjoin one exceptional level to the genuine dyadic angle levels. -/
def slabAngleLevels (levels : Finset κ) : Finset (Option κ) :=
  {none} ∪ levels.image some

/-- Scale used by row summation. The exceptional bucket has scale one. A
genuine angle bucket combines inverse sine with the certified volume lower
bound of the second slab. -/
def certifiedSlabAngleScale
    (C θ : ℝ≥0) (inverseSineWeight : κ → ℝ≥0∞) : Option κ → ℝ≥0∞
  | none => 1
  | some k => inverseSineWeight k * 2 * (θ : ℝ≥0∞) *
      (((C⁻¹ : ℝ≥0) : ℝ≥0∞) ^ 3)⁻¹

omit [Fintype ι] in
/-- The canonical transverse direction realizes the sine bucket as an exact
coordinate determinant. -/
theorem certifiedSlab_abs_det_transverseUnit_eq_pairSine
    (cert : ∀ i, SlabDimensionsCertificate C θ (F i))
    (i j : ι)
    (hangle : 0 < certifiedSlabPairSine cert i j) :
    |LinearMap.det (innerCoordinateMap
      ![transverseUnit ((cert i).box.frame 0) ((cert j).box.frame 0),
        (cert i).box.frame 0, (cert j).box.frame 0])| =
      certifiedSlabPairSine cert i j := by
  unfold certifiedSlabPairSine at hangle ⊢
  exact abs_det_innerCoordinateMap_eq_sin_angle _ _ _
    (norm_transverseUnit_of_unit _ _
      ((cert i).box.frame.norm_eq_one 0)
      ((cert j).box.frame.norm_eq_one 0) hangle)
    ((cert i).box.frame.norm_eq_one 0)
    ((cert j).box.frame.norm_eq_one 0)
    (inner_transverseUnit_left _ _) (inner_transverseUnit_right _ _)
/-- Recover the proposition-level slab certificate from its data-bearing
form. -/
theorem slabDimensionsCertificate_isSlab
    {K : ConvexBody Space} (cert : SlabDimensionsCertificate C θ K) :
    IsSlab C θ K :=
  ⟨cert.theta_pos, cert.theta_le_one,
    ⟨cert.one_le, cert.box, cert.side_eq, cert.inner_le, cert.outer_le⟩⟩

omit [Fintype ι] [DecidableEq κ] in
/-- Certified geometry automatically supplies the pairwise majorant attached
to an exceptional-or-angle level assignment. No overlap estimate is an input.
-/
theorem certifiedSlab_pairwiseOverlap_le_angleScale
    (cert : ∀ i, SlabDimensionsCertificate C θ (F i))
    (level : ι → ι → Option κ)
    (inverseSineWeight : κ → ℝ≥0∞)
    (htransverse : ∀ i j k, level i j = some k →
      0 < certifiedSlabPairSine cert i j)
    (hinverse : ∀ i j k, level i j = some k →
      ENNReal.ofReal ((certifiedSlabPairSine cert i j)⁻¹) ≤
        inverseSineWeight k)
    (i j : ι) :
    volume (Y.carrier i ∩ Y.carrier j) ≤
      certifiedSlabAngleScale C θ inverseSineWeight (level i j) *
        volume (F j : Set Space) := by
  classical
  cases hlevel : level i j with
  | none =>
      calc
        volume (Y.carrier i ∩ Y.carrier j) ≤ volume (Y.carrier j) :=
          measure_mono inter_subset_right
        _ ≤ volume (F j : Set Space) := measure_mono (Y.carrier_subset j)
        _ = certifiedSlabAngleScale C θ inverseSineWeight none *
            volume (F j : Set Space) := by
              simp [certifiedSlabAngleScale]
  | some k =>
      have hangle : 0 < Real.sin (InnerProductGeometry.angle
          ((cert i).box.frame 0) ((cert j).box.frame 0)) := by
        simpa [certifiedSlabPairSine] using htransverse i j k hlevel
      have hgeom :=
        (cert i).volume_inter_body_le_sin_angle_auto (cert j) hangle
      have hslabj : IsSlab C θ (F j) :=
        slabDimensionsCertificate_isSlab (cert j)
      have hvolume := hslabj.volume_lower_bound
      let α : ℝ≥0∞ := (((C⁻¹ : ℝ≥0) : ℝ≥0∞) ^ 3)
      have hCpos : 0 < C := lt_of_lt_of_le zero_lt_one (cert j).one_le
      have hCne : C ≠ 0 := ne_of_gt hCpos
      have hαzero : α ≠ 0 := by simp [α, hCne]
      have hαtop : α ≠ ∞ := by simp [α]
      have hcancel : α⁻¹ * α = 1 :=
        ENNReal.inv_mul_cancel hαzero hαtop
      change α * (θ : ℝ≥0∞) ≤ volume (F j : Set Space) at hvolume
      calc
        volume (Y.carrier i ∩ Y.carrier j) ≤
            volume ((F i : Set Space) ∩ (F j : Set Space)) :=
          measure_mono (inter_subset_inter (Y.carrier_subset i)
            (Y.carrier_subset j))
        _ ≤ ENNReal.ofReal ((certifiedSlabPairSine cert i j)⁻¹) *
            2 * (θ : ℝ≥0∞) * (θ : ℝ≥0∞) := by
          simpa [certifiedSlabPairSine] using hgeom
        _ ≤ inverseSineWeight k * 2 * (θ : ℝ≥0∞) *
            (θ : ℝ≥0∞) := by
          gcongr
          exact hinverse i j k hlevel
        _ = certifiedSlabAngleScale C θ inverseSineWeight (some k) *
            (α * (θ : ℝ≥0∞)) := by
          symm
          calc
            certifiedSlabAngleScale C θ inverseSineWeight (some k) *
                (α * (θ : ℝ≥0∞)) =
                (inverseSineWeight k * 2 * (θ : ℝ≥0∞)) *
                  (α⁻¹ * α) * (θ : ℝ≥0∞) := by
                    simp only [certifiedSlabAngleScale]
                    ring
            _ = inverseSineWeight k * 2 * (θ : ℝ≥0∞) *
                (θ : ℝ≥0∞) := by rw [hcancel]; simp
        _ ≤ certifiedSlabAngleScale C θ inverseSineWeight (some k) *
            volume (F j : Set Space) :=
          mul_le_mul_of_nonneg_left hvolume (by exact bot_le)

/-- The certified sine-bucket estimate feeds directly into the finite row
summation theorem. The remaining inputs are precisely the angle assignment,
row/level containers, nonconcentration, and the container-scale comparison. -/
theorem certifiedSlabDyadicOverlap_row_le
    (cert : ∀ i, SlabDimensionsCertificate C θ (F i))
    (levels : Finset κ)
    (level : ι → ι → Option κ)
    (inverseSineWeight : κ → ℝ≥0∞)
    (container : ι → Option κ → ConvexBody Space)
    (D A : ℝ≥0∞)
    (hlevel : ∀ i j, level i j ∈ slabAngleLevels levels)
    (htransverse : ∀ i j k, level i j = some k →
      0 < certifiedSlabPairSine cert i j)
    (hinverse : ∀ i j k, level i j = some k →
      ENNReal.ofReal ((certifiedSlabPairSine cert i j)⁻¹) ≤
        inverseSineWeight k)
    (hcontained : ∀ i j,
      (F j : Set Space) ⊆ (container i (level i j) : Set Space))
    (hKT : IsKatzTao D F)
    (hscale : ∀ i k, k ∈ slabAngleLevels levels →
      certifiedSlabAngleScale C θ inverseSineWeight k *
          volume (container i k : Set Space) ≤
        A * volume (Y.carrier i))
    (i : ι) :
    (∑ j, volume (Y.carrier i ∩ Y.carrier j)) ≤
      (((slabAngleLevels levels).card : ℝ≥0∞) * D * A) *
        volume (Y.carrier i) := by
  apply dyadicOverlap_row_le
    (slabAngleLevels levels) level container
    (fun _ k => certifiedSlabAngleScale C θ inverseSineWeight k)
    D A hlevel ?_ hcontained hKT hscale i
  intro i' j'
  exact certifiedSlab_pairwiseOverlap_le_angleScale cert level
    inverseSineWeight htransverse hinverse i' j'

/-- Consequently the certified sine buckets provide the corresponding global
second-moment estimate, again without assuming any pairwise overlap bound. -/
theorem certifiedSlabDyadicOverlap_secondMoment_le
    (cert : ∀ i, SlabDimensionsCertificate C θ (F i))
    (levels : Finset κ)
    (level : ι → ι → Option κ)
    (inverseSineWeight : κ → ℝ≥0∞)
    (container : ι → Option κ → ConvexBody Space)
    (D A : ℝ≥0∞)
    (hlevel : ∀ i j, level i j ∈ slabAngleLevels levels)
    (htransverse : ∀ i j k, level i j = some k →
      0 < certifiedSlabPairSine cert i j)
    (hinverse : ∀ i j k, level i j = some k →
      ENNReal.ofReal ((certifiedSlabPairSine cert i j)⁻¹) ≤
        inverseSineWeight k)
    (hcontained : ∀ i j,
      (F j : Set Space) ⊆ (container i (level i j) : Set Space))
    (hKT : IsKatzTao D F)
    (hscale : ∀ i k, k ∈ slabAngleLevels levels →
      certifiedSlabAngleScale C θ inverseSineWeight k *
          volume (container i k : Set Space) ≤
        A * volume (Y.carrier i)) :
    (∫⁻ x, (Y.pointMultiplicity x : ℝ≥0∞) ^ 2 ∂volume) ≤
      (((slabAngleLevels levels).card : ℝ≥0∞) * D * A) *
        Y.shadingMass := by
  apply dyadicOverlap_secondMoment_le
    (slabAngleLevels levels) level container
    (fun _ k => certifiedSlabAngleScale C θ inverseSineWeight k)
    D A hlevel ?_ hcontained hKT hscale
  intro i' j'
  exact certifiedSlab_pairwiseOverlap_le_angleScale cert level
    inverseSineWeight htransverse hinverse i' j'

end

end Submission.Kakeya.ConvexFactoring
