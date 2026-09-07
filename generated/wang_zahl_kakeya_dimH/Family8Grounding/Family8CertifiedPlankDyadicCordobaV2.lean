import Family8Grounding.Family8CertifiedPlankPairOverlapV2
import Submission.Kakeya.ConvexFactoring.DyadicOverlapSummation
import Submission.Kakeya.ConvexFactoring.CordobaAnalytic

/-!
# Genuine plank dyadic angle summation and Cordoba bounds

The imported certificate proves the actual `a x b x 1` pair overlap
`sin(angle)^{-1} * 2 * a^2`.  Dividing by the certified body-volume lower
bound `C^{-3} * a * b` leaves the genuine aspect ratio `a / b` in every
nonexceptional angle scale.  This file then derives row, second-moment,
shaded-union, and average-multiplicity bounds from finite angle containers
and Katz--Tao nonconcentration.  None of those conclusions is an input.
-/

open scoped ENNReal NNReal Pointwise InnerProductSpace
open MeasureTheory Set

namespace Family8CertifiedPlankDyadicCordobaV2

open LeanEval.Analysis.WangZahlKakeya
open Submission.Kakeya.ConvexGeometry
open Submission.Kakeya.ConvexFactoring
open Family8CertifiedPlankPairOverlapV2

noncomputable section

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 4000000

variable {iota kappa : Type*} [Fintype iota] [DecidableEq kappa]
variable {F : ConvexFamily iota} {Y : Shading F}
variable {C a b : NNReal}

/-- Sine of the angle between the certified short normals. -/
def certifiedPlankPairSine
    (cert : forall i, PlankDimensionsCertificate C a b (F i))
    (i j : iota) : Real :=
  Real.sin (InnerProductGeometry.angle
    ((cert i).box.frame 0) ((cert j).box.frame 0))

/-- One exceptional bucket together with all genuine dyadic angle levels. -/
def plankAngleLevels (levels : Finset kappa) : Finset (Option kappa) :=
  {none} ∪ levels.image some

/-- The scale of a genuine plank angle bucket.  The explicit `a / b` is the
gain that is lost if a plank is incorrectly treated as a slab. -/
def certifiedPlankAngleScale
    (C a b : NNReal) (inverseSineWeight : kappa -> ENNReal) :
    Option kappa -> ENNReal
  | none => 1
  | some k => inverseSineWeight k * 2 *
      ((a / b : NNReal) : ENNReal) *
      ((((C⁻¹ : NNReal) : ENNReal) ^ 3)⁻¹)

omit [Fintype iota] [DecidableEq kappa] in
/-- Actual plank geometry supplies the pairwise majorant for the assigned
exceptional-or-angle bucket. -/
theorem certifiedPlank_pairwiseOverlap_le_angleScale
    (cert : forall i, PlankDimensionsCertificate C a b (F i))
    (level : iota -> iota -> Option kappa)
    (inverseSineWeight : kappa -> ENNReal)
    (htransverse : forall i j k, level i j = some k ->
      0 < certifiedPlankPairSine cert i j)
    (hinverse : forall i j k, level i j = some k ->
      ENNReal.ofReal ((certifiedPlankPairSine cert i j)⁻¹) <=
        inverseSineWeight k)
    (i j : iota) :
    volume (Y.carrier i ∩ Y.carrier j) <=
      certifiedPlankAngleScale C a b inverseSineWeight (level i j) *
        volume (F j : Set Space) := by
  classical
  cases hlevel : level i j with
  | none =>
      calc
        volume (Y.carrier i ∩ Y.carrier j) <= volume (Y.carrier j) :=
          measure_mono inter_subset_right
        _ <= volume (F j : Set Space) := measure_mono (Y.carrier_subset j)
        _ = certifiedPlankAngleScale C a b inverseSineWeight none *
            volume (F j : Set Space) := by
          simp [certifiedPlankAngleScale]
  | some k =>
      have hangle : 0 < Real.sin (InnerProductGeometry.angle
          ((cert i).box.frame 0) ((cert j).box.frame 0)) := by
        simpa [certifiedPlankPairSine] using htransverse i j k hlevel
      have hgeom :=
        (cert i).volume_inter_body_le_sin_angle_auto (cert j) hangle
      have hplankj : IsPlank C a b (F j) := (cert j).isPlank
      have hvolume := hplankj.volume_lower_bound
      let alpha : ENNReal := (((C⁻¹ : NNReal) : ENNReal) ^ 3)
      have hCpos : 0 < C := lt_of_lt_of_le zero_lt_one (cert j).one_le
      have hCne : C ≠ 0 := ne_of_gt hCpos
      have halpha0 : alpha ≠ 0 := by simp [alpha, hCne]
      have halphaTop : alpha ≠ ∞ := by simp [alpha]
      have halphaCancel : alpha⁻¹ * alpha = 1 :=
        ENNReal.inv_mul_cancel halpha0 halphaTop
      have hbpos : 0 < b := (cert j).a_pos.trans_le (cert j).a_le_b
      have hbne : b ≠ 0 := ne_of_gt hbpos
      have hratio :
          ((a / b : NNReal) : ENNReal) * (b : ENNReal) =
            (a : ENNReal) := by
        exact_mod_cast div_mul_cancel₀ a hbne
      change alpha * ((a : ENNReal) * (b : ENNReal)) <=
        volume (F j : Set Space) at hvolume
      calc
        volume (Y.carrier i ∩ Y.carrier j) <=
            volume ((F i : Set Space) ∩ (F j : Set Space)) :=
          measure_mono (inter_subset_inter (Y.carrier_subset i)
            (Y.carrier_subset j))
        _ <= ENNReal.ofReal ((certifiedPlankPairSine cert i j)⁻¹) *
            2 * (a : ENNReal) * (a : ENNReal) := by
          simpa [certifiedPlankPairSine] using hgeom
        _ <= inverseSineWeight k * 2 * (a : ENNReal) *
            (a : ENNReal) := by
          gcongr
          exact hinverse i j k hlevel
        _ = certifiedPlankAngleScale C a b inverseSineWeight (some k) *
            (alpha * ((a : ENNReal) * (b : ENNReal))) := by
          change inverseSineWeight k * 2 * (a : ENNReal) * (a : ENNReal) =
            (inverseSineWeight k * 2 * ((a / b : NNReal) : ENNReal) *
              alpha⁻¹) * (alpha * ((a : ENNReal) * (b : ENNReal)))
          symm
          calc
            (inverseSineWeight k * 2 * ((a / b : NNReal) : ENNReal) *
                alpha⁻¹) * (alpha * ((a : ENNReal) * (b : ENNReal))) =
                inverseSineWeight k * 2 *
                  (((a / b : NNReal) : ENNReal) * (b : ENNReal)) *
                  (alpha⁻¹ * alpha) * (a : ENNReal) := by
              ring
            _ = inverseSineWeight k * 2 * (a : ENNReal) *
                (a : ENNReal) := by
              rw [hratio, halphaCancel]
              ring
        _ <= certifiedPlankAngleScale C a b inverseSineWeight (some k) *
            volume (F j : Set Space) :=
          mul_le_mul_of_nonneg_left hvolume (by exact bot_le)

/-- The certified plank pair majorant feeds the finite row summation. -/
theorem certifiedPlankDyadicOverlap_row_le
    (cert : forall i, PlankDimensionsCertificate C a b (F i))
    (levels : Finset kappa)
    (level : iota -> iota -> Option kappa)
    (inverseSineWeight : kappa -> ENNReal)
    (container : iota -> Option kappa -> ConvexBody Space)
    (D A : ENNReal)
    (hlevel : forall i j, level i j ∈ plankAngleLevels levels)
    (htransverse : forall i j k, level i j = some k ->
      0 < certifiedPlankPairSine cert i j)
    (hinverse : forall i j k, level i j = some k ->
      ENNReal.ofReal ((certifiedPlankPairSine cert i j)⁻¹) <=
        inverseSineWeight k)
    (hcontained : forall i j,
      (F j : Set Space) ⊆ (container i (level i j) : Set Space))
    (hKT : IsKatzTao D F)
    (hscale : forall i k, k ∈ plankAngleLevels levels ->
      certifiedPlankAngleScale C a b inverseSineWeight k *
          volume (container i k : Set Space) <=
        A * volume (Y.carrier i))
    (i : iota) :
    (∑ j, volume (Y.carrier i ∩ Y.carrier j)) <=
      (((plankAngleLevels levels).card : ENNReal) * D * A) *
        volume (Y.carrier i) := by
  apply dyadicOverlap_row_le
    (plankAngleLevels levels) level container
    (fun _ k => certifiedPlankAngleScale C a b inverseSineWeight k)
    D A hlevel ?_ hcontained hKT hscale i
  intro i' j'
  exact certifiedPlank_pairwiseOverlap_le_angleScale cert level
    inverseSineWeight htransverse hinverse i' j'

/-- Global second moment derived from the genuine plank overlap. -/
theorem certifiedPlankDyadicOverlap_secondMoment_le
    (cert : forall i, PlankDimensionsCertificate C a b (F i))
    (levels : Finset kappa)
    (level : iota -> iota -> Option kappa)
    (inverseSineWeight : kappa -> ENNReal)
    (container : iota -> Option kappa -> ConvexBody Space)
    (D A : ENNReal)
    (hlevel : forall i j, level i j ∈ plankAngleLevels levels)
    (htransverse : forall i j k, level i j = some k ->
      0 < certifiedPlankPairSine cert i j)
    (hinverse : forall i j k, level i j = some k ->
      ENNReal.ofReal ((certifiedPlankPairSine cert i j)⁻¹) <=
        inverseSineWeight k)
    (hcontained : forall i j,
      (F j : Set Space) ⊆ (container i (level i j) : Set Space))
    (hKT : IsKatzTao D F)
    (hscale : forall i k, k ∈ plankAngleLevels levels ->
      certifiedPlankAngleScale C a b inverseSineWeight k *
          volume (container i k : Set Space) <=
        A * volume (Y.carrier i)) :
    (∫⁻ x, (Y.pointMultiplicity x : ENNReal) ^ 2 ∂volume) <=
      (((plankAngleLevels levels).card : ENNReal) * D * A) *
        Y.shadingMass := by
  apply dyadicOverlap_secondMoment_le
    (plankAngleLevels levels) level container
    (fun _ k => certifiedPlankAngleScale C a b inverseSineWeight k)
    D A hlevel ?_ hcontained hKT hscale
  intro i' j'
  exact certifiedPlank_pairwiseOverlap_le_angleScale cert level
    inverseSineWeight htransverse hinverse i' j'

/-- Explicit Cordoba factor after summing exceptional and genuine angle
buckets.  Its scale premise still exposes `a / b`. -/
def certifiedPlankDyadicFactor
    (levels : Finset kappa) (D A : ENNReal) : ENNReal :=
  ((plankAngleLevels levels).card : ENNReal) * D * A

/-- Restatement of the second moment with the named factor. -/
theorem certifiedPlankDyadicSecondMoment_le
    (cert : forall i, PlankDimensionsCertificate C a b (F i))
    (levels : Finset kappa)
    (level : iota -> iota -> Option kappa)
    (inverseSineWeight : kappa -> ENNReal)
    (container : iota -> Option kappa -> ConvexBody Space)
    (D A : ENNReal)
    (hlevel : forall i j, level i j ∈ plankAngleLevels levels)
    (htransverse : forall i j k, level i j = some k ->
      0 < certifiedPlankPairSine cert i j)
    (hinverse : forall i j k, level i j = some k ->
      ENNReal.ofReal ((certifiedPlankPairSine cert i j)⁻¹) <=
        inverseSineWeight k)
    (hcontained : forall i j,
      (F j : Set Space) ⊆ (container i (level i j) : Set Space))
    (hKT : IsKatzTao D F)
    (hscale : forall i k, k ∈ plankAngleLevels levels ->
      certifiedPlankAngleScale C a b inverseSineWeight k *
          volume (container i k : Set Space) <=
        A * volume (Y.carrier i)) :
    (∫⁻ x, (Y.pointMultiplicity x : ENNReal) ^ 2 ∂volume) <=
      certifiedPlankDyadicFactor levels D A * Y.shadingMass := by
  simpa [certifiedPlankDyadicFactor] using
    certifiedPlankDyadicOverlap_secondMoment_le cert levels level
      inverseSineWeight container D A hlevel htransverse hinverse
      hcontained hKT hscale

/-- Division-free shaded-union estimate. -/
theorem certifiedPlankDyadic_shadingMass_le
    (cert : forall i, PlankDimensionsCertificate C a b (F i))
    (levels : Finset kappa)
    (level : iota -> iota -> Option kappa)
    (inverseSineWeight : kappa -> ENNReal)
    (container : iota -> Option kappa -> ConvexBody Space)
    (D A : ENNReal)
    (hlevel : forall i j, level i j ∈ plankAngleLevels levels)
    (htransverse : forall i j k, level i j = some k ->
      0 < certifiedPlankPairSine cert i j)
    (hinverse : forall i j k, level i j = some k ->
      ENNReal.ofReal ((certifiedPlankPairSine cert i j)⁻¹) <=
        inverseSineWeight k)
    (hcontained : forall i j,
      (F j : Set Space) ⊆ (container i (level i j) : Set Space))
    (hKT : IsKatzTao D F)
    (hscale : forall i k, k ∈ plankAngleLevels levels ->
      certifiedPlankAngleScale C a b inverseSineWeight k *
          volume (container i k : Set Space) <=
        A * volume (Y.carrier i)) :
    Y.shadingMass <= certifiedPlankDyadicFactor levels D A *
      volume Y.shadedUnion := by
  apply shadingMass_le_factor_mul_volume_shadedUnion_of_secondMoment_le
  exact certifiedPlankDyadicSecondMoment_le cert levels level
    inverseSineWeight container D A hlevel htransverse hinverse
    hcontained hKT hscale

/-- Average multiplicity is derived from the certified plank geometry. -/
theorem certifiedPlankDyadic_averageMultiplicity_le
    (cert : forall i, PlankDimensionsCertificate C a b (F i))
    (levels : Finset kappa)
    (level : iota -> iota -> Option kappa)
    (inverseSineWeight : kappa -> ENNReal)
    (container : iota -> Option kappa -> ConvexBody Space)
    (D A : ENNReal)
    (hlevel : forall i j, level i j ∈ plankAngleLevels levels)
    (htransverse : forall i j k, level i j = some k ->
      0 < certifiedPlankPairSine cert i j)
    (hinverse : forall i j k, level i j = some k ->
      ENNReal.ofReal ((certifiedPlankPairSine cert i j)⁻¹) <=
        inverseSineWeight k)
    (hcontained : forall i j,
      (F j : Set Space) ⊆ (container i (level i j) : Set Space))
    (hKT : IsKatzTao D F)
    (hscale : forall i k, k ∈ plankAngleLevels levels ->
      certifiedPlankAngleScale C a b inverseSineWeight k *
          volume (container i k : Set Space) <=
        A * volume (Y.carrier i)) :
    Y.averageMultiplicity <= certifiedPlankDyadicFactor levels D A := by
  apply averageMultiplicity_le_factor_of_secondMoment_le
  exact certifiedPlankDyadicSecondMoment_le cert levels level
    inverseSineWeight container D A hlevel htransverse hinverse
    hcontained hKT hscale

#print axioms certifiedPlank_pairwiseOverlap_le_angleScale
#print axioms certifiedPlankDyadicOverlap_row_le
#print axioms certifiedPlankDyadicOverlap_secondMoment_le
#print axioms certifiedPlankDyadic_shadingMass_le
#print axioms certifiedPlankDyadic_averageMultiplicity_le

end

end Family8CertifiedPlankDyadicCordobaV2
