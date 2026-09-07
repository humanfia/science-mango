import Family6Grounding.Family6Lemma69DeltaBCPlankGeometryV1
import Family8Grounding.Family8Lemma69ActualTubeDensityCardPaymentV1
import Family8Grounding.Family8Prop66AFrostmanUnionVolumeAverageAdapterV1

/-!
# Same-datum `delta x b x c` Lemma 6.9 to Equation (32)

This composer stays on the shading of one `ActualTubeDatum`.  Genuine
`delta x b x c` certificates produce the pairwise overlap estimate through
the normalized plank geometry, so no `hpairwise` callback appears here.
The remaining angle assignment, row containers, Katz--Tao input, and scale
comparison are precisely those consumed by the geometric budget producer.
-/

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 4000000

open Set MeasureTheory
open scoped ENNReal NNReal

namespace Family8Lemma69ActualTubeDeltaBCGeometryEq32ComposerV1

open LeanEval.Analysis.WangZahlKakeya
open Submission.Kakeya.ConvexGeometry
open Submission.Kakeya.ConvexFactoring
open Family6Lemma69DeltaBCPlankGeometryV1
open Family8CertifiedPlankDyadicCordobaV2
open Family8KatzTaoFrostmanPropertiesV1
open Family8Prop66AFrostmanAspectGainAlgebraV1
open Family8Prop66AFrostmanUnionVolumeAverageAdapterV1
open Family8Lemma69ActualTubeDensityCardPaymentV1

noncomputable section

/-- Direct same-object composition of genuine `delta x b x c` pair geometry,
the Lemma 6.9 union floor, and the Equation (32) average adapter.  Compared
with the generic dyadic composer, `hpairwise` is derived internally from
`cert`, `htransverse`, and `hinverse`. -/
theorem actualTube_eq32_of_lemma69_deltaBCGeometry_densityCardPayments
    {delta : NNReal} {index : Type}
    [Fintype index] [DecidableEq index]
    {angleIndex : Type*} [DecidableEq angleIndex]
    (D : ActualTubeDatum delta index)
    {geometryC plankB plankC : NNReal}
    (cert : ∀ i,
      DeltaBCDimensionsCertificate geometryC delta plankB plankC
        (D.family.bodyFamily i))
    (hplankC : 0 < plankC)
    (levels : Finset angleIndex)
    (level : index → index → Option angleIndex)
    (inverseSineWeight : angleIndex → ENNReal)
    (container : index → Option angleIndex → ConvexBody Space)
    (a b : NNReal)
    (CF externalLoss unionVolumeFloor densityFloor KT rowScale : ENNReal)
    (epsilon beta : Real)
    (hdeltaHalf : delta ≤ (2 : NNReal)⁻¹)
    (hdensity : densityFloor ≤ D.shading.shadingDensity)
    (hMass : D.shading.shadingMass ≠ 0)
    (hlevel : ∀ i j, level i j ∈ plankAngleLevels levels)
    (htransverse : ∀ i j k, level i j = some k →
      0 < certifiedPlankPairSine
        (deltaBCNormalizedPlankCertificate cert hplankC) i j)
    (hinverse : ∀ i j k, level i j = some k →
      ENNReal.ofReal
          ((certifiedPlankPairSine
            (deltaBCNormalizedPlankCertificate cert hplankC) i j)⁻¹) ≤
        inverseSineWeight k)
    (hcontained : ∀ i j,
      (D.family.bodyFamily j : Set Space) ⊆
        (container i (level i j) : Set Space))
    (hKT : IsKatzTao KT D.family.bodyFamily)
    (hscale : ∀ i k, k ∈ plankAngleLevels levels →
      certifiedPlankAngleScale geometryC (delta / plankC) (plankB / plankC)
          inverseSineWeight k *
          volume (container i k : Set Space) ≤
        rowScale * volume (D.shading.carrier i))
    (habsorbScalar :
      unionVolumeFloor *
          (((plankAngleLevels levels).card : ENNReal) * KT * rowScale) ≤
        densityFloor *
          ((Fintype.card index : ENNReal) *
            ((delta : ENNReal) ^ 2 / 2)))
    (hupperScalar :
      (Fintype.card index : ENNReal) *
          (8 * (delta : ENNReal) ^ 2) ≤
        (externalLoss * proposition66AFrostmanFactor delta a b
          (Fintype.card index) CF epsilon beta) * unionVolumeFloor) :
    D.shading.averageMultiplicity ≤
      externalLoss * proposition66AFrostmanFactor delta a b
        (Fintype.card index) CF epsilon beta := by
  let rhs : ENNReal :=
    externalLoss * proposition66AFrostmanFactor delta a b
      (Fintype.card index) CF epsilon beta
  have hpayments :
      unionVolumeFloor *
            (((plankAngleLevels levels).card : ENNReal) * KT * rowScale) ≤
          D.shading.shadingMass ∧
        D.shading.shadingMass ≤ rhs * unionVolumeFloor := by
    apply lemma69_actualTube_productPayments_of_densityCardBudgets
      D (plankAngleLevels levels) densityFloor KT rowScale
        unionVolumeFloor rhs hdeltaHalf hdensity
    · exact habsorbScalar
    · exact hupperScalar
  have hbudget :
      unionVolumeFloor *
          (∑ i, ∑ j,
            volume (D.shading.carrier i ∩ D.shading.carrier j)) ≤
        D.shading.shadingMass ^ 2 := by
    exact lemma69_overlapBudget_of_deltaBCPairwiseFrostman
      D.shading cert hplankC levels level inverseSineWeight container
        KT rowScale unionVolumeFloor hlevel htransverse hinverse
        hcontained hKT hscale hpayments.1
  have hunion :
      unionVolumeFloor ≤ volume D.shading.shadedUnion :=
    lemma69_union_of_overlapBudget D.shading hMass hbudget
  exact
    actualTube_averageMultiplicity_le_loss_mul_proposition66AFrostmanFactor_of_unionVolumeFloor
      D a b CF externalLoss unionVolumeFloor epsilon beta hunion hpayments.2

#print axioms
  actualTube_eq32_of_lemma69_deltaBCGeometry_densityCardPayments

end
end Family8Lemma69ActualTubeDeltaBCGeometryEq32ComposerV1
