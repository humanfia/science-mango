import Family8Grounding.Family8Lemma69ActualTubeDensityCardPaymentV1
import Family8Grounding.Family8Prop66AFrostmanUnionVolumeAverageAdapterV1
import Family6Grounding.Family6Lemma69OverlapBudgetProducerV1

/-!
# Thin Lemma 6.9 to Equation (32) composer

This file only composes three existing stages on the shading of one actual
tube datum: the dyadic pair-overlap budget, the Lemma 6.9 union-volume floor,
and the union-floor-to-average adapter.  The geometric pairwise inputs, the
nonzero-mass input, and both scalar payments remain explicit premises.
-/

open Set MeasureTheory
open scoped ENNReal NNReal

namespace Family8Lemma69ActualTubeEq32ComposerV1
open LeanEval.Analysis.WangZahlKakeya

open Submission.Kakeya.ConvexGeometry
open Submission.Kakeya.ConvexFactoring
open Family8KatzTaoFrostmanPropertiesV1
open Family8Prop66AFrostmanAspectGainAlgebraV1
open Family8Prop66AFrostmanUnionVolumeAverageAdapterV1
open Family8Lemma69ActualTubeDensityCardPaymentV1

noncomputable section

set_option autoImplicit false
set_option warningAsError true

/-- Direct composition of the dyadic Lemma 6.9 overlap producer, its union
floor, and the Equation (32) average-multiplicity adapter.  No division or
cancellation is exposed at this interface. -/
theorem actualTube_eq32_of_lemma69_dyadicOverlap_densityCardPayments
    {delta : NNReal} {index : Type}
    [Fintype index] [DecidableEq index]
    {levelIndex : Type*} [DecidableEq levelIndex]
    (D : ActualTubeDatum delta index)
    (levels : Finset levelIndex)
    (level : index -> index -> levelIndex)
    (container : index -> levelIndex -> ConvexBody Space)
    (pairFactor : index -> levelIndex -> ENNReal)
    (a b : NNReal)
    (CF externalLoss unionVolumeFloor densityFloor C A : ENNReal)
    (epsilon beta : Real)
    (hdeltaHalf : delta <= (2 : NNReal)⁻¹)
    (hdensity : densityFloor <= D.shading.shadingDensity)
    (hMass : D.shading.shadingMass ≠ 0)
    (hlevel : forall i j, level i j ∈ levels)
    (hpairwise : forall i j,
      volume (D.shading.carrier i ∩ D.shading.carrier j) <=
        pairFactor i (level i j) *
          volume (D.family.bodyFamily j : Set Space))
    (hcontained : forall i j,
      (D.family.bodyFamily j : Set Space) <=
        (container i (level i j) : Set Space))
    (hKT : IsKatzTao C D.family.bodyFamily)
    (hscale : forall i k, k ∈ levels ->
      pairFactor i k * volume (container i k : Set Space) <=
        A * volume (D.shading.carrier i))
    (habsorbScalar :
      unionVolumeFloor * (((levels.card : ENNReal) * C * A)) <=
        densityFloor *
          ((Fintype.card index : ENNReal) *
            ((delta : ENNReal) ^ 2 / 2)))
    (hupperScalar :
      (Fintype.card index : ENNReal) *
          (8 * (delta : ENNReal) ^ 2) <=
        (externalLoss * proposition66AFrostmanFactor delta a b
          (Fintype.card index) CF epsilon beta) * unionVolumeFloor) :
    D.shading.averageMultiplicity <=
      externalLoss * proposition66AFrostmanFactor delta a b
        (Fintype.card index) CF epsilon beta := by
  let rhs : ENNReal :=
    externalLoss * proposition66AFrostmanFactor delta a b
      (Fintype.card index) CF epsilon beta
  have hpayments :
      unionVolumeFloor * (((levels.card : ENNReal) * C * A)) <=
          D.shading.shadingMass ∧
        D.shading.shadingMass <= rhs * unionVolumeFloor := by
    apply lemma69_actualTube_productPayments_of_densityCardBudgets
      D levels densityFloor C A unionVolumeFloor rhs hdeltaHalf hdensity
    · exact habsorbScalar
    · exact hupperScalar
  have hbudget :
      unionVolumeFloor *
          (∑ i, ∑ j,
            volume (D.shading.carrier i ∩ D.shading.carrier j)) <=
        D.shading.shadingMass ^ 2 := by
    exact lemma69_overlapBudget_of_dyadicPairwiseFrostman
      D.shading levels level container pairFactor C A unionVolumeFloor
        hlevel hpairwise hcontained hKT hscale hpayments.1
  have hunion :
      unionVolumeFloor <= volume D.shading.shadedUnion :=
    lemma69_union_of_overlapBudget D.shading hMass hbudget
  exact
    actualTube_averageMultiplicity_le_loss_mul_proposition66AFrostmanFactor_of_unionVolumeFloor
      D a b CF externalLoss unionVolumeFloor epsilon beta hunion hpayments.2

#print axioms
  actualTube_eq32_of_lemma69_dyadicOverlap_densityCardPayments

end
end Family8Lemma69ActualTubeEq32ComposerV1
