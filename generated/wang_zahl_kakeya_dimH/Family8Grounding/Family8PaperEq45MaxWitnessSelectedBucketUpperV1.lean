import Family8Grounding.Family8PaperEq45MaxWitnessCommonScaleCanonicalV2
import Mathlib.Tactic

/-!
# Max-witness Equation (45) with actual selected-bucket target scales

The geometric Family 6 datum remains the literal common-scale max-witness
family.  Its final scalar absorption may target any pair `a,b`; downstream
these are instantiated by the actual mass-popular selected-parent bucket.
This is a scalar-only generalization of the existing isotropic absorption,
not a multiplicity callback or an occurrence-dependent affine reindexing.
-/

open Set MeasureTheory
open scoped BigOperators ENNReal NNReal

namespace Family8PaperEq45MaxWitnessSelectedBucketUpperV1

open LeanEval.Analysis.WangZahlKakeya
open Submission.Kakeya.ConvexGeometry
open Submission.Kakeya.ConvexFactoring
open Submission.Kakeya.ConvexFactoring.FullConvexMaximalDensity
open Submission.Kakeya.ConvexFactoring.GreedyOccurrenceFactorization
open Submission.Kakeya.Uniformity
open Family6AffinePlankAnalyticHypothesesStableV1
open Family8DoubledParentConflictWeightedRetentionV3.ScaleCover
open Family8PaperEq45MaxWitnessCommonScaleCanonicalV2
open Family8PaperEq45MaxWitnessCommonScaleCanonicalV2.PaperEq45MaxWitnessCommonScaleInput
open Family8Prop66AOuterInnerProductAlgebraV1
open Family8SelectedOccurrenceDensityFrostmanV1
open Family8SelectedOccurrenceMaxOwnerWeightedRetentionV1
open Family8SelectedOccurrenceMaxWitnessCommonScaleV1
open FamilyStickyAtEveryScaleCoreV1

noncomputable section

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 5000000

local instance (p : Prop) : Decidable p := Classical.propDecidable p

variable {delta rho : NNReal} {index : Type}
  [Fintype index] [DecidableEq index]
  {fine : UniformTubeFamily delta index}
  (C : StickyScaleCover fine rho)
  {P : GreedyDensityPartition fine.bodyFamily
    (hullCandidates C.activeFine) (hullContainer fine.bodyFamily)
    C.activeFine}
  {Y : Shading fine.bodyFamily}
  {R0 : Finset (Fin (blocks fine.bodyFamily P).length)}
  {conflictLoss : ENNReal}
  {W : DoubledParentConflictWeightedSelection C
    (occurrenceMaxOwnerMass C P Y R0) conflictLoss}

/-- Scalar-only absorption of the genuine max-witness Family 6 factor into
Equation (45) at the two scales selected by a downstream actual bucket. -/
def SelectedBucketScaleAbsorption
    (I : PaperEq45MaxWitnessCommonScaleInput C Y R0 conflictLoss W)
    (delta0 a b : NNReal) (lemmaEpsilon epsilon beta : Real) : Prop :=
  family6Factor C I lemmaEpsilon beta ≤
    proposition66AOuterFactor delta0 a b (plankCount C I)
      I.frostmanConstant epsilon beta

/-- Callback-free Eq. (45) upper producer at arbitrary target scales. -/
theorem exists_family6Parameters_sourceAverage_le_eq45_at_selectedBucketScales
    (I : PaperEq45MaxWitnessCommonScaleInput C Y R0 conflictLoss W)
    {a b : NNReal} {beta : Real}
    (H : ConvexPlankFrostmanMultiplicityHypothesis
      {q // q ∈ selectedOccurrenceIndices P (selected C I)} beta)
    (delta0 : NNReal) (lemmaEpsilon epsilon : Real)
    (hlemmaEpsilon : 0 < lemmaEpsilon)
    (habsorb : SelectedBucketScaleAbsorption C I delta0 a b
      lemmaEpsilon epsilon beta) :
    ∃ eta : Real, ∃ b0 : NNReal,
      0 < eta ∧ 0 < b0 ∧
      ∀ (_hw : 0 < maxWitnessCommonWidth delta),
        maxWitnessCommonWidth delta ≤ b0 →
        (maxWitnessCommonWidth delta : ENNReal) ^ eta ≤
          (datum C I).shading.shadingDensity →
        (selectedOccurrenceOuterShading P Y R0).averageMultiplicity ≤
          ((((I.fibreCardCap : ENNReal) * conflictLoss) *
            (I.fibreCardCap : ENNReal)) *
              proposition66AOuterFactor delta0 a b (plankCount C I)
                I.frostmanConstant epsilon beta) := by
  obtain ⟨eta, b0, heta, hb0, hrefined⟩ :=
    exists_family6Parameters_refinedAverage_le C I H lemmaEpsilon
      hlemmaEpsilon
  refine ⟨eta, b0, heta, hb0, ?_⟩
  intro hw hwb0 hdensity
  exact (sourceAverage_le_refined C I).trans (by
    gcongr
    exact (hrefined hw hwb0 hdensity).trans habsorb)

#print axioms SelectedBucketScaleAbsorption
#print axioms
  exists_family6Parameters_sourceAverage_le_eq45_at_selectedBucketScales

end
end Family8PaperEq45MaxWitnessSelectedBucketUpperV1
