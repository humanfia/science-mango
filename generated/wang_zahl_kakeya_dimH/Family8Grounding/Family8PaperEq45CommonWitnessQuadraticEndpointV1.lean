import Family8Grounding.Family8PaperEq45CommonWitnessQuadraticInnerV1
import Mathlib.Tactic

/-!
# Callback-free common-witness Equation (45) x Equation (46) endpoint

This successor discharges the sole analytic-fibre premise of the SAFE V13
endpoint with the actual-source quadratic natural cap constructed in
`Family8PaperEq45CommonWitnessQuadraticInnerV1`.

The result is deliberately a coarse fallback: it makes no claim that the
quadratic cap is the sharper adaptive selected-bucket cap from the paper.
-/

open Set MeasureTheory
open scoped BigOperators ENNReal NNReal

namespace Family8PaperEq45CommonWitnessQuadraticEndpointV1

open LeanEval.Analysis.WangZahlKakeya
open Submission.Kakeya.ConvexGeometry
open Submission.Kakeya.ConvexFactoring
open Submission.Kakeya.ConvexFactoring.FactoringMultiplicityAssembly
open Submission.Kakeya.ConvexFactoring.FullConvexMaximalDensity
open Submission.Kakeya.ConvexFactoring.GreedyOccurrenceFactorization
open Submission.Kakeya.Uniformity
open Family6AffinePlankAnalyticHypothesesStableV1
open Family8DoubledParentConflictWeightedRetentionV3.ScaleCover
open Family8ExactAssemblyActualAverageBridgeV1
open Family8ExactAssemblyActualAverageBridgeV1.ExactAssembly
open Family8GreedyHighOccurrenceSelectedParentJohnPlankConnectorV1
open Family8KatzTaoFrostmanPropertiesV1
open Family8PaperEq45CommonWitnessQuadraticInnerV1
open Family8PaperEq45MaxWitnessAdaptiveEq46EndpointV13
open Family8PaperEq45MaxWitnessCommonScaleCanonicalV2
open Family8PaperEq45MaxWitnessCommonScaleCanonicalV2.PaperEq45MaxWitnessCommonScaleInput
open Family8Prop66AActualFamilyVolumeTransportV1
open Family8Prop66AFrostmanAspectGainAlgebraV1
open Family8SelectedOccurrenceDensityFrostmanV1
open Family8SelectedOccurrenceMaxOwnerWeightedRetentionV1
open Family8SelectedOccurrenceMaxWitnessCommonScaleV1
open Family8SelectedParentGreedyBlockFiberIdentityV2
open Family8StickySelectedParentGreedyBlockFrostmanV3
open FamilyStickyAtEveryScaleCoreV1
open FamilyStickyHierarchyEndpointPrefixShadingTransportV1.StickyScaleCover

noncomputable section

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 6000000

variable {delta rho sigma : NNReal} {index : Type}
  [Fintype index] [DecidableEq index]
  (D : ActualTubeDatum delta index)
  (S : StickyScaleCover D.family rho)
  (U : StickyScaleCover (S.coarse.restrictTo S.activeCoarse) sigma)
  (P : GreedyDensityPartition S.activeCoarseFamily
    (hullCandidates (Finset.univ : Finset (ActiveParentIndex S)))
    (hullContainer S.activeCoarseFamily) Finset.univ)
  {assemblyLoss : Nat}
  (A : FactoringMultiplicityAssembly.ExactAssembly
    (greedyParentFactorization S P)
    (parentAggregatedShading S D.shading) assemblyLoss)
  {conflictLoss : ENNReal}
  (W : DoubledParentConflictWeightedSelection U
    (occurrenceMaxOwnerMass U
      (canonicalUpperPartition S U P)
      A.refinement.shading Finset.univ) conflictLoss)
  (I : PaperEq45MaxWitnessCommonScaleInput U
    A.refinement.shading Finset.univ conflictLoss W)

/-- The V13 same-object endpoint with its final `hinner` premise generated
from the actual active-parent cardinality. -/
theorem exists_family6Parameters_refinementAverage_le_commonWitnessQuadratic_eq45_mul_eq46
    (hsource :
      (IndexedShadingRefinement.restrictTo
        (parentAggregatedShading S D.shading)
        (greedyParentFactorization S P).index.fine).shading.shadingMass ≠ 0)
    {beta : Real}
    (H : ConvexPlankFrostmanMultiplicityHypothesis
      {q // q ∈ selectedOccurrenceIndices
        (canonicalUpperPartition S U P) (selected U I)} beta)
    (lemmaEpsilon epsilon : Real) (hlemmaEpsilon : 0 < lemmaEpsilon)
    (habsorb : ScaleAbsorption U I rho lemmaEpsilon epsilon beta)
    (hrho : 0 < rho) (hrhoHalf : rho <= (2 : NNReal)⁻¹)
    (hepsilon : 0 <= epsilon)
    (hbeta : 0 <= beta) (hbetaOne : beta <= 1) :
    ∃ eta : Real, ∃ b0 : NNReal,
      0 < eta ∧ 0 < b0 ∧
      ∀ (_hw : 0 < maxWitnessCommonWidth rho),
        maxWitnessCommonWidth rho <= b0 →
        (maxWitnessCommonWidth rho : ENNReal) ^ eta <=
          (datum U I).shading.shadingDensity →
        A.refinement.shading.averageMultiplicity <=
          ((((I.fibreCardCap : ENNReal) * conflictLoss) *
              (I.fibreCardCap : ENNReal)) *
            (commonWitnessQuadraticSourceNatCap
              (Fintype.card (ActiveParentIndex S)) : ENNReal) ^
                (1 - beta / 2)) *
          ((proposition66AFrostmanAspectGain
              (maxWitnessCommonWidth rho) (maxWitnessCommonWidth rho)
              I.frostmanConstant beta *
              (2 : ENNReal) ^ (1 - beta / 2)) *
            frostmanMultiplicityRHS rho
              (activeParentActualTubeDatum S D.shading).actualFamilyVolume
              epsilon beta) := by
  apply exists_family6Parameters_refinementAverage_le_witnessEq45_mul_eq46
    D S U P A W I hsource
    (commonWitnessQuadraticSourceNatCap
      (Fintype.card (ActiveParentIndex S)))
    H lemmaEpsilon epsilon hlemmaEpsilon habsorb hrhoHalf hbeta hbetaOne
  intro k hk
  exact sourceFineLevelShading_average_le_commonWitnessQuadraticInner
    D S P A ⟨k, hk⟩ hrho hrhoHalf hepsilon hbeta hbetaOne

#print axioms
  exists_family6Parameters_refinementAverage_le_commonWitnessQuadratic_eq45_mul_eq46

end
end Family8PaperEq45CommonWitnessQuadraticEndpointV1
