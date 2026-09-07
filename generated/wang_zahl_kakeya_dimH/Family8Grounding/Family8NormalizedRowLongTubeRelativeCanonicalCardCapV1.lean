import Family8Grounding.Family8GeneralizedFrostmanRelativeCanonicalCardInterpolationV1
import Family8Grounding.Family8NormalizedRowLongTubeCanonicalFrostmanComparisonV1
import Mathlib.Tactic

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 1000000
set_option linter.unusedSectionVars false

open Set MeasureTheory
open scoped ENNReal NNReal BigOperators

namespace Family8NormalizedRowLongTubeRelativeCanonicalCardCapV1

open LeanEval.Analysis.WangZahlKakeya
open Submission.Kakeya.ConvexGeometry
open Submission.Kakeya.ConvexFactoring
open Submission.Kakeya.Uniformity
open Family6AffinePlankAnalyticHypothesesStableV1
open Family8FiniteRandomRigidMotionB2NormalizedDatumV1
open Family8GeneralizedFrostmanCanonicalCardInterpolationV1
open Family8GeneralizedFrostmanRelativeCanonicalCardInterpolationV1
open Family8NormalizedRowLongTubeCanonicalFrostmanComparisonV1
open Family8PlankFixedThetaAllSlabEq43FrostmanProducerV1
open Family8PlankFixedThetaAllSlabRowsV1
open Family8PlankHeavyRetainedOwnerActualDatumV2
open Family8PlankLongTubeFrostmanAtParametersProducerV1
open Family8PlankThickControlMutualContainmentClusteringV2

noncomputable section

/-!
# Relative canonical-card cap for a normalized plank row

This is only the monotone substitution seam from the canonical Frostman
constant comparison for the genuine normalized row long-tube source into the
relative canonical-card interpolation target.  It neither constructs the
good rigid-copy/refinement datum nor applies generalized Frostman, and it uses
no convex-plank `BoundAt` or Family 7 union conclusion.

The row comparison loss remains a separate
`(1 - gamma / 2)`-power.  This makes the later row-base cancellation ledger
visible instead of hiding it in the row Frostman envelope.
-/

/-- Substituting the row canonical-Frostman comparison into the relative
canonical-card RHS exposes separate powers of the geometric comparison loss
and the retained-source row Frostman envelope. -/
theorem relativeCanonicalCardFrostmanRHS_normalizedRowLongTubeSource_le
    {iota : Type} [Fintype iota] [DecidableEq iota]
    {a b theta : NNReal}
    {D : ShadedConvexPlankFamily iota a b}
    {C : MutualThickeningClustering D theta}
    {q : Fin (Nat.log 2 (Fintype.card iota) + 1)}
    {rowIndex : Type} [Fintype rowIndex] [DecidableEq rowIndex]
    {slabComparisonConstant : NNReal}
    {R : FixedThetaAllSlabRows D C q rowIndex slabComparisonConstant}
    {normalize : rowIndex → Space ≃ᵃ[Real] Space}
    (P : FixedThetaAllSlabRowNormalizationGeometry R normalize)
    (r : rowIndex)
    {restrictionLoss sourceCF : ENNReal}
    {tau : NNReal} {epsilon gamma : Real}
    (hsource : IsFrostmanIn sourceCF
      (heavyRetainedOwnerThickenedFamily D C q) P.sourceAmbient)
    (Hretention : FixedThetaAllSlabRowRestrictionLossCertificate
      P restrictionLoss)
    (hlongHalf : P.longWidth r ≤ (2 : NNReal)⁻¹)
    (hgamma : gamma ≤ 2) :
    relativeCanonicalCardFrostmanRHS
        (eighthNormalizedDatum (normalizedRowLongTubeSource P r))
        tau epsilon gamma ≤
      (tau : ENNReal) ^ (-epsilon) *
        ((normalizedRowLongTubeCanonicalFrostmanLoss P r) ^
            (1 - gamma / 2) *
          (P.rowFrostmanEnvelopeWithRestrictionLoss
            restrictionLoss sourceCF r) ^ (1 - gamma / 2)) *
        (((P.longWidth r / 8 : NNReal) : ENNReal) ^ (-2 * gamma)) *
        sourceCardScaleVolume
          (eighthNormalizedDatum (normalizedRowLongTubeSource P r)) ^
            (1 - gamma / 2) := by
  have hp : 0 ≤ 1 - gamma / 2 := by
    linarith
  have hcanonical :=
    sourceCanonicalFrostmanConstant_normalizedRowLongTubeSource_le
      P r (restrictionLoss := restrictionLoss) (sourceCF := sourceCF)
        hsource Hretention hlongHalf
  have hcanonicalPow :
      sourceCanonicalFrostmanConstant
          (eighthNormalizedDatum (normalizedRowLongTubeSource P r)) ^
            (1 - gamma / 2) ≤
        (normalizedRowLongTubeCanonicalFrostmanLoss P r *
          P.rowFrostmanEnvelopeWithRestrictionLoss
            restrictionLoss sourceCF r) ^ (1 - gamma / 2) :=
    ENNReal.rpow_le_rpow hcanonical hp
  unfold relativeCanonicalCardFrostmanRHS
  calc
    (tau : ENNReal) ^ (-epsilon) *
          sourceCanonicalFrostmanConstant
              (eighthNormalizedDatum
                (normalizedRowLongTubeSource P r)) ^
            (1 - gamma / 2) *
          (((P.longWidth r / 8 : NNReal) : ENNReal) ^ (-2 * gamma)) *
          sourceCardScaleVolume
              (eighthNormalizedDatum
                (normalizedRowLongTubeSource P r)) ^
            (1 - gamma / 2) ≤
        (tau : ENNReal) ^ (-epsilon) *
          (normalizedRowLongTubeCanonicalFrostmanLoss P r *
            P.rowFrostmanEnvelopeWithRestrictionLoss
              restrictionLoss sourceCF r) ^ (1 - gamma / 2) *
          (((P.longWidth r / 8 : NNReal) : ENNReal) ^ (-2 * gamma)) *
          sourceCardScaleVolume
              (eighthNormalizedDatum
                (normalizedRowLongTubeSource P r)) ^
            (1 - gamma / 2) := by
      exact mul_le_mul'
        (mul_le_mul' (mul_le_mul' le_rfl hcanonicalPow) le_rfl) le_rfl
    _ = (tau : ENNReal) ^ (-epsilon) *
          ((normalizedRowLongTubeCanonicalFrostmanLoss P r) ^
              (1 - gamma / 2) *
            (P.rowFrostmanEnvelopeWithRestrictionLoss
              restrictionLoss sourceCF r) ^ (1 - gamma / 2)) *
          (((P.longWidth r / 8 : NNReal) : ENNReal) ^ (-2 * gamma)) *
          sourceCardScaleVolume
              (eighthNormalizedDatum
                (normalizedRowLongTubeSource P r)) ^
            (1 - gamma / 2) := by
      rw [ENNReal.mul_rpow_of_nonneg
        (normalizedRowLongTubeCanonicalFrostmanLoss P r)
        (P.rowFrostmanEnvelopeWithRestrictionLoss
          restrictionLoss sourceCF r) hp]

#print axioms
  relativeCanonicalCardFrostmanRHS_normalizedRowLongTubeSource_le

end
end Family8NormalizedRowLongTubeRelativeCanonicalCardCapV1
