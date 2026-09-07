import Family8Grounding.Family8PlankLongTubeFrostmanAtParametersProducerV1
import Family8Grounding.Family8GeneralizedFrostmanRelativeCanonicalCardInterpolationV1
import Family8Grounding.Family8SeparateExactAndRelativeScaleParametersV1
import Mathlib.Tactic

/-!
# Single-row relative canonical-card adapter at an external scale

The all-slab adapter fixes its relative Frostman call scale to the normalized
row's short width.  The plank Frostman argument also needs the more primitive
interface in which a caller supplies one common fine scale `tau` after the
source `FrostmanProperty` has selected its parameters.

This file provides exactly that single-row interface.  Its certificate is
literal refined-datum data, not a conclusion-valued callback: it consists of
`RelativeCanonicalCardRefinedFrostmanData` at the caller's `tau` and the
remaining epsilon-slack inequality.  No good rigid-copy refinement is
constructed here, and no all-row, convex-plank `BoundAt`, or Family 7
hypothesis is used.
-/

set_option autoImplicit false
set_option warningAsError true
set_option linter.unusedSectionVars false
set_option maxHeartbeats 3000000

open Set MeasureTheory
open scoped BigOperators ENNReal NNReal

namespace Family8PlankFixedThetaSingleRowExternalTauCanonicalCardFrostmanAdapterV1

open LeanEval.Analysis.WangZahlKakeya
open Submission.Kakeya.ConvexGeometry
open Submission.Kakeya.ConvexFactoring
open Submission.Kakeya.Uniformity
open Family6AffinePlankAnalyticHypothesesStableV1
open Family8KatzTaoFrostmanPropertiesV1
open Family8GeneralizedScaleTrivialBranchV1
open Family8GeneralizedFrostmanRelativeCanonicalCardInterpolationV1
open Family8SeparateExactAndRelativeScaleParametersV1
open Family8FiniteRandomRigidMotionB2NormalizedDatumV1
open Family8PlankThickControlMutualContainmentClusteringV2
open Family8PlankFixedThetaAllSlabRowsV1
open Family8PlankFixedThetaAllSlabEq43FrostmanProducerV1
open Family8PlankLongTubeFrostmanAtParametersProducerV1
open Family8PlankHeavyActiveSelectedOwnerPropertyReadyFrostmanConnectorV1

noncomputable section

variable {iota : Type} [Fintype iota] [DecidableEq iota]
variable {a b theta : NNReal}
variable {D : ShadedConvexPlankFamily iota a b}
variable {C : MutualThickeningClustering D theta}
variable {q : Fin (Nat.log 2 (Fintype.card iota) + 1)}
variable {rowIndex : Type} [Fintype rowIndex] [DecidableEq rowIndex]
variable {slabComparisonConstant : NNReal}
variable {R : FixedThetaAllSlabRows D C q rowIndex slabComparisonConstant}
variable {normalize : rowIndex → Space ≃ᵃ[Real] Space}

/-- The canonical actual-tube source for the external-`tau` row adapter:
the genuine centered row long-tube datum followed by the common eighth
normalization. -/
abbrev normalizedRowExternalTauCanonicalCardSource
    (P : FixedThetaAllSlabRowNormalizationGeometry R normalize)
    (r : rowIndex) :
    ActualTubeDatum
      (plankLongTubeNormalizedRadius (P.normalizedRowDatum r))
      (Unit × {s // s ∈ R.rowOwners r}) :=
  eighthNormalizedDatum (normalizedRowLongTubeSource P r)

/-- The weakest relative canonical-card good-copy certificate for one row at
a caller-supplied scale `tau`.

The refined type and datum are literal existential witnesses.  The first
conjunct records admissibility, relative density and Frostman control,
average retention, and the copied-cardinality estimate.  The second conjunct
is the sole remaining scalar absorption. -/
def NormalizedRowExternalTauRelativeCanonicalCardGoodCopyCertificate
    (P : FixedThetaAllSlabRowNormalizationGeometry R normalize)
    (r : rowIndex) (tau : NNReal)
    (eta epsilonF epsilon gamma : Real) : Prop :=
  ∃ refinedIndex : Type,
  ∃ refinedFintype : Fintype refinedIndex,
  ∃ refinedDecidableEq : DecidableEq refinedIndex,
  ∃ refined : @ActualTubeDatum
      (plankLongTubeNormalizedRadius (P.normalizedRowDatum r))
      refinedIndex refinedFintype refinedDecidableEq,
  ∃ greedyLoss copyCardLoss : ENNReal,
    @RelativeCanonicalCardRefinedFrostmanData
        (plankLongTubeNormalizedRadius (P.normalizedRowDatum r))
        (Unit × {s // s ∈ R.rowOwners r}) refinedIndex
        inferInstance inferInstance refinedFintype refinedDecidableEq
        (normalizedRowExternalTauCanonicalCardSource P r) refined tau eta
        greedyLoss copyCardLoss ∧
    greedyLoss * (8 * copyCardLoss) ^ (1 - gamma / 2) *
          (tau : ENNReal) ^ (-epsilonF) ≤
      (tau : ENNReal) ^ (-epsilon)

/-- Apply the relative Frostman estimate to one normalized row at a completely
external call scale.  The scale's positivity, comparison with the actual
long-tube radius, and terminal-radius comparison remain explicit geometric
premises. -/
theorem
    normalizedRow_averageMultiplicity_le_externalTauRelativeCanonicalCardFrostmanRHS
    {eta epsilonF epsilon gamma : Real} {delta0 : NNReal}
    (hF : FrostmanAtRelativeScaleParameters gamma epsilonF eta delta0)
    (P : FixedThetaAllSlabRowNormalizationGeometry R normalize)
    (r : rowIndex) (tau : NNReal)
    (hdelta0 :
      plankLongTubeNormalizedRadius (P.normalizedRowDatum r) ≤ delta0)
    (htau : 0 < tau)
    (htauRadius :
      tau ≤ plankLongTubeNormalizedRadius (P.normalizedRowDatum r))
    (hgamma : gamma ≤ 2)
    (G : NormalizedRowExternalTauRelativeCanonicalCardGoodCopyCertificate
      P r tau eta epsilonF epsilon gamma) :
    (P.normalizedRowDatum r).shading.averageMultiplicity ≤
      relativeCanonicalCardFrostmanRHS
        (normalizedRowExternalTauCanonicalCardSource P r)
        tau epsilon gamma := by
  obtain ⟨refinedIndex, refinedFintype, refinedDecidableEq, refined,
      greedyLoss, copyCardLoss, hgoodCopy, hscalar⟩ := G
  let _ : Fintype refinedIndex := refinedFintype
  let _ : DecidableEq refinedIndex := refinedDecidableEq
  have hcanonical :
      (normalizedRowExternalTauCanonicalCardSource P r).shading.averageMultiplicity ≤
        relativeCanonicalCardFrostmanRHS
          (normalizedRowExternalTauCanonicalCardSource P r)
          tau epsilon gamma := by
    exact averageMultiplicity_le_relativeCanonicalCardFrostmanRHS
      hF hgoodCopy hdelta0 htau htauRadius hgamma hscalar
  have hcentered :
      (P.normalizedRowDatum r).shading.averageMultiplicity ≤
        (normalizedRowLongTubeSource P r).shading.averageMultiplicity :=
    source_averageMultiplicity_le_centeredPlankLongTubeActualDatum
      (P.normalizedRowDatum r)
  calc
    (P.normalizedRowDatum r).shading.averageMultiplicity ≤
        (normalizedRowLongTubeSource P r).shading.averageMultiplicity :=
      hcentered
    _ = (normalizedRowExternalTauCanonicalCardSource P r).shading.averageMultiplicity :=
      (eighthNormalizedDatum_averageMultiplicity
        (normalizedRowLongTubeSource P r)).symm
    _ ≤ relativeCanonicalCardFrostmanRHS
        (normalizedRowExternalTauCanonicalCardSource P r)
        tau epsilon gamma := hcanonical

/-- Property-level single-row adapter with the correct quantifier order.
The source property chooses one common `eta` and `delta0` before the plank
family, catalogue, normalization, row, external `tau`, and literal good-copy
certificate are introduced. -/
theorem
    exists_parameters_normalizedRow_externalTauRelativeCanonicalCardFrostmanRHS
    {gamma epsilonF epsilon : Real}
    (hF : FrostmanProperty gamma) (hgamma0 : 0 ≤ gamma)
    (hgamma1 : gamma ≤ 1) (hepsilonF : 0 < epsilonF) :
    ∃ eta : Real, ∃ delta0 : NNReal,
      0 < eta ∧ 0 < delta0 ∧ delta0 ≤ (2 : NNReal)⁻¹ ∧
      ∀ {iota : Type} [Fintype iota] [DecidableEq iota]
        {a b theta : NNReal}
        {D : ShadedConvexPlankFamily iota a b}
        {C : MutualThickeningClustering D theta}
        {q : Fin (Nat.log 2 (Fintype.card iota) + 1)}
        {rowIndex : Type} [Fintype rowIndex] [DecidableEq rowIndex]
        {slabComparisonConstant : NNReal}
        {R : FixedThetaAllSlabRows D C q rowIndex slabComparisonConstant}
        {normalize : rowIndex → Space ≃ᵃ[Real] Space}
        (P : FixedThetaAllSlabRowNormalizationGeometry R normalize)
        (r : rowIndex) (tau : NNReal),
        plankLongTubeNormalizedRadius (P.normalizedRowDatum r) ≤ delta0 →
        0 < tau →
        tau ≤ plankLongTubeNormalizedRadius (P.normalizedRowDatum r) →
        NormalizedRowExternalTauRelativeCanonicalCardGoodCopyCertificate
            P r tau eta epsilonF epsilon gamma →
        (P.normalizedRowDatum r).shading.averageMultiplicity ≤
          relativeCanonicalCardFrostmanRHS
            (normalizedRowExternalTauCanonicalCardSource P r)
            tau epsilon gamma := by
  obtain ⟨eta, delta0, heta, hdelta0, hdelta0Half,
      _hExact, hRelative⟩ :=
    exists_exactAndRelativeScale_frostman_parameters
      hF hgamma0 hgamma1 hepsilonF
  refine ⟨eta, delta0, heta, hdelta0, hdelta0Half, ?_⟩
  intro iota _ _ a b theta D C q rowIndex _ _ slabComparisonConstant
    R normalize P r tau hterminal htau htauRadius G
  exact
    normalizedRow_averageMultiplicity_le_externalTauRelativeCanonicalCardFrostmanRHS
      hRelative P r tau hterminal htau htauRadius
        (hgamma1.trans (by norm_num)) G

#print axioms
  normalizedRow_averageMultiplicity_le_externalTauRelativeCanonicalCardFrostmanRHS
#print axioms
  exists_parameters_normalizedRow_externalTauRelativeCanonicalCardFrostmanRHS

end
end Family8PlankFixedThetaSingleRowExternalTauCanonicalCardFrostmanAdapterV1
