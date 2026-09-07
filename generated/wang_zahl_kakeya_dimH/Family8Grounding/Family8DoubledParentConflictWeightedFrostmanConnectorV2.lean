import Family8Grounding.Family8DoubledParentConflictWeightedShadingMassBridgeV2
import Family8Grounding.Family8FiniteRandomRigidMotionFrostmanConnectorV1
import Mathlib.Tactic

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 3000000

open Set MeasureTheory
open scoped ENNReal NNReal BigOperators

namespace Family8DoubledParentConflictWeightedFrostmanConnectorV2

open LeanEval.Analysis.WangZahlKakeya
open Submission.Kakeya.ConvexGeometry
open Submission.Kakeya.ConvexFactoring
open Submission.Kakeya.Uniformity
open Family8KatzTaoFrostmanPropertiesV1
open Family8GeneralizedKatzTaoMultiplicityV1
open Family8RestrictedActualDatumMassBridgeV1
open Family8RestrictedActualDatumDensityRetentionV1
open Family8FiniteRandomRigidMotionFrostmanConnectorV1
open Family8DoubledParentConflictWeightedRetentionV3.ScaleCover
open Family8DoubledParentConflictWeightedRestrictedCoverEndpointV2.ScaleCover
open Family8DoubledParentConflictWeightedShadingMassBridgeV2.ScaleCover
open FamilyStickyAtEveryScaleCoreV1

noncomputable section

/-!
# Weighted doubled-parent selection to the source Frostman right-hand side

The parent-weight bridge supplies the exact selected actual datum and the
source multiplicity loss.  Restriction preserves source Katz--Tao control.
Consequently the standard density and unit-ball base scalar budgets are the
only remaining numerical inputs before applying `FrostmanAtParameters`.
-/

namespace ScaleCover

/-- Source Katz--Tao control restricts losslessly to the literal fine
subtype selected by the weighted parent selection. -/
theorem restrictActualTubeDatum_weightedSelected_isKatzTao
    {delta rho : NNReal} {index : Type} [Fintype index]
    [DecidableEq index] (D : ActualTubeDatum delta index)
    {S : StickyScaleCover D.family rho} {B C : ENNReal}
    (W : DoubledParentConflictWeightedSelection S
      (parentShadingWeight S D.shading) B)
    (hKT : IsKatzTao C D.family.bodyFamily) :
    IsKatzTao C
      (restrictActualTubeDatum D
        (weightedSelectedFineIndices D.shading W)).family.bodyFamily := by
  intro K
  unfold IsKatzTaoAt
  rw [restrictActualTubeDatum_containedMass]
  exact hKT.on (weightedSelectedFineIndices D.shading W) K

/-- Direct source-Frostman consumer for the sharp doubled-parent loss.

The selected actual datum is the same selected fine family used by the
weighted Definition 2.12 endpoint (through the proved canonical
equivalence).  No coarse-card degree estimate and no neighbour callback
appears in this statement. -/
theorem source_averageMultiplicity_le_mul_frostmanRHS_of_weightedSelection
    {beta epsilon eta : Real} {delta0 delta rho : NNReal}
    {index : Type} [Fintype index] [DecidableEq index]
    (hF : FrostmanAtParameters beta epsilon eta delta0)
    (D : ActualTubeDatum delta index) (hD : D.IsAdmissible)
    {S : StickyScaleCover D.family rho} {B C : ENNReal}
    (W : DoubledParentConflictWeightedSelection S
      (parentShadingWeight S D.shading) B)
    (hactive : S.activeFine = Finset.univ)
    (hdelta0 : delta ≤ delta0)
    (hKT : IsKatzTao C D.family.bodyFamily)
    (hdensityBudget : (delta : ENNReal) ^ eta ≤
      D.shading.shadingDensity / B)
    (hbaseBudget : C * volume (unitBallBody : Set Space) ≤
      (delta : ENNReal) ^ (-eta) *
        (restrictActualTubeDatum D
          (weightedSelectedFineIndices D.shading W)).actualFamilyVolume) :
    D.shading.averageMultiplicity ≤
      B * frostmanMultiplicityRHS delta
        (restrictActualTubeDatum D
          (weightedSelectedFineIndices D.shading W)).actualFamilyVolume
        epsilon beta := by
  let selected := weightedSelectedFineIndices D.shading W
  let refined := restrictActualTubeDatum D selected
  have hadmissible : refined.IsAdmissible :=
    Family8GeneralizedKatzTaoMultiplicityV1.ActualTubeDatum.IsAdmissible.restrictTo
      hD selected
  have hmass : D.shading.shadingMass ≤
      B * refined.shading.shadingMass := by
    exact source_shadingMass_le_mul_weightedSelected_shadingMass
      D W hactive
  have hdensityTransport : D.shading.shadingDensity / B ≤
      refined.shading.shadingDensity :=
    source_shadingDensity_div_loss_le_restrictActualTubeDatum
      D selected B hmass
  have hrefinedDensity : (delta : ENNReal) ^ eta ≤
      refined.shading.shadingDensity :=
    hdensityBudget.trans hdensityTransport
  have hrefinedKT : IsKatzTao C refined.family.bodyFamily := by
    exact restrictActualTubeDatum_weightedSelected_isKatzTao D W hKT
  have hrefinedFrostman : FrostmanHypotheses refined eta :=
    frostmanHypotheses_of_density_isKatzTao_base
      refined hadmissible eta C hrefinedDensity hrefinedKT hbaseBudget
  have hrefinedMultiplicity :=
    FrostmanAtParameters.apply hF refined hadmissible hdelta0
      hrefinedFrostman
  have hsourceMultiplicity : D.shading.averageMultiplicity ≤
      B * refined.shading.averageMultiplicity :=
    source_averageMultiplicity_le_mul_weightedSelected D W hactive
  exact hsourceMultiplicity.trans
    (mul_le_mul' le_rfl hrefinedMultiplicity)

#print axioms restrictActualTubeDatum_weightedSelected_isKatzTao
#print axioms source_averageMultiplicity_le_mul_frostmanRHS_of_weightedSelection

end ScaleCover
end
end Family8DoubledParentConflictWeightedFrostmanConnectorV2
