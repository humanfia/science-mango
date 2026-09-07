import Family8Grounding.Family8GeneralizedFrostmanCanonicalCardInterpolationV1
import Family8Grounding.Family8GeneralizedScaleTrivialBranchV1
import Mathlib.Tactic

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 1000000

open Set MeasureTheory
open scoped ENNReal NNReal BigOperators

namespace Family8GeneralizedFrostmanRelativeCanonicalCardInterpolationV1

open LeanEval.Analysis.WangZahlKakeya
open Submission.Kakeya.ConvexGeometry
open Submission.Kakeya.ConvexFactoring
open Submission.Kakeya.Uniformity
open Family6CanonicalFrostmanConstantCoreV1
open Family8ActualFamilyVolumePackingV1
open Family8GeneralizedFrostmanCanonicalCardInterpolationV1
open Family8GeneralizedScalePropertiesV1
open Family8GeneralizedScaleTrivialBranchV1
open Family8KatzTaoFrostmanPropertiesV1

noncomputable section

/-!
# Relative-scale canonical-card interpolation after generalized Frostman

This is the relative-loss-scale analogue of
`Family8GeneralizedFrostmanCanonicalCardInterpolationV1`.  Both source and
refined families are genuine `delta`-tube data.  Only the Frostman density,
nonconcentration, and epsilon loss are evaluated at the supplied call scale
`tau`; the geometric normalization remains at `delta`.

The package below deliberately stops before the random-copy step.  In
particular, it does not assert that a refinement with the average-retention
and copied-cardinality fields exists.  Those fields must come from a separate
good-rigid-copy/refinement producer.

For the plank-row application the intended fixed call scale is
`tau = shortWidth / 8`, while the actual tube radius is `longWidth / 8`.
Positivity and `tau <= delta` follow formally from the plank dimensions, but
the current fixed-John base ledger does not follow: after its
`copyLoss ~ longWidth / shortWidth`, it asks schematically for
`shortWidth ^ (-2) <= shortWidth ^ (-eta)`.  This is unavailable at the small
`eta` used in the argument.  Accordingly, neither the builder nor the final
theorem below selects an existentially smaller scale; the exact fixed-scale
density and base certificates remain honest inputs to the missing good-copy
producer.
-/

/-- The canonical-card Frostman target with epsilon loss measured at `tau`
and geometric normalization measured at the actual tube radius `delta`. -/
def relativeCanonicalCardFrostmanRHS
    {delta : NNReal} {sourceIndex : Type}
    [Fintype sourceIndex] [DecidableEq sourceIndex]
    (source : ActualTubeDatum delta sourceIndex) (tau : NNReal)
    (epsilon gamma : Real) : ENNReal :=
  (tau : ENNReal) ^ (-epsilon) *
    sourceCanonicalFrostmanConstant source ^ (1 - gamma / 2) *
    (delta : ENNReal) ^ (-2 * gamma) *
    sourceCardScaleVolume source ^ (1 - gamma / 2)

/-- The weakest datum-level package consumed by relative-scale canonical-card
interpolation.  Source admissibility is intentionally absent: the source is
used only through its average multiplicity, canonical Frostman constant, and
cardinality.  Refined admissibility is needed both by the relative Frostman
call and by literal tube-volume packing. -/
structure RelativeCanonicalCardRefinedFrostmanData
    {delta : NNReal}
    {sourceIndex refinedIndex : Type}
    [Fintype sourceIndex] [DecidableEq sourceIndex]
    [Fintype refinedIndex] [DecidableEq refinedIndex]
    (source : ActualTubeDatum delta sourceIndex)
    (refined : ActualTubeDatum delta refinedIndex)
    (tau : NNReal) (eta : Real)
    (greedyLoss copyCardLoss : ENNReal) : Prop where
  refined_admissible : refined.IsAdmissible
  refined_density :
    (tau : ENNReal) ^ eta <= refined.shading.shadingDensity
  refined_frostman :
    IsFrostmanIn ((tau : ENNReal) ^ (-eta))
      refined.family.bodyFamily unitBallBody
  source_average_le :
    source.shading.averageMultiplicity <=
      greedyLoss * refined.shading.averageMultiplicity
  refined_card_le :
    (Fintype.card refinedIndex : ENNReal) <=
      copyCardLoss * sourceCanonicalFrostmanConstant source *
        (Fintype.card sourceIndex : ENNReal)

/-- At a caller-chosen relative scale, density plus a Katz--Tao certificate
and the exact unit-ball base payment produce the required relative Frostman
hypotheses.  This is the public certificate-level fact used internally by
the existing relative connector; it does not choose `tau`. -/
theorem frostmanHypothesesAtRelativeScale_of_density_isKatzTao_base
    {delta tau : NNReal} {index : Type}
    [Fintype index] [DecidableEq index]
    (D : ActualTubeDatum delta index) (hD : D.IsAdmissible)
    (eta : Real) (C : ENNReal)
    (hdensity :
      (tau : ENNReal) ^ eta <= D.shading.shadingDensity)
    (hKT : IsKatzTao C D.family.bodyFamily)
    (hbase :
      C * volume (unitBallBody : Set Space) <=
        (tau : ENNReal) ^ (-eta) * D.actualFamilyVolume) :
    FrostmanHypothesesAtRelativeScale D tau eta := by
  refine ⟨hdensity, ?_⟩
  apply IsKatzTao.isFrostmanIn hKT
  · intro i
    simpa only [UniformTubeFamily.bodyFamily, Tube.coe_body,
      coe_unitBallBody] using hD.contained_in_unit_ball i
  · have hambient :
        containedMass D.family.bodyFamily unitBallBody =
          D.actualFamilyVolume := by
      simpa only [ActualTubeDatum.actualFamilyVolume] using
        (containedMass_eq_familyVolume_of_contained
          D.family.bodyFamily unitBallBody (fun i => by
            simpa only [UniformTubeFamily.bodyFamily, Tube.coe_body,
              coe_unitBallBody] using hD.contained_in_unit_ball i))
    rw [hambient]
    exact hbase

/-- Builder for the relative canonical-card package when the selected
refinement is supplied with Katz--Tao control and its exact base payment.
This exposes the useful certificate that the conclusion-only connector
constructs internally. -/
theorem RelativeCanonicalCardRefinedFrostmanData.of_isKatzTao_base
    {delta tau : NNReal}
    {sourceIndex refinedIndex : Type}
    [Fintype sourceIndex] [DecidableEq sourceIndex]
    [Fintype refinedIndex] [DecidableEq refinedIndex]
    {source : ActualTubeDatum delta sourceIndex}
    {refined : ActualTubeDatum delta refinedIndex}
    {eta : Real} {greedyLoss copyCardLoss C : ENNReal}
    (hrefined : refined.IsAdmissible)
    (hdensity :
      (tau : ENNReal) ^ eta <= refined.shading.shadingDensity)
    (hKT : IsKatzTao C refined.family.bodyFamily)
    (hbase :
      C * volume (unitBallBody : Set Space) <=
        (tau : ENNReal) ^ (-eta) * refined.actualFamilyVolume)
    (haverage :
      source.shading.averageMultiplicity <=
        greedyLoss * refined.shading.averageMultiplicity)
    (hcard :
      (Fintype.card refinedIndex : ENNReal) <=
        copyCardLoss * sourceCanonicalFrostmanConstant source *
          (Fintype.card sourceIndex : ENNReal)) :
    RelativeCanonicalCardRefinedFrostmanData source refined tau eta
      greedyLoss copyCardLoss where
  refined_admissible := hrefined
  refined_density := hdensity
  refined_frostman :=
    (frostmanHypothesesAtRelativeScale_of_density_isKatzTao_base
      refined hrefined eta C hdensity hKT hbase).2
  source_average_le := haverage
  refined_card_le := hcard

/-- The relative density and Frostman fields are exactly the hypotheses
accepted by `FrostmanAtRelativeScaleParameters`. -/
theorem RelativeCanonicalCardRefinedFrostmanData.frostmanHypotheses
    {delta : NNReal}
    {sourceIndex refinedIndex : Type}
    [Fintype sourceIndex] [DecidableEq sourceIndex]
    [Fintype refinedIndex] [DecidableEq refinedIndex]
    {source : ActualTubeDatum delta sourceIndex}
    {refined : ActualTubeDatum delta refinedIndex}
    {tau : NNReal} {eta : Real} {greedyLoss copyCardLoss : ENNReal}
    (G : RelativeCanonicalCardRefinedFrostmanData source refined tau eta
      greedyLoss copyCardLoss) :
    FrostmanHypothesesAtRelativeScale refined tau eta :=
  ⟨G.refined_density, G.refined_frostman⟩

/-- Literal tube packing and the copied-cardinality field give the refined
actual-volume estimate. -/
theorem RelativeCanonicalCardRefinedFrostmanData.refined_actualFamilyVolume_le
    {delta : NNReal}
    {sourceIndex refinedIndex : Type}
    [Fintype sourceIndex] [DecidableEq sourceIndex]
    [Fintype refinedIndex] [DecidableEq refinedIndex]
    {source : ActualTubeDatum delta sourceIndex}
    {refined : ActualTubeDatum delta refinedIndex}
    {tau : NNReal} {eta : Real} {greedyLoss copyCardLoss : ENNReal}
    (G : RelativeCanonicalCardRefinedFrostmanData source refined tau eta
      greedyLoss copyCardLoss) :
    refined.actualFamilyVolume <=
      (8 * copyCardLoss) *
        (sourceCanonicalFrostmanConstant source *
          sourceCardScaleVolume source) := by
  calc
    refined.actualFamilyVolume <=
        (Fintype.card refinedIndex : ENNReal) *
          (8 * (delta : ENNReal) ^ 2) :=
      actualFamilyVolume_le_card_mul_eight_sq refined
        G.refined_admissible.delta_le_half
    _ <=
        (copyCardLoss * sourceCanonicalFrostmanConstant source *
            (Fintype.card sourceIndex : ENNReal)) *
          (8 * (delta : ENNReal) ^ 2) := by
      exact mul_le_mul' G.refined_card_le le_rfl
    _ = (8 * copyCardLoss) *
        (sourceCanonicalFrostmanConstant source *
          sourceCardScaleVolume source) := by
      unfold sourceCardScaleVolume
      ac_rfl

/-- Transport of the relative Frostman RHS through the literal
copied-cardinality volume bound. -/
theorem RelativeCanonicalCardRefinedFrostmanData.refined_rhs_le
    {delta : NNReal}
    {sourceIndex refinedIndex : Type}
    [Fintype sourceIndex] [DecidableEq sourceIndex]
    [Fintype refinedIndex] [DecidableEq refinedIndex]
    {source : ActualTubeDatum delta sourceIndex}
    {refined : ActualTubeDatum delta refinedIndex}
    {tau : NNReal} {eta epsilonF gamma : Real}
    {greedyLoss copyCardLoss : ENNReal}
    (G : RelativeCanonicalCardRefinedFrostmanData source refined tau eta
      greedyLoss copyCardLoss)
    (hgamma : gamma <= 2) :
    frostmanRelativeScaleMultiplicityRHS delta tau
        refined.actualFamilyVolume epsilonF gamma <=
      ((tau : ENNReal) ^ (-epsilonF) *
        sourceCanonicalFrostmanConstant source ^ (1 - gamma / 2) *
        (delta : ENNReal) ^ (-2 * gamma) *
        sourceCardScaleVolume source ^ (1 - gamma / 2)) *
      (8 * copyCardLoss) ^ (1 - gamma / 2) := by
  have hp : 0 <= 1 - gamma / 2 := by linarith
  have hpow :
      refined.actualFamilyVolume ^ (1 - gamma / 2) <=
        ((8 * copyCardLoss) *
          (sourceCanonicalFrostmanConstant source *
            sourceCardScaleVolume source)) ^ (1 - gamma / 2) :=
    ENNReal.rpow_le_rpow G.refined_actualFamilyVolume_le hp
  unfold frostmanRelativeScaleMultiplicityRHS
  calc
    (tau : ENNReal) ^ (-epsilonF) *
          (delta : ENNReal) ^ (-2 * gamma) *
          refined.actualFamilyVolume ^ (1 - gamma / 2) <=
        ((tau : ENNReal) ^ (-epsilonF) *
          (delta : ENNReal) ^ (-2 * gamma)) *
          ((8 * copyCardLoss) *
            (sourceCanonicalFrostmanConstant source *
              sourceCardScaleVolume source)) ^ (1 - gamma / 2) := by
      exact mul_le_mul_right hpow _
    _ = ((tau : ENNReal) ^ (-epsilonF) *
          sourceCanonicalFrostmanConstant source ^ (1 - gamma / 2) *
          (delta : ENNReal) ^ (-2 * gamma) *
          sourceCardScaleVolume source ^ (1 - gamma / 2)) *
        (8 * copyCardLoss) ^ (1 - gamma / 2) := by
      rw [ENNReal.mul_rpow_of_nonneg
        (8 * copyCardLoss)
        (sourceCanonicalFrostmanConstant source *
          sourceCardScaleVolume source) hp]
      rw [ENNReal.mul_rpow_of_nonneg
        (sourceCanonicalFrostmanConstant source)
        (sourceCardScaleVolume source) hp]
      ac_rfl

/-- Non-circular relative-scale generalized-Frostman interpolation.

The residual scalar ledger contains only the average-retention loss, tube
packing/copy-card loss, and the epsilon slack at `tau`.  It contains neither
the source canonical Frostman constant nor its cardinality. -/
theorem averageMultiplicity_le_relativeCanonicalCardFrostmanRHS
    {delta delta0 tau : NNReal}
    {sourceIndex refinedIndex : Type}
    [Fintype sourceIndex] [DecidableEq sourceIndex]
    [Fintype refinedIndex] [DecidableEq refinedIndex]
    {source : ActualTubeDatum delta sourceIndex}
    {refined : ActualTubeDatum delta refinedIndex}
    {eta epsilonF epsilon gamma : Real}
    {greedyLoss copyCardLoss : ENNReal}
    (hF : FrostmanAtRelativeScaleParameters gamma epsilonF eta delta0)
    (G : RelativeCanonicalCardRefinedFrostmanData source refined tau eta
      greedyLoss copyCardLoss)
    (hdelta0 : delta <= delta0)
    (htau : 0 < tau)
    (htauDelta : tau <= delta)
    (hgamma : gamma <= 2)
    (hscalar :
      greedyLoss * (8 * copyCardLoss) ^ (1 - gamma / 2) *
          (tau : ENNReal) ^ (-epsilonF) <=
        (tau : ENNReal) ^ (-epsilon)) :
    source.shading.averageMultiplicity <=
      relativeCanonicalCardFrostmanRHS source tau epsilon gamma := by
  have hrefined := hF delta tau refinedIndex refined G.refined_admissible
    hdelta0 htau htauDelta G.frostmanHypotheses
  have hinterpolation := G.refined_rhs_le (epsilonF := epsilonF) hgamma
  calc
    source.shading.averageMultiplicity <=
        greedyLoss * refined.shading.averageMultiplicity :=
      G.source_average_le
    _ <= greedyLoss * frostmanRelativeScaleMultiplicityRHS delta tau
        refined.actualFamilyVolume epsilonF gamma := by
      exact mul_le_mul' le_rfl hrefined
    _ <= greedyLoss *
        (((tau : ENNReal) ^ (-epsilonF) *
            sourceCanonicalFrostmanConstant source ^ (1 - gamma / 2) *
            (delta : ENNReal) ^ (-2 * gamma) *
            sourceCardScaleVolume source ^ (1 - gamma / 2)) *
          (8 * copyCardLoss) ^ (1 - gamma / 2)) := by
      exact mul_le_mul' le_rfl hinterpolation
    _ = (greedyLoss * (8 * copyCardLoss) ^ (1 - gamma / 2) *
          (tau : ENNReal) ^ (-epsilonF)) *
        (sourceCanonicalFrostmanConstant source ^ (1 - gamma / 2) *
          (delta : ENNReal) ^ (-2 * gamma) *
          sourceCardScaleVolume source ^ (1 - gamma / 2)) := by
      ac_rfl
    _ <= (tau : ENNReal) ^ (-epsilon) *
        (sourceCanonicalFrostmanConstant source ^ (1 - gamma / 2) *
          (delta : ENNReal) ^ (-2 * gamma) *
          sourceCardScaleVolume source ^ (1 - gamma / 2)) := by
      exact mul_le_mul' hscalar le_rfl
    _ = relativeCanonicalCardFrostmanRHS source tau epsilon gamma := by
      unfold relativeCanonicalCardFrostmanRHS
      ac_rfl

#print axioms frostmanHypothesesAtRelativeScale_of_density_isKatzTao_base
#print axioms RelativeCanonicalCardRefinedFrostmanData.of_isKatzTao_base
#print axioms
  RelativeCanonicalCardRefinedFrostmanData.refined_actualFamilyVolume_le
#print axioms RelativeCanonicalCardRefinedFrostmanData.refined_rhs_le
#print axioms averageMultiplicity_le_relativeCanonicalCardFrostmanRHS

end
end Family8GeneralizedFrostmanRelativeCanonicalCardInterpolationV1
