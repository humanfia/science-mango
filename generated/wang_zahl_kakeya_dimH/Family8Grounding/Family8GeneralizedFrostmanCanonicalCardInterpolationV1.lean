import Family6Grounding.Family6CanonicalFrostmanConstantCoreV1
import Family8Grounding.Family8ActualFamilyVolumePackingV1
import Family8Grounding.Family8FrostmanRHSScaleVolumeAlgebraV4
import Mathlib.Tactic

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 1000000

open Set MeasureTheory
open scoped ENNReal NNReal BigOperators

namespace Family8GeneralizedFrostmanCanonicalCardInterpolationV1

open LeanEval.Analysis.WangZahlKakeya
open Submission.Kakeya.ConvexGeometry
open Submission.Kakeya.ConvexFactoring
open Submission.Kakeya.Uniformity
open Family6CanonicalFrostmanConstantCoreV1
open Family8KatzTaoFrostmanPropertiesV1
open Family8ActualFamilyVolumePackingV1
open Family8FrostmanRHSScaleVolumeAlgebraV4

noncomputable section

/-!
# Non-circular canonical-card interpolation after generalized Frostman

This file is the deterministic last step of the generalized-Frostman
argument.  It applies `FrostmanAtParameters` only to a genuine admissible
actual tube datum, bounds its actual indexed volume using its literal
cardinality, and exposes the canonical source Frostman constant with the
power `1 - gamma / 2`.

The package below deliberately does not contain a convex-plank `BoundAt`, a
Family 7 union conclusion, or the desired multiplicity bound.  Its two
substantive selection fields are instead the honest outputs required from a
separate random-copy/refinement theorem:

* average multiplicity is retained up to `greedyLoss`; and
* the refined cardinality is at most `copyCardLoss` times the source
  canonical Frostman constant times the source cardinality.

The current fixed-John construction does not prove these fields with loss
small enough for arbitrary epsilon slack: its known greedy envelope has a
fixed inverse power.  Thus this module is an interpolation producer, not a
replacement for the missing good-random-rigid-copy theorem.
-/

/-- The exact source canonical Frostman constant in the actual datum's unit
ball ambient. -/
def sourceCanonicalFrostmanConstant
    {delta : NNReal} {sourceIndex : Type}
    [Fintype sourceIndex] [DecidableEq sourceIndex]
    (source : ActualTubeDatum delta sourceIndex) : ENNReal :=
  canonicalFrostmanConstant source.family.bodyFamily unitBallBody

/-- The source scale-cardinality volume used by the generalized-Frostman
right-hand side. -/
def sourceCardScaleVolume
    {delta : NNReal} {sourceIndex : Type}
    [Fintype sourceIndex] [DecidableEq sourceIndex]
    (_source : ActualTubeDatum delta sourceIndex) : ENNReal :=
  (delta : ENNReal) ^ (2 : Nat) *
    (Fintype.card sourceIndex : ENNReal)

/-- The requested generalized-Frostman interpolation target. -/
def canonicalCardFrostmanRHS
    {delta : NNReal} {sourceIndex : Type}
    [Fintype sourceIndex] [DecidableEq sourceIndex]
    (source : ActualTubeDatum delta sourceIndex)
    (epsilon gamma : Real) : ENNReal :=
  (delta : ENNReal) ^ (-epsilon) *
    sourceCanonicalFrostmanConstant source ^ (1 - gamma / 2) *
    (delta : ENNReal) ^ (-2 * gamma) *
    sourceCardScaleVolume source ^ (1 - gamma / 2)

/-- The weakest datum-level geometric package consumed by the interpolation
step.  Density and Frostman control are kept as the literal two fields of
`FrostmanHypotheses`; the other two non-structural fields are a greedy
average-retention inequality and a copied-cardinality inequality. -/
structure CanonicalCardRefinedFrostmanData
    {delta : NNReal}
    {sourceIndex refinedIndex : Type}
    [Fintype sourceIndex] [DecidableEq sourceIndex]
    [Fintype refinedIndex] [DecidableEq refinedIndex]
    (source : ActualTubeDatum delta sourceIndex)
    (refined : ActualTubeDatum delta refinedIndex)
    (eta : Real) (greedyLoss copyCardLoss : ENNReal) : Prop where
  refined_admissible : refined.IsAdmissible
  refined_density :
    (delta : ENNReal) ^ eta <= refined.shading.shadingDensity
  refined_frostman :
    IsFrostmanIn ((delta : ENNReal) ^ (-eta))
      refined.family.bodyFamily unitBallBody
  source_average_le :
    source.shading.averageMultiplicity <=
      greedyLoss * refined.shading.averageMultiplicity
  refined_card_le :
    (Fintype.card refinedIndex : ENNReal) <=
      copyCardLoss * sourceCanonicalFrostmanConstant source *
        (Fintype.card sourceIndex : ENNReal)

/-- The package gives exactly the hypotheses accepted by
`FrostmanAtParameters.apply`. -/
theorem CanonicalCardRefinedFrostmanData.frostmanHypotheses
    {delta : NNReal}
    {sourceIndex refinedIndex : Type}
    [Fintype sourceIndex] [DecidableEq sourceIndex]
    [Fintype refinedIndex] [DecidableEq refinedIndex]
    {source : ActualTubeDatum delta sourceIndex}
    {refined : ActualTubeDatum delta refinedIndex}
    {eta : Real} {greedyLoss copyCardLoss : ENNReal}
    (G : CanonicalCardRefinedFrostmanData source refined eta
      greedyLoss copyCardLoss) :
    FrostmanHypotheses refined eta :=
  ⟨G.refined_density, G.refined_frostman⟩

/-- Literal tube packing and the copied-cardinality field give the refined
actual-volume estimate needed for interpolation.  This is a geometric
volume bound, not a multiplicity or union conclusion. -/
theorem CanonicalCardRefinedFrostmanData.refined_actualFamilyVolume_le
    {delta : NNReal}
    {sourceIndex refinedIndex : Type}
    [Fintype sourceIndex] [DecidableEq sourceIndex]
    [Fintype refinedIndex] [DecidableEq refinedIndex]
    {source : ActualTubeDatum delta sourceIndex}
    {refined : ActualTubeDatum delta refinedIndex}
    {eta : Real} {greedyLoss copyCardLoss : ENNReal}
    (G : CanonicalCardRefinedFrostmanData source refined eta
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

/-- The actual refined Frostman RHS interpolates to the canonical source
card-scale RHS, with only the explicit packing/copy-card factor left. -/
theorem CanonicalCardRefinedFrostmanData.refined_rhs_le
    {delta : NNReal}
    {sourceIndex refinedIndex : Type}
    [Fintype sourceIndex] [DecidableEq sourceIndex]
    [Fintype refinedIndex] [DecidableEq refinedIndex]
    {source : ActualTubeDatum delta sourceIndex}
    {refined : ActualTubeDatum delta refinedIndex}
    {eta epsilonF gamma : Real}
    {greedyLoss copyCardLoss : ENNReal}
    (G : CanonicalCardRefinedFrostmanData source refined eta
      greedyLoss copyCardLoss)
    (hgamma : gamma <= 2) :
    frostmanMultiplicityRHS delta refined.actualFamilyVolume
        epsilonF gamma <=
      ((delta : ENNReal) ^ (-epsilonF) *
        sourceCanonicalFrostmanConstant source ^ (1 - gamma / 2) *
        (delta : ENNReal) ^ (-2 * gamma) *
        sourceCardScaleVolume source ^ (1 - gamma / 2)) *
      (8 * copyCardLoss) ^ (1 - gamma / 2) := by
  have hp : 0 <= 1 - gamma / 2 := by linarith
  have htransport :=
    frostmanMultiplicityRHS_le_of_volume_le_factor_mul
      (delta := delta)
      (selectedVolume := refined.actualFamilyVolume)
      (sourceVolume := sourceCanonicalFrostmanConstant source *
        sourceCardScaleVolume source)
      (factor := 8 * copyCardLoss)
      (epsilon := epsilonF) (gamma := gamma)
      hgamma G.refined_actualFamilyVolume_le
  calc
    frostmanMultiplicityRHS delta refined.actualFamilyVolume
        epsilonF gamma <=
      frostmanMultiplicityRHS delta
          (sourceCanonicalFrostmanConstant source *
            sourceCardScaleVolume source) epsilonF gamma *
        (8 * copyCardLoss) ^ (1 - gamma / 2) := htransport
    _ = ((delta : ENNReal) ^ (-epsilonF) *
          sourceCanonicalFrostmanConstant source ^ (1 - gamma / 2) *
          (delta : ENNReal) ^ (-2 * gamma) *
          sourceCardScaleVolume source ^ (1 - gamma / 2)) *
        (8 * copyCardLoss) ^ (1 - gamma / 2) := by
      unfold frostmanMultiplicityRHS
      rw [ENNReal.mul_rpow_of_nonneg _ _ hp]
      ac_rfl

/-- Non-circular generalized-Frostman interpolation.

The sole residual scalar ledger says that the greedy loss together with the
fixed tube-packing and copy-card loss fits into the epsilon slack.  It
contains neither the canonical Frostman constant nor the source cardinality,
so it is not a restatement of the conclusion. -/
theorem averageMultiplicity_le_canonicalCardFrostmanRHS
    {delta delta0 : NNReal}
    {sourceIndex refinedIndex : Type}
    [Fintype sourceIndex] [DecidableEq sourceIndex]
    [Fintype refinedIndex] [DecidableEq refinedIndex]
    {source : ActualTubeDatum delta sourceIndex}
    {refined : ActualTubeDatum delta refinedIndex}
    {eta epsilonF epsilon gamma : Real}
    {greedyLoss copyCardLoss : ENNReal}
    (hF : FrostmanAtParameters gamma epsilonF eta delta0)
    (G : CanonicalCardRefinedFrostmanData source refined eta
      greedyLoss copyCardLoss)
    (hdelta0 : delta <= delta0)
    (hgamma : gamma <= 2)
    (hscalar :
      greedyLoss * (8 * copyCardLoss) ^ (1 - gamma / 2) *
          (delta : ENNReal) ^ (-epsilonF) <=
        (delta : ENNReal) ^ (-epsilon)) :
    source.shading.averageMultiplicity <=
      canonicalCardFrostmanRHS source epsilon gamma := by
  have hrefined := FrostmanAtParameters.apply hF refined
    G.refined_admissible hdelta0 G.frostmanHypotheses
  have hinterpolation := G.refined_rhs_le (epsilonF := epsilonF) hgamma
  calc
    source.shading.averageMultiplicity <=
        greedyLoss * refined.shading.averageMultiplicity :=
      G.source_average_le
    _ <= greedyLoss * frostmanMultiplicityRHS delta
        refined.actualFamilyVolume epsilonF gamma := by
      exact mul_le_mul' le_rfl hrefined
    _ <= greedyLoss *
        (((delta : ENNReal) ^ (-epsilonF) *
            sourceCanonicalFrostmanConstant source ^ (1 - gamma / 2) *
            (delta : ENNReal) ^ (-2 * gamma) *
            sourceCardScaleVolume source ^ (1 - gamma / 2)) *
          (8 * copyCardLoss) ^ (1 - gamma / 2)) := by
      exact mul_le_mul' le_rfl hinterpolation
    _ = (greedyLoss * (8 * copyCardLoss) ^ (1 - gamma / 2) *
          (delta : ENNReal) ^ (-epsilonF)) *
        (sourceCanonicalFrostmanConstant source ^ (1 - gamma / 2) *
          (delta : ENNReal) ^ (-2 * gamma) *
          sourceCardScaleVolume source ^ (1 - gamma / 2)) := by
      ac_rfl
    _ <= (delta : ENNReal) ^ (-epsilon) *
        (sourceCanonicalFrostmanConstant source ^ (1 - gamma / 2) *
          (delta : ENNReal) ^ (-2 * gamma) *
          sourceCardScaleVolume source ^ (1 - gamma / 2)) := by
      exact mul_le_mul' hscalar le_rfl
    _ = canonicalCardFrostmanRHS source epsilon gamma := by
      unfold canonicalCardFrostmanRHS
      ac_rfl

#print axioms CanonicalCardRefinedFrostmanData.refined_actualFamilyVolume_le
#print axioms CanonicalCardRefinedFrostmanData.refined_rhs_le
#print axioms averageMultiplicity_le_canonicalCardFrostmanRHS

end
end Family8GeneralizedFrostmanCanonicalCardInterpolationV1
