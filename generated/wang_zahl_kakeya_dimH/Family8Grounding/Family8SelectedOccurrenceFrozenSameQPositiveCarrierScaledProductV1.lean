import Family8Grounding.Family8FrozenComparableSourceAverageRetentionV2
import Family8Grounding.Family8SelectedOccurrenceFrozenSameQPositiveCarrierCrossComposerV3
import Mathlib.Tactic

/-!
# Honest scaled outer/inner product for one selected positive carrier

The local-power cross estimate retains the literal source factor

`affineJacobian * (source.shadingDensity * (rho^2 / 2))`.

This file propagates that factor through the frozen actual-average product.
It deliberately does not cancel it.  The source shading occurring in this
factor is the source of the frozen assembly, whereas an Equation (45) bound
is applied downstream to the outer shading built from `A.refinement.shading`.
Those are not the same shading object; the exact assembly retention theorem
is the one-way bridge between their average multiplicities.

Consequently the two conclusions below are scaled conclusions.  Recovering
an unscaled source average would require a separate positive finite lower
bound for the complete source factor, including its `rho^2 / 2` term.
-/

open Set MeasureTheory
open scoped BigOperators ENNReal NNReal

namespace Family8SelectedOccurrenceFrozenSameQPositiveCarrierScaledProductV1

open LeanEval.Analysis.WangZahlKakeya
open Submission.Kakeya.ConvexGeometry
open Submission.Kakeya.ConvexFactoring
open Submission.Kakeya.ConvexFactoring.FullConvexMaximalDensity
open Submission.Kakeya.ConvexFactoring.GreedyOccurrenceFactorization
open Submission.Kakeya.ConvexFactoring.HeavyParentSelection
open Submission.Kakeya.Uniformity
open Family8FrozenComparableActualAverageMassDensityV1
open Family8FrozenComparableActualAverageMassDensityV1.Assembly
open Family8FrozenComparableSourceAverageRetentionV2.SourceAverage
open Family8FrozenNeighborhoodAssemblyV1
open Family8SelectedOccurrenceDensityFrostmanV1
open Family8SelectedOccurrenceFrozenSameQPositiveCarrierCrossComposerV3
open Family8SelectedOccurrenceFrozenSameQPositiveCarrierEq46ComposerV1
open Family8StickySelectedParentGreedyBlockFrostmanV3
open FamilyStickyAtEveryScaleCoreV1
open FamilyStickyHierarchyEndpointPrefixShadingTransportV1.StickyScaleCover

noncomputable section

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 3000000

local instance (p : Prop) : Decidable p := Classical.propDecidable p

variable {delta rho : NNReal} {index : Type}
  [Fintype index] [DecidableEq index]
  {fine : UniformTubeFamily delta index}

/-- The V3 fixed-label cross estimate propagates through the literal
same-assembly actual-average product.  No property of `sourceFactor` is used,
and in particular it is not cancelled. -/
theorem
    sourceFactor_mul_actualRefinementAverage_le_four_mul_outer_mul_cross
    (S : StickyScaleCover fine rho) (hrho : 0 < rho)
    (P : GreedyDensityPartition S.activeCoarseFamily
      (hullCandidates (Finset.univ : Finset (ActiveParentIndex S)))
      (hullContainer S.activeCoarseFamily) Finset.univ)
    (R : Finset (Fin (blocks S.activeCoarseFamily P).length))
    (source : Shading S.activeCoarseFamily) {rFrozen : Real}
    (A : Family8FrozenNeighborhoodAssemblyV1.Assembly
      (selectedOccurrenceFactorization P R) source rFrozen)
    (q : Fin (blocks S.activeCoarseFamily P).length)
    (r : NNReal) (hr : 0 < r) (label : Fin 3 -> Int)
    (crossRHS : ENNReal)
    (hproduct :
      (actualRefinementShading A).averageMultiplicity <=
        4 * (A.frozenCoarse.averageMultiplicity *
          (finalFiberShading A (some q)).averageMultiplicity))
    (hcross :
      selectedOccurrenceFrozenSameQPositiveCarrierSourceFactor
          S hrho P q source r hr label *
        (finalFiberShading A (some q)).averageMultiplicity <= crossRHS) :
    selectedOccurrenceFrozenSameQPositiveCarrierSourceFactor
          S hrho P q source r hr label *
        (actualRefinementShading A).averageMultiplicity <=
      4 * A.frozenCoarse.averageMultiplicity * crossRHS := by
  let sourceFactor :=
    selectedOccurrenceFrozenSameQPositiveCarrierSourceFactor
      S hrho P q source r hr label
  calc
    sourceFactor * (actualRefinementShading A).averageMultiplicity <=
        sourceFactor *
          (4 * (A.frozenCoarse.averageMultiplicity *
            (finalFiberShading A (some q)).averageMultiplicity)) :=
      mul_le_mul' le_rfl hproduct
    _ = 4 * A.frozenCoarse.averageMultiplicity *
        (sourceFactor *
          (finalFiberShading A (some q)).averageMultiplicity) := by
      ac_rfl
    _ <= 4 * A.frozenCoarse.averageMultiplicity * crossRHS :=
      mul_le_mul' le_rfl (by simpa only [sourceFactor] using hcross)

/-- Paying the frozen assembly's genuine source-average retention once gives
the corresponding scaled conclusion on the literal active-fine source.
The source factor remains untouched. -/
theorem
    sourceFactor_mul_sourceActiveFineAverage_le_four_mul_loss_mul_outer_mul_cross
    (S : StickyScaleCover fine rho) (hrho : 0 < rho)
    (P : GreedyDensityPartition S.activeCoarseFamily
      (hullCandidates (Finset.univ : Finset (ActiveParentIndex S)))
      (hullContainer S.activeCoarseFamily) Finset.univ)
    (R : Finset (Fin (blocks S.activeCoarseFamily P).length))
    (source : Shading S.activeCoarseFamily) {rFrozen : Real}
    (A : Family8FrozenNeighborhoodAssemblyV1.Assembly
      (selectedOccurrenceFactorization P R) source rFrozen)
    (q : Fin (blocks S.activeCoarseFamily P).length)
    (r : NNReal) (hr : 0 < r) (label : Fin 3 -> Int)
    (crossRHS : ENNReal)
    (hproduct :
      (actualRefinementShading A).averageMultiplicity <=
        4 * (A.frozenCoarse.averageMultiplicity *
          (finalFiberShading A (some q)).averageMultiplicity))
    (hcross :
      selectedOccurrenceFrozenSameQPositiveCarrierSourceFactor
          S hrho P q source r hr label *
        (finalFiberShading A (some q)).averageMultiplicity <= crossRHS) :
    selectedOccurrenceFrozenSameQPositiveCarrierSourceFactor
          S hrho P q source r hr label *
        (sourceActiveFineShading
          (selectedOccurrenceFactorization P R) source).averageMultiplicity <=
      4 * (A.loss : ENNReal) * A.frozenCoarse.averageMultiplicity *
        crossRHS := by
  let sourceFactor :=
    selectedOccurrenceFrozenSameQPositiveCarrierSourceFactor
      S hrho P q source r hr label
  have hsourceAverage :
      (sourceActiveFineShading
          (selectedOccurrenceFactorization P R) source).averageMultiplicity <=
        (A.loss : ENNReal) *
          (actualRefinementShading A).averageMultiplicity :=
    sourceActiveFineShading_averageMultiplicity_le_loss_mul_actualRefinement A
  have hactual :=
    sourceFactor_mul_actualRefinementAverage_le_four_mul_outer_mul_cross
      S hrho P R source A q r hr label crossRHS hproduct hcross
  calc
    sourceFactor *
        (sourceActiveFineShading
          (selectedOccurrenceFactorization P R) source).averageMultiplicity <=
      sourceFactor *
        ((A.loss : ENNReal) *
          (actualRefinementShading A).averageMultiplicity) :=
      mul_le_mul' le_rfl hsourceAverage
    _ = (A.loss : ENNReal) *
        (sourceFactor *
          (actualRefinementShading A).averageMultiplicity) := by
      ac_rfl
    _ <= (A.loss : ENNReal) *
        (4 * A.frozenCoarse.averageMultiplicity * crossRHS) :=
      mul_le_mul' le_rfl (by simpa only [sourceFactor] using hactual)
    _ = 4 * (A.loss : ENNReal) * A.frozenCoarse.averageMultiplicity *
        crossRHS := by
      ac_rfl

#print axioms
  sourceFactor_mul_actualRefinementAverage_le_four_mul_outer_mul_cross
#print axioms
  sourceFactor_mul_sourceActiveFineAverage_le_four_mul_loss_mul_outer_mul_cross

end
end Family8SelectedOccurrenceFrozenSameQPositiveCarrierScaledProductV1
