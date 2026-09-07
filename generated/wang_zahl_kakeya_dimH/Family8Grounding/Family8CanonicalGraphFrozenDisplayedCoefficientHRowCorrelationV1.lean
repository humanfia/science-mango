import Family8Grounding.Family8CanonicalGraphFrozenHRowSelectionFirstConnectorV1
import Family8Grounding.Family8HRowDisplayedCoefficientCorrelationFromIncidenceV1
import Mathlib.Tactic

/-!
# Canonical graph displayed coefficient to the same selected H-row

The canonical graph is selected before its square-plank owner decomposition.
The existing selection-first connector then bounds the literal graph average
by `H.loss` times the average of the exact H-row stored in `B`.  Consequently
the only remaining comparison for the downstream displayed coefficient is
its forward domination by that literal graph average.

This module packages that shortest direction both as the row-average
correlation consumed by Prop. 6.6 and as its division-free incidence form.
No row is reselected and no local/global Frostman constants are compared.
-/

set_option autoImplicit false
set_option warningAsError true
set_option linter.unusedSectionVars false
set_option maxHeartbeats 4000000

open Set MeasureTheory
open scoped BigOperators ENNReal NNReal InnerProductSpace

namespace Family8CanonicalGraphFrozenDisplayedCoefficientHRowCorrelationV1

open LeanEval.Analysis.WangZahlKakeya
open Submission.Kakeya.ConvexGeometry
open Submission.Kakeya.ConvexFactoring
open Submission.Kakeya.Uniformity
open Family8CanonicalGraphFrozenHRowSelectionFirstConnectorV1
open Family8CanonicalGraphFrozenRawEq66IdentityBridgeV1
open Family8ExactAssemblyActualAverageBridgeV1
open Family8HRowDisplayedCoefficientCorrelationFromIncidenceV1
open Family8PlankHeavyActiveSelectedOwnerHRowFreshPropertyBundleV1
open Family8Prop66RowAutomaticFactorSandwichRawCorrelationConnectorV1
open Family8SquarePlankHRowSelectionFirstSetupV1
open Family8StickyScaleCoverActiveFineRestrictionV2.ScaleCover
open FamilyStickyAtEveryScaleCoreV1

noncomputable section

variable {tau rho delta : NNReal} {fineIndex : Type}
  [Fintype fineIndex] [DecidableEq fineIndex]
  {F : UniformTubeFamily tau fineIndex}
  {T : StickyScaleCover F rho}
  {P : ConvexFactorization F.bodyFamily T.coarse.bodyFamily}
  {Y : Shading F.bodyFamily} {fibreCF : ENNReal}

/-! ## The actual downstream direction -/

/-- Once the displayed coefficient is below the literal selected graph
average, owner-bucket selection supplies the complete same-`B` row
correlation with its explicit loss. -/
theorem displayedCoefficient_le_setupLoss_mul_sameHRowAverage
    (R : SameAssemblyFullCoefficientGraphIdentity F T P Y fibreCF)
    (htau : 0 < tau) (hrho : 0 < rho) (hrhoOne : rho ≤ 1)
    (htauRho : tau ≤ rho) (hk : R.k ∈ T.activeCoarse)
    (H : SquarePlankHRowSelectionFirstSetup
      (sameAssemblyGraphBufferedPlankDatum
        R htau hrho hrhoOne htauRho hk))
    {epsilon beta eta : Real}
    (B : HRowFreshPropertyBundle
      (sameAssemblyGraphBufferedPlankDatum
        R htau hrho hrhoOne htauRho hk)
      H.C H.q universalHRowCell universalHRowCell_measurable
      (Finset.univ : Finset Unit) H.retained_mass_ne_zero H.active_nonempty
        epsilon beta eta)
    (X selectorLoss : ENNReal) (outputEta : Real)
    (hDisplayedGraph :
      selectorLoss * (128 * (delta : ENNReal) ^ (-outputEta) * X) ≤
        R.graphAverage) :
    HRowFreshDisplayedCoefficientRowCorrelation
      (delta := delta) X selectorLoss outputEta
      (sameAssemblyGraphBufferedPlankDatum
        R htau hrho hrhoOne htauRho hk)
      H.C H.q universalHRowCell universalHRowCell_measurable
      (Finset.univ : Finset Unit) H.retained_mass_ne_zero H.active_nonempty
        B H.loss := by
  unfold HRowFreshDisplayedCoefficientRowCorrelation
  exact hDisplayedGraph.trans
    (graphAverage_le_setupLoss_mul_sameHRowAverage
      R htau hrho hrhoOne htauRho hk H B)

/-! ## Equivalent division-free endpoint -/

/-- The same selection-first chain also produces the raw incidence form.
The multiplication back by the exact row volume is justified by the proved
nonzero and finite volume of that very row. -/
theorem displayedCoefficient_sameHRowIncidence_of_le_graphAverage
    (R : SameAssemblyFullCoefficientGraphIdentity F T P Y fibreCF)
    (htau : 0 < tau) (hrho : 0 < rho) (hrhoOne : rho ≤ 1)
    (htauRho : tau ≤ rho) (hk : R.k ∈ T.activeCoarse)
    (H : SquarePlankHRowSelectionFirstSetup
      (sameAssemblyGraphBufferedPlankDatum
        R htau hrho hrhoOne htauRho hk))
    {epsilon beta eta : Real}
    (B : HRowFreshPropertyBundle
      (sameAssemblyGraphBufferedPlankDatum
        R htau hrho hrhoOne htauRho hk)
      H.C H.q universalHRowCell universalHRowCell_measurable
      (Finset.univ : Finset Unit) H.retained_mass_ne_zero H.active_nonempty
        epsilon beta eta)
    (X selectorLoss : ENNReal) (outputEta : Real)
    (hDisplayedGraph :
      selectorLoss * (128 * (delta : ENNReal) ^ (-outputEta) * X) ≤
        R.graphAverage) :
    HRowFreshDisplayedCoefficientRowIncidence
      (delta := delta) X selectorLoss outputEta
      (sameAssemblyGraphBufferedPlankDatum
        R htau hrho hrhoOne htauRho hk)
      H.C H.q universalHRowCell universalHRowCell_measurable
      (Finset.univ : Finset Unit) H.retained_mass_ne_zero H.active_nonempty
        B H.loss := by
  let Drow := sameAssemblyGraphBufferedPlankDatum
    R htau hrho hrhoOne htauRho hk
  let rowD := HRowFreshPlankDatum
    Drow H.C H.q universalHRowCell universalHRowCell_measurable
      (Finset.univ : Finset Unit) H.retained_mass_ne_zero H.active_nonempty
        B.tau B.S
  have hcorrelation :
      selectorLoss * (128 * (delta : ENNReal) ^ (-outputEta) * X) ≤
        H.loss * rowD.shading.averageMultiplicity := by
    simpa only [Drow, rowD,
      HRowFreshDisplayedCoefficientRowCorrelation] using
      displayedCoefficient_le_setupLoss_mul_sameHRowAverage
        R htau hrho hrhoOne htauRho hk H B X selectorLoss outputEta
          hDisplayedGraph
  have hvolume0 : volume rowD.shading.shadedUnion ≠ 0 := by
    simpa only [Drow, rowD] using
      hRowFreshPlankDatum_volume_shadedUnion_ne_zero
        Drow H.C H.q universalHRowCell universalHRowCell_measurable
          (Finset.univ : Finset Unit) H.retained_mass_ne_zero
            H.active_nonempty B
  have hvolumeTop : volume rowD.shading.shadedUnion ≠ ∞ :=
    volume_shadedUnion_ne_top rowD.shading
  change
    (selectorLoss * (128 * (delta : ENNReal) ^ (-outputEta) * X)) *
        volume rowD.shading.shadedUnion ≤
      H.loss * rowD.shading.shadingMass
  calc
    (selectorLoss * (128 * (delta : ENNReal) ^ (-outputEta) * X)) *
          volume rowD.shading.shadedUnion ≤
        (H.loss * rowD.shading.averageMultiplicity) *
          volume rowD.shading.shadedUnion :=
      mul_le_mul' hcorrelation le_rfl
    _ = H.loss *
        (rowD.shading.shadingMass / volume rowD.shading.shadedUnion) *
          volume rowD.shading.shadedUnion := by
      rfl
    _ = H.loss *
        ((rowD.shading.shadingMass / volume rowD.shading.shadedUnion) *
          volume rowD.shading.shadedUnion) := by ring
    _ = H.loss * rowD.shading.shadingMass := by
      rw [ENNReal.div_mul_cancel hvolume0 hvolumeTop]

#print axioms displayedCoefficient_le_setupLoss_mul_sameHRowAverage
#print axioms displayedCoefficient_sameHRowIncidence_of_le_graphAverage

end
end Family8CanonicalGraphFrozenDisplayedCoefficientHRowCorrelationV1
