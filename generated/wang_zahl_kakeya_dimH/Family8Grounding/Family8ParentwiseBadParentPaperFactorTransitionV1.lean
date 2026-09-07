import Family8Grounding.Family8PaperFactorStateV1
import Family8Grounding.Family8ParentwiseBadParentMassAwareFactorListStateV2
import Mathlib.Tactic

/-!
# Paper-factor transition for one literal bad parent

This module turns the mass-aware same-parent successor into one transition
between heterogeneous paper factor states.  The source and successor lists
are definitionally the actual lists carried by `StateV2`.  Readiness is
supplied structurally for every unchanged atom and explicitly for the old,
coarse, and fresh atoms; no identity cover is manufactured.

The transition records only the local factor replacement.  It deliberately
does not duplicate the independent dual-child orchestration certificate or
the accumulated scalar-loss algebra.
-/

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 4000000

open Set MeasureTheory
open scoped BigOperators ENNReal NNReal

namespace Family8ParentwiseBadParentPaperFactorTransitionV1

open LeanEval.Analysis.WangZahlKakeya
open Submission.Kakeya.ConvexFactoring
open Submission.Kakeya.Uniformity
open Family8KatzTaoFrostmanPropertiesV1
open Family8NormalizedCFDividingWitnessBridgeV2.StickyScaleCover
open Family8PaperFactorStateV1
open Family8ParentwiseBadParentActualFactorListSuccessorV1
open Family8ParentwiseBadParentFactorListStateV1
open Family8ParentwiseBadParentFactorProductV1
open Family8ParentwiseBadParentFactorReplacementV1
open Family8ParentwiseBadParentFreshProxyFrostmanV2
open Family8ParentwiseBadParentMassAwareFactorListStateV2
open Family8ParentwiseBadParentMassAwareFactorListStateV2.ParentwiseBadParentMassAwareFactorListState
open Family8StickyActiveCoarseAdmissibleChildV1
open Family8StickySelectedFiberLowCFFreshRetentionProducerV2
open FamilyStickyAtEveryScaleCoreV1
open FamilyStickyHierarchyEndpointPrefixShadingTransportV1.StickyScaleCover

noncomputable section

variable {delta rho : NNReal} {iota : Type}
  [Fintype iota] [DecidableEq iota]

/-- A paper-faithful single replacement certificate.

Both factor states are tied to the literal lists in `X`.  Every quantitative
field is the corresponding concrete theorem of that same `X`, including the
fixed `3/64` geometric coefficient, its displayed inverse `64/3`, both count
directions, the selected fresh-child certificates, and the aggregated
coarse-shading correlations. -/
structure ParentwiseBadParentPaperFactorTransition
    (D : ActualTubeDatum delta iota)
    (S : StickyScaleCover D.family rho)
    (left right : List ActualFactorDatum)
    (hrho : 0 < rho) (hrhoOne : rho ≤ 1)
    (q : {q // q ∈ S.activeCoarse})
    (lower C : ENNReal)
    (X : ParentwiseBadParentMassAwareFactorListState
      D S left right hrho hrhoOne q lower C) where
  source : PaperFactorState
  successor : PaperFactorState
  source_factors_eq : source.factors = X.sourceFactors
  successor_factors_eq : successor.factors = X.successorFactors
  paper_radius_product_eq :
    X.scale.coarsePaperRadius * X.scale.childPaperRadius =
      X.scale.sourcePaperRadius
  actual_radius_product_eq :
    X.scale.coarseActualRadius * X.scale.childActualRadius =
      (3 / 64 : NNReal) * X.scale.sourceActualRadius
  child_geom_coefficient_eq :
    X.scale.childGeomCoeff = (3 / 64 : NNReal)
  successor_radiusProduct_eq :
    factorRadiusProduct X.successorFactors =
      (3 / 64 : NNReal) * factorRadiusProduct X.sourceFactors
  source_radiusProduct_eq_fixedLoss_mul :
    factorRadiusProduct X.sourceFactors =
      (64 / 3 : NNReal) * factorRadiusProduct X.successorFactors
  successor_cardProduct_le :
    factorCardProduct X.successorFactors ≤
      C * factorCardProduct X.sourceFactors
  source_cardProduct_le :
    factorCardProduct X.sourceFactors ≤
      (C * badParentFreshRetentionLoss
        S hrho hrhoOne q X.base.selected lower) *
        factorCardProduct X.successorFactors
  fresh_selected_nonempty : X.base.selected.Nonempty
  fresh_child_admissible :
    (badParentFreshSuccessorDatum
      S D.shading hrho hrhoOne q X.base.selected).IsAdmissible
  fresh_unitBall_frostman :
    IsFrostmanIn
      (badParentFreshProxyFrostmanConstant
        S D.shading hrho hrhoOne q X.base.selected
          (lower *
            (16 * selectedParentLowCFFreshLoss
              S hrho hrhoOne q lower)))
      (badParentFreshSuccessorDatum
        S D.shading hrho hrhoOne q X.base.selected).family.bodyFamily
      unitBallBody
  fresh_shadingMass_retention :
    (badParentRescaledFibreDatum
      S D.shading hrho hrhoOne q).shading.shadingMass ≤
      badParentFreshRetentionLoss
          S hrho hrhoOne q X.base.selected lower *
        (badParentFreshSuccessorDatum
          S D.shading hrho hrhoOne q X.base.selected).shading.shadingMass
  coarse_shadingMass_le_source :
    (activeCoarseAggregatedDatum D S).shading.shadingMass ≤
      (activeFineShading S D.shading).shadingMass
  coarse_shadedUnion_eq_source :
    (activeCoarseAggregatedDatum D S).shading.shadedUnion =
      (activeFineShading S D.shading).shadedUnion
  coarse_averageMultiplicity_le_source :
    (activeCoarseAggregatedDatum D S).shading.averageMultiplicity ≤
      (activeFineShading S D.shading).averageMultiplicity

/-- Construct the transition from structurally aligned readiness data.

The five readiness arguments are literal: readiness for every atom in the
unchanged left and right lists, readiness for the exposed old atom, and
separate readiness for the actual aggregated coarse and selected fresh
atoms.  Thus the producer contains no readiness callback. -/
def parentwiseBadParentPaperFactorTransition
    (D : ActualTubeDatum delta iota)
    (S : StickyScaleCover D.family rho)
    (left right : List ActualFactorDatum)
    (hrho : 0 < rho) (hrhoOne : rho ≤ 1)
    (q : {q // q ∈ S.activeCoarse})
    (lower C : ENNReal)
    (X : ParentwiseBadParentMassAwareFactorListState
      D S left right hrho hrhoOne q lower C)
    (leftReadiness : PaperFactorReadinessList left)
    (sourceAtomReadiness :
      PaperFactorAtomReadiness (badParentActiveFineSourceAtom D S))
    (rightReadiness : PaperFactorReadinessList right)
    (coarseAtomReadiness :
      PaperFactorAtomReadiness (badParentCoarseAtom D S))
    (freshAtomReadiness :
      PaperFactorAtomReadiness
        (badParentFreshChildAtom
          D S hrho hrhoOne q X.base.selected)) :
    ParentwiseBadParentPaperFactorTransition
      D S left right hrho hrhoOne q lower C X := by
  let sourceReadiness : PaperFactorReadinessList
      (badParentSourceFactorList D left right S) :=
    PaperFactorReadinessList.append leftReadiness
      (.cons sourceAtomReadiness rightReadiness)
  let successorReadiness : PaperFactorReadinessList
      (badParentSuccessorFactorList
        D left right S hrho hrhoOne q X.base.selected) :=
    PaperFactorReadinessList.append leftReadiness
      (.cons coarseAtomReadiness
        (.cons freshAtomReadiness rightReadiness))
  exact
    { source := PaperFactorState.ofFactors
        (badParentSourceFactorList D left right S) sourceReadiness
      successor := PaperFactorState.ofFactors
        (badParentSuccessorFactorList
          D left right S hrho hrhoOne q X.base.selected)
        successorReadiness
      source_factors_eq := rfl
      successor_factors_eq := rfl
      paper_radius_product_eq := X.scale.paper_product_eq
      actual_radius_product_eq := X.scale.actual_product_eq
      child_geom_coefficient_eq := X.scale.childGeomCoeff_eq
      successor_radiusProduct_eq := X.successor_radiusProduct
      source_radiusProduct_eq_fixedLoss_mul :=
        X.source_radiusProduct_eq_fixedLoss_mul
      successor_cardProduct_le := X.successor_cardProduct_le
      source_cardProduct_le := X.source_cardProduct_le
      fresh_selected_nonempty := X.base.selected_nonempty
      fresh_child_admissible := X.base.child_admissible
      fresh_unitBall_frostman := X.child_proxy_frostman
      fresh_shadingMass_retention := X.base.shading_mass_retention
      coarse_shadingMass_le_source := X.coarse_shadingMass_le_source
      coarse_shadedUnion_eq_source := X.coarse_shadedUnion_eq_source
      coarse_averageMultiplicity_le_source :=
        X.coarse_averageMultiplicity_le_source }

#print axioms ParentwiseBadParentPaperFactorTransition
#print axioms parentwiseBadParentPaperFactorTransition

end
end Family8ParentwiseBadParentPaperFactorTransitionV1
