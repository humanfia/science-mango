import Family8Grounding.Family8NormalizedLongIntervalPointwiseFrostmanInheritanceV1
import Family8Grounding.Family8ParentwiseBadParentFactorListStateV1
import Family8Grounding.Family8ParentwiseBadParentFreshProxyFrostmanV2
import Family8Grounding.Family8ParentwiseBadParentMassAwareActualFactorListV1
import Mathlib.Tactic

/-!
# Formal mass-aware state for one parentwise bad-factor successor

This is the callback-free composer for the literal bad parent `q`.  It keeps
the same selected subtype returned by the product producer, uses its source
Frostman certificate directly in the same-selected proxy transport, and
stores the parent-aggregated coarse shading.  Paper and actual radii are
kept separately: the paper radii multiply exactly, while the actual
contracted-John child exposes the fixed coefficient `3/64`.
-/

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 4000000

open Set MeasureTheory
open scoped BigOperators ENNReal NNReal

namespace Family8ParentwiseBadParentMassAwareFactorListStateV2

open LeanEval.Analysis.WangZahlKakeya
open Submission.Kakeya.ConvexGeometry
open Submission.Kakeya.ConvexFactoring
open Submission.Kakeya.Uniformity
open Family8ContractedJohnActualTubeProxyV1
open Family8Def212ConvexWolffAtEveryScaleV2.ScaleCover
open Family8KatzTaoFrostmanPropertiesV1
open Family8NormalizedCFDividingWitnessBridgeV2.StickyScaleCover
open Family8NormalizedLongIntervalFrostmanInheritanceV1
open Family8NormalizedLongIntervalPointwiseFrostmanInheritanceV1
open Family8ParentwiseBadParentActualFactorListSuccessorV1
open Family8ParentwiseBadParentFactorListStateV1
open Family8ParentwiseBadParentFactorProductV1
open Family8ParentwiseBadParentFactorReplacementV1
open Family8ParentwiseBadParentFreshProxyFrostmanV2
open Family8ParentwiseBadParentMassAwareActualFactorListV1
open Family8StickyActiveCoarseAdmissibleChildV1
open Family8StickySelectedFiberLowCFFreshRetentionProducerV2
open FamilyStickyAtEveryScaleCoreV1
open FamilyStickyHierarchyEndpointPrefixShadingTransportV1.StickyScaleCover
open FamilyStickyScaleChainCoherentIntervalProducerV1

noncomputable section

variable {delta rho : NNReal} {iota : Type}
  [Fintype iota] [DecidableEq iota]

/-! ## Exact paper/actual scale ledger -/

/-- The exact local scale ledger for one paper factor replacement.

The paper child has radius `delta / rho`, whereas the actual normalized
proxy child has radius `(3/64) * (delta/rho)`.  All fields are pinned to
these literal values, so the fixed coefficient cannot be silently erased. -/
structure BadParentScaleLedger (delta rho : NNReal) where
  sourcePaperRadius : NNReal
  coarsePaperRadius : NNReal
  childPaperRadius : NNReal
  sourceActualRadius : NNReal
  coarseActualRadius : NNReal
  childActualRadius : NNReal
  sourceGeomCoeff : NNReal
  coarseGeomCoeff : NNReal
  childGeomCoeff : NNReal
  sourcePaperRadius_eq : sourcePaperRadius = delta
  coarsePaperRadius_eq : coarsePaperRadius = rho
  childPaperRadius_eq : childPaperRadius = delta / rho
  sourceActualRadius_eq : sourceActualRadius = delta
  coarseActualRadius_eq : coarseActualRadius = rho
  childActualRadius_eq :
    childActualRadius = badParentFreshChildRadius delta rho
  sourceGeomCoeff_eq : sourceGeomCoeff = 1
  coarseGeomCoeff_eq : coarseGeomCoeff = 1
  childGeomCoeff_eq : childGeomCoeff = 3 / 64
  source_actual_eq_geom_mul_paper :
    sourceActualRadius = sourceGeomCoeff * sourcePaperRadius
  coarse_actual_eq_geom_mul_paper :
    coarseActualRadius = coarseGeomCoeff * coarsePaperRadius
  child_actual_eq_geom_mul_paper :
    childActualRadius = childGeomCoeff * childPaperRadius
  paper_product_eq :
    coarsePaperRadius * childPaperRadius = sourcePaperRadius
  actual_product_eq :
    coarseActualRadius * childActualRadius =
      (3 / 64 : NNReal) * sourceActualRadius

/-- Canonical exact ledger at the literal bad split. -/
def canonicalBadParentScaleLedger
    (delta rho : NNReal) (hrho : 0 < rho) :
    BadParentScaleLedger delta rho where
  sourcePaperRadius := delta
  coarsePaperRadius := rho
  childPaperRadius := delta / rho
  sourceActualRadius := delta
  coarseActualRadius := rho
  childActualRadius := badParentFreshChildRadius delta rho
  sourceGeomCoeff := 1
  coarseGeomCoeff := 1
  childGeomCoeff := 3 / 64
  sourcePaperRadius_eq := rfl
  coarsePaperRadius_eq := rfl
  childPaperRadius_eq := rfl
  sourceActualRadius_eq := rfl
  coarseActualRadius_eq := rfl
  childActualRadius_eq := rfl
  sourceGeomCoeff_eq := rfl
  coarseGeomCoeff_eq := rfl
  childGeomCoeff_eq := rfl
  source_actual_eq_geom_mul_paper := by simp
  coarse_actual_eq_geom_mul_paper := by simp
  child_actual_eq_geom_mul_paper :=
    badParentFreshChildRadius_eq_fixed_mul_ratio hrho
  paper_product_eq := by
    apply NNReal.eq
    simp only [NNReal.coe_mul, NNReal.coe_div]
    have hrhoReal : (rho : Real) ≠ 0 := by
      exact_mod_cast hrho.ne'
    field_simp [hrhoReal]
  actual_product_eq := rho_mul_badParentFreshChildRadius_eq hrho

/-! ## Same-selected mass-aware successor state -/

/-- Formal state for one concrete parentwise successor.

`base` contains the selected subtype and the honest product certificate.
The proxy Frostman field consumes `base.child_frostman` on exactly that
selected subtype; it does not run another selection or rebuild a different
object. -/
structure ParentwiseBadParentMassAwareFactorListState
    (D : ActualTubeDatum delta iota)
    (S : StickyScaleCover D.family rho)
    (left right : List ActualFactorDatum)
    (hrho : 0 < rho) (hrhoOne : rho ≤ 1)
    (q : {q // q ∈ S.activeCoarse})
    (lower C : ENNReal) where
  base : ParentwiseBadParentFactorListState
    D S left right hrho hrhoOne q lower C
  scale : BadParentScaleLedger delta rho
  child_proxy_frostman :
    IsFrostmanIn
      (badParentFreshProxyFrostmanConstant
        S D.shading hrho hrhoOne q base.selected
          (lower *
            (16 * selectedParentLowCFFreshLoss
              S hrho hrhoOne q lower)))
      (badParentFreshSuccessorDatum
        S D.shading hrho hrhoOne q base.selected).family.bodyFamily
      unitBallBody
  coarse_shadingMass_le_source :
    (activeCoarseAggregatedDatum D S).shading.shadingMass ≤
      (activeFineShading S D.shading).shadingMass
  coarse_shadedUnion_eq_source :
    (activeCoarseAggregatedDatum D S).shading.shadedUnion =
      (activeFineShading S D.shading).shadedUnion
  coarse_averageMultiplicity_le_source :
    (activeCoarseAggregatedDatum D S).shading.averageMultiplicity ≤
      (activeFineShading S D.shading).averageMultiplicity

namespace ParentwiseBadParentMassAwareFactorListState

variable {D : ActualTubeDatum delta iota}
  {S : StickyScaleCover D.family rho}
  {left right : List ActualFactorDatum}
  {hrho : 0 < rho} {hrhoOne : rho ≤ 1}
  {q : {q // q ∈ S.activeCoarse}}
  {lower C : ENNReal}

/-- The concrete pre-replacement factor list. -/
def sourceFactors
    (_X : ParentwiseBadParentMassAwareFactorListState
      D S left right hrho hrhoOne q lower C) :
    List ActualFactorDatum :=
  badParentSourceFactorList D left right S

/-- The concrete mass-aware successor factor list. -/
def successorFactors
    (X : ParentwiseBadParentMassAwareFactorListState
      D S left right hrho hrhoOne q lower C) :
    List ActualFactorDatum :=
  badParentSuccessorFactorList
    D left right S hrho hrhoOne q X.base.selected

/-- Exact actual-radius update of the entire surrounding factor list. -/
theorem successor_radiusProduct
    (X : ParentwiseBadParentMassAwareFactorListState
      D S left right hrho hrhoOne q lower C) :
    factorRadiusProduct X.successorFactors =
      (3 / 64 : NNReal) * factorRadiusProduct X.sourceFactors := by
  exact badParentSuccessorFactorList_radiusProduct
    D left right S hrho hrhoOne q X.base.selected

/-- Exact inverse form exposing the fixed `64/3` scale loss. -/
theorem source_radiusProduct_eq_fixedLoss_mul
    (X : ParentwiseBadParentMassAwareFactorListState
      D S left right hrho hrhoOne q lower C) :
    factorRadiusProduct X.sourceFactors =
      (64 / 3 : NNReal) * factorRadiusProduct X.successorFactors := by
  exact badParentSourceFactorList_radiusProduct_eq_fixedLoss_mul
    D left right S hrho hrhoOne q X.base.selected

/-- Honest forward count-product comparison. -/
theorem successor_cardProduct_le
    (X : ParentwiseBadParentMassAwareFactorListState
      D S left right hrho hrhoOne q lower C) :
    factorCardProduct X.successorFactors ≤
      C * factorCardProduct X.sourceFactors := by
  exact badParentSuccessorFactorList_cardProduct_le
    D left right S hrho hrhoOne q X.base.selected lower C X.base.product

/-- Honest reverse count-product comparison with the selected fresh loss. -/
theorem source_cardProduct_le
    (X : ParentwiseBadParentMassAwareFactorListState
      D S left right hrho hrhoOne q lower C) :
    factorCardProduct X.sourceFactors ≤
      (C * badParentFreshRetentionLoss
        S hrho hrhoOne q X.base.selected lower) *
        factorCardProduct X.successorFactors := by
  exact badParentSourceFactorList_cardProduct_le
    D left right S hrho hrhoOne q X.base.selected lower C X.base.product

end ParentwiseBadParentMassAwareFactorListState

/-! ## Callback-free producer on the same selected subtype -/

/-- Build the formal mass-aware successor from one literal low-CF parent.

The selected-source Frostman proof in `base` is passed directly to V2 to
obtain Frostman control of the actual fresh proxy datum. -/
theorem exists_parentwiseBadParentMassAwareFactorListState
    (D : ActualTubeDatum delta iota)
    (S : StickyScaleCover D.family rho)
    (left right : List ActualFactorDatum)
    (hdelta : 0 < delta) (hdeltaHalf : delta ≤ (2 : NNReal)⁻¹)
    (hrho : 0 < rho) (hrhoOne : rho ≤ 1)
    (hdeltaRho : delta ≤ rho)
    (q : {q // q ∈ S.activeCoarse})
    {lower C : ENNReal} (hlowerTop : lower ≠ ∞)
    (hbad : parentNormalizedFiberCFAt S q < lower)
    (huniform : IsCUniform S C) :
    Nonempty (ParentwiseBadParentMassAwareFactorListState
      D S left right hrho hrhoOne q lower C) := by
  obtain ⟨selected, hselected, hadmissible, hfreshTop,
      hSourceFrostman, hmass, hproduct⟩ :=
    exists_badParent_freshFactorReplacement_with_product
      S D.shading hdelta hdeltaHalf hrho hrhoOne hdeltaRho q
        hlowerTop hbad huniform
  let X : ParentwiseBadParentFactorListState
      D S left right hrho hrhoOne q lower C :=
    { selected := selected
      selected_nonempty := hselected
      child_admissible := hadmissible
      fresh_loss_ne_top := hfreshTop
      child_frostman := hSourceFrostman
      shading_mass_retention := hmass
      current_c_uniform := huniform
      product := hproduct }
  have hProxyFrostman : IsFrostmanIn
      (badParentFreshProxyFrostmanConstant
        S D.shading hrho hrhoOne q selected
          (lower *
            (16 * selectedParentLowCFFreshLoss
              S hrho hrhoOne q lower)))
      (badParentFreshSuccessorDatum
        S D.shading hrho hrhoOne q selected).family.bodyFamily
      unitBallBody :=
    badParentFreshSuccessorDatum_isFrostmanIn_unitBall_of_source
      S D.shading hdelta hdeltaHalf hrho hrhoOne hdeltaRho
        q selected hselected X.child_frostman hadmissible
  exact ⟨
    { base := X
      scale := canonicalBadParentScaleLedger delta rho hrho
      child_proxy_frostman := hProxyFrostman
      coarse_shadingMass_le_source :=
        badParentAggregatedCoarse_shadingMass_le_activeFine D S
      coarse_shadedUnion_eq_source :=
        badParentAggregatedCoarse_shadedUnion_eq_activeFine D S
      coarse_averageMultiplicity_le_source :=
        badParentAggregatedCoarse_averageMultiplicity_le_activeFine D S }⟩

#print axioms canonicalBadParentScaleLedger
#print axioms ParentwiseBadParentMassAwareFactorListState.sourceFactors
#print axioms ParentwiseBadParentMassAwareFactorListState.successorFactors
#print axioms ParentwiseBadParentMassAwareFactorListState.successor_radiusProduct
#print axioms
  ParentwiseBadParentMassAwareFactorListState.source_radiusProduct_eq_fixedLoss_mul
#print axioms ParentwiseBadParentMassAwareFactorListState.successor_cardProduct_le
#print axioms ParentwiseBadParentMassAwareFactorListState.source_cardProduct_le
#print axioms exists_parentwiseBadParentMassAwareFactorListState

end
end Family8ParentwiseBadParentMassAwareFactorListStateV2
