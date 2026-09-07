import Family8Grounding.Family8ParentwiseBadParentActualFactorListSuccessorV1
import Family8Grounding.Family8NormalizedLongIntervalFiniteDef212InputsV4
import Mathlib.Tactic

/-!
# Callback-free state for one parentwise bad-factor replacement

The actual factor-list layer packages different radii and index types in one
heterogeneous list.  This file adds the analytic state carried by one genuine
parentwise replacement.  The state remembers the literal bad parent, its
fresh selected affine child, the current Definition 2.12 uniformity field,
and the honest count/scale product certificate.

The successor list is not an abstract callback result: it is definitionally
the old active-fine atom replaced by `badParentCoarseDatum S` and the selected
restriction of `badParentRescaledFibreDatum S D.shading ... q`.
-/

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 3000000

open Set MeasureTheory
open scoped BigOperators ENNReal NNReal

namespace Family8ParentwiseBadParentFactorListStateV1

open LeanEval.Analysis.WangZahlKakeya
open Submission.Kakeya.ConvexFactoring
open Submission.Kakeya.Uniformity
open Family8Def212ConvexWolffAtEveryScaleV2
open Family8Def212ConvexWolffAtEveryScaleV2.ScaleCover
open Family8GeneralizedKatzTaoMultiplicityV1
open Family8KatzTaoFrostmanPropertiesV1
open Family8NormalizedLongIntervalFrostmanInheritanceV1
open Family8NormalizedCFDividingWitnessBridgeV2.StickyScaleCover
open Family8ParentwiseBadParentActualFactorListSuccessorV1
open Family8ParentwiseBadParentFactorProductV1
open Family8ParentwiseBadParentFactorReplacementV1
open Family8StickyFiberContractedJohnFixedSourceEnvelopeV1
open Family8StickySelectedFiberLowCFFreshRetentionProducerV2
open FamilyStickyAtEveryScaleCoreV1
open FamilyStickyScaleChainCoherentIntervalProducerV1

noncomputable section

variable {delta rho : NNReal} {iota : Type}
  [Fintype iota] [DecidableEq iota]

/-! ## Concrete successor state -/

/-- All object-level and analytic data produced by one literal parentwise
bad replacement in a fixed surrounding factor-list context.

The `selected` field is data, not a callback.  Every remaining field is a
certificate about the concrete coarse and fresh-child data determined by
`D`, `S`, `q`, and `selected`. -/
structure ParentwiseBadParentFactorListState
    (D : ActualTubeDatum delta iota)
    (S : StickyScaleCover D.family rho)
    (left right : List ActualFactorDatum)
    (hrho : 0 < rho) (hrhoOne : rho <= 1)
    (q : {q // q ∈ S.activeCoarse})
    (lower C : ENNReal) where
  selected : Finset {i // i ∈ S.fiber q.1}
  selected_nonempty : selected.Nonempty
  child_admissible :
    (badParentFreshSuccessorDatum
      S D.shading hrho hrhoOne q selected).IsAdmissible
  fresh_loss_ne_top :
    selectedParentLowCFFreshLoss S hrho hrhoOne q lower ≠ ∞
  child_frostman :
    IsFrostmanIn
      (lower *
        (16 * selectedParentLowCFFreshLoss S hrho hrhoOne q lower))
      (activeSubtypeFamily (S.fiberFamily q.1) selected)
      (S.activeCoarseFamily q)
  shading_mass_retention :
    (badParentRescaledFibreDatum
      S D.shading hrho hrhoOne q).shading.shadingMass <=
      badParentFreshRetentionLoss S hrho hrhoOne q selected lower *
        (badParentFreshSuccessorDatum
          S D.shading hrho hrhoOne q selected).shading.shadingMass
  current_c_uniform : IsCUniform S C
  product :
    BadParentFreshFactorProductCertificate
      S hrho hrhoOne q selected lower C

namespace ParentwiseBadParentFactorListState

variable {D : ActualTubeDatum delta iota}
  {S : StickyScaleCover D.family rho}
  {left right : List ActualFactorDatum}
  {hrho : 0 < rho} {hrhoOne : rho <= 1}
  {q : {q // q ∈ S.activeCoarse}}
  {lower C : ENNReal}

/-- The concrete list before the replacement. -/
def sourceFactors
    (_X : ParentwiseBadParentFactorListState
      D S left right hrho hrhoOne q lower C) :
    List ActualFactorDatum :=
  badParentSourceFactorList D left right S

/-- The concrete list after the replacement.  The two new consecutive atoms
are the genuine active-coarse datum and the selected affine-child datum. -/
def successorFactors
    (X : ParentwiseBadParentFactorListState
      D S left right hrho hrhoOne q lower C) :
    List ActualFactorDatum :=
  badParentSuccessorFactorList
    D left right S hrho hrhoOne q X.selected

/-- The literal coarse datum occurs in the successor factor list. -/
theorem coarseAtom_mem_successorFactors
    (X : ParentwiseBadParentFactorListState
      D S left right hrho hrhoOne q lower C) :
    badParentCoarseAtom D S ∈ X.successorFactors := by
  simp only [successorFactors, badParentSuccessorFactorList,
    List.mem_append, List.mem_cons]
  exact Or.inr (Or.inl trivial)

/-- The selected restriction of the literal rescaled `q`-fibre occurs in the
successor factor list. -/
theorem freshChildAtom_mem_successorFactors
    (X : ParentwiseBadParentFactorListState
      D S left right hrho hrhoOne q lower C) :
    badParentFreshChildAtom
      D S hrho hrhoOne q X.selected ∈ X.successorFactors := by
  simp only [successorFactors, badParentSuccessorFactorList,
    List.mem_append, List.mem_cons]
  exact Or.inr (Or.inr (Or.inl trivial))

/-- State-level exact scale product for the actual surrounding list. -/
theorem successor_radiusProduct
    (X : ParentwiseBadParentFactorListState
      D S left right hrho hrhoOne q lower C) :
    factorRadiusProduct X.successorFactors =
      (3 / 64 : NNReal) * factorRadiusProduct X.sourceFactors := by
  exact badParentSuccessorFactorList_radiusProduct
    D left right S hrho hrhoOne q X.selected

/-- State-level forward count-product comparison. -/
theorem successor_cardProduct_le
    (X : ParentwiseBadParentFactorListState
      D S left right hrho hrhoOne q lower C) :
    factorCardProduct X.successorFactors <=
      C * factorCardProduct X.sourceFactors := by
  exact badParentSuccessorFactorList_cardProduct_le
    D left right S hrho hrhoOne q X.selected lower C X.product

/-- State-level reverse count-product comparison with the explicit fresh
retention loss. -/
theorem source_cardProduct_le
    (X : ParentwiseBadParentFactorListState
      D S left right hrho hrhoOne q lower C) :
    factorCardProduct X.sourceFactors <=
      (C * badParentFreshRetentionLoss
        S hrho hrhoOne q X.selected lower) *
        factorCardProduct X.successorFactors := by
  exact badParentSourceFactorList_cardProduct_le
    D left right S hrho hrhoOne q X.selected lower C X.product

end ParentwiseBadParentFactorListState

/-! ## Callback-free producers -/

/-- Build the concrete successor state from the literal bad parent and the
current-scale Definition 2.12 uniformity field. -/
theorem exists_parentwiseBadParentFactorListState
    (D : ActualTubeDatum delta iota)
    (S : StickyScaleCover D.family rho)
    (left right : List ActualFactorDatum)
    (hD : D.IsAdmissible)
    (hrho : 0 < rho) (hrhoOne : rho <= 1)
    (hdeltaRho : delta <= rho)
    (q : {q // q ∈ S.activeCoarse})
    {lower C : ENNReal} (hlowerTop : lower ≠ ∞)
    (hbad : parentNormalizedFiberCFAt S q < lower)
    (huniform : IsCUniform S C) :
    Nonempty (ParentwiseBadParentFactorListState
      D S left right hrho hrhoOne q lower C) := by
  obtain ⟨selected, hselected, hadmissible, hfreshTop,
      hFrostman, hmass, hproduct⟩ :=
    exists_badParent_freshFactorReplacement_with_product
      S D.shading hD.delta_pos hD.delta_le_half
        hrho hrhoOne hdeltaRho q hlowerTop hbad huniform
  exact ⟨
    { selected := selected
      selected_nonempty := hselected
      child_admissible := hadmissible
      fresh_loss_ne_top := hfreshTop
      child_frostman := hFrostman
      shading_mass_retention := hmass
      current_c_uniform := huniform
      product := hproduct }⟩

/-- A full exact Definition 2.12 package supplies the uniformity field at the
literal radius, hence constructs the same callback-free factor-list state.
No other all-scale field is discarded or replaced by a synthetic child
hierarchy: the theorem uses exactly the current cover `M.base.cover rho`. -/
theorem exists_parentwiseBadParentFactorListState_of_exactScaleDef212
    (D : ActualTubeDatum delta iota) (hD : D.IsAdmissible)
    (M : CoherentStickyMultiscaleCover D.family)
    (left right : List ActualFactorDatum)
    (rho : NNReal) (hdeltaRho : delta <= rho) (hrhoOne : rho <= 1)
    (q : {q // q ∈
      (M.base.cover rho hdeltaRho hrhoOne).activeCoarse})
    {K : NNReal} (H : ExactScaleDef212Inputs M.base K)
    {lower : ENNReal} (hlowerTop : lower ≠ ∞)
    (hbad : parentNormalizedFiberCFAt
      (M.base.cover rho hdeltaRho hrhoOne) q < lower) :
    Nonempty (ParentwiseBadParentFactorListState
      D (M.base.cover rho hdeltaRho hrhoOne) left right
        (hD.delta_pos.trans_le hdeltaRho) hrhoOne q lower (K : ENNReal)) := by
  exact exists_parentwiseBadParentFactorListState
    D (M.base.cover rho hdeltaRho hrhoOne) left right hD
      (hD.delta_pos.trans_le hdeltaRho) hrhoOne hdeltaRho q
      hlowerTop hbad (H.c_uniform rho hdeltaRho hrhoOne)

#print axioms ParentwiseBadParentFactorListState.sourceFactors
#print axioms ParentwiseBadParentFactorListState.successorFactors
#print axioms ParentwiseBadParentFactorListState.coarseAtom_mem_successorFactors
#print axioms ParentwiseBadParentFactorListState.freshChildAtom_mem_successorFactors
#print axioms ParentwiseBadParentFactorListState.successor_radiusProduct
#print axioms ParentwiseBadParentFactorListState.successor_cardProduct_le
#print axioms ParentwiseBadParentFactorListState.source_cardProduct_le
#print axioms exists_parentwiseBadParentFactorListState
#print axioms exists_parentwiseBadParentFactorListState_of_exactScaleDef212

end
end Family8ParentwiseBadParentFactorListStateV1
