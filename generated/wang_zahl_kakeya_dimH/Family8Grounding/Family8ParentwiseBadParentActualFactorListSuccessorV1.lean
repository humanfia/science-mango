import Family8Grounding.Family8ParentwiseBadParentFactorProductV1
import Family8Grounding.Family8StickyActiveCoarseAdmissibleChildV1
import Mathlib.Tactic

/-!
# Actual-datum factor-list update at one bad parent

The parentwise bad branch replaces one actual active-fine factor by two
literal actual data: its active coarse family and the fresh selected
contracted-John fibre.  This file performs that replacement in a
heterogeneous list and transports the honest scale/cardinality product data
from `Family8ParentwiseBadParentFactorProductV1`.

Only actual data and their computable radii/cardinalities are packaged here.
In particular, no identity-radius cover is advertised as the transported
coherent hierarchy of the selected fibre.
-/

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 3000000

open scoped BigOperators ENNReal NNReal

namespace Family8ParentwiseBadParentActualFactorListSuccessorV1

open LeanEval.Analysis.WangZahlKakeya
open Submission.Kakeya.ConvexFactoring
open Submission.Kakeya.Uniformity
open Family8GeneralizedKatzTaoMultiplicityV1
open Family8KatzTaoFrostmanPropertiesV1
open Family8ParentwiseBadParentFactorProductV1
open Family8ParentwiseBadParentFactorReplacementV1
open Family8StickyActiveCoarseAdmissibleChildV1
open FamilyStickyAtEveryScaleCoreV1

noncomputable section

/-! ## A heterogeneous list of literal actual data -/

/-- An existentially packaged actual tube datum.  Its radius and finite
index type remain available for exact products even when adjacent factors
have different types. -/
structure ActualFactorDatum where
  radius : NNReal
  index : Type
  fintypeIndex : Fintype index
  decidableEqIndex : DecidableEq index
  datum : @ActualTubeDatum radius index fintypeIndex decidableEqIndex

namespace ActualFactorDatum

/-- Package an actual datum without changing its radius or index type. -/
def ofDatum {radius : NNReal} {index : Type}
    [Fintype index] [DecidableEq index]
    (D : ActualTubeDatum radius index) : ActualFactorDatum where
  radius := radius
  index := index
  fintypeIndex := inferInstance
  decidableEqIndex := inferInstance
  datum := D

/-- Literal cardinality of the packaged actual factor. -/
def card (A : ActualFactorDatum) : Nat :=
  @Fintype.card A.index A.fintypeIndex

@[simp] theorem ofDatum_radius
    {radius : NNReal} {index : Type}
    [Fintype index] [DecidableEq index]
    (D : ActualTubeDatum radius index) :
    (ofDatum D).radius = radius :=
  rfl

@[simp] theorem ofDatum_card
    {radius : NNReal} {index : Type}
    [Fintype index] [DecidableEq index]
    (D : ActualTubeDatum radius index) :
    (ofDatum D).card = Fintype.card index :=
  rfl

end ActualFactorDatum

/-- Product of the literal radii in a heterogeneous factor list. -/
def factorRadiusProduct (factors : List ActualFactorDatum) : NNReal :=
  (factors.map ActualFactorDatum.radius).prod

/-- Product of the literal finite index cardinalities in a heterogeneous
factor list. -/
def factorCardProduct (factors : List ActualFactorDatum) : ENNReal :=
  (factors.map fun A => (A.card : ENNReal)).prod

@[simp] theorem factorRadiusProduct_nil :
    factorRadiusProduct [] = 1 := by
  rfl

@[simp] theorem factorRadiusProduct_cons
    (A : ActualFactorDatum) (tail : List ActualFactorDatum) :
    factorRadiusProduct (A :: tail) =
      A.radius * factorRadiusProduct tail := by
  rfl

@[simp] theorem factorRadiusProduct_append
    (left right : List ActualFactorDatum) :
    factorRadiusProduct (left ++ right) =
      factorRadiusProduct left * factorRadiusProduct right := by
  simp only [factorRadiusProduct, List.map_append, List.prod_append]

@[simp] theorem factorCardProduct_nil :
    factorCardProduct [] = 1 := by
  rfl

@[simp] theorem factorCardProduct_cons
    (A : ActualFactorDatum) (tail : List ActualFactorDatum) :
    factorCardProduct (A :: tail) =
      (A.card : ENNReal) * factorCardProduct tail := by
  rfl

@[simp] theorem factorCardProduct_append
    (left right : List ActualFactorDatum) :
    factorCardProduct (left ++ right) =
      factorCardProduct left * factorCardProduct right := by
  simp only [factorCardProduct, List.map_append, List.prod_append]

/-! ## The three literal factor atoms at one replacement -/

variable {delta rho : NNReal} {iota : Type}
  [Fintype iota] [DecidableEq iota]
  (D : ActualTubeDatum delta iota)

/-- The old factor restricted to the literal active fine indices of the
selected Sticky cover. -/
def badParentActiveFineSourceDatum
    (S : StickyScaleCover D.family rho) :
    ActualTubeDatum delta {i // i ∈ S.activeFine} :=
  restrictActualTubeDatum D S.activeFine

def badParentActiveFineSourceAtom
    (S : StickyScaleCover D.family rho) : ActualFactorDatum :=
  ActualFactorDatum.ofDatum (badParentActiveFineSourceDatum D S)

/-- The genuine active coarse datum supplied by the Sticky cover. -/
def badParentCoarseAtom
    (S : StickyScaleCover D.family rho) : ActualFactorDatum :=
  ActualFactorDatum.ofDatum (activeCoarseAggregatedDatum D S)

/-- The genuine fresh selected affine-child datum. -/
def badParentFreshChildAtom
    (S : StickyScaleCover D.family rho)
    (hrho : 0 < rho) (hrhoOne : rho ≤ 1)
    (q : {q // q ∈ S.activeCoarse})
    (selected : Finset {i // i ∈ S.fiber q.1}) : ActualFactorDatum :=
  ActualFactorDatum.ofDatum
    (badParentFreshSuccessorDatum
      S D.shading hrho hrhoOne q selected)

@[simp] theorem badParentActiveFineSourceAtom_radius
    (S : StickyScaleCover D.family rho) :
    (badParentActiveFineSourceAtom D S).radius = delta :=
  rfl

@[simp] theorem badParentActiveFineSourceAtom_card
    (S : StickyScaleCover D.family rho) :
    (badParentActiveFineSourceAtom D S).card = S.activeFine.card := by
  simp only [badParentActiveFineSourceAtom,
    ActualFactorDatum.ofDatum_card, Fintype.card_coe]

@[simp] theorem badParentCoarseAtom_radius
    (S : StickyScaleCover D.family rho) :
    (badParentCoarseAtom D S).radius = rho :=
  rfl

@[simp] theorem badParentCoarseAtom_card
    (S : StickyScaleCover D.family rho) :
    (badParentCoarseAtom D S).card = S.activeCoarse.card := by
  simp only [badParentCoarseAtom,
    ActualFactorDatum.ofDatum_card, Fintype.card_coe]

@[simp] theorem badParentFreshChildAtom_radius
    (S : StickyScaleCover D.family rho)
    (hrho : 0 < rho) (hrhoOne : rho ≤ 1)
    (q : {q // q ∈ S.activeCoarse})
    (selected : Finset {i // i ∈ S.fiber q.1}) :
    (badParentFreshChildAtom D S hrho hrhoOne q selected).radius =
      badParentFreshChildRadius delta rho :=
  rfl

@[simp] theorem badParentFreshChildAtom_card
    (S : StickyScaleCover D.family rho)
    (hrho : 0 < rho) (hrhoOne : rho ≤ 1)
    (q : {q // q ∈ S.activeCoarse})
    (selected : Finset {i // i ∈ S.fiber q.1}) :
    (badParentFreshChildAtom D S hrho hrhoOne q selected).card =
      selected.card := by
  simp only [badParentFreshChildAtom, ActualFactorDatum.ofDatum_card,
    Fintype.card_coe]

/-! ## Replace one actual factor by the two literal children -/

/-- The old list, written with the selected active-fine factor exposed. -/
def badParentSourceFactorList
    (left right : List ActualFactorDatum)
    (S : StickyScaleCover D.family rho) : List ActualFactorDatum :=
  left ++ badParentActiveFineSourceAtom D S :: right

/-- The paper-style successor list: the exposed factor is replaced by its
active coarse datum and the selected fresh affine-child datum. -/
def badParentSuccessorFactorList
    (left right : List ActualFactorDatum)
    (S : StickyScaleCover D.family rho)
    (hrho : 0 < rho) (hrhoOne : rho ≤ 1)
    (q : {q // q ∈ S.activeCoarse})
    (selected : Finset {i // i ∈ S.fiber q.1}) :
    List ActualFactorDatum :=
  left ++ badParentCoarseAtom D S ::
    badParentFreshChildAtom D S hrho hrhoOne q selected :: right

/-- Replacing one factor by the two actual children multiplies the literal
radius product by exactly `3/64`. -/
theorem badParentSuccessorFactorList_radiusProduct
    (left right : List ActualFactorDatum)
    (S : StickyScaleCover D.family rho)
    (hrho : 0 < rho) (hrhoOne : rho ≤ 1)
    (q : {q // q ∈ S.activeCoarse})
    (selected : Finset {i // i ∈ S.fiber q.1}) :
    factorRadiusProduct
        (badParentSuccessorFactorList
          D left right S hrho hrhoOne q selected) =
      (3 / 64 : NNReal) *
        factorRadiusProduct (badParentSourceFactorList D left right S) := by
  simp only [badParentSuccessorFactorList, badParentSourceFactorList,
    factorRadiusProduct_append, factorRadiusProduct_cons,
    badParentActiveFineSourceAtom_radius, badParentCoarseAtom_radius,
    badParentFreshChildAtom_radius]
  rw [← mul_assoc rho (badParentFreshChildRadius delta rho)
    (factorRadiusProduct right)]
  rw [rho_mul_badParentFreshChildRadius_eq hrho]
  ac_rfl

/-- The forward half of the honest count-product comparison survives in an
arbitrary surrounding factor list. -/
theorem badParentSuccessorFactorList_cardProduct_le
    (left right : List ActualFactorDatum)
    (S : StickyScaleCover D.family rho)
    (hrho : 0 < rho) (hrhoOne : rho ≤ 1)
    (q : {q // q ∈ S.activeCoarse})
    (selected : Finset {i // i ∈ S.fiber q.1})
    (lower C : ENNReal)
    (P : BadParentFreshFactorProductCertificate
      S hrho hrhoOne q selected lower C) :
    factorCardProduct
        (badParentSuccessorFactorList
          D left right S hrho hrhoOne q selected) ≤
      C * factorCardProduct
        (badParentSourceFactorList D left right S) := by
  simp only [badParentSuccessorFactorList, badParentSourceFactorList,
    factorCardProduct_append, factorCardProduct_cons,
    badParentActiveFineSourceAtom_card, badParentCoarseAtom_card,
    badParentFreshChildAtom_card]
  calc
    factorCardProduct left *
          ((S.activeCoarse.card : ENNReal) *
            ((selected.card : ENNReal) * factorCardProduct right)) =
        factorCardProduct left *
          (((S.activeCoarse.card * selected.card : Nat) : ENNReal)) *
            factorCardProduct right := by
      rw [Nat.cast_mul]
      ac_rfl
    _ ≤ factorCardProduct left *
          (C * (S.activeFine.card : ENNReal)) *
            factorCardProduct right := by
      gcongr
      exact P.coarse_mul_child_le
    _ = C *
        (factorCardProduct left *
          ((S.activeFine.card : ENNReal) * factorCardProduct right)) := by
      ac_rfl

/-- The reverse half of the honest count-product comparison survives in an
arbitrary surrounding factor list with exactly the explicit uniformity and
fresh-retention loss. -/
theorem badParentSourceFactorList_cardProduct_le
    (left right : List ActualFactorDatum)
    (S : StickyScaleCover D.family rho)
    (hrho : 0 < rho) (hrhoOne : rho ≤ 1)
    (q : {q // q ∈ S.activeCoarse})
    (selected : Finset {i // i ∈ S.fiber q.1})
    (lower C : ENNReal)
    (P : BadParentFreshFactorProductCertificate
      S hrho hrhoOne q selected lower C) :
    factorCardProduct (badParentSourceFactorList D left right S) ≤
      (C * badParentFreshRetentionLoss
          S hrho hrhoOne q selected lower) *
        factorCardProduct
          (badParentSuccessorFactorList
            D left right S hrho hrhoOne q selected) := by
  simp only [badParentSuccessorFactorList, badParentSourceFactorList,
    factorCardProduct_append, factorCardProduct_cons,
    badParentActiveFineSourceAtom_card, badParentCoarseAtom_card,
    badParentFreshChildAtom_card]
  calc
    factorCardProduct left *
          ((S.activeFine.card : ENNReal) * factorCardProduct right) =
        factorCardProduct left * (S.activeFine.card : ENNReal) *
          factorCardProduct right := by
      ac_rfl
    _ ≤ factorCardProduct left *
          ((C * badParentFreshRetentionLoss
              S hrho hrhoOne q selected lower) *
            (((S.activeCoarse.card * selected.card : Nat) : ENNReal))) *
          factorCardProduct right := by
      gcongr
      exact P.source_le_loss_mul_coarse_mul_child
    _ = (C * badParentFreshRetentionLoss
          S hrho hrhoOne q selected lower) *
        (factorCardProduct left *
          ((S.activeCoarse.card : ENNReal) *
            ((selected.card : ENNReal) * factorCardProduct right))) := by
      rw [Nat.cast_mul]
      ac_rfl

#print axioms ActualFactorDatum.ofDatum
#print axioms badParentSuccessorFactorList_radiusProduct
#print axioms badParentSuccessorFactorList_cardProduct_le
#print axioms badParentSourceFactorList_cardProduct_le

end
end Family8ParentwiseBadParentActualFactorListSuccessorV1
