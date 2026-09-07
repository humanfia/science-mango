import Family8Grounding.Family8ParentwiseBadParentMassAwareFactorListStateV2
import Mathlib.Tactic

/-!
# Exact finite ledger for repeated bad-parent successors

`ParentwiseBadParentMassAwareFactorListState` proves the three honest
one-step product statements:

* source radius product is `(64 / 3)` times successor radius product;
* successor cardinality product is at most `C` times source cardinality;
* source cardinality product is at most `C * L` times successor
  cardinality, where `L` is the literal fresh-retention loss.

This file forgets none of those scalar losses and composes a supplied finite
chain of such steps.  The chain is indexed by its literal source and final
factor lists, so adjacent factors must agree definitionally.  Its `steps`
field is an ordinary `List`; the cumulative theorems display the exact list
products of all `C` and `C * L` factors.

Finiteness of the ledger is an explicit input.  No theorem here constructs
a terminating recursion, and no `hSmall` or stopping assumption is stored
or discharged implicitly.  A later orchestration layer must supply those
hypotheses when it constructs this finite ledger.
-/

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 4000000

open scoped BigOperators ENNReal NNReal

namespace Family8ParentwiseBadParentRepeatedSuccessorLedgerV1

open LeanEval.Analysis.WangZahlKakeya
open Submission.Kakeya.ConvexFactoring
open Submission.Kakeya.Uniformity
open Family8KatzTaoFrostmanPropertiesV1
open Family8ParentwiseBadParentActualFactorListSuccessorV1
open Family8ParentwiseBadParentFactorProductV1
open Family8ParentwiseBadParentMassAwareFactorListStateV2
open Family8ParentwiseBadParentMassAwareFactorListStateV2.ParentwiseBadParentMassAwareFactorListState
open Family8StickySelectedFiberLowCFFreshRetentionProducerV2
open FamilyStickyAtEveryScaleCoreV1

noncomputable section

/-! ## The scalar certificate exported by one genuine StateV2 step -/

/-- The product data needed to iterate one bad-parent successor.  Both
factor lists remain literal; the two count losses are stored separately. -/
structure BadParentProductStep where
  sourceFactors : List ActualFactorDatum
  successorFactors : List ActualFactorDatum
  uniformityLoss : ENNReal
  freshRetentionLoss : ENNReal
  source_radiusProduct_eq_fixedLoss_mul :
    factorRadiusProduct sourceFactors =
      (64 / 3 : NNReal) * factorRadiusProduct successorFactors
  successor_cardProduct_le :
    factorCardProduct successorFactors <=
      uniformityLoss * factorCardProduct sourceFactors
  source_cardProduct_le :
    factorCardProduct sourceFactors <=
      (uniformityLoss * freshRetentionLoss) *
        factorCardProduct successorFactors

namespace BadParentProductStep

/-- Export the exact scalar ledger from one concrete mass-aware StateV2
successor.  This is a projection, not a replacement callback. -/
def ofState
    {delta rho : NNReal} {iota : Type}
    [Fintype iota] [DecidableEq iota]
    {D : ActualTubeDatum delta iota}
    {S : StickyScaleCover D.family rho}
    {left right : List ActualFactorDatum}
    {hrho : 0 < rho} {hrhoOne : rho <= 1}
    {q : {q // q ∈ S.activeCoarse}}
    {lower C : ENNReal}
    (X : ParentwiseBadParentMassAwareFactorListState
      D S left right hrho hrhoOne q lower C) :
    BadParentProductStep where
  sourceFactors := X.sourceFactors
  successorFactors := X.successorFactors
  uniformityLoss := C
  freshRetentionLoss :=
    badParentFreshRetentionLoss
      S hrho hrhoOne q X.base.selected lower
  source_radiusProduct_eq_fixedLoss_mul :=
    X.source_radiusProduct_eq_fixedLoss_mul
  successor_cardProduct_le := X.successor_cardProduct_le
  source_cardProduct_le := X.source_cardProduct_le

end BadParentProductStep

/-! ## A definitionally composable finite chain -/

/-- A finite chain of literal product steps.  `cons step tail` is legal only
when the tail starts at `step.successorFactors`, so no equality transport is
hidden between consecutive replacements. -/
inductive RepeatedBadParentLedger :
    List ActualFactorDatum -> List ActualFactorDatum -> Type 2
  | nil (factors : List ActualFactorDatum) :
      RepeatedBadParentLedger factors factors
  | cons {finalFactors : List ActualFactorDatum}
      (step : BadParentProductStep)
      (tail : RepeatedBadParentLedger
        step.successorFactors finalFactors) :
      RepeatedBadParentLedger step.sourceFactors finalFactors

namespace RepeatedBadParentLedger

/-- The ordinary list of one-step scalar certificates. -/
def steps {sourceFactors finalFactors : List ActualFactorDatum} :
    RepeatedBadParentLedger sourceFactors finalFactors ->
      List BadParentProductStep
  | .nil _ => []
  | .cons step tail => step :: tail.steps

/-- Literal number of performed bad-parent replacements. -/
def stepCount {sourceFactors finalFactors : List ActualFactorDatum} :
    RepeatedBadParentLedger sourceFactors finalFactors -> Nat
  | .nil _ => 0
  | .cons _ tail => tail.stepCount + 1

/-- Product of the forward count losses `C_j`. -/
def forwardCardLoss {sourceFactors finalFactors : List ActualFactorDatum} :
    RepeatedBadParentLedger sourceFactors finalFactors -> ENNReal
  | .nil _ => 1
  | .cons step tail => step.uniformityLoss * tail.forwardCardLoss

/-- Product of the reverse count losses `C_j * L_j`. -/
def reverseCardLoss {sourceFactors finalFactors : List ActualFactorDatum} :
    RepeatedBadParentLedger sourceFactors finalFactors -> ENNReal
  | .nil _ => 1
  | .cons step tail =>
      (step.uniformityLoss * step.freshRetentionLoss) *
        tail.reverseCardLoss

@[simp] theorem stepCount_eq_steps_length
    {sourceFactors finalFactors : List ActualFactorDatum}
    (ledger : RepeatedBadParentLedger sourceFactors finalFactors) :
    ledger.stepCount = ledger.steps.length := by
  induction ledger with
  | nil factors => rfl
  | cons step tail ih =>
      simp only [stepCount, steps, List.length_cons, ih]

/-- The recursive forward loss is definitionally the ordinary list product
of the displayed `C_j` factors. -/
theorem forwardCardLoss_eq_list_prod
    {sourceFactors finalFactors : List ActualFactorDatum}
    (ledger : RepeatedBadParentLedger sourceFactors finalFactors) :
    ledger.forwardCardLoss =
      (ledger.steps.map (fun step => step.uniformityLoss)).prod := by
  induction ledger with
  | nil factors => rfl
  | cons step tail ih =>
      simp only [forwardCardLoss, steps, List.map_cons, List.prod_cons, ih]

/-- The recursive reverse loss is exactly the ordinary list product of all
honest one-step factors `C_j * L_j`. -/
theorem reverseCardLoss_eq_list_prod
    {sourceFactors finalFactors : List ActualFactorDatum}
    (ledger : RepeatedBadParentLedger sourceFactors finalFactors) :
    ledger.reverseCardLoss =
      (ledger.steps.map (fun step =>
        step.uniformityLoss * step.freshRetentionLoss)).prod := by
  induction ledger with
  | nil factors => rfl
  | cons step tail ih =>
      simp only [reverseCardLoss, steps, List.map_cons, List.prod_cons, ih]

/-! ## Exact accumulated radius and count products -/

/-- After `stepCount` replacements, the initial radius product is exactly
`(64 / 3)^stepCount` times the final radius product. -/
theorem source_radiusProduct_eq_fixedLoss_pow_mul :
    forall {sourceFactors finalFactors : List ActualFactorDatum}
      (ledger : RepeatedBadParentLedger sourceFactors finalFactors),
      factorRadiusProduct sourceFactors =
        (64 / 3 : NNReal) ^ ledger.stepCount *
          factorRadiusProduct finalFactors
  | _, _, .nil factors => by
      simp only [stepCount, pow_zero, one_mul]
  | _, finalFactors, .cons step tail => by
      calc
        factorRadiusProduct step.sourceFactors =
            (64 / 3 : NNReal) *
              factorRadiusProduct step.successorFactors :=
          step.source_radiusProduct_eq_fixedLoss_mul
        _ = (64 / 3 : NNReal) *
              ((64 / 3 : NNReal) ^ tail.stepCount *
                factorRadiusProduct finalFactors) := by
          rw [source_radiusProduct_eq_fixedLoss_pow_mul tail]
        _ = (64 / 3 : NNReal) ^ (tail.stepCount + 1) *
              factorRadiusProduct finalFactors := by
          rw [pow_succ]
          ac_rfl

/-- The same exact radius theorem with the exponent displayed as the length
of the ordinary step list. -/
theorem source_radiusProduct_eq_fixedLoss_pow_length_mul
    {sourceFactors finalFactors : List ActualFactorDatum}
    (ledger : RepeatedBadParentLedger sourceFactors finalFactors) :
    factorRadiusProduct sourceFactors =
      (64 / 3 : NNReal) ^ ledger.steps.length *
        factorRadiusProduct finalFactors := by
  rw [← ledger.stepCount_eq_steps_length]
  exact ledger.source_radiusProduct_eq_fixedLoss_pow_mul

/-- Iterating the forward count inequality multiplies precisely the `C_j`
losses and nothing else. -/
theorem final_cardProduct_le_forwardCardLoss_mul_source :
    forall {sourceFactors finalFactors : List ActualFactorDatum}
      (ledger : RepeatedBadParentLedger sourceFactors finalFactors),
      factorCardProduct finalFactors <=
        ledger.forwardCardLoss * factorCardProduct sourceFactors
  | _, _, .nil factors => by
      simpa only [forwardCardLoss, one_mul] using
        (le_refl (factorCardProduct factors))
  | _, finalFactors, .cons step tail => by
      calc
        factorCardProduct finalFactors <=
            tail.forwardCardLoss *
              factorCardProduct step.successorFactors :=
          final_cardProduct_le_forwardCardLoss_mul_source tail
        _ <= tail.forwardCardLoss *
              (step.uniformityLoss *
                factorCardProduct step.sourceFactors) := by
          gcongr
          exact step.successor_cardProduct_le
        _ = (step.uniformityLoss * tail.forwardCardLoss) *
              factorCardProduct step.sourceFactors := by ac_rfl

/-- Iterating the reverse count inequality multiplies precisely the honest
one-step losses `C_j * L_j`. -/
theorem source_cardProduct_le_reverseCardLoss_mul_final :
    forall {sourceFactors finalFactors : List ActualFactorDatum}
      (ledger : RepeatedBadParentLedger sourceFactors finalFactors),
      factorCardProduct sourceFactors <=
        ledger.reverseCardLoss * factorCardProduct finalFactors
  | _, _, .nil factors => by
      simpa only [reverseCardLoss, one_mul] using
        (le_refl (factorCardProduct factors))
  | _, finalFactors, .cons step tail => by
      calc
        factorCardProduct step.sourceFactors <=
            (step.uniformityLoss * step.freshRetentionLoss) *
              factorCardProduct step.successorFactors :=
          step.source_cardProduct_le
        _ <= (step.uniformityLoss * step.freshRetentionLoss) *
              (tail.reverseCardLoss *
                factorCardProduct finalFactors) := by
          gcongr
          exact source_cardProduct_le_reverseCardLoss_mul_final tail
        _ = ((step.uniformityLoss * step.freshRetentionLoss) *
              tail.reverseCardLoss) *
                factorCardProduct finalFactors := by ac_rfl

/-- Forward count comparison with the cumulative loss written literally as
a `List.prod`. -/
theorem final_cardProduct_le_list_prod_mul_source
    {sourceFactors finalFactors : List ActualFactorDatum}
    (ledger : RepeatedBadParentLedger sourceFactors finalFactors) :
    factorCardProduct finalFactors <=
      (ledger.steps.map (fun step => step.uniformityLoss)).prod *
        factorCardProduct sourceFactors := by
  rw [← ledger.forwardCardLoss_eq_list_prod]
  exact ledger.final_cardProduct_le_forwardCardLoss_mul_source

/-- Reverse count comparison with the requested cumulative
`prod_j (C_j * L_j)` displayed literally. -/
theorem source_cardProduct_le_list_prod_mul_final
    {sourceFactors finalFactors : List ActualFactorDatum}
    (ledger : RepeatedBadParentLedger sourceFactors finalFactors) :
    factorCardProduct sourceFactors <=
      (ledger.steps.map (fun step =>
        step.uniformityLoss * step.freshRetentionLoss)).prod *
          factorCardProduct finalFactors := by
  rw [← ledger.reverseCardLoss_eq_list_prod]
  exact ledger.source_cardProduct_le_reverseCardLoss_mul_final

/-- The three accumulated conclusions packaged for direct consumers. -/
theorem cumulative_exactProductCertificate
    {sourceFactors finalFactors : List ActualFactorDatum}
    (ledger : RepeatedBadParentLedger sourceFactors finalFactors) :
    factorRadiusProduct sourceFactors =
        (64 / 3 : NNReal) ^ ledger.steps.length *
          factorRadiusProduct finalFactors ∧
      factorCardProduct finalFactors <=
        (ledger.steps.map (fun step => step.uniformityLoss)).prod *
          factorCardProduct sourceFactors ∧
      factorCardProduct sourceFactors <=
        (ledger.steps.map (fun step =>
          step.uniformityLoss * step.freshRetentionLoss)).prod *
            factorCardProduct finalFactors := by
  exact ⟨
    ledger.source_radiusProduct_eq_fixedLoss_pow_length_mul,
    ledger.final_cardProduct_le_list_prod_mul_source,
    ledger.source_cardProduct_le_list_prod_mul_final⟩

end RepeatedBadParentLedger

#print axioms BadParentProductStep.ofState
#print axioms RepeatedBadParentLedger.stepCount_eq_steps_length
#print axioms RepeatedBadParentLedger.forwardCardLoss_eq_list_prod
#print axioms RepeatedBadParentLedger.reverseCardLoss_eq_list_prod
#print axioms
  RepeatedBadParentLedger.source_radiusProduct_eq_fixedLoss_pow_mul
#print axioms
  RepeatedBadParentLedger.source_radiusProduct_eq_fixedLoss_pow_length_mul
#print axioms
  RepeatedBadParentLedger.final_cardProduct_le_list_prod_mul_source
#print axioms
  RepeatedBadParentLedger.source_cardProduct_le_list_prod_mul_final
#print axioms RepeatedBadParentLedger.cumulative_exactProductCertificate

end
end Family8ParentwiseBadParentRepeatedSuccessorLedgerV1
