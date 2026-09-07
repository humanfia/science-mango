import Family8Grounding.Family8PaperEq45SelectedOccurrenceBundleV3
import Mathlib.Tactic

/-!
# Conclusion-free structural core for selected-occurrence Equation (45)

This record contains every non-owner input of the paper-facing V3 bundle.
It deliberately contains neither a thick-count conclusion nor a unique-owner
field, so an actual geometric owner producer can be connected downstream.
-/

open Set MeasureTheory
open scoped BigOperators ENNReal NNReal

namespace Family8SelectedOccurrenceEq45CoreV2

open LeanEval.Analysis.WangZahlKakeya
open Submission.Kakeya.ConvexGeometry
open Submission.Kakeya.ConvexFactoring
open Submission.Kakeya.ConvexFactoring.FullConvexMaximalDensity
open Submission.Kakeya.ConvexFactoring.GreedyOccurrenceFactorization
open Submission.Kakeya.ConvexFactoring.GreedyDensityBucketing
open Family6AffinePlankAnalyticHypothesesStableV1
open Family8PaperEq45SelectedOccurrenceBundleV2
open Family8PaperEq45SelectedOccurrenceBundleV3
open Family8SelectedOccurrenceDensityFrostmanV1

noncomputable section

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 3000000

local instance (p : Prop) : Decidable p := Classical.propDecidable p

variable {iota kappa : Type*} [Fintype iota] [DecidableEq iota]
  {F : ConvexFamily iota} {candidates : Finset kappa}
  {container : kappa → ConvexBody Space} {active : Finset iota}

/-- Every Eq. (45) input except its owner and local-concentration data. -/
structure PaperEq45SelectedOccurrenceCore
    (P : GreedyDensityPartition F candidates container active)
    (Y : Shading F) (S : Finset (Fin (blocks F P).length))
    (a b : NNReal) where
  comparisonConstant : NNReal
  all_isPlank : ∀ q,
    IsPlank comparisonConstant a b (selectedOccurrenceOuterFamily P S q)
  ambient : ConvexBody Space
  ambientComparisonConstant : NNReal
  ambient_is_unit_scale : IsPlank ambientComparisonConstant 1 1 ambient
  contained_in_ambient : ∀ q,
    (selectedOccurrenceOuterFamily P S q : Set Space) ⊆ (ambient : Set Space)
  fiberCard_dyadicUniform : ∀ k ∈ S, ∀ l ∈ S,
    (((blockAt F P k).fiber.card : Nat) : ENNReal) ≤
      2 * (((blockAt F P l).fiber.card : Nat) : ENNReal)
  sourceCF : ENNReal
  lowerDensity : ENNReal
  upperDensity : ENNReal
  lowerDensity_ne_zero : lowerDensity ≠ 0
  lowerDensity_ne_top : lowerDensity ≠ ∞
  source_fine_frostman :
    IsFrostmanOn sourceCF F (selectedOccurrenceFineIndices P S) ambient
  blockMass_lower : ∀ k ∈ S,
    lowerDensity * volume ((blockAt F P k).body : Set Space) ≤
      blockMass F (blockAt F P k)
  blockMass_upper : ∀ k ∈ S,
    blockMass F (blockAt F P k) ≤
      upperDensity * volume ((blockAt F P k).body : Set Space)

namespace PaperEq45SelectedOccurrenceCore

variable {P : GreedyDensityPartition F candidates container active}
  {Y : Shading F} {S : Finset (Fin (blocks F P).length)}
  {a b : NNReal}

/-- The exact selected datum associated to the conclusion-free core. -/
abbrev datum (K : PaperEq45SelectedOccurrenceCore P Y S a b) :
    ShadedConvexPlankFamily
      {q // q ∈ selectedOccurrenceIndices P S} a b :=
  selectedOccurrenceOuterPlankDatum P Y S a b K.comparisonConstant
    K.all_isPlank K.ambient K.ambientComparisonConstant
    K.ambient_is_unit_scale K.contained_in_ambient

@[simp] theorem datum_family
    (K : PaperEq45SelectedOccurrenceCore P Y S a b) :
    K.datum.family = selectedOccurrenceOuterFamily P S := rfl

end PaperEq45SelectedOccurrenceCore

#print axioms PaperEq45SelectedOccurrenceCore.datum_family

end


end Family8SelectedOccurrenceEq45CoreV2
