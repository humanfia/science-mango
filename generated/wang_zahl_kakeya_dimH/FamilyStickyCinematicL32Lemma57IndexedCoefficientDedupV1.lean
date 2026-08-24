import FamilyStickyCinematicL32Lemma57EssentiallyDistinctCoefficientFiberV1

set_option autoImplicit false

open Set

namespace FamilyStickyCinematicL32Lemma57IndexedCoefficientDedupV1

open Submission.Kakeya.ConvexGeometry
open Submission.Kakeya.Uniformity
open Family4GlobalExtremalUpstream
open FamilyStickyCinematicL32Lemma57EssentiallyDistinctTubeImageV1
open FamilyStickyCinematicL32Lemma57EssentiallyDistinctCoefficientFiberV1
open FamilyStickyCinematicL32Lemma57TubeCoefficientDedupV1

noncomputable section

/-!
# Indexed project-family coefficient deduplication

This composes the lossless essentially-distinct index-to-Tube image with the
maximal coefficient-separated selection.  A cap stated on the actual active
index fibre now gives cardinal retention and a three-member selected family
directly in the concrete Tube representation.
-/

/-- An indexed local coefficient cap gives exact active-card retention by
the concrete maximal separated Tube selection. -/
theorem active_card_le_multiplicity_mul_selectedTubes_card
    {delta : NNReal} {iota : Type*} [DecidableEq iota]
    (fine : UniformTubeFamily delta iota) (active : Finset iota)
    (hdelta : 0 < delta)
    (hpair : Set.Pairwise (active : Set iota) fun i j =>
      EssentiallyDistinct (fine.tubes i) (fine.tubes j))
    (multiplicity : Nat)
    (hactiveCap : forall center,
      center ∈ selectedTubes (activeTubeImage fine active) (delta : Real) ->
      (activeNearCoefficientIndices fine active center
        (delta : Real)).card <= multiplicity) :
    active.card <= multiplicity *
      (selectedTubes (activeTubeImage fine active)
        (delta : Real)).card := by
  have hdeltaReal : 0 < (delta : Real) := by
    exact_mod_cast hdelta
  have hconcreteCap :=
    concrete_nearCap_of_activeNearCoefficientIndices_cap
      fine active hdelta hpair (delta : Real) multiplicity hactiveCap
  have hretention :=
    family_card_le_mul_selectedTubes_card_of_near_cap
      (activeTubeImage fine active) hdeltaReal multiplicity hconcreteCap
  rw [activeTubeImage_card fine active hdelta hpair] at hretention
  exact hretention

/-- If the active project family has at least `3*multiplicity` members, the
concrete selected family contains at least three coefficient-separated
tubes. -/
theorem three_le_selectedTubes_card_of_active_cap
    {delta : NNReal} {iota : Type*} [DecidableEq iota]
    (fine : UniformTubeFamily delta iota) (active : Finset iota)
    (hdelta : 0 < delta)
    (hpair : Set.Pairwise (active : Set iota) fun i j =>
      EssentiallyDistinct (fine.tubes i) (fine.tubes j))
    {multiplicity : Nat} (hmultiplicity : 0 < multiplicity)
    (hlarge : 3 * multiplicity <= active.card)
    (hactiveCap : forall center,
      center ∈ selectedTubes (activeTubeImage fine active) (delta : Real) ->
      (activeNearCoefficientIndices fine active center
        (delta : Real)).card <= multiplicity) :
    3 <= (selectedTubes (activeTubeImage fine active)
      (delta : Real)).card := by
  have hdeltaReal : 0 < (delta : Real) := by
    exact_mod_cast hdelta
  have hconcreteCap :=
    concrete_nearCap_of_activeNearCoefficientIndices_cap
      fine active hdelta hpair (delta : Real) multiplicity hactiveCap
  apply three_le_selectedTubes_card_of_near_cap
    (activeTubeImage fine active) hdeltaReal hmultiplicity
  · rw [activeTubeImage_card fine active hdelta hpair]
    exact hlarge
  · exact hconcreteCap

/-- The selected concrete family is nonempty under the same indexed data. -/
theorem selectedTubes_nonempty_of_active_cap
    {delta : NNReal} {iota : Type*} [DecidableEq iota]
    (fine : UniformTubeFamily delta iota) (active : Finset iota)
    (hdelta : 0 < delta)
    (hpair : Set.Pairwise (active : Set iota) fun i j =>
      EssentiallyDistinct (fine.tubes i) (fine.tubes j))
    {multiplicity : Nat} (hmultiplicity : 0 < multiplicity)
    (hlarge : 3 * multiplicity <= active.card)
    (hactiveCap : forall center,
      center ∈ selectedTubes (activeTubeImage fine active) (delta : Real) ->
      (activeNearCoefficientIndices fine active center
        (delta : Real)).card <= multiplicity) :
    (selectedTubes (activeTubeImage fine active)
      (delta : Real)).Nonempty := by
  apply Finset.card_pos.mp
  exact lt_of_lt_of_le (by decide)
    (three_le_selectedTubes_card_of_active_cap fine active hdelta hpair
      hmultiplicity hlarge hactiveCap)

#print axioms active_card_le_multiplicity_mul_selectedTubes_card
#print axioms three_le_selectedTubes_card_of_active_cap
#print axioms selectedTubes_nonempty_of_active_cap

end


end FamilyStickyCinematicL32Lemma57IndexedCoefficientDedupV1
