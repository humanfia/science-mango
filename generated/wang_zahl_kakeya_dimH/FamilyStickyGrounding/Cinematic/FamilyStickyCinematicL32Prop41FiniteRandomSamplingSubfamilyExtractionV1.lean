import FamilyStickyGrounding.Cinematic.FamilyStickyCinematicL32Prop41FiniteRandomSamplingExtractionV1
import Mathlib.Tactic

set_option autoImplicit false
set_option warningAsError true

namespace FamilyStickyCinematicL32Prop41FiniteRandomSamplingSubfamilyExtractionV1

open FamilyStickyCinematicL32Prop41FiniteRandomSamplingExtractionV1

noncomputable section

/-!
# Sampling inside finite ambient curve subfamilies

This module transports the explicit two-colouring extraction from finite
types to literal finite ambient curve families.  A local neighbour finset is
viewed as a finset of the ambient subtype without changing its cardinality.
-/

/-- A literal subfamily, retyped as elements of a finite ambient family. -/
def ambientSubtypeRestriction
    {alpha : Type*} [DecidableEq alpha]
    (ambient subsetFamily : Finset alpha) : Finset ambient :=
  ambient.attach.filter fun a => (a : alpha) ∈ subsetFamily

@[simp]
theorem mem_ambientSubtypeRestriction_iff
    {alpha : Type*} [DecidableEq alpha]
    (ambient subsetFamily : Finset alpha) (a : ambient) :
    a ∈ ambientSubtypeRestriction ambient subsetFamily ↔
      (a : alpha) ∈ subsetFamily := by
  simp [ambientSubtypeRestriction]

/-- Retyping a genuine subfamily into the ambient subtype loses no elements. -/
theorem ambientSubtypeRestriction_card_eq
    {alpha : Type*} [DecidableEq alpha]
    (ambient subsetFamily : Finset alpha)
    (hsub : subsetFamily ⊆ ambient) :
    (ambientSubtypeRestriction ambient subsetFamily).card =
      subsetFamily.card := by
  have hfilter :
      ambient.filter (fun a => a ∈ subsetFamily) = subsetFamily := by
    ext a
    constructor
    · intro ha
      exact (Finset.mem_filter.mp ha).2
    · intro ha
      exact Finset.mem_filter.mpr ⟨hsub ha, ha⟩
  unfold ambientSubtypeRestriction
  rw [Finset.filter_attach (fun a : alpha => a ∈ subsetFamily) ambient]
  simp only [Finset.card_map, Finset.card_attach]
  rw [hfilter]

/-- The paper-ready finite-subfamily form of the random sampling endpoint.

Each rectangle has literal left and right neighbour finsets contained in the
corresponding finite ambient family.  If their sizes are at least `mu` and
`nu`, one pair of independent colourings retains at least one eighth of all
rectangles while selecting at most seven times
`|leftAmbient| / mu + |rightAmbient| / nu` curves. -/
theorem exists_ambientSubfamily_sample_with_eighth_survival_and_sevenfold_load
    {Rectangle alpha beta : Type*}
    [Fintype Rectangle] [DecidableEq Rectangle]
    [DecidableEq alpha] [DecidableEq beta]
    (leftAmbient : Finset alpha) (rightAmbient : Finset beta)
    (mu nu : Nat) [NeZero mu] [NeZero nu]
    (leftNeighbors : Rectangle -> Finset alpha)
    (rightNeighbors : Rectangle -> Finset beta)
    (hleftSubset : forall R, leftNeighbors R ⊆ leftAmbient)
    (hrightSubset : forall R, rightNeighbors R ⊆ rightAmbient)
    (hleftCard : forall R, mu ≤ (leftNeighbors R).card)
    (hrightCard : forall R, nu ≤ (rightNeighbors R).card) :
    exists omega : (leftAmbient -> Fin mu) × (rightAmbient -> Fin nu),
      (Fintype.card Rectangle : Real) / 8 ≤
          ((twoSidedZeroColorSurvivors mu nu
            (fun R => ambientSubtypeRestriction leftAmbient (leftNeighbors R))
            (fun R => ambientSubtypeRestriction rightAmbient (rightNeighbors R))
            omega).card : Real) ∧
        twoSidedZeroColorLoad mu nu omega ≤
          7 * ((leftAmbient.card : Real) / (mu : Real) +
            (rightAmbient.card : Real) / (nu : Real)) := by
  have hleftRestricted : forall R,
      mu ≤ (ambientSubtypeRestriction leftAmbient (leftNeighbors R)).card := by
    intro R
    rw [ambientSubtypeRestriction_card_eq leftAmbient (leftNeighbors R)
      (hleftSubset R)]
    exact hleftCard R
  have hrightRestricted : forall R,
      nu ≤ (ambientSubtypeRestriction rightAmbient (rightNeighbors R)).card := by
    intro R
    rw [ambientSubtypeRestriction_card_eq rightAmbient (rightNeighbors R)
      (hrightSubset R)]
    exact hrightCard R
  simpa using
    (exists_twoSidedZeroColor_sample_with_eighth_survival_and_sevenfold_load
      (Rectangle := Rectangle) (alpha := leftAmbient) (beta := rightAmbient)
      mu nu
      (fun R => ambientSubtypeRestriction leftAmbient (leftNeighbors R))
      (fun R => ambientSubtypeRestriction rightAmbient (rightNeighbors R))
      hleftRestricted hrightRestricted)

#print axioms ambientSubtypeRestriction_card_eq
#print axioms exists_ambientSubfamily_sample_with_eighth_survival_and_sevenfold_load

end

end FamilyStickyCinematicL32Prop41FiniteRandomSamplingSubfamilyExtractionV1
