import Mathlib.Data.Sym.Card

set_option autoImplicit false

namespace FamilyStickyCinematicL32Prop41FirstGenerationLensCarrierV1

noncomputable section

/-!
# PYZ Proposition 4.1: finite first-generation lens carrier

For a finite curve family, a first-generation lens is encoded either by a
whole curve, or by one of four nontrivial lens choices attached to an
unordered pair of distinct curves.  This is exactly the finite carrier used
in the paragraph preceding PYZ Definition 4.5: the other two of the six
lenses associated to a pair are the two whole curves, which are recorded
only once globally.

No lens-counting estimate, rectangle bound, topology, or geometric
non-overlap conclusion is assumed here.
-/

/-- The curves actually present in a finite family. -/
abbrev FirstGenerationCurve {curve : Type*} [DecidableEq curve]
    (curves : Finset curve) := {c // c ∈ curves}

/-- An unordered pair of distinct curves from the finite family. -/
abbrev FirstGenerationCurvePair {curve : Type*} [DecidableEq curve]
    (curves : Finset curve) :=
  {p : Sym2 (FirstGenerationCurve curves) // ¬ p.IsDiag}

/-- The honest finite code space for first-generation lenses: one code for
each whole curve and four codes for each unordered distinct curve pair. -/
abbrev FirstGenerationLensCode {curve : Type*} [DecidableEq curve]
    (curves : Finset curve) :=
  Sum (FirstGenerationCurve curves) (FirstGenerationCurvePair curves × Fin 4)

/-- The first-generation carrier has exactly
`#curves + 4 * choose (#curves) 2` codes. -/
theorem card_firstGenerationLensCode
    {curve : Type*} [DecidableEq curve] (curves : Finset curve) :
    Fintype.card (FirstGenerationLensCode curves) =
      curves.card + 4 * Nat.choose curves.card 2 := by
  simp only [FirstGenerationLensCode, FirstGenerationCurvePair,
    FirstGenerationCurve, Fintype.card_sum, Fintype.card_coe,
    Fintype.card_prod, Sym2.card_subtype_not_diag, Fintype.card_fin]
  omega

/-- Any finite family honestly embedded into the first-generation carrier
obeys the same exact cardinality upper bound. -/
theorem card_le_firstGenerationLensCode_of_embedding
    {curve lens : Type*} [DecidableEq curve] [Fintype lens]
    (curves : Finset curve)
    (encode : lens ↪ FirstGenerationLensCode curves) :
    Fintype.card lens <= curves.card + 4 * Nat.choose curves.card 2 := by
  rw [← card_firstGenerationLensCode curves]
  exact Fintype.card_le_of_injective encode encode.injective

#print axioms card_firstGenerationLensCode
#print axioms card_le_firstGenerationLensCode_of_embedding

end


end FamilyStickyCinematicL32Prop41FirstGenerationLensCarrierV1
