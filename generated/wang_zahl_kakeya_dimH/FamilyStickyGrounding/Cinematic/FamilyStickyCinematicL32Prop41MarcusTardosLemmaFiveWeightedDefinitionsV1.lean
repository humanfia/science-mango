import FamilyStickyGrounding.Cinematic.FamilyStickyCinematicL32Prop41MarcusTardosLemmaTwoSumAlgebraV1
import Mathlib.Data.Fintype.Sigma

set_option autoImplicit false

open scoped BigOperators

namespace FamilyStickyCinematicL32Prop41MarcusTardosLemmaFiveWeightedDefinitionsV1

open FamilyStickyCinematicL32Prop41MarcusTardosLemmaTwoSumAlgebraV1

/-! # Weighted quantities in Marcus--Tardos Lemma 5 -/

noncomputable def totalWeightedQ
    {level : Type*} [Fintype level]
    {pair : level → Type*} [∀ l, Fintype (pair l)]
    (weight : level → Real) (q : ∀ l, pair l → Real) : Real :=
  ∑ l, weight l * ∑ p, q l p

noncomputable def totalWeightedRegularSquare
    {level : Type*} [Fintype level]
    {pair : level → Type*} [∀ l, Fintype (pair l)]
    (weight : level → Real) (mass : ∀ l, pair l → Real)
    (singular : ∀ l, pair l → Prop) : Real :=
  ∑ l, weight l * regularSquareMass (singular l) (mass l)

noncomputable def leaderWeightedSquare
    {level : Type*} {pair : level → Type*}
    (leaders : Finset (Sigma pair))
    (weight : level → Real) (mass : ∀ l, pair l → Real) : Real :=
  ∑ x ∈ leaders, weight x.1 * (mass x.1 x.2) ^ 2

noncomputable def leaderMass
    {level : Type*} {pair : level → Type*}
    (leaders : Finset (Sigma pair))
    (mass : ∀ l, pair l → Real) : Real :=
  ∑ x ∈ leaders, mass x.1 x.2

#print axioms totalWeightedQ
#print axioms totalWeightedRegularSquare
#print axioms leaderWeightedSquare
#print axioms leaderMass

end FamilyStickyCinematicL32Prop41MarcusTardosLemmaFiveWeightedDefinitionsV1
