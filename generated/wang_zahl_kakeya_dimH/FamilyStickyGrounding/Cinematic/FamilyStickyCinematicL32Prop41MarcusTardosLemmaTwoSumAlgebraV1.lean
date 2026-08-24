import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Tactic

set_option autoImplicit false

open scoped BigOperators

namespace FamilyStickyCinematicL32Prop41MarcusTardosLemmaTwoSumAlgebraV1

/-!
# Summing the singular/regular `Q_st` alternatives

This is the exact subtraction-free algebra in Marcus--Tardos Lemma 2.  It
does not assume the geometric/block classification which supplies the two
pointwise hypotheses.
-/

noncomputable def regularSquareMass
    {ι : Type*} [Fintype ι]
    (singular : ι → Prop) (length : ι → Real) : Real := by
  classical
  exact ∑ i, if singular i then 0 else (length i) ^ 2

theorem sum_q_add_regularSquareMass_le_sum_length
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (q length : ι → Real) (singular : ι → Prop)
    (hsingular : ∀ i, singular i → q i ≤ length i)
    (hregular : ∀ i, ¬singular i →
      q i = length i - (length i) ^ 2) :
    (∑ i, q i) + regularSquareMass singular length ≤
      ∑ i, length i := by
  classical
  simp only [regularSquareMass, ← Finset.sum_add_distrib]
  apply Finset.sum_le_sum
  intro i hi
  by_cases hs : singular i
  · simpa [hs] using hsingular i hs
  · rw [hregular i hs]
    simp [hs]

theorem sum_q_le_sum_length
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (q length : ι → Real) (singular : ι → Prop)
    (hsingular : ∀ i, singular i → q i ≤ length i)
    (hregular : ∀ i, ¬singular i →
      q i = length i - (length i) ^ 2) :
    ∑ i, q i ≤ ∑ i, length i := by
  have hfull := sum_q_add_regularSquareMass_le_sum_length
    q length singular hsingular hregular
  exact le_trans (le_add_of_nonneg_right <|
    Finset.sum_nonneg fun i _ => by
      classical
      split <;> positivity) hfull

#print axioms regularSquareMass
#print axioms sum_q_add_regularSquareMass_le_sum_length
#print axioms sum_q_le_sum_length

end FamilyStickyCinematicL32Prop41MarcusTardosLemmaTwoSumAlgebraV1
