import FamilyStickyGrounding.Cinematic.FamilyStickyCinematicL32FiniteIntervalPackingV1
import Mathlib.Tactic.Linarith

set_option autoImplicit false

open Set MeasureTheory

namespace FamilyStickyCinematicL32FiniteSeparatedSlopePackingV1

open FamilyStickyCinematicL32FiniteIntervalPackingV1

noncomputable section

/-!
# Finite packing of separated slopes

This is the one-dimensional counting step in the proof of
Pramanik--Yang--Zahl, arXiv:2207.02259v3, Lemma 3.15.  At a fixed point,
pairwise incomparable cinematic rectangles have separated tangent slopes,
while containment in one enlarged rectangle places every slope in a common
bounded interval.  The present module proves the resulting finite packing;
the rectangle geometry producing those two hypotheses remains separate.
-/

/-- Points in `[a,b]` separated by at least `sep` pack into the enlarged
interval `(a,b+sep)`.  The denominator-free conclusion is suited to later
`ENNReal` measure estimates and does not require choosing an integer ceiling.
-/
theorem card_mul_sep_le_of_slopes_mem_Icc
    {index : Type*} (indices : Finset index) (slope : index -> Real)
    {a b sep : Real} (hsep : 0 <= sep)
    (hrange : forall i, i ∈ indices -> slope i ∈ Icc a b)
    (hseparated : forall i, i ∈ indices -> forall j, j ∈ indices ->
      i ≠ j -> sep <= |slope i - slope j|) :
    (indices.card : ENNReal) * ENNReal.ofReal sep <=
      ENNReal.ofReal ((b + sep) - a) := by
  have hdisjoint : Set.PairwiseDisjoint (indices : Set index)
      (fun i => Ioo (slope i) (slope i + sep)) := by
    intro i hi j hj hij
    change Disjoint (Ioo (slope i) (slope i + sep))
      (Ioo (slope j) (slope j + sep))
    rw [Set.disjoint_left]
    intro x hxi hxj
    have hforward : slope i - slope j < sep := by
      linarith [hxi.1, hxj.2]
    have hbackward : -(sep) < slope i - slope j := by
      linarith [hxj.1, hxi.2]
    have habs : |slope i - slope j| < sep := by
      rw [abs_lt]
      exact ⟨hbackward, hforward⟩
    exact (not_lt_of_ge (hseparated i hi j hj hij)) habs
  have hsubset : forall i, i ∈ indices ->
      Ioo (slope i) (slope i + sep) ⊆ Ioo a (b + sep) := by
    intro i hi x hx
    have hirange := hrange i hi
    constructor <;> linarith [hirange.1, hirange.2, hx.1, hx.2]
  have hpacking := card_mul_intervalLength_le_volume
    indices slope (fun i => slope i + sep) (Ioo a (b + sep))
    hsep (fun _i _hi => by linarith) hdisjoint hsubset
  simpa [Real.volume_Ioo] using hpacking

/-- Centered form of the same slope packing.  If all slopes lie within
`radius` of `center`, their total separated mass is at most
`2 * radius + sep`. -/
theorem card_mul_sep_le_of_slopes_near
    {index : Type*} (indices : Finset index) (slope : index -> Real)
    {center radius sep : Real} (hsep : 0 <= sep)
    (hrange : forall i, i ∈ indices -> |slope i - center| <= radius)
    (hseparated : forall i, i ∈ indices -> forall j, j ∈ indices ->
      i ≠ j -> sep <= |slope i - slope j|) :
    (indices.card : ENNReal) * ENNReal.ofReal sep <=
      ENNReal.ofReal (2 * radius + sep) := by
  have hIcc : forall i, i ∈ indices ->
      slope i ∈ Icc (center - radius) (center + radius) := by
    intro i hi
    have hirange := hrange i hi
    rw [abs_le] at hirange
    constructor <;> linarith
  have hpacking := card_mul_sep_le_of_slopes_mem_Icc
    indices slope hsep hIcc hseparated
  have heq : ((center + radius + sep) - (center - radius)) =
      2 * radius + sep := by
    ring
  simpa only [heq] using hpacking

#print axioms card_mul_sep_le_of_slopes_mem_Icc
#print axioms card_mul_sep_le_of_slopes_near

end

end FamilyStickyCinematicL32FiniteSeparatedSlopePackingV1
