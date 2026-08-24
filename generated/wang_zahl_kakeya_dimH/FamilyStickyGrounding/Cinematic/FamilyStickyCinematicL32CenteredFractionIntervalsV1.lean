import Mathlib.Data.Real.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

set_option autoImplicit false

open Set

namespace FamilyStickyCinematicL32CenteredFractionIntervalsV1
noncomputable section

/-!
# Centered fractional subintervals

Provenance: Pramanik--Yang--Zahl, arXiv:2207.02259v3,
Definition 3.7 and Lemma 5.3, where `J/2`, `J/4`, `J/8`, and `J/16`
denote concentric intervals with the indicated fraction of the length of
`J`.
-/

/-- Left endpoint of the concentric `q`-fraction of `[A,B]`. -/
def centeredFractionLeft (A B q : Real) : Real :=
  (A + B) / 2 - q * (B - A) / 2

/-- Right endpoint of the concentric `q`-fraction of `[A,B]`. -/
def centeredFractionRight (A B q : Real) : Real :=
  (A + B) / 2 + q * (B - A) / 2

/-- The concentric `q`-fraction of `[A,B]`. -/
def centeredFractionIcc (A B q : Real) : Set Real :=
  Icc (centeredFractionLeft A B q) (centeredFractionRight A B q)

/-- A point of `J/16` has a `3|J|/32` margin to each endpoint of `J/4`. -/
theorem mem_sixteenth_has_quarter_margin
    {A B x : Real} (hx : x ∈ centeredFractionIcc A B (1 / 16 : Real)) :
    3 * (B - A) / 32 <=
        x - centeredFractionLeft A B (1 / 4 : Real) ∧
      3 * (B - A) / 32 <=
        centeredFractionRight A B (1 / 4 : Real) - x := by
  rcases hx with ⟨hxLeft, hxRight⟩
  constructor <;>
    simp only [centeredFractionLeft, centeredFractionRight] at * <;>
    linarith

/-- A centered interval around a point of `J/16` lies in `J/8` whenever
its radius is at most `|J|/32`. -/
theorem centered_Icc_subset_eighth_of_mem_sixteenth
    {A B x radius : Real}
    (hx : x ∈ centeredFractionIcc A B (1 / 16 : Real))
    (hradius : radius <= (B - A) / 32) :
    Icc (x - radius) (x + radius) ⊆
      centeredFractionIcc A B (1 / 8 : Real) := by
  intro z hz
  rcases hx with ⟨hxLeft, hxRight⟩
  rcases hz with ⟨hzLeft, hzRight⟩
  constructor <;>
    simp only [centeredFractionLeft,
      centeredFractionRight] at * <;>
    linarith

/-- The `J/16` interval is contained in the interior of `J/4` when the
ambient interval has positive length. -/
theorem sixteenth_subset_Ioo_quarter
    {A B : Real} (hAB : A < B) :
    centeredFractionIcc A B (1 / 16 : Real) ⊆
      Ioo (centeredFractionLeft A B (1 / 4 : Real))
        (centeredFractionRight A B (1 / 4 : Real)) := by
  intro x hx
  have hmargins := mem_sixteenth_has_quarter_margin hx
  have hpositive : 0 < 3 * (B - A) / 32 := by positivity
  constructor
  · linarith [hmargins.1]
  · linarith [hmargins.2]

#print axioms centeredFractionLeft
#print axioms centeredFractionRight
#print axioms centeredFractionIcc
#print axioms mem_sixteenth_has_quarter_margin
#print axioms centered_Icc_subset_eighth_of_mem_sixteenth
#print axioms sixteenth_subset_Ioo_quarter

end

end FamilyStickyCinematicL32CenteredFractionIntervalsV1
