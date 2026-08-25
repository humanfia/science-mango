import FamilyStickyGrounding.FamilyStickyRandomTwoFamilyChernoffV1

namespace FamilyStickyRandomTwoFamilyTailV1

noncomputable section

/-!
# Explicit completion of a two-family tail budget

Suppose the first family has already reserved one full unit of exponential
room, `x + 1 <= exp A`.  This is the exact stronger property enjoyed by the
GWZ source tail `max 1 (log (x + 1))`.  The tail below then pays for a second
finite family while retaining the original first-family threshold.
-/

/-- Fixed Chernoff chord cost used by both finite event families. -/
def chordCost : Real := Real.exp (Real.exp 1 - 1)

/-- Tail assigned to the second family after the first tail `A` is fixed. -/
def completionTail (secondCount : Nat) (A : Real) : Real :=
  max 1 (Real.log ((secondCount : Real) * chordCost * Real.exp A + 1))

theorem one_le_completionTail (secondCount : Nat) (A : Real) :
    1 <= completionTail secondCount A := le_max_left _ _

theorem second_cost_lt_exp_completionTail
    (secondCount : Nat) (A : Real) :
    (secondCount : Real) * chordCost * Real.exp A <
      Real.exp (completionTail secondCount A) := by
  let y : Real := (secondCount : Real) * chordCost * Real.exp A
  have hy : 0 <= y := by
    exact mul_nonneg
      (mul_nonneg (Nat.cast_nonneg _) (Real.exp_pos _).le)
      (Real.exp_pos _).le
  have hy1 : 0 < y + 1 := by linarith
  have hylt : y < Real.exp (Real.log (y + 1)) := by
    rw [Real.exp_log hy1]
    linarith
  have hmono : Real.exp (Real.log (y + 1)) <=
      Real.exp (max 1 (Real.log (y + 1))) :=
    Real.exp_le_exp.mpr (le_max_right _ _)
  change y < Real.exp (max 1 (Real.log (y + 1)))
  exact hylt.trans_le hmono

/-- The explicit second tail satisfies the exact joint-union inequality used
by `exists_product_choice_two_load_bounds`. -/
theorem two_family_tail_room
    (firstCount secondCount : Nat) (A : Real)
    (hfirst :
      (firstCount : Real) * chordCost + 1 <= Real.exp A) :
    (firstCount : Real) * Real.exp (Real.exp 1 - 1) *
          Real.exp (completionTail secondCount A) +
        (secondCount : Real) * Real.exp (Real.exp 1 - 1) * Real.exp A <
      Real.exp A * Real.exp (completionTail secondCount A) := by
  let x : Real := (firstCount : Real) * chordCost
  let y : Real := (secondCount : Real) * chordCost
  let b : Real := Real.exp (completionTail secondCount A)
  have hb0 : 0 <= b := (Real.exp_pos _).le
  have hyA : y * Real.exp A < b := by
    simpa [y, b, chordCost, mul_assoc] using
      second_cost_lt_exp_completionTail secondCount A
  have hmul : (x + 1) * b <= Real.exp A * b :=
    mul_le_mul_of_nonneg_right (by simpa [x] using hfirst) hb0
  change x * b + y * Real.exp A < Real.exp A * b
  nlinarith

#print axioms second_cost_lt_exp_completionTail
#print axioms two_family_tail_room

end

end FamilyStickyRandomTwoFamilyTailV1
