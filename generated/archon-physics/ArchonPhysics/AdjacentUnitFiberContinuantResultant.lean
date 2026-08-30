import Mathlib.Algebra.Polynomial.Degree.IsMonicOfDegree
import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Data.Real.Basic
import Mathlib.RingTheory.Polynomial.Resultant.Basic

/-!
# The adjacent unit-fiber continuant resultant

This file proves the exact algebraic identity expected at the zero endpoint of
an adjacent two-site inverse-mass fiber.  The type-A continuants satisfy

`K 0 = 1`, `K 1 = X - 2`, and
`K (n+2) = (X-2) K (n+1) - K n`.

For the endpoint pair

`P n = X * K n`, `Q n = K (n+1) - X * K n`,

the fixed-size resultant is

`Res(P n,Q n) = (-1)^((n+2).choose 2) * (n+2)`.

Thus it is nonzero in both `Int` and `Real` for every `n`.  For a cycle of
volume `N = n+2`, this is exactly the conjectured value
`(-1)^(N*(N-1)/2) * N`.

The theorem here is the abstract continuant/resultant half of the canonical
adjacent-site calculation.  It does not itself identify `P n` and `Q n` with
the specialization of the canonical sliced cycle characteristic polynomial
and its vertical mass partial; that matrix-specialization bridge is a separate
obligation.
-/

namespace ArchonPhysics.AdjacentUnitFiberContinuantResultant

noncomputable section

open Polynomial

/-- Successive type-A continuants, stored as `(K n, K (n+1))`.  Using a
first-order state recursion keeps reduction of the two-step recurrence small. -/
private noncomputable def cartanContinuantState : Nat →
    Polynomial Int × Polynomial Int
  | 0 => (1, X - C 2)
  | n + 1 =>
      let state := cartanContinuantState n
      (state.2, (X - C 2) * state.2 - state.1)

/-- The monic type-A continuant, over the integers. -/
noncomputable def cartanContinuant (n : Nat) : Polynomial Int :=
  (cartanContinuantState n).1

@[simp] theorem cartanContinuant_zero : cartanContinuant 0 = 1 := rfl

@[simp] theorem cartanContinuant_one : cartanContinuant 1 = X - C 2 := rfl

@[simp] theorem cartanContinuant_add_two (n : Nat) :
    cartanContinuant (n + 2) =
      (X - C 2) * cartanContinuant (n + 1) - cartanContinuant n := rfl

attribute [irreducible] cartanContinuant

/-- `K n` is monic of degree exactly `n`. -/
theorem cartanContinuant_isMonicOfDegree (n : Nat) :
    (cartanContinuant n).IsMonicOfDegree n := by
  induction n using Nat.twoStepInduction with
  | zero => simp
  | one =>
      simpa using Polynomial.isMonicOfDegree_X_sub_one (2 : Int)
  | more n hn hn1 =>
      rw [cartanContinuant_add_two]
      have hproduct :
          ((X - C 2) * cartanContinuant (n + 1)).IsMonicOfDegree (n + 2) := by
        simpa only [Nat.add_assoc, Nat.one_add] using
          (Polynomial.isMonicOfDegree_X_sub_one (2 : Int)).mul hn1
      apply hproduct.sub
      rw [hn.natDegree_eq]
      omega

theorem cartanContinuant_monic (n : Nat) : (cartanContinuant n).Monic :=
  (cartanContinuant_isMonicOfDegree n).monic

theorem cartanContinuant_natDegree (n : Nat) :
    (cartanContinuant n).natDegree = n :=
  (cartanContinuant_isMonicOfDegree n).natDegree_eq

/-- The constant term is the signed determinant of the type-A Cartan matrix. -/
theorem cartanContinuant_coeff_zero (n : Nat) :
    (cartanContinuant n).coeff 0 = (-1 : Int) ^ n * (n + 1 : Nat) := by
  induction n using Nat.twoStepInduction with
  | zero => simp
  | one => norm_num [cartanContinuant]
  | more n hn hn1 =>
      rw [coeff_zero_eq_eval_zero] at hn hn1 ⊢
      rw [cartanContinuant_add_two]
      simp only [eval_sub, eval_mul, eval_X, eval_C, zero_sub]
      rw [hn, hn1]
      push_cast
      simp only [pow_succ]
      ring

/-- Consecutive type-A continuants have a unit resultant, with the exact
alternating sign needed by the endpoint calculation. -/
theorem cartanContinuant_resultant_consecutive (n : Nat) :
    Polynomial.resultant (cartanContinuant n) (cartanContinuant (n + 1)) n (n + 1) =
      (-1 : Int) ^ ((n + 1).choose 2) := by
  induction n with
  | zero => simp
  | succ n ih =>
      have hn := cartanContinuant_isMonicOfDegree n
      have hn1 := cartanContinuant_isMonicOfDegree (n + 1)
      have hrewrite :
          cartanContinuant (n + 2) =
            -cartanContinuant n + cartanContinuant (n + 1) * (X - C 2) := by
        rw [cartanContinuant_add_two]
        ring
      have hadd := Polynomial.resultant_add_mul_right
        (cartanContinuant (n + 1)) (-cartanContinuant n) (X - C (2 : Int))
        (n + 1) (n + 2) (by
          calc
            (X - C (2 : Int)).natDegree + (n + 1) ≤ 1 + (n + 1) :=
              Nat.add_le_add_right
                (Polynomial.natDegree_X_sub_C_le (R := Int) 2) (n + 1)
            _ = n + 2 := by omega) hn1.natDegree_eq.le
      have hpad := Polynomial.resultant_add_right_deg
        (cartanContinuant (n + 1)) (-cartanContinuant n)
        (n + 1) n 2 (by simp [hn.natDegree_eq])
      have hscale := Polynomial.resultant_C_mul_right
        (f := cartanContinuant (n + 1)) (g := cartanContinuant n)
        (m := n + 1) (n := n) (-1 : Int)
      have heven : Even ((n + 1) * n) := by
        rw [mul_comm]
        exact Nat.even_mul_succ_self n
      have hcomm := Polynomial.resultant_comm
        (cartanContinuant (n + 1)) (cartanContinuant n) (n + 1) n
      rw [heven.neg_one_pow, one_mul] at hcomm
      rw [hrewrite, hadd]
      rw [hpad]
      have hn1coeff : (cartanContinuant (n + 1)).coeff (n + 1) = 1 := by
        calc
          (cartanContinuant (n + 1)).coeff (n + 1) =
              (cartanContinuant (n + 1)).coeff
                (cartanContinuant (n + 1)).natDegree := by
            exact congrArg ((cartanContinuant (n + 1)).coeff)
              hn1.natDegree_eq.symm
          _ = 1 := hn1.monic.coeff_natDegree
      rw [hn1coeff]
      norm_num
      rw [show -cartanContinuant n = C (-1 : Int) * cartanContinuant n by simp]
      rw [hscale, hcomm, ih]
      conv_rhs => rw [Nat.choose_succ_succ, Nat.choose_one_right, pow_add]

/-- The polynomial modeling the positive characteristic polynomial at the
zero endpoint of the adjacent unit fiber. -/
def adjacentEndpointCharacteristic (n : Nat) : Polynomial Int :=
  X * cartanContinuant n

/-- The polynomial modeling the endpoint vertical mass partial. -/
def adjacentEndpointVerticalPartial (n : Nat) : Polynomial Int :=
  cartanContinuant (n + 1) - adjacentEndpointCharacteristic n

theorem adjacentEndpointCharacteristic_isMonicOfDegree (n : Nat) :
    (adjacentEndpointCharacteristic n).IsMonicOfDegree (n + 1) := by
  simpa [adjacentEndpointCharacteristic, Nat.add_comm] using
    (Polynomial.isMonicOfDegree_X Int).mul
      (cartanContinuant_isMonicOfDegree n)

theorem adjacentEndpointVerticalPartial_natDegree_le (n : Nat) :
    (adjacentEndpointVerticalPartial n).natDegree ≤ n := by
  have hleft := cartanContinuant_isMonicOfDegree (n + 1)
  have hright := adjacentEndpointCharacteristic_isMonicOfDegree n
  exact Nat.lt_succ_iff.mp
    (hleft.natDegree_sub_lt (Nat.succ_ne_zero n) hright)

/-- Exact integer endpoint resultant.  Both size bounds are the actual energy
degrees: `n+1` for the characteristic polynomial and at most `n` for its
vertical partial. -/
theorem adjacentEndpoint_resultant (n : Nat) :
    Polynomial.resultant (adjacentEndpointCharacteristic n)
        (adjacentEndpointVerticalPartial n) (n + 1) n =
      (-1 : Int) ^ ((n + 2).choose 2) * (n + 2 : Nat) := by
  let P := adjacentEndpointCharacteristic n
  let Q := adjacentEndpointVerticalPartial n
  have hP := adjacentEndpointCharacteristic_isMonicOfDegree n
  have hP' : P.IsMonicOfDegree (n + 1) := hP
  have hQ := adjacentEndpointVerticalPartial_natDegree_le n
  have hQ' : Q.natDegree ≤ n := hQ
  have hpad := Polynomial.resultant_add_right_deg P Q (n + 1) n 1 hQ'
  have hadd := Polynomial.resultant_add_mul_right P Q (1 : Polynomial Int)
    (n + 1) (n + 1) (by simp) hP'.natDegree_eq.le
  have hmul := Polynomial.resultant_mul_left X (cartanContinuant n)
    (cartanContinuant (n + 1)) (n + 1)
    (cartanContinuant_natDegree (n + 1)).le
  have hX := Polynomial.resultant_X_sub_C_left
    (cartanContinuant (n + 1)) (n + 1) (0 : Int)
    (cartanContinuant_natDegree (n + 1)).le
  calc
    Polynomial.resultant P Q (n + 1) n =
        Polynomial.resultant P Q (n + 1) (n + 1) := by
      have hPcoeff : P.coeff (n + 1) = 1 := by
        rw [← hP'.natDegree_eq]
        exact hP'.monic.coeff_natDegree
      rw [hpad, hPcoeff]
      simp
    _ = Polynomial.resultant P (Q + P * 1) (n + 1) (n + 1) := hadd.symm
    _ = Polynomial.resultant P (cartanContinuant (n + 1)) (n + 1) (n + 1) := by
      congr 1
      dsimp [Q, P, adjacentEndpointVerticalPartial]
      ring
    _ = Polynomial.resultant X (cartanContinuant (n + 1)) 1 (n + 1) *
          Polynomial.resultant (cartanContinuant n) (cartanContinuant (n + 1)) n
            (n + 1) := by
      simpa [P, adjacentEndpointCharacteristic, cartanContinuant_natDegree,
        Nat.add_comm] using hmul
    _ = (cartanContinuant (n + 1)).coeff 0 *
          Polynomial.resultant (cartanContinuant n) (cartanContinuant (n + 1)) n
            (n + 1) := by
      have hX' :
          Polynomial.resultant X (cartanContinuant (n + 1)) 1 (n + 1) =
            (cartanContinuant (n + 1)).coeff 0 := by
        rw [show C (0 : Int) = (0 : Polynomial Int) by simp, sub_zero,
          ← coeff_zero_eq_eval_zero] at hX
        exact hX
      rw [hX']
    _ = (-1 : Int) ^ (n + 1) * (n + 2 : Nat) *
          (-1 : Int) ^ ((n + 1).choose 2) := by
      rw [cartanContinuant_coeff_zero,
        cartanContinuant_resultant_consecutive]
    _ = (-1 : Int) ^ ((n + 2).choose 2) * (n + 2 : Nat) := by
      conv_rhs => rw [Nat.choose_succ_succ, Nat.choose_one_right, pow_add]
      ring

theorem adjacentEndpoint_resultant_ne_zero (n : Nat) :
    Polynomial.resultant (adjacentEndpointCharacteristic n)
        (adjacentEndpointVerticalPartial n) (n + 1) n ≠ 0 := by
  rw [adjacentEndpoint_resultant]
  exact mul_ne_zero (by simp) (by exact_mod_cast Nat.succ_ne_zero (n + 1))

/-- Real-coefficient form used by the canonical mass-fiber construction. -/
def realCartanContinuant (n : Nat) : Polynomial Real :=
  (cartanContinuant n).map (Int.castRingHom Real)

def realAdjacentEndpointCharacteristic (n : Nat) : Polynomial Real :=
  X * realCartanContinuant n

def realAdjacentEndpointVerticalPartial (n : Nat) : Polynomial Real :=
  realCartanContinuant (n + 1) - realAdjacentEndpointCharacteristic n

theorem realAdjacentEndpoint_resultant (n : Nat) :
    Polynomial.resultant (realAdjacentEndpointCharacteristic n)
        (realAdjacentEndpointVerticalPartial n) (n + 1) n =
      (-1 : Real) ^ ((n + 2).choose 2) * (n + 2 : Nat) := by
  let phi : Int →+* Real := Int.castRingHom Real
  calc
    Polynomial.resultant (realAdjacentEndpointCharacteristic n)
        (realAdjacentEndpointVerticalPartial n) (n + 1) n =
      Polynomial.resultant ((adjacentEndpointCharacteristic n).map phi)
        ((adjacentEndpointVerticalPartial n).map phi) (n + 1) n := by
          simp only [phi, realAdjacentEndpointCharacteristic,
            realAdjacentEndpointVerticalPartial, realCartanContinuant,
            adjacentEndpointCharacteristic, adjacentEndpointVerticalPartial]
          rw [Polynomial.map_mul, Polynomial.map_X, Polynomial.map_sub,
            Polynomial.map_mul,
            Polynomial.map_X]
    _ = phi (Polynomial.resultant (adjacentEndpointCharacteristic n)
        (adjacentEndpointVerticalPartial n) (n + 1) n) :=
      Polynomial.resultant_map_map _ _ _ _ _
    _ = phi ((-1 : Int) ^ ((n + 2).choose 2) * (n + 2 : Nat)) := by
      rw [adjacentEndpoint_resultant]
    _ = (-1 : Real) ^ ((n + 2).choose 2) * (n + 2 : Nat) := by
      simp [phi]

theorem realAdjacentEndpoint_resultant_ne_zero (n : Nat) :
    Polynomial.resultant (realAdjacentEndpointCharacteristic n)
        (realAdjacentEndpointVerticalPartial n) (n + 1) n ≠ 0 := by
  rw [realAdjacentEndpoint_resultant]
  exact mul_ne_zero (by simp) (by positivity)

end

end ArchonPhysics.AdjacentUnitFiberContinuantResultant
