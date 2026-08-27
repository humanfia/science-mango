import Mathlib.LinearAlgebra.Matrix.Kronecker
import Mathlib.LinearAlgebra.Matrix.ToLinearEquiv
import ArchonPhysics.ActualSixSiteNearResonantPathSeparable

/-!
# Scaled companion matrix for the six-site path quintic

The characteristic quintic has leading coefficient `a(t) = 1 - t^2`.
Multiplying its ordinary companion matrix by `a(t)` produces a matrix with
polynomial entries.  Evaluation rows at roots are left eigenvectors with
eigenvalue `a(t) E`; this is the algebraic core of the denominator-free
quotient norm.
-/

open scoped BigOperators Matrix Polynomial

namespace ArchonPhysics.ActualSixSiteNearResonantScaledCompanion

open ArchonPhysics.ActualSixSiteNearResonantPathSeparable

noncomputable section

def nearResonantLeadingPolynomial : Real[X] :=
  1 - Polynomial.X ^ 2

/-- `a(t)` times the ordinary degree-five companion matrix. -/
def nearResonantScaledCompanionPolynomial :
    Matrix (Fin 5) (Fin 5) Real[X] :=
  let u : Real[X] := Polynomial.X ^ 2
  let a : Real[X] := 1 - u
  !![0, 0, 0, 0, 36;
     a, 0, 0, 0, -105 + 5 * u;
     0, a, 0, 0, 112 - 20 * u;
     0, 0, a, 0, -54 + 21 * u;
     0, 0, 0, a, 12 - 8 * u]

def nearResonantScaledCompanion (t : Real) :
    Matrix (Fin 5) (Fin 5) Real :=
  let u := t ^ 2
  let a := 1 - u
  !![0, 0, 0, 0, 36;
     a, 0, 0, 0, -105 + 5 * u;
     0, a, 0, 0, 112 - 20 * u;
     0, 0, a, 0, -54 + 21 * u;
     0, 0, 0, a, 12 - 8 * u]

theorem evaluate_nearResonantScaledCompanionPolynomial (t : Real) :
    (Polynomial.evalRingHom t).mapMatrix
        nearResonantScaledCompanionPolynomial =
      nearResonantScaledCompanion t := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [nearResonantScaledCompanionPolynomial,
      nearResonantScaledCompanion,
      RingHom.mapMatrix_apply]

def quinticEvaluationRow (energy : Real) : Fin 5 → Real :=
  ![1, energy, energy ^ 2, energy ^ 3, energy ^ 4]

/-- A root of the path quintic gives a left eigenvector of the scaled
companion matrix. -/
theorem quinticEvaluationRow_vecMul_scaledCompanion
    {t energy : Real}
    (hroot : (nearResonantPathQuintic (t ^ 2)).eval energy = 0) :
    quinticEvaluationRow energy ᵥ* nearResonantScaledCompanion t =
      ((1 - t ^ 2) * energy) • quinticEvaluationRow energy := by
  have hpoly :
      (1 - t ^ 2) * energy ^ 5 +
        (-12 + 8 * t ^ 2) * energy ^ 4 +
        (54 - 21 * t ^ 2) * energy ^ 3 +
        (-112 + 20 * t ^ 2) * energy ^ 2 +
        (105 - 5 * t ^ 2) * energy - 36 = 0 := by
    simpa [nearResonantPathQuintic, Polynomial.eval_add,
      Polynomial.eval_sub, Polynomial.eval_mul, Polynomial.eval_pow] using hroot
  funext j
  fin_cases j <;>
    norm_num [quinticEvaluationRow, nearResonantScaledCompanion,
      Matrix.vecMul, dotProduct, Fin.sum_univ_succ, Pi.smul_apply]
  all_goals ring_nf
  nlinarith [hpoly]

/-- The same row is an eigenvector for every matrix power. -/
theorem quinticEvaluationRow_vecMul_scaledCompanion_pow
    {t energy : Real}
    (hroot : (nearResonantPathQuintic (t ^ 2)).eval energy = 0)
    (n : Nat) :
    quinticEvaluationRow energy ᵥ* nearResonantScaledCompanion t ^ n =
      ((1 - t ^ 2) * energy) ^ n • quinticEvaluationRow energy := by
  induction n with
  | zero => simp
  | succ n ih =>
      calc
        quinticEvaluationRow energy ᵥ*
            nearResonantScaledCompanion t ^ (n + 1) =
          (quinticEvaluationRow energy ᵥ*
              nearResonantScaledCompanion t ^ n) ᵥ*
            nearResonantScaledCompanion t := by
              rw [pow_succ, Matrix.vecMul_vecMul]
        _ = ((1 - t ^ 2) * energy) ^ n •
            (quinticEvaluationRow energy ᵥ*
              nearResonantScaledCompanion t) := by
                rw [ih, Matrix.smul_vecMul]
        _ = ((1 - t ^ 2) * energy) ^ (n + 1) •
            quinticEvaluationRow energy := by
              rw [quinticEvaluationRow_vecMul_scaledCompanion hroot, smul_smul]
              exact congrArg
                (fun c : Real => c • quinticEvaluationRow energy)
                (pow_succ ((1 - t ^ 2) * energy) n).symm

end

end ArchonPhysics.ActualSixSiteNearResonantScaledCompanion
