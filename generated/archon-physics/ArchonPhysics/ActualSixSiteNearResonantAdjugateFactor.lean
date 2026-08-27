import ArchonPhysics.ActualSixSiteThreeMassSimpleSpectrum

/-!
# Algebraic adjugate factor on the six-site near-resonant path

This module isolates the exact three-column alternant calculation.  The
separate matrix-identification theorem can later show that these displayed
columns are the shifted-adjugate quadratic weights of the actual model.
-/

open scoped Matrix

namespace ArchonPhysics.ActualSixSiteNearResonantAdjugateFactor

open ArchonPhysics

noncomputable section

/-- First displayed shifted-adjugate quadratic weight. -/
def nearResonantAdjugateColumnZero (t energy : Real) : Real :=
  energy *
    (2 * energy ^ 4 * t + 2 * energy ^ 4 -
      15 * energy ^ 3 * t - 18 * energy ^ 3 +
      36 * energy ^ 2 * t + 56 * energy ^ 2 -
      30 * energy * t - 70 * energy + 6 * t + 30) / (t + 1)

/-- Second displayed shifted-adjugate quadratic weight. -/
def nearResonantAdjugateColumnOne (t energy : Real) : Real :=
  energy *
    (2 * energy ^ 4 * t - 2 * energy ^ 4 -
      15 * energy ^ 3 * t + 18 * energy ^ 3 +
      36 * energy ^ 2 * t - 56 * energy ^ 2 -
      30 * energy * t + 70 * energy + 6 * t - 30) / (t - 1)

/-- Third displayed shifted-adjugate quadratic weight. -/
def nearResonantAdjugateColumnTwo (t energy : Real) : Real :=
  energy *
    (2 * energy ^ 4 * t ^ 2 - 2 * energy ^ 4 -
      11 * energy ^ 3 * t ^ 2 + energy ^ 3 * t + 18 * energy ^ 3 +
      16 * energy ^ 2 * t ^ 2 - 4 * energy ^ 2 * t - 56 * energy ^ 2 -
      5 * energy * t ^ 2 + 3 * energy * t + 70 * energy - 30) /
        ((t - 1) * (t + 1))

/-- The three displayed columns, evaluated rowwise at three energies. -/
def nearResonantAdjugateWeightMatrix
    (t : Real) (energy : Fin 3 → Real) : Matrix (Fin 3) (Fin 3) Real :=
  fun r s => ![nearResonantAdjugateColumnZero t (energy r),
    nearResonantAdjugateColumnOne t (energy r),
    nearResonantAdjugateColumnTwo t (energy r)] s

/-- Elementary symmetric coordinates of three displayed energies. -/
def nearResonantEnergyEOne (energy : Fin 3 → Real) : Real :=
  energy 0 + energy 1 + energy 2

def nearResonantEnergyETwo (energy : Fin 3 → Real) : Real :=
  energy 0 * energy 1 + energy 0 * energy 2 + energy 1 * energy 2

def nearResonantEnergyEThree (energy : Fin 3 → Real) : Real :=
  energy 0 * energy 1 * energy 2

/-- Symmetric residual after removing the three energies and their
Vandermonde from the displayed adjugate determinant. -/
def nearResonantAdjugateResidual
    (t : Real) (energy : Fin 3 → Real) : Real :=
  let e1 := nearResonantEnergyEOne energy
  let e2 := nearResonantEnergyETwo energy
  let e3 := nearResonantEnergyEThree energy
  (360 * t + 72) * e1 ^ 2 +
    (-360 * t - 96) * e1 * e2 +
    (222 * t + 76) * e1 * e3 +
    (-1785 * t - 273) * e1 +
    (78 * t + 24) * e2 ^ 2 +
    (-85 * t - 31) * e2 * e3 +
    (996 * t + 240) * e2 +
    (20 * t + 8) * e3 ^ 2 +
    (-660 * t - 216) * e3 + 1980 * t + 156

set_option maxHeartbeats 800000 in
-- The exact nine-entry rational alternant normalization needs extra reduction.
/-- Exact alternant factorization of the three displayed adjugate columns. -/
theorem nearResonantAdjugateWeightMatrix_det
    (t : Real) (energy : Fin 3 → Real)
    (hminus : t - 1 ≠ 0) (hplus : t + 1 ≠ 0) :
    (nearResonantAdjugateWeightMatrix t energy).det =
      4 * energy 0 * energy 1 * energy 2 * t ^ 2 *
        (energy 0 - energy 1) * (energy 0 - energy 2) *
        (energy 1 - energy 2) *
        nearResonantAdjugateResidual t energy /
          ((t - 1) ^ 2 * (t + 1) ^ 2) := by
  rw [Matrix.det_fin_three]
  simp [nearResonantAdjugateWeightMatrix,
    nearResonantAdjugateColumnZero, nearResonantAdjugateColumnOne,
    nearResonantAdjugateColumnTwo, nearResonantAdjugateResidual,
    nearResonantEnergyEOne, nearResonantEnergyETwo,
    nearResonantEnergyEThree]
  field_simp [hminus, hplus]
  ring

/-- Three selected ordered-energy branches along a scalar path.  The actual
six-site application instantiates these with modes `0`, `3`, and `4`. -/
def nearResonantSelectedEnergyPath
    (a b c : Real → Real) (t : Real) : Fin 3 → Real :=
  ![a t, b t, c t]

/-- The residual polynomial evaluated on the three selected energy branches. -/
def nearResonantAdjugateResidualPath
    (a b c : Real → Real) (t : Real) : Real :=
  nearResonantAdjugateResidual t
    (nearResonantSelectedEnergyPath a b c t)

/-- The clean resonant base value of the symmetric residual is exactly two. -/
theorem nearResonantAdjugateResidual_zero_clean :
    nearResonantAdjugateResidual 0 ![(4 : Real), 1, 1] = 2 := by
  norm_num [nearResonantAdjugateResidual, nearResonantEnergyEOne,
    nearResonantEnergyETwo, nearResonantEnergyEThree,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two]

/-- Polynomial continuity of the residual along any three continuous selected
energy branches. -/
theorem continuous_nearResonantAdjugateResidualPath
    {a b c : Real → Real}
    (ha : Continuous a) (hb : Continuous b) (hc : Continuous c) :
    Continuous (nearResonantAdjugateResidualPath a b c) := by
  unfold nearResonantAdjugateResidualPath nearResonantAdjugateResidual
    nearResonantEnergyEOne nearResonantEnergyETwo nearResonantEnergyEThree
    nearResonantSelectedEnergyPath
  fun_prop

end

end ArchonPhysics.ActualSixSiteNearResonantAdjugateFactor
