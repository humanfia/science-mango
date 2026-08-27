import ArchonPhysics.BondPotentialHamiltonianPhyslib

/-!
# Quantitative force-level Lennard--Jones Taylor remainder

The existing quantitative Taylor module controls the potential-energy
remainder.  Microscopic Duhamel expansions instead use the bond force.  This
module proves the exact force decomposition

`V'_LJ(x) = k x + alpha x^2 + beta x^3 + R_F(x)`

and a volume-independent fourth-order bound for `R_F` on a relative strain
tube.  This is a static analytic estimate; it does not prove that a trajectory
stays in the tube or that the remainder remains negligible on kinetic times.
-/

namespace ArchonPhysics.LennardJonesForceTaylorTube

open ArchonPhysics.BondPotentialHamiltonianPhyslib
open ArchonPhysics.LennardJonesPotential

noncomputable section

/-- Derivative of the fourth-order local LJ/FPUT potential. -/
def localAlphaBetaForce (depth r₀ x : Real) : Real :=
  harmonicStiffness depth r₀ * x +
    alphaCoefficient depth r₀ * x ^ 2 +
    betaCoefficient depth r₀ * x ^ 3

/-- Positive-coefficient dimensionless numerator of the exact force
remainder. -/
def dimensionlessForceRemainderNumerator (y : Real) : Real :=
  19320 + y *
    (182448 + y *
      (825384 + y *
        (2333760 + y *
          (4555980 + y *
            (6435000 + y *
              (6718140 + y *
                (5209776 + y *
                  (2972580 + y *
                    (1215240 + y *
                      (337500 + y *
                        (57120 + y * 4452)))))))))))

/-- Explicit force-remainder envelope on the relative tube `|x| ≤ rho*r₀`. -/
def forceRemainderTubeConstant (rho : Real) : Real :=
  dimensionlessForceRemainderNumerator rho / (1 - rho) ^ 13

/-- The exact LJ force minus its cubic-in-displacement FPUT force is a
fourth-order dimensionless remainder. -/
theorem lennardJonesDerivative_sub_localAlphaBetaForce_eq_dimensionless
    {depth r₀ x : Real} (hr₀ : r₀ ≠ 0) (hbond : r₀ + x ≠ 0) :
    lennardJonesDerivative depth r₀ x - localAlphaBetaForce depth r₀ x =
      -depth / r₀ * (x / r₀) ^ 4 *
        dimensionlessForceRemainderNumerator (x / r₀) /
          (1 + x / r₀) ^ 13 := by
  unfold lennardJonesDerivative localAlphaBetaForce
  unfold harmonicStiffness alphaCoefficient betaCoefficient
  unfold radialDerivative dimensionlessForceRemainderNumerator
  field_simp [hr₀, hbond]
  ring

private theorem abs_horner_step_radius
    {a b B y rho : Real} (ha : 0 ≤ a) (hrho : 0 ≤ rho)
    (hy : |y| ≤ rho) (hb : |b| ≤ B) :
    |a + y * b| ≤ a + rho * B := by
  calc
    |a + y * b| ≤ |a| + |y * b| := abs_add_le _ _
    _ = a + |y| * |b| := by rw [abs_of_nonneg ha, abs_mul]
    _ ≤ a + rho * B := by
      simpa [add_comm] using add_le_add_left
        (mul_le_mul hy hb (abs_nonneg b) hrho) a

/-- The radius-evaluated positive polynomial bounds the force numerator
throughout the closed tube. -/
theorem abs_dimensionlessForceRemainderNumerator_le
    {rho y : Real} (hrho : 0 ≤ rho) (hy : |y| ≤ rho) :
    |dimensionlessForceRemainderNumerator y| ≤
      dimensionlessForceRemainderNumerator rho := by
  unfold dimensionlessForceRemainderNumerator
  apply abs_horner_step_radius (by norm_num) hrho hy
  apply abs_horner_step_radius (by norm_num) hrho hy
  apply abs_horner_step_radius (by norm_num) hrho hy
  apply abs_horner_step_radius (by norm_num) hrho hy
  apply abs_horner_step_radius (by norm_num) hrho hy
  apply abs_horner_step_radius (by norm_num) hrho hy
  apply abs_horner_step_radius (by norm_num) hrho hy
  apply abs_horner_step_radius (by norm_num) hrho hy
  apply abs_horner_step_radius (by norm_num) hrho hy
  apply abs_horner_step_radius (by norm_num) hrho hy
  apply abs_horner_step_radius (by norm_num) hrho hy
  apply abs_horner_step_radius (by norm_num) hrho hy
  norm_num

/-- The positive-coefficient force numerator is positive at every
nonnegative tube radius. -/
theorem dimensionlessForceRemainderNumerator_pos_of_nonneg
    {rho : Real} (hrho : 0 ≤ rho) :
    0 < dimensionlessForceRemainderNumerator rho := by
  unfold dimensionlessForceRemainderNumerator
  positivity

/-- The explicit force tube constant is positive before the LJ singular
radius. -/
theorem forceRemainderTubeConstant_pos
    {rho : Real} (hrho0 : 0 ≤ rho) (hrho1 : rho < 1) :
    0 < forceRemainderTubeConstant rho := by
  unfold forceRemainderTubeConstant
  exact div_pos (dimensionlessForceRemainderNumerator_pos_of_nonneg hrho0)
    (pow_pos (sub_pos.mpr hrho1) 13)

/-- Quantitative fourth-order LJ force remainder on a closed relative-strain
tube. -/
theorem abs_lennardJonesDerivative_sub_localAlphaBetaForce_le
    {depth r₀ rho x : Real}
    (hdepth : 0 ≤ depth) (hr₀ : 0 < r₀)
    (hrho0 : 0 ≤ rho) (hrho1 : rho < 1)
    (hx : |x| ≤ rho * r₀) :
    |lennardJonesDerivative depth r₀ x -
        localAlphaBetaForce depth r₀ x| ≤
      depth / r₀ * forceRemainderTubeConstant rho *
        (|x| / r₀) ^ 4 := by
  let y : Real := x / r₀
  have hy : |y| ≤ rho := by
    dsimp [y]
    rw [abs_div, abs_of_pos hr₀]
    exact (div_le_iff₀ hr₀).2 hx
  have hyLower : -rho ≤ y := by
    calc
      -rho ≤ -|y| := neg_le_neg hy
      _ ≤ y := neg_abs_le y
  have hone : 0 < 1 + y := by linarith
  have hbase : 0 < 1 - rho := sub_pos.mpr hrho1
  have hbase_le : 1 - rho ≤ 1 + y := by linarith
  have hden_le : (1 - rho) ^ 13 ≤ (1 + y) ^ 13 :=
    pow_le_pow_left₀ hbase.le hbase_le 13
  have hbondPos : 0 < r₀ + x := by
    have heq : r₀ + x = r₀ * (1 + y) := by
      dsimp [y]
      field_simp [ne_of_gt hr₀]
    rw [heq]
    exact mul_pos hr₀ hone
  rw [lennardJonesDerivative_sub_localAlphaBetaForce_eq_dimensionless
    (ne_of_gt hr₀) (ne_of_gt hbondPos)]
  change
    |-depth / r₀ * y ^ 4 * dimensionlessForceRemainderNumerator y /
        (1 + y) ^ 13| ≤ _
  have habs :
      |-depth / r₀ * y ^ 4 * dimensionlessForceRemainderNumerator y /
          (1 + y) ^ 13| =
        depth / r₀ * |y| ^ 4 *
          |dimensionlessForceRemainderNumerator y| /
            (1 + y) ^ 13 := by
    rw [abs_div, abs_mul, abs_mul, abs_div, abs_neg, abs_pow,
      abs_pow, abs_of_nonneg hdepth, abs_of_pos hr₀, abs_of_pos hone]
  rw [habs]
  calc
    depth / r₀ * |y| ^ 4 *
          |dimensionlessForceRemainderNumerator y| /
          (1 + y) ^ 13 ≤
        depth / r₀ * |y| ^ 4 *
          dimensionlessForceRemainderNumerator rho /
          (1 + y) ^ 13 := by
      apply (div_le_div_iff_of_pos_right (pow_pos hone 13)).2
      exact mul_le_mul_of_nonneg_left
        (abs_dimensionlessForceRemainderNumerator_le hrho0 hy)
        (mul_nonneg (div_nonneg hdepth hr₀.le)
          (pow_nonneg (abs_nonneg y) 4))
    _ ≤ depth / r₀ * |y| ^ 4 *
          dimensionlessForceRemainderNumerator rho /
          (1 - rho) ^ 13 := by
      exact div_le_div_of_nonneg_left
        (mul_nonneg
          (mul_nonneg (div_nonneg hdepth hr₀.le)
            (pow_nonneg (abs_nonneg y) 4))
          (dimensionlessForceRemainderNumerator_pos_of_nonneg hrho0).le)
        (pow_pos hbase 13) hden_le
    _ = depth / r₀ * forceRemainderTubeConstant rho *
        (|x| / r₀) ^ 4 := by
      dsimp [y]
      unfold forceRemainderTubeConstant
      rw [abs_div, abs_of_pos hr₀]
      ring

/-- Relative tube membership automatically excludes the LJ collision
singularity. -/
theorem bond_nonsingular_of_relativeTube
    {r₀ rho x : Real} (hr₀ : 0 < r₀) (_hrho0 : 0 ≤ rho)
    (hrho1 : rho < 1) (hx : |x| ≤ rho * r₀) :
    r₀ + x ≠ 0 := by
  have hxLower : -(rho * r₀) ≤ x := by
    calc
      -(rho * r₀) ≤ -|x| := neg_le_neg hx
      _ ≤ x := neg_abs_le x
  have : 0 < r₀ + x := by
    have hrho : rho * r₀ < r₀ :=
      (mul_lt_iff_lt_one_left hr₀).2 hrho1
    linarith
  exact ne_of_gt this

end

end ArchonPhysics.LennardJonesForceTaylorTube
