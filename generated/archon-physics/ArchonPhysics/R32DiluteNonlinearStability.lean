import ArchonPhysics.CanonicalIIDCoerciveActualExpectationAdapter
import ArchonPhysics.LennardJonesModalRemainderMeanSquareBound

/-!
# R32: deterministic dilute nonlinear stability bookkeeping

This module isolates the deterministic estimate which is available when a
unit-energy free harmonic orbit is dilute in physical bond coordinates.  The
important point is to use the `l2` norm of the periodic transpose difference,
rather than summing the norms of `N` bond directions.  Consequently the force
estimate below has no volume factor.

Writing the exact bond vector as `x + y`, where `x` is the free bond vector
and `y` is the exact-minus-free error, the quadratic and cubic residuals obey

`‖(x+y)^2‖₂ <= a E + 2 a R + R^2`,

`‖(x+y)^3‖₂ <= a^2 E + 3 a^2 R + 3 a R^2 + R^3`

under `‖x‖∞ <= a`, `‖x‖₂ <= E`, and `‖y‖₂ <= R`.  On a kinetic window
`t <= tau / g^2`, this produces the polynomial envelope with leading size
`a / |g|`; the feedback coefficients are `a / |g|` and `R / |g|`, not the
spurious `1 / |g|` obtained by bounding the full exact bond vector at once.

The last section proves a continuous first-exit bootstrap lemma and an exact
inverse-square rescaling theorem.  To apply it to the concrete exact and free
flows, one still has to provide the standard forced-harmonic Duhamel
domination for the running bond-energy error.  No Gronwall exponential,
random-phase statement, kinetic limit, or thermalization claim is made here.
-/

namespace ArchonPhysics.R32DiluteNonlinearStability

open Set
open ArchonPhysics
open ArchonPhysics.CanonicalIIDCoerciveActualExpectationAdapter
open ArchonPhysics.CoerciveHamiltonianPhyslib
open ArchonPhysics.LennardJonesModalRemainderMeanSquareBound
open ArchonPhysics.MassWeightedHamiltonianDynamics

noncomputable section

variable {N : Nat} [NeZero N]

/-! ## Bond `l2` algebra -/

/-- The physical periodic bond vector, bundled with its Euclidean `l2` norm. -/
def bondVector (q : HilbertConfiguration N) : HilbertConfiguration N :=
  WithLp.toLp 2 (Lattice.forwardDifference (asConfiguration q))

@[simp] theorem bondVector_apply (q : HilbertConfiguration N)
    (i : Lattice.Site N) :
    bondVector q i = Lattice.forwardDifference (asConfiguration q) i := rfl

/-- Pointwise multiplication, kept separate from the Hilbert-space scalar
operations. -/
def pointwiseMul (x y : HilbertConfiguration N) : HilbertConfiguration N :=
  WithLp.toLp 2 (fun i => x i * y i)

@[simp] theorem pointwiseMul_apply (x y : HilbertConfiguration N)
    (i : Lattice.Site N) : pointwiseMul x y i = x i * y i := rfl

/-- The bond vector is linear under subtraction. -/
theorem bondVector_sub (q r : HilbertConfiguration N) :
    bondVector (q - r) = bondVector q - bondVector r := by
  ext i
  simp only [bondVector_apply, Lattice.forwardDifference_apply,
    asConfiguration, PiLp.sub_apply]
  ring

/-- Every bond coordinate is controlled by the bond `l2` norm. -/
theorem abs_bondVector_apply_le_norm (q : HilbertConfiguration N)
    (i : Lattice.Site N) :
    |bondVector q i| <= ‖bondVector q‖ := by
  simpa only [Real.norm_eq_abs] using PiLp.norm_apply_le (bondVector q) i

/-- Multiplication by a pointwise bounded vector is bounded on finite `l2`,
with no cardinality loss. -/
theorem norm_pointwiseMul_le_of_left_sup
    (x y : HilbertConfiguration N) {A : Real} (hA : 0 <= A)
    (hx : forall i, |x i| <= A) :
    ‖pointwiseMul x y‖ <= A * ‖y‖ := by
  have hsum : (∑ i : Lattice.Site N, (x i * y i) ^ 2) <=
      A ^ 2 * ∑ i : Lattice.Site N, y i ^ 2 := by
    rw [Finset.mul_sum]
    apply Finset.sum_le_sum
    intro i _hi
    have hxsq : x i ^ 2 <= A ^ 2 := by
      simpa [sq_abs] using (sq_le_sq₀ (abs_nonneg (x i)) hA).2 (hx i)
    calc
      (x i * y i) ^ 2 = x i ^ 2 * y i ^ 2 := by ring
      _ <= A ^ 2 * y i ^ 2 :=
        mul_le_mul_of_nonneg_right hxsq (sq_nonneg (y i))
  have hsq : ‖pointwiseMul x y‖ ^ 2 <= (A * ‖y‖) ^ 2 := by
    rw [EuclideanSpace.real_norm_sq_eq, mul_pow,
      EuclideanSpace.real_norm_sq_eq]
    exact hsum
  nlinarith [norm_nonneg (pointwiseMul x y),
    mul_nonneg hA (norm_nonneg y)]

/-- Symmetric form of the pointwise-product estimate. -/
theorem norm_pointwiseMul_le_of_right_sup
    (x y : HilbertConfiguration N) {B : Real} (hB : 0 <= B)
    (hy : forall i, |y i| <= B) :
    ‖pointwiseMul x y‖ <= B * ‖x‖ := by
  have hcomm : pointwiseMul x y = pointwiseMul y x := by
    ext i
    simp [mul_comm]
  rw [hcomm]
  exact norm_pointwiseMul_le_of_left_sup y x hB hy

/-- An `l2` error bound also supplies the pointwise bound needed in the
nonlinear products. -/
theorem pointwise_bound_of_norm_le
    (y : HilbertConfiguration N) {R : Real} (hy : ‖y‖ <= R)
    (i : Lattice.Site N) :
    |y i| <= R := by
  exact (show |y i| <= ‖y‖ by
    simpa only [Real.norm_eq_abs] using PiLp.norm_apply_le y i).trans hy

/-! ## Sharp quadratic/cubic expansion around the free orbit -/

/-- Quadratic pointwise product after expanding `x + y`. -/
theorem norm_pointwiseSquare_add_le
    (x y : HilbertConfiguration N) {a E R : Real}
    (ha : 0 <= a) (hR : 0 <= R)
    (hxsup : forall i, |x i| <= a)
    (hxnorm : ‖x‖ <= E) (hynorm : ‖y‖ <= R) :
    ‖pointwiseMul (x + y) (x + y)‖ <=
      a * E + 2 * a * R + R ^ 2 := by
  have hysup : forall i, |y i| <= R :=
    fun i => pointwise_bound_of_norm_le y hynorm i
  have hxx := norm_pointwiseMul_le_of_left_sup x x ha hxsup
  have hxy := norm_pointwiseMul_le_of_left_sup x y ha hxsup
  have hyy := norm_pointwiseMul_le_of_left_sup y y hR hysup
  have hexpand : pointwiseMul (x + y) (x + y) =
      pointwiseMul x x + pointwiseMul x y +
        pointwiseMul y x + pointwiseMul y y := by
    ext i
    simp [pointwiseMul]
    ring
  rw [hexpand]
  calc
    ‖pointwiseMul x x + pointwiseMul x y +
        pointwiseMul y x + pointwiseMul y y‖ <=
      ‖pointwiseMul x x‖ + ‖pointwiseMul x y‖ +
        ‖pointwiseMul y x‖ + ‖pointwiseMul y y‖ := by
      calc
        ‖pointwiseMul x x + pointwiseMul x y +
            pointwiseMul y x + pointwiseMul y y‖ <=
          ‖pointwiseMul x x + pointwiseMul x y + pointwiseMul y x‖ +
            ‖pointwiseMul y y‖ := norm_add_le _ _
        _ <= (‖pointwiseMul x x + pointwiseMul x y‖ +
            ‖pointwiseMul y x‖) + ‖pointwiseMul y y‖ := by
          gcongr
          exact norm_add_le _ _
        _ <= ((‖pointwiseMul x x‖ + ‖pointwiseMul x y‖) +
            ‖pointwiseMul y x‖) + ‖pointwiseMul y y‖ := by
          gcongr
          exact norm_add_le _ _
        _ = _ := by ring
    _ <= a * ‖x‖ + a * ‖y‖ + a * ‖y‖ + R * ‖y‖ := by
      have hyx : ‖pointwiseMul y x‖ <= a * ‖y‖ :=
        norm_pointwiseMul_le_of_right_sup y x ha hxsup
      linarith
    _ <= a * E + a * R + a * R + R * R := by
      gcongr
    _ = a * E + 2 * a * R + R ^ 2 := by ring

/-- Cubic pointwise product after expanding `x + y`. -/
theorem norm_pointwiseCube_add_le
    (x y : HilbertConfiguration N) {a E R : Real}
    (ha : 0 <= a) (hR : 0 <= R)
    (hxsup : forall i, |x i| <= a)
    (hxnorm : ‖x‖ <= E) (hynorm : ‖y‖ <= R) :
    ‖pointwiseMul (pointwiseMul (x + y) (x + y)) (x + y)‖ <=
      a ^ 2 * E + 3 * a ^ 2 * R + 3 * a * R ^ 2 + R ^ 3 := by
  have hysup : forall i, |y i| <= R :=
    fun i => pointwise_bound_of_norm_le y hynorm i
  let xxx := pointwiseMul (pointwiseMul x x) x
  let xxy := pointwiseMul (pointwiseMul x x) y
  let xyy := pointwiseMul x (pointwiseMul y y)
  let yyy := pointwiseMul (pointwiseMul y y) y
  have hxxsup : forall i, |pointwiseMul x x i| <= a ^ 2 := by
    intro i
    simp only [pointwiseMul_apply, abs_mul]
    have hmul : |x i| * |x i| <= a * a :=
      mul_le_mul (hxsup i) (hxsup i) (abs_nonneg _) ha
    simpa [pow_two] using hmul
  have hyysup : forall i, |pointwiseMul y y i| <= R ^ 2 := by
    intro i
    simp only [pointwiseMul_apply, abs_mul]
    have hmul : |y i| * |y i| <= R * R :=
      mul_le_mul (hysup i) (hysup i) (abs_nonneg _) hR
    simpa [pow_two] using hmul
  have hxxx : ‖xxx‖ <= a ^ 2 * E := by
    exact (norm_pointwiseMul_le_of_left_sup
      (pointwiseMul x x) x (sq_nonneg a) hxxsup).trans
        (mul_le_mul_of_nonneg_left hxnorm (sq_nonneg a))
  have hxxy : ‖xxy‖ <= a ^ 2 * R := by
    exact (norm_pointwiseMul_le_of_left_sup
      (pointwiseMul x x) y (sq_nonneg a) hxxsup).trans
        (mul_le_mul_of_nonneg_left hynorm (sq_nonneg a))
  have hxyy : ‖xyy‖ <= a * R ^ 2 := by
    have hyy := norm_pointwiseMul_le_of_left_sup y y hR hysup
    calc
      ‖xyy‖ <= a * ‖pointwiseMul y y‖ := by
        exact norm_pointwiseMul_le_of_left_sup x (pointwiseMul y y) ha hxsup
      _ <= a * (R * ‖y‖) := mul_le_mul_of_nonneg_left hyy ha
      _ <= a * (R * R) := by gcongr
      _ = a * R ^ 2 := by ring
  have hyyy : ‖yyy‖ <= R ^ 3 := by
    calc
      ‖yyy‖ <= R ^ 2 * ‖y‖ := by
        exact norm_pointwiseMul_le_of_left_sup
          (pointwiseMul y y) y (sq_nonneg R) hyysup
      _ <= R ^ 2 * R := mul_le_mul_of_nonneg_left hynorm (sq_nonneg R)
      _ = R ^ 3 := by ring
  have hexpand :
      pointwiseMul (pointwiseMul (x + y) (x + y)) (x + y) =
        xxx + (xxy + xxy + xxy) + (xyy + xyy + xyy) + yyy := by
    ext i
    simp [xxx, xxy, xyy, yyy, pointwiseMul]
    ring
  rw [hexpand]
  calc
    ‖xxx + (xxy + xxy + xxy) + (xyy + xyy + xyy) + yyy‖ <=
        ‖xxx‖ + 3 * ‖xxy‖ + 3 * ‖xyy‖ + ‖yyy‖ := by
      calc
        ‖xxx + (xxy + xxy + xxy) + (xyy + xyy + xyy) + yyy‖ <=
            ‖xxx‖ + ‖xxy + xxy + xxy‖ +
              ‖xyy + xyy + xyy‖ + ‖yyy‖ := by
          calc
            _ <= ‖xxx + (xxy + xxy + xxy) + (xyy + xyy + xyy)‖ +
                ‖yyy‖ := norm_add_le _ _
            _ <= (‖xxx + (xxy + xxy + xxy)‖ +
                ‖xyy + xyy + xyy‖) + ‖yyy‖ := by
              gcongr
              exact norm_add_le _ _
            _ <= ((‖xxx‖ + ‖xxy + xxy + xxy‖) +
                ‖xyy + xyy + xyy‖) + ‖yyy‖ := by
              gcongr
              exact norm_add_le _ _
            _ = _ := by ring
        _ <= ‖xxx‖ + 3 * ‖xxy‖ + 3 * ‖xyy‖ + ‖yyy‖ := by
          have hxxy3 : ‖xxy + xxy + xxy‖ <= 3 * ‖xxy‖ := by
            calc
              ‖xxy + xxy + xxy‖ <= ‖xxy + xxy‖ + ‖xxy‖ := norm_add_le _ _
              _ <= (‖xxy‖ + ‖xxy‖) + ‖xxy‖ := by
                gcongr
                exact norm_add_le _ _
              _ = 3 * ‖xxy‖ := by ring
          have hxyy3 : ‖xyy + xyy + xyy‖ <= 3 * ‖xyy‖ := by
            calc
              ‖xyy + xyy + xyy‖ <= ‖xyy + xyy‖ + ‖xyy‖ := norm_add_le _ _
              _ <= (‖xyy‖ + ‖xyy‖) + ‖xyy‖ := by
                gcongr
                exact norm_add_le _ _
              _ = 3 * ‖xyy‖ := by ring
          linarith
    _ <= a ^ 2 * E + 3 * (a ^ 2 * R) +
        3 * (a * R ^ 2) + R ^ 3 := by linarith
    _ = a ^ 2 * E + 3 * a ^ 2 * R + 3 * a * R ^ 2 + R ^ 3 := by ring

/-! ## Concrete frozen-mass nonlinear force bound -/

/-- The residual derivative on every physical bond, bundled in `l2`. -/
def nonlinearBondDerivativeVector (kappa beta g : Real)
    (q : HilbertConfiguration N) : HilbertConfiguration N :=
  WithLp.toLp 2 (fun i => nonlinearPotentialDerivative kappa beta g
    (Lattice.forwardDifference (asConfiguration q) i))

@[simp] theorem nonlinearBondDerivativeVector_apply
    (kappa beta g : Real) (q : HilbertConfiguration N)
    (i : Lattice.Site N) :
    nonlinearBondDerivativeVector kappa beta g q i =
      nonlinearPotentialDerivative kappa beta g
        (Lattice.forwardDifference (asConfiguration q) i) := rfl

theorem bondVector_eq_free_add_error
    (qFree qExact : HilbertConfiguration N) :
    bondVector qExact = bondVector qFree + bondVector (qExact - qFree) := by
  ext i
  simp only [bondVector_apply, Lattice.forwardDifference_apply,
    asConfiguration, PiLp.sub_apply, PiLp.add_apply]
  ring

/-- Exact quadratic/cubic expansion of the residual bond vector. -/
theorem nonlinearBondDerivativeVector_eq_quadratic_add_cubic
    (kappa beta g : Real) (q : HilbertConfiguration N) :
    nonlinearBondDerivativeVector kappa beta g q =
      (kappa * g) • pointwiseMul (bondVector q) (bondVector q) +
        (beta * g ^ 2) •
          pointwiseMul (pointwiseMul (bondVector q) (bondVector q))
            (bondVector q) := by
  ext i
  simp [nonlinearBondDerivativeVector, nonlinearPotentialDerivative,
    pointwiseMul, bondVector]
  ring

/-- The exact bond residual has a volume-free `l2` bound after expansion
around a dilute free bond vector. -/
theorem norm_nonlinearBondDerivativeVector_le_dilute_free_error
    (kappa beta g : Real) (qFree qExact : HilbertConfiguration N)
    {a E R : Real} (ha : 0 <= a) (hR : 0 <= R)
    (hfreeSup : forall i, |bondVector qFree i| <= a)
    (hfreeL2 : ‖bondVector qFree‖ <= E)
    (herrorL2 : ‖bondVector (qExact - qFree)‖ <= R) :
    ‖nonlinearBondDerivativeVector kappa beta g qExact‖ <=
      |kappa| * |g| * (a * E + 2 * a * R + R ^ 2) +
        |beta| * g ^ 2 *
          (a ^ 2 * E + 3 * a ^ 2 * R + 3 * a * R ^ 2 + R ^ 3) := by
  let x := bondVector qFree
  let y := bondVector (qExact - qFree)
  have hsquare := norm_pointwiseSquare_add_le x y ha hR
    (by simpa [x] using hfreeSup) (by simpa [x] using hfreeL2)
      (by simpa [y] using herrorL2)
  have hcube := norm_pointwiseCube_add_le x y ha hR
    (by simpa [x] using hfreeSup) (by simpa [x] using hfreeL2)
      (by simpa [y] using herrorL2)
  rw [nonlinearBondDerivativeVector_eq_quadratic_add_cubic,
    bondVector_eq_free_add_error qFree qExact]
  change ‖(kappa * g) • pointwiseMul (x + y) (x + y) +
      (beta * g ^ 2) • pointwiseMul (pointwiseMul (x + y) (x + y))
        (x + y)‖ <= _
  calc
    _ <= ‖(kappa * g) • pointwiseMul (x + y) (x + y)‖ +
        ‖(beta * g ^ 2) •
          pointwiseMul (pointwiseMul (x + y) (x + y)) (x + y)‖ :=
      norm_add_le _ _
    _ = |kappa| * |g| * ‖pointwiseMul (x + y) (x + y)‖ +
        |beta| * g ^ 2 *
          ‖pointwiseMul (pointwiseMul (x + y) (x + y)) (x + y)‖ := by
      simp only [norm_smul, Real.norm_eq_abs, abs_mul, abs_pow, sq_abs]
    _ <= |kappa| * |g| * (a * E + 2 * a * R + R ^ 2) +
        |beta| * g ^ 2 *
          (a ^ 2 * E + 3 * a ^ 2 * R + 3 * a * R ^ 2 + R ^ 3) := by
      exact add_le_add
        (mul_le_mul_of_nonneg_left hsquare
          (mul_nonneg (abs_nonneg _) (abs_nonneg _)))
        (mul_le_mul_of_nonneg_left hcube
          (mul_nonneg (abs_nonneg _) (sq_nonneg g)))

/-- The explicit nonlinear physical gradient is the transpose periodic
difference applied to the residual bond vector. -/
theorem nonlinearPotentialGradient_eq_transposeDifferenceMatrix
    (kappa beta g : Real) (q : HilbertConfiguration N) :
    nonlinearPotentialGradient kappa beta g q =
      WithLp.toLp 2 (Matrix.mulVec
        (Matrix.transpose HarmonicModes.differenceMatrix)
        (asConfiguration (nonlinearBondDerivativeVector kappa beta g q))) := by
  ext j
  unfold nonlinearPotentialGradient nonlinearBondDerivativeVector
  simp only [WithLp.ofLp_sum, WithLp.ofLp_smul, Finset.sum_apply,
    Pi.smul_apply, smul_eq_mul, Matrix.mulVec, dotProduct,
    Matrix.transpose_apply, asConfiguration]
  apply Finset.sum_congr rfl
  intro i _hi
  rw [bondDirection_apply_eq_differenceMatrix]
  ring

/-- Sharp periodic `D transpose` control: the physical nonlinear gradient
costs a factor two, independent of `N`. -/
theorem norm_nonlinearPotentialGradient_le_two_mul_bondDerivative
    (kappa beta g : Real) (q : HilbertConfiguration N) :
    ‖nonlinearPotentialGradient kappa beta g q‖ <=
      2 * ‖nonlinearBondDerivativeVector kappa beta g q‖ := by
  let r : Lattice.Configuration N :=
    asConfiguration (nonlinearBondDerivativeVector kappa beta g q)
  have hsum := sum_sq_transposeDifferenceMatrix_mulVec_le_four_mul_sum_sq r
  have hsq : ‖nonlinearPotentialGradient kappa beta g q‖ ^ 2 <=
      (2 * ‖nonlinearBondDerivativeVector kappa beta g q‖) ^ 2 := by
    rw [nonlinearPotentialGradient_eq_transposeDifferenceMatrix,
      EuclideanSpace.real_norm_sq_eq, mul_pow,
      EuclideanSpace.real_norm_sq_eq]
    norm_num [r, asConfiguration] at hsum ⊢
    exact hsum
  nlinarith [norm_nonneg (nonlinearPotentialGradient kappa beta g q),
    norm_nonneg (nonlinearBondDerivativeVector kappa beta g q)]

/-- Main concrete force estimate.  The constant four is the product of the
sharp periodic-difference cost two and the frozen-support inverse-mass cost
two already proved in the canonical flow library.  There is no `N` factor. -/
theorem norm_transformedNonlinearForce_le_dilute_free_error
    (m : Lattice.PositiveMassConfig N)
    (hmass : forall i, (4 / 5 : Real) <= m.mass i)
    (kappa beta g : Real) (qFree qExact : HilbertConfiguration N)
    {a E R : Real} (ha : 0 <= a) (hR : 0 <= R)
    (hfreeSup : forall i, |bondVector qFree i| <= a)
    (hfreeL2 : ‖bondVector qFree‖ <= E)
    (herrorL2 : ‖bondVector (qExact - qFree)‖ <= R) :
    ‖transformedNonlinearForce m kappa beta g qExact‖ <=
      4 * (|kappa| * |g| * (a * E + 2 * a * R + R ^ 2) +
        |beta| * g ^ 2 *
          (a ^ 2 * E + 3 * a ^ 2 * R + 3 * a * R ^ 2 + R ^ 3)) := by
  have hmassTransform := norm_inverseSqrtMassTransform_le_two_mul m hmass
    (nonlinearPotentialGradient kappa beta g qExact)
  have hgradient := norm_nonlinearPotentialGradient_le_two_mul_bondDerivative
    kappa beta g qExact
  have hbond := norm_nonlinearBondDerivativeVector_le_dilute_free_error
    kappa beta g qFree qExact ha hR hfreeSup hfreeL2 herrorL2
  calc
    ‖transformedNonlinearForce m kappa beta g qExact‖ =
        ‖inverseSqrtMassTransform m
          (nonlinearPotentialGradient kappa beta g qExact)‖ := by
      simp [transformedNonlinearForce]
    _ <= 2 * ‖nonlinearPotentialGradient kappa beta g qExact‖ := hmassTransform
    _ <= 2 * (2 * ‖nonlinearBondDerivativeVector kappa beta g qExact‖) := by
      gcongr
    _ <= 2 * (2 * (|kappa| * |g| * (a * E + 2 * a * R + R ^ 2) +
        |beta| * g ^ 2 *
          (a ^ 2 * E + 3 * a ^ 2 * R + 3 * a * R ^ 2 + R ^ 3))) := by
      gcongr
    _ = _ := by ring

end

end ArchonPhysics.R32DiluteNonlinearStability
