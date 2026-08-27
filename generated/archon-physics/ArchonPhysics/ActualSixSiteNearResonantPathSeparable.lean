import Mathlib

/-!
# Separability along the six-site near-resonant path

This file records an exact Bezout certificate for the quintic factor that
occurs on the one-parameter six-site path.  The certificate proves
separability at every strictly positive value of the squared path parameter.
It also proves that adjoining the structural zero mode preserves
separability.
-/

namespace ArchonPhysics.ActualSixSiteNearResonantPathSeparable

open Polynomial

noncomputable section

/-- The nonzero-mode quintic on the six-site near-resonant path. -/
def nearResonantPathQuintic (u : Real) : Real[X] :=
  C (1 - u) * X ^ 5 +
  C (-12 + 8 * u) * X ^ 4 +
  C (54 - 21 * u) * X ^ 3 +
  C (-112 + 20 * u) * X ^ 2 +
  C (105 - 5 * u) * X -
  C 36

/-- The quotient after removing the constant term from the path quintic. -/
def nearResonantPathQuinticTail (u : Real) : Real[X] :=
  C (1 - u) * X ^ 4 +
  C (-12 + 8 * u) * X ^ 3 +
  C (54 - 21 * u) * X ^ 2 +
  C (-112 + 20 * u) * X +
  C (105 - 5 * u)

/-- The scalar on the right-hand side of the exact Bezout identity. -/
def nearResonantPathDiscriminantCertificate (u : Real) : Real :=
  2 * u *
    (625 * u ^ 6 + 34500 * u ^ 5 + 86490 * u ^ 4 +
      93960 * u ^ 3 + 37233 * u ^ 2 + 1080 * u + 1296)

/-- First coefficient in the exact Bezout certificate. -/
def nearResonantPathBezoutA (u : Real) : Real[X] :=
  C (1625 * u ^ 6 + 35425 * u ^ 5 + 11385 * u ^ 4 - 21795 * u ^ 3 -
      26190 * u ^ 2 + 630 * u - 1080) * X ^ 3 +
  C (-9150 * u ^ 6 - 166820 * u ^ 5 + 60786 * u ^ 4 + 270780 * u ^ 3 +
      206784 * u ^ 2 - 1692 * u + 8208) * X ^ 2 +
  C (14350 * u ^ 6 + 164850 * u ^ 5 - 473865 * u ^ 4 - 881262 * u ^ 3 -
      511551 * u ^ 2 - 2610 * u - 19656) * X +
  C (-5500 * u ^ 6 + 26420 * u ^ 5 + 558090 * u ^ 4 + 811314 * u ^ 3 +
      405360 * u ^ 2 + 5508 * u + 15120)

/-- Second coefficient in the exact Bezout certificate. -/
def nearResonantPathBezoutB (u : Real) : Real[X] :=
  C (-325 * u ^ 6 - 7085 * u ^ 5 - 2277 * u ^ 4 + 4359 * u ^ 3 +
      5238 * u ^ 2 - 126 * u + 216) * X ^ 4 +
  C (2350 * u ^ 6 + 44440 * u ^ 5 - 14442 * u ^ 4 - 68880 * u ^ 3 -
      54000 * u ^ 2 + 468 * u - 2160) * X ^ 3 +
  C (-5200 * u ^ 6 - 70890 * u ^ 5 + 169335 * u ^ 4 + 321786 * u ^ 3 +
      194319 * u ^ 2 + 738 * u + 7560) * X ^ 2 +
  C (3500 * u ^ 6 + 3860 * u ^ 5 - 375930 * u ^ 4 - 551646 * u ^ 3 -
      284724 * u ^ 2 - 3564 * u - 10800) * X +
  C (-250 * u ^ 6 + 20550 * u ^ 5 + 206730 * u ^ 4 + 285498 * u ^ 3 +
      139104 * u ^ 2 + 2160 * u + 5184)

/-- The supplied integer certificate is an exact polynomial identity. -/
theorem nearResonantPath_bezout_identity (u : Real) :
    nearResonantPathBezoutA u * nearResonantPathQuintic u +
        nearResonantPathBezoutB u * (nearResonantPathQuintic u).derivative =
      C (nearResonantPathDiscriminantCertificate u) := by
  set_option maxRecDepth 1000000 in
    simp [nearResonantPathBezoutA, nearResonantPathBezoutB,
      nearResonantPathQuintic, nearResonantPathDiscriminantCertificate, Polynomial.C_ofNat]
    ring

theorem nearResonantPathDiscriminantCertificate_pos {u : Real} (hu : 0 < u) :
    0 < nearResonantPathDiscriminantCertificate u := by
  unfold nearResonantPathDiscriminantCertificate
  positivity

/-- For positive squared path parameter, the quintic has no repeated root. -/
theorem nearResonantPathQuintic_separable {u : Real} (hu : 0 < u) :
    (nearResonantPathQuintic u).Separable := by
  rw [Polynomial.separable_def']
  let d := nearResonantPathDiscriminantCertificate u
  have hd : d ≠ 0 := ne_of_gt (nearResonantPathDiscriminantCertificate_pos hu)
  refine ⟨C d⁻¹ * nearResonantPathBezoutA u,
    C d⁻¹ * nearResonantPathBezoutB u, ?_⟩
  calc
    (C d⁻¹ * nearResonantPathBezoutA u) * nearResonantPathQuintic u +
          (C d⁻¹ * nearResonantPathBezoutB u) *
            (nearResonantPathQuintic u).derivative =
        C d⁻¹ *
          (nearResonantPathBezoutA u * nearResonantPathQuintic u +
            nearResonantPathBezoutB u *
              (nearResonantPathQuintic u).derivative) := by ring
    _ = C d⁻¹ * C d := by
      rw [nearResonantPath_bezout_identity]
    _ = 1 := by
      rw [← C_mul]
      simp [hd]

/-- The zero mode and the quintic are coprime because the latter has constant
coefficient `-36`. -/
theorem X_isCoprime_nearResonantPathQuintic (u : Real) :
    IsCoprime (X : Real[X]) (nearResonantPathQuintic u) := by
  have hunit : IsUnit (C (-36 : Real) : Real[X]) := by
    rw [Polynomial.isUnit_C]
    exact isUnit_iff_ne_zero.mpr (by norm_num)
  have hconstant : IsCoprime (X : Real[X]) (C (-36 : Real)) := by
    have hcoprime :
        IsCoprime (X : Real[X]) (C (-36 : Real) * 1) :=
      (isCoprime_mul_unit_left_right hunit (X : Real[X]) (1 : Real[X])).mpr
        isCoprime_one_right
    simpa using hcoprime
  have hq :
      nearResonantPathQuintic u =
        C (-36 : Real) + X * nearResonantPathQuinticTail u := by
    simp [nearResonantPathQuintic, nearResonantPathQuinticTail, Polynomial.C_ofNat]
    ring
  rw [hq]
  exact hconstant.add_mul_left_right (nearResonantPathQuinticTail u)

/-- The full characteristic polynomial, including its structural zero mode,
is separable for every positive squared path parameter. -/
theorem X_mul_nearResonantPathQuintic_separable {u : Real} (hu : 0 < u) :
    (X * nearResonantPathQuintic u).Separable :=
  Polynomial.separable_X.mul (nearResonantPathQuintic_separable hu)
    (X_isCoprime_nearResonantPathQuintic u)

/-- Parameterization by a nonzero real path coordinate `t`, with `u = t²`. -/
theorem nearResonantPathQuintic_separable_sq {t : Real} (ht : t ≠ 0) :
    (nearResonantPathQuintic (t ^ 2)).Separable :=
  nearResonantPathQuintic_separable (sq_pos_of_ne_zero ht)

/-- The full polynomial is separable at every nonzero real path coordinate. -/
theorem X_mul_nearResonantPathQuintic_separable_sq {t : Real} (ht : t ≠ 0) :
    (X * nearResonantPathQuintic (t ^ 2)).Separable :=
  X_mul_nearResonantPathQuintic_separable (sq_pos_of_ne_zero ht)

end

end ArchonPhysics.ActualSixSiteNearResonantPathSeparable
