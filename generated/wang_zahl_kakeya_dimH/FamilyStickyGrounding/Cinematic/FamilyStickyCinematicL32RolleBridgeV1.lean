import FamilyStickyGrounding.Cinematic.FamilyStickyCinematicL32JetSeparationV1
import Mathlib.Analysis.Calculus.LocalExtr.Rolle
import Mathlib.Analysis.Calculus.Deriv.Mul

set_option autoImplicit false

open Set

namespace FamilyStickyCinematicL32RolleBridgeV1

open FamilyStickyCinematicL32JetSeparationV1

/-!
# Rolle bridges for the cinematic trace

Provenance: Pramanik--Yang--Zahl, arXiv:2207.02259v3, Lemma 3.6.
That lemma uses Rolle's theorem twice: three zeros of a curve difference
produce two zeros of its first derivative, which in turn produce a zero of
its second derivative.

This module instantiates Mathlib's `exists_hasDerivAt_eq_zero`; derivative
zeros are conclusions, never callbacks.  It also verifies that the algebraic
jets from `FamilyStickyCinematicL32JetSeparationV1` are the actual first and
second derivatives of the Wang--Zahl trace.
-/

/-- The explicit Wang--Zahl coefficient-difference trace. -/
def traceFunction (f : Real -> Real) (da db dd : Real) (t : Real) : Real :=
  traceJet0 da db dd (f t) t

/-- Its candidate first derivative. -/
def traceFirstDerivative (f f1 : Real -> Real)
    (db dd : Real) (t : Real) : Real :=
  traceJet1 db dd (f t) (f1 t) t

/-- Its candidate second derivative. -/
def traceSecondDerivative (f1 f2 : Real -> Real)
    (db dd : Real) (t : Real) : Real :=
  traceJet2 db dd (f1 t) (f2 t) t

/-- The first algebraic jet is the actual derivative of the trace. -/
theorem hasDerivAt_traceFunction
    (f f1 : Real -> Real) (da db dd t : Real)
    (hf : HasDerivAt f (f1 t) t) :
    HasDerivAt (traceFunction f da db dd)
      (traceFirstDerivative f f1 db dd t) t := by
  change HasDerivAt (fun s => da + db * f s + dd * s * f s)
    (db * f1 t + dd * (f t + t * f1 t)) t
  have hlinear : HasDerivAt (fun s => db * f s) (db * f1 t) t :=
    hf.const_mul db
  have hparameter : HasDerivAt (fun s => s * f s)
      (f t + t * f1 t) t := by
    convert! (hasDerivAt_id t).mul hf using 1
    simp
  have hquadratic : HasDerivAt (fun s => dd * s * f s)
      (dd * (f t + t * f1 t)) t := by
    convert! hparameter.const_mul dd using 1
    funext s
    ring
  convert! (hlinear.add hquadratic).const_add da using 1
  funext s
  simp only [Pi.add_apply]
  ring

/-- The second algebraic jet is the actual derivative of the first jet. -/
theorem hasDerivAt_traceFirstDerivative
    (f f1 f2 : Real -> Real) (db dd t : Real)
    (hf : HasDerivAt f (f1 t) t)
    (hf1 : HasDerivAt f1 (f2 t) t) :
    HasDerivAt (traceFirstDerivative f f1 db dd)
      (traceSecondDerivative f1 f2 db dd t) t := by
  change HasDerivAt (fun s => db * f1 s + dd * (f s + s * f1 s))
    (db * f2 t + dd * (2 * f1 t + t * f2 t)) t
  have hlinear : HasDerivAt (fun s => db * f1 s) (db * f2 t) t :=
    hf1.const_mul db
  have hinside : HasDerivAt (fun s => f s + s * f1 s)
      (2 * f1 t + t * f2 t) t := by
    convert! hf.add ((hasDerivAt_id t).mul hf1) using 1
    simp [two_mul, add_assoc]
  have hquadratic : HasDerivAt (fun s => dd * (f s + s * f1 s))
      (dd * (2 * f1 t + t * f2 t)) t :=
    hinside.const_mul dd
  convert! hlinear.add hquadratic using 1

/-- A thin `HasDerivAt` adapter to Mathlib's Rolle theorem. -/
theorem exists_derivative_zero_between_zeros
    (h h1 : Real -> Real) {a b : Real}
    (hab : a < b)
    (hderiv : forall x, x ∈ Icc a b -> HasDerivAt h (h1 x) x)
    (ha : h a = 0) (hb : h b = 0) :
    ∃ x ∈ Ioo a b, h1 x = 0 := by
  apply exists_hasDerivAt_eq_zero hab
      (HasDerivAt.continuousOn hderiv) (ha.trans hb.symm)
  intro x hx
  exact hderiv x (Ioo_subset_Icc_self hx)

/-- Three ordered zeros produce two ordered first-derivative zeros. -/
theorem two_derivative_zeros_between_three_zeros
    (h h1 : Real -> Real) {a b c : Real}
    (hab : a < b) (hbc : b < c)
    (hderiv : forall x, x ∈ Icc a c -> HasDerivAt h (h1 x) x)
    (ha : h a = 0) (hb : h b = 0) (hc : h c = 0) :
    ∃ x ∈ Ioo a b, ∃ y ∈ Ioo b c,
      h1 x = 0 ∧ h1 y = 0 := by
  obtain ⟨x, hx, hx0⟩ := exists_derivative_zero_between_zeros
    h h1 hab
    (fun u hu => hderiv u ⟨hu.1, hu.2.trans (le_of_lt hbc)⟩) ha hb
  obtain ⟨y, hy, hy0⟩ := exists_derivative_zero_between_zeros
    h h1 hbc
    (fun u hu => hderiv u ⟨(le_of_lt hab).trans hu.1, hu.2⟩) hb hc
  exact ⟨x, hx, y, hy, hx0, hy0⟩

/-- The exact twice-iterated Rolle bridge used in PYZ Lemma 3.6. -/
theorem second_derivative_zero_between_three_zeros
    (h h1 h2 : Real -> Real) {a b c : Real}
    (hab : a < b) (hbc : b < c)
    (hderiv : forall x, x ∈ Icc a c -> HasDerivAt h (h1 x) x)
    (hderiv1 : forall x, x ∈ Icc a c -> HasDerivAt h1 (h2 x) x)
    (ha : h a = 0) (hb : h b = 0) (hc : h c = 0) :
    ∃ x ∈ Ioo a b, ∃ y ∈ Ioo b c, ∃ z ∈ Ioo x y,
      h1 x = 0 ∧ h1 y = 0 ∧ h2 z = 0 := by
  obtain ⟨x, hx, y, hy, hx0, hy0⟩ :=
    two_derivative_zeros_between_three_zeros
      h h1 hab hbc hderiv ha hb hc
  have hxy : x < y := hx.2.trans hy.1
  obtain ⟨z, hz, hz0⟩ := exists_derivative_zero_between_zeros
    h1 h2 hxy
    (fun u hu => hderiv1 u
      ⟨(le_of_lt hx.1).trans hu.1, hu.2.trans (le_of_lt hy.2)⟩)
    hx0 hy0
  exact ⟨x, hx, y, hy, z, hz, hx0, hy0, hz0⟩

#print axioms hasDerivAt_traceFunction
#print axioms hasDerivAt_traceFirstDerivative
#print axioms exists_derivative_zero_between_zeros
#print axioms two_derivative_zeros_between_three_zeros
#print axioms second_derivative_zero_between_three_zeros

end FamilyStickyCinematicL32RolleBridgeV1
