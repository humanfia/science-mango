import FamilyStickyGrounding.Cinematic.FamilyStickyCinematicL32GlobalCoefficientRegimeSharpV1
import FamilyStickyGrounding.Cinematic.FamilyStickyCinematicL32Prop41StrictCurvatureOppositeEndpointRootsV1

set_option autoImplicit false

open Set

namespace FamilyStickyCinematicL32Prop41ActualOppositeEndpointRootEncCardV1

open FamilyStickyCinematicL32JetSeparationV1
open FamilyStickyCinematicL32LocalTangencyV1
open FamilyStickyCinematicL32RolleBridgeV1
open FamilyStickyCinematicL32GlobalCoefficientRegimeSharpV1
open FamilyStickyCinematicL32SublevelIntervalV1
open FamilyStickyCinematicL32Prop41StrictCurvatureOppositeEndpointRootsV1

/-!
# Actual endpoint-reversal root bound

The explicit global jet trichotomy is consumed branch by branch.  Uniform
value separation is contradicted by the IVT root, uniform first-jet
separation makes the trace strictly monotone, and uniform second-jet
separation invokes the independently proved strict-curvature theorem.
-/

theorem absFirstDerivative_rootSet_encard_le_one
    (h q : Real -> Real) {A B kappa : Real}
    (hAB : A <= B) (hkappa : 0 < kappa)
    (hderiv : forall z, z ∈ Icc A B -> HasDerivAt h (q z) z)
    (hqContinuous : ContinuousOn q (Icc A B))
    (hqLower : forall z, z ∈ Icc A B -> kappa <= |q z|) :
    {z | z ∈ Icc A B ∧ h z = 0}.encard <= 1 := by
  have hhContinuous : ContinuousOn h (Icc A B) :=
    HasDerivAt.continuousOn hderiv
  have hsubsingleton : {z | z ∈ Icc A B ∧ h z = 0}.Subsingleton := by
    rcases continuous_fixed_sign_of_abs_lower_on_Icc q hAB hkappa
        hqContinuous hqLower with hpositive | hnegative
    · have hstrict : StrictMonoOn h (Icc A B) := by
        apply strictMonoOn_of_hasDerivWithinAt_pos
          (convex_Icc A B) hhContinuous
        · intro z hz
          exact (hderiv z (interior_subset hz)).hasDerivWithinAt
        · intro z hz
          exact hkappa.trans_le (hpositive z (interior_subset hz))
      intro x hx y hy
      apply hstrict.injOn hx.1 hy.1
      rw [hx.2, hy.2]
    · have hstrict : StrictAntiOn h (Icc A B) := by
        apply strictAntiOn_of_hasDerivWithinAt_neg
          (convex_Icc A B) hhContinuous
        · intro z hz
          exact (hderiv z (interior_subset hz)).hasDerivWithinAt
        · intro z hz
          have := hnegative z (interior_subset hz)
          linarith
      intro x hx y hy
      apply hstrict.injOn hx.1 hy.1
      rw [hx.2, hy.2]
  exact encard_le_one_iff_subsingleton.mpr hsubsingleton

theorem traceFunction_oppositeEndpoint_rootSet_encard_le_one
    (f f1 f2 : Real -> Real) (da db dd : Real) {A B : Real}
    (hAB : A < B)
    (hcoefficient : 0 < coefficientDistance da db dd)
    (hleft : traceFunction f da db dd A < 0)
    (hright : 0 < traceFunction f da db dd B)
    (hparameter : forall z, z ∈ Icc A B -> |z| <= 1)
    (hft : forall z, z ∈ Icc A B -> |f z| <= 2)
    (hf1Lower : forall z, z ∈ Icc A B -> 1 <= |f1 z|)
    (hf1Upper : forall z, z ∈ Icc A B -> |f1 z| <= 2)
    (hf2 : forall z, z ∈ Icc A B -> |f2 z| <= 1 / 100)
    (hfDeriv : forall z, z ∈ Icc A B -> HasDerivAt f (f1 z) z)
    (hf1Deriv : forall z, z ∈ Icc A B -> HasDerivAt f1 (f2 z) z)
    (hf2Continuous : ContinuousOn f2 (Icc A B)) :
    {z | z ∈ Icc A B ∧ traceFunction f da db dd z = 0}.encard <= 1 := by
  have htraceDeriv : forall z, z ∈ Icc A B ->
      HasDerivAt (traceFunction f da db dd)
        (traceFirstDerivative f f1 db dd z) z := by
    intro z hz
    exact hasDerivAt_traceFunction f f1 da db dd z (hfDeriv z hz)
  have hfirstDeriv : forall z, z ∈ Icc A B ->
      HasDerivAt (traceFirstDerivative f f1 db dd)
        (traceSecondDerivative f1 f2 db dd z) z := by
    intro z hz
    exact hasDerivAt_traceFirstDerivative f f1 f2 db dd z
      (hfDeriv z hz) (hf1Deriv z hz)
  have hf1Continuous : ContinuousOn f1 (Icc A B) :=
    HasDerivAt.continuousOn hf1Deriv
  have hsecondContinuous :
      ContinuousOn (traceSecondDerivative f1 f2 db dd) (Icc A B) := by
    unfold traceSecondDerivative traceJet2
    fun_prop
  rcases global_value_or_first_or_second_jet_separation_sharp da db dd with
      hvalue | hfirst | hsecond
  · have htraceContinuous :
        ContinuousOn (traceFunction f da db dd) (Icc A B) :=
      HasDerivAt.continuousOn htraceDeriv
    obtain ⟨z, hz, hz0⟩ := intermediate_value_Icc hAB.le htraceContinuous
      (show (0 : Real) ∈ Icc (traceFunction f da db dd A)
          (traceFunction f da db dd B) from
        ⟨le_of_lt hleft, le_of_lt hright⟩)
    have hlarge : coefficientDistance da db dd / 3 <=
        |traceFunction f da db dd z| := by
      simpa [traceFunction] using
        hvalue (f z) z (hparameter z hz) (hft z hz)
    rw [hz0, abs_zero] at hlarge
    exfalso
    nlinarith
  · have hkappa : 0 < coefficientDistance da db dd / 12 := by
      positivity
    apply absFirstDerivative_rootSet_encard_le_one
      (traceFunction f da db dd) (traceFirstDerivative f f1 db dd)
      hAB.le hkappa htraceDeriv
      (HasDerivAt.continuousOn hfirstDeriv)
    intro z hz
    simpa [traceFirstDerivative] using
      hfirst (f z) (f1 z) z (hparameter z hz) (hft z hz)
        (hf1Lower z hz) (hf1Upper z hz)
  · have hkappa : 0 < coefficientDistance da db dd / 45 := by
      positivity
    apply strictCurvature_oppositeEndpoint_rootSet_encard_le_one
      (traceFunction f da db dd) (traceFirstDerivative f f1 db dd)
      (traceSecondDerivative f1 f2 db dd)
      hAB hkappa hleft hright htraceDeriv hfirstDeriv hsecondContinuous
    intro z hz
    exact le_of_lt (by
      simpa [traceSecondDerivative] using
        hsecond (f1 z) (f2 z) z (hparameter z hz)
          (hf1Lower z hz) (hf2 z hz))

#print axioms absFirstDerivative_rootSet_encard_le_one
#print axioms traceFunction_oppositeEndpoint_rootSet_encard_le_one

end FamilyStickyCinematicL32Prop41ActualOppositeEndpointRootEncCardV1
