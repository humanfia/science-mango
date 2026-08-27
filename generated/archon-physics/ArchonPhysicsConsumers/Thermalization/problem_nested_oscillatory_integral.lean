import ArchonPhysics.NestedOscillatoryIntegral

/-!
# Consumer: nested finite-time oscillatory coefficients

These endpoints expose the exact triangular coefficient needed by a
quadratic-after-quadratic second-Picard character expansion.  They retain
all finite-time phases and treat resonant mismatches without division.  No
large-time, kinetic, collision, or FGR identification is made.
-/

namespace ArchonPhysicsConsumers.Thermalization.NestedOscillatoryIntegral

open MeasureTheory
open ArchonPhysics.NestedOscillatoryIntegral
open ArchonPhysics.NonresonantOscillatoryGain
open scoped Interval

noncomputable section

/-- Consumer endpoint for the exact triangular iterated-integral form. -/
theorem problem_nestedOscillatoryIntegral_iterated_exact
    (deltaOut deltaIn time : Real) :
    nestedOscillatoryIntegral deltaOut deltaIn time =
      ∫ s in (0 : Real)..time,
        ∫ u in (0 : Real)..s,
          Complex.exp ((Complex.I * deltaOut) * s) *
            Complex.exp ((Complex.I * deltaIn) * u) := by
  exact nestedOscillatoryIntegral_eq_iteratedIntegral
    deltaOut deltaIn time

/-- Consumer endpoint for the nonzero-inner-mismatch divided difference. -/
theorem problem_nestedOscillatoryIntegral_nonzeroInner_exact
    {deltaOut deltaIn time : Real} (hdeltaIn : deltaIn ≠ 0) :
    nestedOscillatoryIntegral deltaOut deltaIn time =
      (oscillatoryIntegral (deltaOut + deltaIn) time -
        oscillatoryIntegral deltaOut time) /
          (Complex.I * deltaIn) := by
  exact nestedOscillatoryIntegral_eq_sub_div hdeltaIn

/-- Consumer endpoint for the division-free inner- and outer-resonant
normal forms. -/
theorem problem_nestedOscillatoryIntegral_singleResonances_exact
    (deltaOut deltaIn time : Real) :
    nestedOscillatoryIntegral deltaOut 0 time =
        ∫ s in (0 : Real)..time,
          Complex.exp ((Complex.I * deltaOut) * s) * (s : Complex) ∧
      nestedOscillatoryIntegral 0 deltaIn time =
        ∫ s in (0 : Real)..time, oscillatoryIntegral deltaIn s := by
  exact ⟨nestedOscillatoryIntegral_inner_zero deltaOut time,
    nestedOscillatoryIntegral_outer_zero deltaIn time⟩

/-- Consumer endpoint for exact double and combined resonance values. -/
theorem problem_nestedOscillatoryIntegral_resonantValues_exact
    {deltaOut deltaIn time : Real} (hdeltaIn : deltaIn ≠ 0)
    (htotal : deltaOut + deltaIn = 0) :
    nestedOscillatoryIntegral 0 0 time =
          ((time ^ 2 / 2 : Real) : Complex) ∧
      nestedOscillatoryIntegral deltaOut deltaIn time =
        ((time : Complex) - oscillatoryIntegral deltaOut time) /
          (Complex.I * deltaIn) := by
  exact ⟨nestedOscillatoryIntegral_zero_zero time,
    nestedOscillatoryIntegral_total_zero_eq_sub_div hdeltaIn htotal⟩

/-- Consumer endpoint for continuity, finite-interval integrability, and the
exact endpoint derivative. -/
theorem problem_nestedOscillatoryIntegral_regularity
    (deltaOut deltaIn : Real) :
    Continuous (nestedOscillatoryIntegral deltaOut deltaIn) ∧
      (∀ a b : Real,
        IntervalIntegrable (fun s : Real ↦
          Complex.exp ((Complex.I * deltaOut) * s) *
            oscillatoryIntegral deltaIn s) volume a b) ∧
      (∀ time : Real,
        HasDerivAt (nestedOscillatoryIntegral deltaOut deltaIn)
          (Complex.exp ((Complex.I * deltaOut) * time) *
            oscillatoryIntegral deltaIn time) time) := by
  exact ⟨continuous_nestedOscillatoryIntegral deltaOut deltaIn,
    intervalIntegrable_nestedOscillatoryIntegrand deltaOut deltaIn,
    hasDerivAt_nestedOscillatoryIntegral deltaOut deltaIn⟩

#print axioms problem_nestedOscillatoryIntegral_iterated_exact
#print axioms problem_nestedOscillatoryIntegral_nonzeroInner_exact
#print axioms problem_nestedOscillatoryIntegral_singleResonances_exact
#print axioms problem_nestedOscillatoryIntegral_resonantValues_exact
#print axioms problem_nestedOscillatoryIntegral_regularity

end

end ArchonPhysicsConsumers.Thermalization.NestedOscillatoryIntegral
