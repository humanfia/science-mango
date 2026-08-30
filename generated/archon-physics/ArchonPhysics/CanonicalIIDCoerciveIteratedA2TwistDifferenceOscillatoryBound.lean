import ArchonPhysics.CanonicalIIDCoerciveIteratedA2TwistRenormalizedRemainder
import ArchonPhysics.PhyslibFPUTActualHaarSecondOrderEnergyDrift

/-!
# Quantitative oscillatory bounds for the iterated-A2 twist difference

The phase-renormalized iterated/iterated remainder is controlled by a
difference of two triangular oscillatory integrals.  This module gives its
exact divided-difference form, including a continuous integral extension
through resonant inner mismatches, and separates what follows from an
ordinary good-mismatch cutoff from the additional cancellation that would
be needed to close the kinetic `g^4` remainder.

The inner-branch twist preserves the total mismatch `outer + inner`, but it
does not preserve either local mismatch separately.  On a sector where the
outer, inner, twisted outer, twisted inner, and common total mismatches all
have size at least `gamma`, the unconditional pointwise estimate is

`norm (nested - nestedTwist) <= 8 / gamma^2`.

Thus the twist grouping alone does not supply an extra cutoff power.  The
exact common-denominator numerator is exposed below.  If a later
oscillatory, time-ordering, or probabilistic argument proves that this
numerator is `O(gamma)`, then the difference improves to `O(1 / gamma)`;
its square has effective loss two and the existing `alpha = 5/4` cutoff
closes.  No such numerator gain is assumed unconditionally here.
-/

namespace ArchonPhysics.CanonicalIIDCoerciveIteratedA2TwistDifferenceOscillatoryBound

open scoped BigOperators Interval

open ArchonPhysics
open ArchonPhysics.CanonicalIIDCoerciveCorrectedStructuralRankRPAAdapter
open ArchonPhysics.CanonicalIIDCoerciveIteratedA2TwistRenormalizedRemainder
open ArchonPhysics.CanonicalIIDCoerciveMatchedDenominatorForestRank
open ArchonPhysics.CanonicalIIDCoerciveRegularGoodCutoffExponentBalance
open ArchonPhysics.FiniteSecondOrderCharacterFamilyExpansion
open ArchonPhysics.FreeFPUTTadpoleFeedbackCancellation
open ArchonPhysics.FreeFPUTMismatchPhaseExpansion
open ArchonPhysics.ModalPhaseMismatch
open ArchonPhysics.NestedOscillatoryIntegral
open ArchonPhysics.NonresonantOscillatoryGain
open ArchonPhysics.PhyslibFPUTActualHaarSecondOrderEnergyDrift
open ArchonPhysics.PhyslibFPUTActualHaarPostSecondPicardDecomposition
open ArchonPhysics.PhyslibFPUTIteratedQuadraticSecondPicardCharacterFamily

noncomputable section

/-! ## Exact form and continuous extension -/

/-- The elementary twist difference for two ordered two-layer mismatch
histories. -/
def nestedTwistDifference
    (outer inner outerTwist innerTwist time : Real) : Complex :=
  nestedOscillatoryIntegral outer inner time -
    nestedOscillatoryIntegral outerTwist innerTwist time

/-- A division-free closed form.  At an inner resonance it uses the exact
continuous integral extension; away from resonance it is the usual divided
difference. -/
def nestedOscillatoryClosedForm
    (outer inner time : Real) : Complex :=
  if inner = 0 then
    ∫ s in (0 : Real)..time,
      Complex.exp ((Complex.I * outer) * s) * (s : Complex)
  else
    (oscillatoryIntegral (outer + inner) time -
      oscillatoryIntegral outer time) / (Complex.I * inner)

/-- The division-free closed form agrees with the triangular integral at
every mismatch, including exact inner resonance. -/
theorem nestedOscillatoryClosedForm_eq
    (outer inner time : Real) :
    nestedOscillatoryClosedForm outer inner time =
      nestedOscillatoryIntegral outer inner time := by
  unfold nestedOscillatoryClosedForm
  by_cases hinner : inner = 0
  · rw [if_pos hinner, hinner]
    exact (nestedOscillatoryIntegral_inner_zero outer time).symm
  · rw [if_neg hinner]
    exact (nestedOscillatoryIntegral_eq_sub_div hinner).symm

/-- The preceding resonant/nonresonant closed form is continuous in the
time endpoint. -/
theorem continuous_nestedOscillatoryClosedForm_time
    (outer inner : Real) :
    Continuous (nestedOscillatoryClosedForm outer inner) := by
  have heq : nestedOscillatoryClosedForm outer inner =
      nestedOscillatoryIntegral outer inner := by
    funext time
    exact nestedOscillatoryClosedForm_eq outer inner time
  rw [heq]
  exact continuous_nestedOscillatoryIntegral outer inner

/-- The one-step integral is jointly continuous in its mismatch and time
endpoint.  This is the analytic reason that the integral representation is
the continuous extension of the quotient through a zero denominator. -/
theorem continuous_oscillatoryIntegral_joint :
    Continuous (fun p : Real × Real =>
      oscillatoryIntegral p.1 p.2) := by
  let rescaled : Real × Real → Complex := fun p =>
    (p.2 : Complex) *
      ∫ u in (0 : Real)..1,
        Complex.exp ((Complex.I * p.1) * (u * p.2))
  have hrescaled : Continuous rescaled := by
    unfold rescaled
    apply (Complex.continuous_ofReal.comp continuous_snd).mul
    exact intervalIntegral.continuous_parametric_intervalIntegral_of_continuous'
      (f := fun p : Real × Real => fun u : Real =>
        Complex.exp ((Complex.I * p.1) * (u * p.2)))
      (by fun_prop) 0 1
  have heq : (fun p : Real × Real => oscillatoryIntegral p.1 p.2) =
      rescaled := by
    funext p
    rcases p with ⟨omega, time⟩
    unfold rescaled
    change oscillatoryIntegral omega time =
      (time : Complex) *
        ∫ u in (0 : Real)..1,
          Complex.exp ((Complex.I * omega) * ((u : Complex) * time))
    by_cases htime : time = 0
    · subst time
      simp [oscillatoryIntegral]
    · unfold oscillatoryIntegral
      have hchange := intervalIntegral.integral_comp_mul_right
        (fun s : Real => Complex.exp ((Complex.I * omega) * s)) htime
        (a := 0) (b := 1)
      simp only [zero_mul, one_mul] at hchange
      have hchangePrime :
          (∫ u in (0 : Real)..1,
              Complex.exp ((Complex.I * omega) * ((u : Complex) * time))) =
            time⁻¹ • ∫ s in (0 : Real)..time,
              Complex.exp ((Complex.I * omega) * s) := by
        simpa [Complex.ofReal_mul] using hchange
      rw [hchangePrime]
      simp [htime]
  rw [heq]
  exact hrescaled

/-- For every fixed time, the triangular integral is jointly continuous in
the outer and inner mismatches, including both resonant hyperplanes. -/
theorem continuous_nestedOscillatoryIntegral_mismatches (time : Real) :
    Continuous (fun p : Real × Real =>
      nestedOscillatoryIntegral p.1 p.2 time) := by
  unfold nestedOscillatoryIntegral
  exact intervalIntegral.continuous_parametric_intervalIntegral_of_continuous'
    (f := fun p : Real × Real => fun s : Real =>
      Complex.exp ((Complex.I * p.1) * s) *
        oscillatoryIntegral p.2 s)
    ((by fun_prop : Continuous (fun q : (Real × Real) × Real =>
        Complex.exp ((Complex.I * q.1.1) * q.2))).mul
      (continuous_oscillatoryIntegral_joint.comp
        ((continuous_fst.snd).prodMk continuous_snd))) 0 time

/-- The displayed resonant/nonresonant closed form itself is jointly
continuous across both mismatch variables. -/
theorem continuous_nestedOscillatoryClosedForm_mismatches (time : Real) :
    Continuous (fun p : Real × Real =>
      nestedOscillatoryClosedForm p.1 p.2 time) := by
  have heq : (fun p : Real × Real =>
      nestedOscillatoryClosedForm p.1 p.2 time) =
      fun p : Real × Real =>
        nestedOscillatoryIntegral p.1 p.2 time := by
    funext p
    exact nestedOscillatoryClosedForm_eq p.1 p.2 time
  rw [heq]
  exact continuous_nestedOscillatoryIntegral_mismatches time

/-- Consequently the twist difference is jointly continuous in all four
local mismatches at fixed time. -/
theorem continuous_nestedTwistDifference_mismatches (time : Real) :
    Continuous (fun p : (Real × Real) × (Real × Real) =>
      nestedTwistDifference p.1.1 p.1.2 p.2.1 p.2.2 time) := by
  unfold nestedTwistDifference
  exact (continuous_nestedOscillatoryIntegral_mismatches time).comp
      continuous_fst |>.sub
    ((continuous_nestedOscillatoryIntegral_mismatches time).comp
      continuous_snd)

/-! ## Common-total exact numerator -/

/-- Numerator obtained after putting two divided differences with the same
total mismatch over a common denominator. -/
def nestedTwistCancellationNumerator
    (outer inner outerTwist innerTwist time : Real) : Complex :=
  (oscillatoryIntegral (outer + inner) time -
      oscillatoryIntegral outer time) * (Complex.I * innerTwist) -
    (oscillatoryIntegral (outer + inner) time -
      oscillatoryIntegral outerTwist time) * (Complex.I * inner)

/-- Exact common-denominator formula away from the two inner resonances.
The only use of equality of total mismatches is replacing the twisted total
by the common untwisted total in the second numerator. -/
theorem nestedTwistDifference_eq_numerator_div
    {outer inner outerTwist innerTwist time : Real}
    (hinner : inner ≠ 0) (hinnerTwist : innerTwist ≠ 0)
    (htotal : outer + inner = outerTwist + innerTwist) :
    nestedTwistDifference outer inner outerTwist innerTwist time =
      nestedTwistCancellationNumerator
          outer inner outerTwist innerTwist time /
        ((Complex.I * inner) * (Complex.I * innerTwist)) := by
  unfold nestedTwistDifference nestedTwistCancellationNumerator
  rw [nestedOscillatoryIntegral_eq_sub_div hinner,
    nestedOscillatoryIntegral_eq_sub_div hinnerTwist, ← htotal]
  have hdenom : (Complex.I * (inner : Complex)) ≠ 0 :=
    mul_ne_zero Complex.I_ne_zero (Complex.ofReal_ne_zero.mpr hinner)
  have hdenomTwist : (Complex.I * (innerTwist : Complex)) ≠ 0 :=
    mul_ne_zero Complex.I_ne_zero
      (Complex.ofReal_ne_zero.mpr hinnerTwist)
  have hinnerComplex : (inner : Complex) ≠ 0 :=
    Complex.ofReal_ne_zero.mpr hinner
  have hinnerTwistComplex : (innerTwist : Complex) ≠ 0 :=
    Complex.ofReal_ne_zero.mpr hinnerTwist
  field_simp [hdenom, hdenomTwist, hinnerComplex,
    hinnerTwistComplex, Complex.I_ne_zero]

/-! ## General nonresonant estimates -/

/-- Uniform finite-time control valid on the resonant and nonresonant
sectors alike.  It is deliberately used on the bad-cutoff part, where no
inverse-gap estimate is available. -/
theorem norm_nestedOscillatoryIntegral_le_abs_time_sq
    (outer inner time : Real) :
    ‖nestedOscillatoryIntegral outer inner time‖ ≤ |time| ^ 2 := by
  unfold nestedOscillatoryIntegral
  calc
    ‖∫ s in (0 : Real)..time,
        Complex.exp ((Complex.I * outer) * s) *
          oscillatoryIntegral inner s‖ ≤ |time| * |time - 0| := by
      apply intervalIntegral.norm_integral_le_of_norm_le_const
      intro s hs
      have hsabs : |s| ≤ |time| := by
        rcases Set.mem_uIoc.mp hs with hpos | hneg
        · have hs0 : 0 ≤ s := le_of_lt hpos.1
          have ht0 : 0 ≤ time := hs0.trans hpos.2
          simpa [abs_of_nonneg hs0, abs_of_nonneg ht0] using hpos.2
        · have hs0 : s ≤ 0 := hneg.2
          have ht0 : time ≤ 0 := (le_of_lt hneg.1).trans hs0
          rw [abs_of_nonpos hs0, abs_of_nonpos ht0]
          linarith
      have hexp :
          ‖Complex.exp ((Complex.I * outer) * s)‖ = 1 := by
        rw [show (Complex.I * (outer : Complex)) * (s : Complex) =
            Complex.I * ((outer * s : Real) : Complex) by push_cast; ring]
        exact Complex.norm_exp_I_mul_ofReal (outer * s)
      rw [norm_mul, hexp, one_mul]
      exact (norm_oscillatoryIntegral_le_abs_time inner s).trans hsabs
    _ = |time| ^ 2 := by simp [pow_two]

/-- The twist difference is always bounded by twice the finite triangular
volume, with no gap assumptions. -/
theorem norm_nestedTwistDifference_le_two_mul_abs_time_sq
    (outer inner outerTwist innerTwist time : Real) :
    ‖nestedTwistDifference outer inner outerTwist innerTwist time‖ ≤
      2 * |time| ^ 2 := by
  unfold nestedTwistDifference
  calc
    ‖nestedOscillatoryIntegral outer inner time -
        nestedOscillatoryIntegral outerTwist innerTwist time‖ ≤
      ‖nestedOscillatoryIntegral outer inner time‖ +
        ‖nestedOscillatoryIntegral outerTwist innerTwist time‖ :=
          norm_sub_le _ _
    _ ≤ |time| ^ 2 + |time| ^ 2 :=
      add_le_add
        (norm_nestedOscillatoryIntegral_le_abs_time_sq outer inner time)
        (norm_nestedOscillatoryIntegral_le_abs_time_sq
          outerTwist innerTwist time)
    _ = 2 * |time| ^ 2 := by ring

/-- A triangular history is bounded by the sum of its total- and
outer-resolvent gains divided by its inner mismatch. -/
theorem norm_nestedOscillatoryIntegral_le_resolventSum
    {outer inner time : Real}
    (hinner : inner ≠ 0) (houter : outer ≠ 0)
    (htotal : outer + inner ≠ 0) :
    ‖nestedOscillatoryIntegral outer inner time‖ ≤
      (2 / |outer + inner| + 2 / |outer|) / |inner| := by
  rw [nestedOscillatoryIntegral_eq_sub_div hinner, norm_div]
  have hsub := norm_sub_le
    (oscillatoryIntegral (outer + inner) time)
    (oscillatoryIntegral outer time)
  have htotalBound :=
    norm_oscillatoryIntegral_le_two_div_abs (t := time) htotal
  have houterBound :=
    norm_oscillatoryIntegral_le_two_div_abs (t := time) houter
  calc
    ‖oscillatoryIntegral (outer + inner) time -
          oscillatoryIntegral outer time‖ /
        ‖Complex.I * (inner : Complex)‖ ≤
      (‖oscillatoryIntegral (outer + inner) time‖ +
          ‖oscillatoryIntegral outer time‖) / |inner| := by
        simpa [norm_mul, Complex.norm_real, Real.norm_eq_abs] using
          div_le_div_of_nonneg_right hsub
            (norm_nonneg (Complex.I * (inner : Complex)))
    _ ≤ (2 / |outer + inner| + 2 / |outer|) / |inner| := by
      exact div_le_div_of_nonneg_right
        (add_le_add htotalBound houterBound) (abs_nonneg inner)

/-- Five-gap good sector for one twist orbit.  The fifth gap is the common
total mismatch. -/
abbrev NestedTwistGood
    (gamma outer inner outerTwist innerTwist : Real) : Prop :=
  gamma ≤ |outer| ∧ gamma ≤ |inner| ∧
    gamma ≤ |outerTwist| ∧ gamma ≤ |innerTwist| ∧
      gamma ≤ |outer + inner|

/-- Complementary bad sector: at least one local or common total mismatch is
strictly below the cutoff. -/
abbrev NestedTwistBad
    (gamma outer inner outerTwist innerTwist : Real) : Prop :=
  |outer| < gamma ∨ |inner| < gamma ∨
    |outerTwist| < gamma ∨ |innerTwist| < gamma ∨
      |outer + inner| < gamma

theorem nestedTwistGood_iff_not_bad
    (gamma outer inner outerTwist innerTwist : Real) :
    NestedTwistGood gamma outer inner outerTwist innerTwist ↔
      ¬ NestedTwistBad gamma outer inner outerTwist innerTwist := by
  simp [NestedTwistGood, NestedTwistBad]

theorem nestedTwistGood_or_bad
    (gamma outer inner outerTwist innerTwist : Real) :
    NestedTwistGood gamma outer inner outerTwist innerTwist ∨
      NestedTwistBad gamma outer inner outerTwist innerTwist := by
  by_cases hbad :
      NestedTwistBad gamma outer inner outerTwist innerTwist
  · exact Or.inr hbad
  · exact Or.inl ((nestedTwistGood_iff_not_bad _ _ _ _ _).mpr hbad)

/-- Good-cutoff component of one twist difference. -/
def nestedTwistGoodPart
    (gamma outer inner outerTwist innerTwist time : Real) : Complex :=
  if NestedTwistGood gamma outer inner outerTwist innerTwist then
    nestedTwistDifference outer inner outerTwist innerTwist time
  else 0

/-- Bad-cutoff component of one twist difference. -/
def nestedTwistBadPart
    (gamma outer inner outerTwist innerTwist time : Real) : Complex :=
  if NestedTwistBad gamma outer inner outerTwist innerTwist then
    nestedTwistDifference outer inner outerTwist innerTwist time
  else 0

/-- Exact deterministic good/bad cutoff partition. -/
theorem nestedTwistDifference_eq_goodPart_add_badPart
    (gamma outer inner outerTwist innerTwist time : Real) :
    nestedTwistDifference outer inner outerTwist innerTwist time =
      nestedTwistGoodPart gamma outer inner outerTwist innerTwist time +
        nestedTwistBadPart gamma outer inner outerTwist innerTwist time := by
  by_cases hgood : NestedTwistGood gamma outer inner outerTwist innerTwist
  · have hbad :
        ¬ NestedTwistBad gamma outer inner outerTwist innerTwist :=
      (nestedTwistGood_iff_not_bad _ _ _ _ _).mp hgood
    simp [nestedTwistGoodPart, nestedTwistBadPart, hgood, hbad]
  · have hbad : NestedTwistBad gamma outer inner outerTwist innerTwist := by
      by_contra hnotbad
      exact hgood ((nestedTwistGood_iff_not_bad _ _ _ _ _).mpr hnotbad)
    simp [nestedTwistGoodPart, nestedTwistBadPart, hgood, hbad]

/-- The unconditional good-sector bound.  It has exactly two inverse-gap
powers and therefore does not by itself yield the missing twist gain. -/
theorem norm_nestedTwistDifference_le_eight_div_sq
    {gamma outer inner outerTwist innerTwist time : Real}
    (hgamma : 0 < gamma)
    (htotal : outer + inner = outerTwist + innerTwist)
    (hgood : NestedTwistGood gamma outer inner outerTwist innerTwist) :
    ‖nestedTwistDifference outer inner outerTwist innerTwist time‖ ≤
      8 / gamma ^ 2 := by
  rcases hgood with ⟨houterGap, hinnerGap, houterTwistGap,
    hinnerTwistGap, htotalGap⟩
  have houter : outer ≠ 0 := abs_ne_zero.mp (ne_of_gt (hgamma.trans_le houterGap))
  have hinner : inner ≠ 0 := abs_ne_zero.mp (ne_of_gt (hgamma.trans_le hinnerGap))
  have houterTwist : outerTwist ≠ 0 :=
    abs_ne_zero.mp (ne_of_gt (hgamma.trans_le houterTwistGap))
  have hinnerTwist : innerTwist ≠ 0 :=
    abs_ne_zero.mp (ne_of_gt (hgamma.trans_le hinnerTwistGap))
  have htotalNonzero : outer + inner ≠ 0 :=
    abs_ne_zero.mp (ne_of_gt (hgamma.trans_le htotalGap))
  have htotalTwistNonzero : outerTwist + innerTwist ≠ 0 := by
    rw [← htotal]
    exact htotalNonzero
  have hleft := norm_nestedOscillatoryIntegral_le_resolventSum
    (time := time) hinner houter htotalNonzero
  have hright := norm_nestedOscillatoryIntegral_le_resolventSum
    (time := time) hinnerTwist houterTwist htotalTwistNonzero
  unfold nestedTwistDifference
  calc
    ‖nestedOscillatoryIntegral outer inner time -
        nestedOscillatoryIntegral outerTwist innerTwist time‖ ≤
      ‖nestedOscillatoryIntegral outer inner time‖ +
        ‖nestedOscillatoryIntegral outerTwist innerTwist time‖ := norm_sub_le _ _
    _ ≤
      (2 / |outer + inner| + 2 / |outer|) / |inner| +
      (2 / |outerTwist + innerTwist| + 2 / |outerTwist|) /
        |innerTwist| := add_le_add hleft hright
    _ ≤ 8 / gamma ^ 2 := by
      have hgamma0 : 0 ≤ gamma := le_of_lt hgamma
      have htotalTwistGap : gamma ≤ |outerTwist + innerTwist| := by
        rw [← htotal]
        exact htotalGap
      have hleftGamma :
          (2 / |outer + inner| + 2 / |outer|) / |inner| ≤
            4 / gamma ^ 2 := by
        calc
          (2 / |outer + inner| + 2 / |outer|) / |inner| ≤
              (2 / gamma + 2 / gamma) / gamma := by
            gcongr
          _ = 4 / gamma ^ 2 := by field_simp; ring
      have hrightGamma :
          (2 / |outerTwist + innerTwist| + 2 / |outerTwist|) /
              |innerTwist| ≤ 4 / gamma ^ 2 := by
        calc
          (2 / |outerTwist + innerTwist| + 2 / |outerTwist|) /
              |innerTwist| ≤ (2 / gamma + 2 / gamma) / gamma := by
            gcongr
          _ = 4 / gamma ^ 2 := by field_simp; ring
      calc
        (2 / |outer + inner| + 2 / |outer|) / |inner| +
            (2 / |outerTwist + innerTwist| + 2 / |outerTwist|) /
              |innerTwist| ≤
          4 / gamma ^ 2 + 4 / gamma ^ 2 :=
            add_le_add hleftGamma hrightGamma
        _ = 8 / gamma ^ 2 := by ring

/-! ## Cutoff-component bounds -/

/-- The deterministic good component has the two-resolvent bound. -/
theorem norm_nestedTwistGoodPart_le_eight_div_sq
    {gamma outer inner outerTwist innerTwist time : Real}
    (hgamma : 0 < gamma)
    (htotal : outer + inner = outerTwist + innerTwist) :
    ‖nestedTwistGoodPart
        gamma outer inner outerTwist innerTwist time‖ ≤
      8 / gamma ^ 2 := by
  unfold nestedTwistGoodPart
  split_ifs with hgood
  · exact norm_nestedTwistDifference_le_eight_div_sq
      hgamma htotal hgood
  · simp
    positivity

/-- The deterministic bad component is controlled only by finite time; its
probability must be estimated separately by a small-ball argument. -/
theorem norm_nestedTwistBadPart_le_two_mul_abs_time_sq
    (gamma outer inner outerTwist innerTwist time : Real) :
    ‖nestedTwistBadPart
        gamma outer inner outerTwist innerTwist time‖ ≤
      2 * |time| ^ 2 := by
  unfold nestedTwistBadPart
  split_ifs
  · exact norm_nestedTwistDifference_le_two_mul_abs_time_sq
      outer inner outerTwist innerTwist time
  · simp
    positivity

/-- Single piecewise estimate attached to the exact good/bad partition. -/
theorem norm_nestedTwistDifference_le_cutoffPiecewise
    {gamma outer inner outerTwist innerTwist time : Real}
    (hgamma : 0 < gamma)
    (htotal : outer + inner = outerTwist + innerTwist) :
    ‖nestedTwistDifference outer inner outerTwist innerTwist time‖ ≤
      if NestedTwistGood gamma outer inner outerTwist innerTwist then
        8 / gamma ^ 2
      else
        2 * |time| ^ 2 := by
  split_ifs with hgood
  · exact norm_nestedTwistDifference_le_eight_div_sq
      hgamma htotal hgood
  · exact norm_nestedTwistDifference_le_two_mul_abs_time_sq
      outer inner outerTwist innerTwist time

/-! ## An exact all-good noncancellation obstruction -/

private theorem oscillatoryIntegral_one_pi :
    oscillatoryIntegral 1 Real.pi = 2 * Complex.I := by
  rw [oscillatoryIntegral_eq_div (by norm_num)]
  norm_num
  rw [show Complex.I * (Real.pi : Complex) =
      (Real.pi : Complex) * Complex.I by ring]
  rw [Complex.exp_pi_mul_I]
  apply Complex.ext <;> norm_num

private theorem oscillatoryIntegral_two_pi :
    oscillatoryIntegral 2 Real.pi = 0 := by
  rw [oscillatoryIntegral_eq_div (by norm_num)]
  norm_num
  rw [show Complex.I * ((2 : Complex) * (Real.pi : Complex)) =
      2 * (Real.pi : Complex) * Complex.I by ring]
  rw [Complex.exp_two_pi_mul_I]
  simp

private theorem exp_three_pi_mul_I :
    Complex.exp (3 * (Real.pi : Complex) * Complex.I) = -1 := by
  rw [show 3 * (Real.pi : Complex) * Complex.I =
      2 * (Real.pi : Complex) * Complex.I +
        (Real.pi : Complex) * Complex.I by ring]
  rw [Complex.exp_add, Complex.exp_two_pi_mul_I,
    Complex.exp_pi_mul_I]
  ring

private theorem oscillatoryIntegral_three_pi :
    oscillatoryIntegral 3 Real.pi =
      (2 / 3 : Real) * Complex.I := by
  rw [oscillatoryIntegral_eq_div (by norm_num)]
  norm_num
  rw [show Complex.I * ((3 : Complex) * (Real.pi : Complex)) =
      3 * (Real.pi : Complex) * Complex.I by ring]
  rw [exp_three_pi_mul_I]
  field_simp [Complex.I_ne_zero]
  simp [Complex.I_sq]
  ring

/-- An exact common-total, five-gap-good orbit whose twist difference is
nonzero.  Hence the good inequalities and total-mismatch relation alone
cannot imply the missing numerator cancellation. -/
theorem nestedTwistDifference_unitGood_exact :
    nestedTwistDifference 1 1 3 (-1) Real.pi =
      ((-8 / 3 : Real) : Complex) := by
  unfold nestedTwistDifference
  rw [nestedOscillatoryIntegral_eq_sub_div
      (by norm_num : (1 : Real) ≠ 0),
    nestedOscillatoryIntegral_eq_sub_div
      (by norm_num : (-1 : Real) ≠ 0)]
  norm_num
  rw [oscillatoryIntegral_one_pi, oscillatoryIntegral_two_pi,
    oscillatoryIntegral_three_pi]
  apply Complex.ext <;> norm_num

theorem nestedTwistDifference_unitGood_obstruction :
    NestedTwistGood 1 1 1 3 (-1) ∧
      (1 : Real) + 1 = 3 + (-1) ∧
      nestedTwistDifference 1 1 3 (-1) Real.pi ≠ 0 := by
  refine ⟨by norm_num [NestedTwistGood], by norm_num, ?_⟩
  rw [nestedTwistDifference_unitGood_exact]
  norm_num

/-! ## The explicit additional cancellation condition -/

/-- Quantitative numerator cancellation at cutoff scale `gamma`.  This is
the precise extra input not supplied by the twist algebra itself. -/
def NestedTwistNumeratorGain
    (constant gamma outer inner outerTwist innerTwist time : Real) : Prop :=
  ‖nestedTwistCancellationNumerator
      outer inner outerTwist innerTwist time‖ ≤ constant * gamma

/-- An `O(gamma)` numerator gain removes one of the two inner denominator
losses in the exact common-denominator formula. -/
theorem norm_nestedTwistDifference_le_constant_div
    {constant gamma outer inner outerTwist innerTwist time : Real}
    (hconstant : 0 ≤ constant) (hgamma : 0 < gamma)
    (hinnerGap : gamma ≤ |inner|)
    (hinnerTwistGap : gamma ≤ |innerTwist|)
    (htotal : outer + inner = outerTwist + innerTwist)
    (hgain : NestedTwistNumeratorGain constant gamma
      outer inner outerTwist innerTwist time) :
    ‖nestedTwistDifference outer inner outerTwist innerTwist time‖ ≤
      constant / gamma := by
  have hinner : inner ≠ 0 :=
    abs_ne_zero.mp (ne_of_gt (hgamma.trans_le hinnerGap))
  have hinnerTwist : innerTwist ≠ 0 :=
    abs_ne_zero.mp (ne_of_gt (hgamma.trans_le hinnerTwistGap))
  rw [nestedTwistDifference_eq_numerator_div hinner hinnerTwist htotal,
    norm_div]
  have hdenom : gamma ^ 2 ≤
      ‖(Complex.I * (inner : Complex)) *
        (Complex.I * (innerTwist : Complex))‖ := by
    simp only [norm_mul, Complex.norm_I, one_mul, Complex.norm_real,
      Real.norm_eq_abs]
    nlinarith [mul_le_mul hinnerGap hinnerTwistGap
      (le_of_lt hgamma) (abs_nonneg inner)]
  calc
    ‖nestedTwistCancellationNumerator
        outer inner outerTwist innerTwist time‖ /
        ‖(Complex.I * (inner : Complex)) *
          (Complex.I * (innerTwist : Complex))‖ ≤
      (constant * gamma) / (gamma ^ 2) :=
        div_le_div₀ (mul_nonneg hconstant (le_of_lt hgamma)) hgain
          (sq_pos_of_pos hgamma) hdenom
    _ = constant / gamma := by
      field_simp [ne_of_gt hgamma]

/-! ## Actual FPUT mismatch orbit -/

/-- The two local mismatches telescope to a total mismatch invariant under
the physical inner-branch twist. -/
theorem physicalIteratedA2_totalMismatch_flip_eq
    {N : Nat} [NeZero N] (m : Lattice.PositiveMassConfig N)
    (observed : Lattice.Site N)
    (term : IteratedQuadraticSecondPicardCharacterTerm N) :
    iteratedQuadraticOuterMismatch m observed term +
        iteratedQuadraticInnerMismatch m term =
      iteratedQuadraticOuterMismatch m observed
          (flipIteratedQuadraticInnerBranch term) +
        iteratedQuadraticInnerMismatch m
          (flipIteratedQuadraticInnerBranch term) := by
  calc
    iteratedQuadraticOuterMismatch m observed term +
        iteratedQuadraticInnerMismatch m term =
      outputChargeMismatch (modeFrequency m observed)
        (iteratedQuadraticSecondPicardCharge term) (modeFrequency m) := by
          simpa [physicalIteratedA2PhaseHistory] using
            sum_physicalIteratedA2PhaseHistory m observed term
    _ = outputChargeMismatch (modeFrequency m observed)
        (iteratedQuadraticSecondPicardCharge
          (flipIteratedQuadraticInnerBranch term)) (modeFrequency m) := by
          rw [iteratedQuadraticSecondPicardCharge_flipIteratedQuadraticInnerBranch]
    _ = iteratedQuadraticOuterMismatch m observed
          (flipIteratedQuadraticInnerBranch term) +
        iteratedQuadraticInnerMismatch m
          (flipIteratedQuadraticInnerBranch term) := by
          simpa [physicalIteratedA2PhaseHistory] using
            (sum_physicalIteratedA2PhaseHistory m observed
              (flipIteratedQuadraticInnerBranch term)).symm

/-- Actual five-gap predicate for one physical twist orbit. -/
def PhysicalIteratedA2TwistGood
    {N : Nat} [NeZero N] (gamma : Real)
    (m : Lattice.PositiveMassConfig N) (observed : Lattice.Site N)
    (term : IteratedQuadraticSecondPicardCharacterTerm N) : Prop :=
  NestedTwistGood gamma
    (iteratedQuadraticOuterMismatch m observed term)
    (iteratedQuadraticInnerMismatch m term)
    (iteratedQuadraticOuterMismatch m observed
      (flipIteratedQuadraticInnerBranch term))
    (iteratedQuadraticInnerMismatch m
      (flipIteratedQuadraticInnerBranch term))

/-- Actual physical twist difference inherits the unconditional
`8 / gamma^2` good-sector bound. -/
theorem norm_physicalIteratedA2_nestedTwistDifference_le_eight_div_sq
    {N : Nat} [NeZero N] {gamma time : Real}
    (hgamma : 0 < gamma) (m : Lattice.PositiveMassConfig N)
    (observed : Lattice.Site N)
    (term : IteratedQuadraticSecondPicardCharacterTerm N)
    (hgood : PhysicalIteratedA2TwistGood gamma m observed term) :
    ‖nestedTwistDifference
        (iteratedQuadraticOuterMismatch m observed term)
        (iteratedQuadraticInnerMismatch m term)
        (iteratedQuadraticOuterMismatch m observed
          (flipIteratedQuadraticInnerBranch term))
        (iteratedQuadraticInnerMismatch m
          (flipIteratedQuadraticInnerBranch term)) time‖ ≤
      8 / gamma ^ 2 := by
  exact norm_nestedTwistDifference_le_eight_div_sq hgamma
    (physicalIteratedA2_totalMismatch_flip_eq m observed term) hgood

/-- Under the explicit numerator-gain hypothesis, the actual physical
twist difference improves to one inverse cutoff. -/
theorem norm_physicalIteratedA2_nestedTwistDifference_le_constant_div
    {N : Nat} [NeZero N] {constant gamma time : Real}
    (hconstant : 0 ≤ constant) (hgamma : 0 < gamma)
    (m : Lattice.PositiveMassConfig N) (observed : Lattice.Site N)
    (term : IteratedQuadraticSecondPicardCharacterTerm N)
    (hinnerGap : gamma ≤ |iteratedQuadraticInnerMismatch m term|)
    (hinnerTwistGap : gamma ≤
      |iteratedQuadraticInnerMismatch m
        (flipIteratedQuadraticInnerBranch term)|)
    (hgain : NestedTwistNumeratorGain constant gamma
      (iteratedQuadraticOuterMismatch m observed term)
      (iteratedQuadraticInnerMismatch m term)
      (iteratedQuadraticOuterMismatch m observed
        (flipIteratedQuadraticInnerBranch term))
      (iteratedQuadraticInnerMismatch m
        (flipIteratedQuadraticInnerBranch term)) time) :
    ‖nestedTwistDifference
        (iteratedQuadraticOuterMismatch m observed term)
        (iteratedQuadraticInnerMismatch m term)
        (iteratedQuadraticOuterMismatch m observed
          (flipIteratedQuadraticInnerBranch term))
        (iteratedQuadraticInnerMismatch m
          (flipIteratedQuadraticInnerBranch term)) time‖ ≤
      constant / gamma := by
  exact norm_nestedTwistDifference_le_constant_div hconstant hgamma
    hinnerGap hinnerTwistGap
    (physicalIteratedA2_totalMismatch_flip_eq m observed term) hgain

/-! ## Remainder-level consumer bounds and cutoff consequence -/

/-- `l1` mass of the static physical iterated-A2 tree coefficients. -/
def physicalIteratedA2StaticAbsMass
    {N : Nat} [NeZero N]
    (m : Lattice.PositiveMassConfig N) (kappa : Real)
    (radius : Lattice.Site N → Real) (observed : Lattice.Site N) : Real :=
  ∑ term : IteratedQuadraticSecondPicardCharacterTerm N,
    ‖iteratedQuadraticSecondPicardStaticCoefficient
      m kappa radius observed term‖

/-- A uniform one-gap twist bound controls the complete isolated Haar
remainder by an explicit loss-two square. -/
theorem abs_completeA2IteratedIteratedRemainder_le_of_uniformTwistGain
    {N : Nat} [NeZero N] {constant gamma : Real}
    (hconstant : 0 ≤ constant) (hgamma : 0 < gamma)
    (m : Lattice.PositiveMassConfig N) (kappa : Real)
    (radius : Lattice.Site N → Real) (observed : Lattice.Site N)
    (time : Real)
    (hbound : ∀ term : IteratedQuadraticSecondPicardCharacterTerm N,
      ‖nestedTwistDifference
          (iteratedQuadraticOuterMismatch m observed term)
          (iteratedQuadraticInnerMismatch m term)
          (iteratedQuadraticOuterMismatch m observed
            (flipIteratedQuadraticInnerBranch term))
          (iteratedQuadraticInnerMismatch m
            (flipIteratedQuadraticInnerBranch term)) time‖ ≤
        constant / gamma) :
    |completeA2IteratedIteratedRemainder
        m kappa radius observed time| ≤
      (1 / 4 : Real) *
        ((constant / gamma) *
          physicalIteratedA2StaticAbsMass
            m kappa radius observed) ^ 2 := by
  rw [completeA2IteratedIteratedRemainder_eq_quarter_phaseRenormalizedSquare]
  rw [abs_mul, abs_of_nonneg (by norm_num : (0 : Real) ≤ 1 / 4)]
  apply mul_le_mul_of_nonneg_left
    (abs_sameChargeFamilySquare_le_absMass_sq
      (phaseRenormalizedPhysicalIteratedA2Coefficient
        m kappa radius observed time)
      iteratedQuadraticSecondPicardCharge |>.trans ?_)
    (by norm_num)
  rw [sq_le_sq₀ (by unfold finiteCharacterCoefficientAbsMass; positivity)
    (mul_nonneg (div_nonneg hconstant (le_of_lt hgamma))
      (by unfold physicalIteratedA2StaticAbsMass; positivity))]
  unfold finiteCharacterCoefficientAbsMass physicalIteratedA2StaticAbsMass
  calc
    (∑ term : IteratedQuadraticSecondPicardCharacterTerm N,
        ‖phaseRenormalizedPhysicalIteratedA2Coefficient
          m kappa radius observed time term‖) ≤
      ∑ term : IteratedQuadraticSecondPicardCharacterTerm N,
        ‖iteratedQuadraticSecondPicardStaticCoefficient
          m kappa radius observed term‖ * (constant / gamma) := by
      apply Finset.sum_le_sum
      intro term hterm
      rw [phaseRenormalizedPhysicalIteratedA2Coefficient_eq_nestedDifference,
        norm_mul]
      exact mul_le_mul_of_nonneg_left (hbound term) (norm_nonneg _)
    _ = (constant / gamma) *
        ∑ term : IteratedQuadraticSecondPicardCharacterTerm N,
          ‖iteratedQuadraticSecondPicardStaticCoefficient
            m kappa radius observed term‖ := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro term hterm
      ring

/-- The proved generic rank-three balance remains infeasible: twist
renormalization plus a good cutoff alone does not close the `g^4` sector. -/
theorem generic_rankThree_g4_still_has_no_cutoff :
    ¬ ∃ alpha, CutoffExponentAdmissible 4 3
      quadraticKineticDeficit alpha :=
  no_quadraticCutoffExponent_g4_loss_three

/-- If the explicit numerator gain reduces the squared twist remainder to
effective loss two, the already established `alpha = 5/4` cutoff closes it. -/
theorem numeratorGain_lossTwo_cutoff_admissible :
    CutoffExponentAdmissible 4 2 quadraticKineticDeficit
      correctedSecondPicardG4CutoffExponent :=
  correctedSecondPicardG4CutoffExponent_loss_two

end

end ArchonPhysics.CanonicalIIDCoerciveIteratedA2TwistDifferenceOscillatoryBound
