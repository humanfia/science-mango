import ArchonPhysics.NestedOscillatoryEnergyIdentity

/-!
# First normal form for a quadratic oscillatory mode equation

This module proves the exact first integration-by-parts step for a finite
quadratic interaction equation.  It is the algebraic form needed after the
equal-mass periodic alpha-FPUT Hamiltonian is written in interaction-picture
Fourier variables: a nonresonant three-wave source is removed at first order,
and the renormalized amplitude has an explicit cubic, second-order source.

The statement is finite dimensional and makes no kinetic, random-phase, or
large-volume assumption.  In particular, it does not postulate a kinetic
equation.  A separate FPUT specialization must prove that its three-wave
mismatches are nonzero and identify the connected higher-order resonances.
-/

namespace ArchonPhysics.QuadraticInteractionFirstNormalForm

open ArchonPhysics.NestedOscillatoryEnergyIdentity
open ArchonPhysics.NonresonantOscillatoryGain

noncomputable section

variable {Mode : Type*} [Fintype Mode]

/-- The instantaneous quadratic interaction-picture source. -/
def quadraticOscillatorySource
    (vertex : Mode -> Mode -> Mode -> Complex)
    (mismatch : Mode -> Mode -> Mode -> Real)
    (amplitude : Mode -> Complex) (time : Real) (out : Mode) : Complex :=
  ∑ left, ∑ right,
    vertex out left right *
      Complex.exp ((Complex.I * mismatch out left right) * time) *
      amplitude left * amplitude right

/-- The time primitive used to remove a nonresonant quadratic source.  The
primitive is normalized to vanish at time zero. -/
def quadraticPrimitiveCorrection
    (vertex : Mode -> Mode -> Mode -> Complex)
    (mismatch : Mode -> Mode -> Mode -> Real)
    (amplitude : Mode -> Complex) (time : Real) (out : Mode) : Complex :=
  ∑ left, ∑ right,
    vertex out left right *
      oscillatoryIntegral (mismatch out left right) time *
      amplitude left * amplitude right

/-- The product-rule feedback generated when the two input amplitudes in the
normal-form correction evolve. -/
def quadraticHistoryFeedback
    (vertex : Mode -> Mode -> Mode -> Complex)
    (mismatch : Mode -> Mode -> Mode -> Real)
    (amplitude velocity : Mode -> Complex)
    (time : Real) (out : Mode) : Complex :=
  ∑ left, ∑ right,
    vertex out left right *
      oscillatoryIntegral (mismatch out left right) time *
      (velocity left * amplitude right + amplitude left * velocity right)

/-- Substitution of the quadratic equation into its first normal-form
feedback.  This is a cubic source and is fully explicit. -/
def quadraticCubicNormalFormSource
    (vertex : Mode -> Mode -> Mode -> Complex)
    (mismatch : Mode -> Mode -> Mode -> Real)
    (amplitude : Mode -> Complex) (time : Real) (out : Mode) : Complex :=
  quadraticHistoryFeedback vertex mismatch amplitude
    (quadraticOscillatorySource vertex mismatch amplitude time) time out

/-- Exact product-rule derivative of the first normal-form correction. -/
theorem hasDerivAt_quadraticPrimitiveCorrection
    (vertex : Mode -> Mode -> Mode -> Complex)
    (mismatch : Mode -> Mode -> Mode -> Real)
    (path : Real -> Mode -> Complex) (velocity : Mode -> Complex)
    (time : Real) (out : Mode)
    (hpath : ∀ mode, HasDerivAt (fun s => path s mode) (velocity mode) time) :
    HasDerivAt
      (fun s => quadraticPrimitiveCorrection vertex mismatch (path s) s out)
      (quadraticOscillatorySource vertex mismatch (path time) time out +
        quadraticHistoryFeedback vertex mismatch (path time) velocity time out)
      time := by
  unfold quadraticPrimitiveCorrection quadraticOscillatorySource
    quadraticHistoryFeedback
  have hsum : HasDerivAt
      (∑ left, ∑ right, fun s =>
        vertex out left right *
          oscillatoryIntegral (mismatch out left right) s *
          path s left * path s right)
      (∑ left, ∑ right,
        (((vertex out left right *
              Complex.exp ((Complex.I * mismatch out left right) * time)) *
                path time left +
            (vertex out left right *
              oscillatoryIntegral (mismatch out left right) time) *
                velocity left) * path time right +
          (vertex out left right *
            oscillatoryIntegral (mismatch out left right) time *
              path time left) * velocity right))
      time := by
    apply HasDerivAt.sum (u := Finset.univ)
    intro left _hleft
    apply HasDerivAt.sum (u := Finset.univ)
    intro right _hright
    exact (((hasDerivAt_oscillatoryIntegral
      (mismatch out left right) time).const_mul
        (vertex out left right)).mul (hpath left)).mul (hpath right)
  convert hsum using 1
  · funext s
    simp only [Finset.sum_apply]
  · rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro left _hleft
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro right _hright
    ring

/-- The history feedback is linear in its velocity argument. -/
theorem quadraticHistoryFeedback_smul
    (vertex : Mode -> Mode -> Mode -> Complex)
    (mismatch : Mode -> Mode -> Mode -> Real)
    (amplitude velocity : Mode -> Complex)
    (epsilon : Complex) (time : Real) (out : Mode) :
    quadraticHistoryFeedback vertex mismatch amplitude
        (fun mode => epsilon * velocity mode) time out =
      epsilon * quadraticHistoryFeedback vertex mismatch amplitude velocity time out := by
  unfold quadraticHistoryFeedback
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro left _hleft
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro right _hright
  ring

/-- A uniform mismatch gap gives the standard inverse-gap bound on the
normal-form correction.  This is the quantitative reason the first
nonresonant interaction can be removed before taking a kinetic limit. -/
theorem norm_quadraticPrimitiveCorrection_le
    (vertex : Mode -> Mode -> Mode -> Complex)
    (mismatch : Mode -> Mode -> Mode -> Real)
    (amplitude : Mode -> Complex) (time : Real) (out : Mode)
    (gap : Real) (hgap : 0 < gap)
    (hmismatch : ∀ left right, gap ≤ |mismatch out left right|) :
    ‖quadraticPrimitiveCorrection vertex mismatch amplitude time out‖ ≤
      (2 / gap) *
        ∑ left, ∑ right,
          ‖vertex out left right‖ * ‖amplitude left‖ * ‖amplitude right‖ := by
  unfold quadraticPrimitiveCorrection
  calc
    ‖∑ left, ∑ right,
        vertex out left right *
          oscillatoryIntegral (mismatch out left right) time *
          amplitude left * amplitude right‖ ≤
        ∑ left, ‖∑ right,
          vertex out left right *
            oscillatoryIntegral (mismatch out left right) time *
            amplitude left * amplitude right‖ := norm_sum_le _ _
    _ ≤ ∑ left, ∑ right,
        ‖vertex out left right *
          oscillatoryIntegral (mismatch out left right) time *
          amplitude left * amplitude right‖ := by
      apply Finset.sum_le_sum
      intro left _hleft
      exact norm_sum_le _ _
    _ ≤ ∑ left, ∑ right,
        (2 / gap) *
          (‖vertex out left right‖ * ‖amplitude left‖ * ‖amplitude right‖) := by
      apply Finset.sum_le_sum
      intro left _hleft
      apply Finset.sum_le_sum
      intro right _hright
      have hnonzero : mismatch out left right ≠ 0 := by
        intro hzero
        have := hmismatch left right
        rw [hzero, abs_zero] at this
        exact (not_lt_of_ge this) hgap
      have hosc :
          ‖oscillatoryIntegral (mismatch out left right) time‖ ≤ 2 / gap :=
        (norm_oscillatoryIntegral_le_two_div_abs hnonzero).trans
          (div_le_div_of_nonneg_left (by positivity) hgap
            (hmismatch left right))
      rw [norm_mul, norm_mul, norm_mul]
      calc
        ‖vertex out left right‖ *
              ‖oscillatoryIntegral (mismatch out left right) time‖ *
              ‖amplitude left‖ * ‖amplitude right‖ ≤
            ‖vertex out left right‖ * (2 / gap) *
              ‖amplitude left‖ * ‖amplitude right‖ := by
          gcongr
        _ = (2 / gap) *
            (‖vertex out left right‖ * ‖amplitude left‖ *
              ‖amplitude right‖) := by ring
    _ = (2 / gap) *
        ∑ left, ∑ right,
          ‖vertex out left right‖ * ‖amplitude left‖ * ‖amplitude right‖ := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro left _hleft
      rw [Finset.mul_sum]

/-- Exact first normal-form identity.  If the microscopic interaction-picture
amplitudes solve the quadratic equation with coupling `epsilon`, then the
renormalized amplitude has no order-`epsilon` term: its derivative is exactly
the displayed order-`epsilon^2` cubic feedback. -/
theorem hasDerivAt_firstNormalForm
    (vertex : Mode -> Mode -> Mode -> Complex)
    (mismatch : Mode -> Mode -> Mode -> Real)
    (path : Real -> Mode -> Complex)
    (epsilon : Complex) (time : Real) (out : Mode)
    (hpath : ∀ mode, HasDerivAt (fun s => path s mode)
      (epsilon * quadraticOscillatorySource vertex mismatch (path time) time mode)
      time) :
    HasDerivAt
      (fun s => path s out - epsilon *
        quadraticPrimitiveCorrection vertex mismatch (path s) s out)
      (-(epsilon ^ 2) *
        quadraticCubicNormalFormSource vertex mismatch (path time) time out)
      time := by
  have hcorrection := hasDerivAt_quadraticPrimitiveCorrection
    vertex mismatch path
      (fun mode => epsilon *
        quadraticOscillatorySource vertex mismatch (path time) time mode)
      time out hpath
  have hscaled := hcorrection.const_mul epsilon
  have hsub := (hpath out).sub hscaled
  rw [quadraticHistoryFeedback_smul] at hsub
  convert hsub using 1 <;> try rfl
  unfold quadraticCubicNormalFormSource
  ring

/-- At time zero the normal-form correction vanishes exactly. -/
@[simp] theorem quadraticPrimitiveCorrection_zero
    (vertex : Mode -> Mode -> Mode -> Complex)
    (mismatch : Mode -> Mode -> Mode -> Real)
    (amplitude : Mode -> Complex) (out : Mode) :
    quadraticPrimitiveCorrection vertex mismatch amplitude 0 out = 0 := by
  have hzero (delta : Real) : oscillatoryIntegral delta 0 = 0 := by
    unfold oscillatoryIntegral
    exact intervalIntegral.integral_same
  simp [quadraticPrimitiveCorrection, hzero]

end

end ArchonPhysics.QuadraticInteractionFirstNormalForm
