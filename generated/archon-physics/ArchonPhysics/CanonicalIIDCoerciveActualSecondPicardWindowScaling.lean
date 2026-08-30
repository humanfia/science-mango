import ArchonPhysics.CanonicalIIDCoerciveActualTimeWindowQuantitativeBounds

/-!
# Explicit quadratic window scaling for the actual second-Picard source

The deterministic second-Picard source envelope is exactly a
time-independent finite-volume slope times the absolute time.  Combining this
identity with the existing product-space finite-window estimate gives a raw
source L1 bound proportional to the square of a nonnegative symmetric-window
radius.

This is a fixed-finite-volume estimate.  Its coefficient depends on N, and
the result makes no uniform-in-window or kinetic-scale assertion.
-/

namespace ArchonPhysics.CanonicalIIDCoerciveActualSecondPicardWindowScaling

open Set
open ArchonPhysics
open ArchonPhysics.CanonicalIIDCoerciveActualExpectationAdapter
open ArchonPhysics.CanonicalIIDCoerciveActualExpectationClosure
open ArchonPhysics.CanonicalIIDCoerciveActualFreeQuadraticHistoryIntegrability
open ArchonPhysics.CanonicalIIDCoerciveActualPointwiseDuhamelHistoryExpansion
open ArchonPhysics.CanonicalIIDCoerciveActualQuadraticSecondPicardHistoryIntegrability
open ArchonPhysics.CanonicalIIDCoerciveActualTimeWindowQuantitativeBounds
open ArchonPhysics.CanonicalIIDCoerciveSignedModalHierarchy
open ArchonPhysics.FinitePhaseMonomials
open ArchonPhysics.OrderedTranslationLastMode
open ArchonPhysics.PhyslibFPUTActualDuhamelSourceHistoryExpansion
open ArchonPhysics.RandomMassPositiveCollisionData
open MeasureTheory

noncomputable section

variable {N : Nat} [NeZero N]

/-- The time-independent coefficient of the fixed-time second-Picard source
envelope.  Every factor is an explicit finite-volume deterministic envelope.
-/
def canonicalQuadraticSecondPicardEnvelopeSlope
    (N : Nat) [NeZero N] (kappa : Real) : Real :=
  canonicalPositiveFrequencyNormalizationEnvelope N *
    (|kappa| *
      (2 * canonicalFreeQuadraticTensorRowEnvelope N *
        canonicalFreeRadiusL1Envelope N *
        canonicalFirstPicardModalL1RateEnvelope N kappa))

/-- The source envelope has exactly linear dependence on absolute time. -/
theorem canonicalQuadraticSecondPicardSourceEnvelope_eq_slope_mul_abs
    (kappa time : Real) :
    canonicalQuadraticSecondPicardSourceEnvelope N kappa time =
      canonicalQuadraticSecondPicardEnvelopeSlope N kappa * |time| := by
  unfold canonicalQuadraticSecondPicardSourceEnvelope
    canonicalQuadraticSecondPicardEnvelopeSlope
  ring

/-- The explicit envelope slope is nonnegative. -/
theorem canonicalQuadraticSecondPicardEnvelopeSlope_nonneg
    (kappa : Real) :
    0 <= canonicalQuadraticSecondPicardEnvelopeSlope N kappa := by
  unfold canonicalQuadraticSecondPicardEnvelopeSlope
  have hnormalization :
      0 <= canonicalPositiveFrequencyNormalizationEnvelope N :=
    canonicalPositiveFrequencyNormalizationEnvelope_nonneg (N := N)
  have hrow : 0 <= canonicalFreeQuadraticTensorRowEnvelope N := by
    unfold canonicalFreeQuadraticTensorRowEnvelope
    positivity
  have hradius : 0 <= canonicalFreeRadiusL1Envelope N := by
    unfold canonicalFreeRadiusL1Envelope
    positivity
  have hrate : 0 <= canonicalFirstPicardModalL1RateEnvelope N kappa := by
    unfold canonicalFirstPicardModalL1RateEnvelope
    positivity
  exact mul_nonneg hnormalization
    (mul_nonneg (abs_nonneg kappa)
      (mul_nonneg
        (mul_nonneg (mul_nonneg (by norm_num) hrow) hradius)
        hrate))

/-- The coefficient appearing after integration over the symmetric window.
The factor 2 is the exact length-to-radius conversion for [-T,T]. -/
def canonicalQuadraticSecondPicardWindowQuadraticConstant
    (N : Nat) [NeZero N] (kappa : Real) : Real :=
  2 * canonicalQuadraticSecondPicardEnvelopeSlope N kappa

/-- The quadratic window coefficient is nonnegative. -/
theorem canonicalQuadraticSecondPicardWindowQuadraticConstant_nonneg
    (kappa : Real) :
    0 <= canonicalQuadraticSecondPicardWindowQuadraticConstant N kappa := by
  unfold canonicalQuadraticSecondPicardWindowQuadraticConstant
  exact mul_nonneg (by norm_num)
    (canonicalQuadraticSecondPicardEnvelopeSlope_nonneg (N := N) kappa)

/-- For a nonnegative window radius, the envelope bound used by the existing
L1 theorem is exactly the explicit coefficient times T squared. -/
theorem canonicalQuadraticSecondPicardSourceEnvelope_mul_window_eq_quadratic
    (kappa window : Real) (hwindow : 0 <= window) :
    canonicalQuadraticSecondPicardSourceEnvelope N kappa window *
        (2 * window) =
      canonicalQuadraticSecondPicardWindowQuadraticConstant N kappa *
        window ^ 2 := by
  rw [canonicalQuadraticSecondPicardSourceEnvelope_eq_slope_mul_abs,
    abs_of_nonneg hwindow]
  unfold canonicalQuadraticSecondPicardWindowQuadraticConstant
  ring

/-- The raw actual quadratic second-Picard Duhamel source has an explicit
finite-window L1 bound of order T squared.  The raw canonical history uses
unit quadratic source strength, hence the coefficient is evaluated at one.
-/
theorem integral_norm_canonicalQuadraticSecondPicardDuhamelSource_timeWindow_le_quadratic
    (hN : 3 <= N) {a : Real} (ha0 : 0 <= a) (ha1 : a <= 1 / 4)
    (flowKappa flowBeta flowG : Real)
    (hflowBeta : 2 * flowKappa ^ 2 / 9 < flowBeta)
    (entry : PhaseSign × OrderedModeIndex N)
    (hentry : entry.2 ≠ lastOrderedIndex (ι := Lattice.Site N))
    (window : Real) (hwindow : 0 <= window) :
    (∫ st, ‖canonicalQuadraticDuhamelHistorySource (N := N)
        flowKappa flowBeta flowG hflowBeta a
        (canonicalOrientedPhyslibFreeRadius (N := N) a)
        (canonicalReindexedPhyslibHaarPhase (N := N))
        entry .quadraticSecondPicard (st.2, st.1)‖
      ∂((volume.restrict (Icc (-window) window)).prod
        canonicalIIDMassPhaseEnsemble.probability)) <=
      canonicalQuadraticSecondPicardWindowQuadraticConstant N 1 *
        window ^ 2 := by
  calc
    _ <= canonicalQuadraticSecondPicardSourceEnvelope N 1 window *
          (2 * window) :=
      integral_norm_canonicalQuadraticSecondPicardDuhamelSource_timeWindow_le
        (N := N) hN ha0 ha1 flowKappa flowBeta flowG hflowBeta
        entry hentry window hwindow
    _ = _ :=
      canonicalQuadraticSecondPicardSourceEnvelope_mul_window_eq_quadratic
        (N := N) 1 window hwindow

end
end ArchonPhysics.CanonicalIIDCoerciveActualSecondPicardWindowScaling
