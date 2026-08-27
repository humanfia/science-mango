import ArchonPhysics.FiniteMeasureClosedSmallBallLowerWeakLimit
import ArchonPhysics.CanonicalOnShellInverseTimeSmallBallLower
import ArchonPhysics.CanonicalRankFrequencyMarkedBroadenedMarginal

/-!
# Canonical decay linear small-ball lower bridge

This module records the exact remaining model-facing input: a single positive
slope and a vanishing finite-volume error for the honest canonical annealed
decay mismatch measures.  From that input, closed-set Portmanteau gives the
same linear lower bound for the deterministic collision limit, and the
inverse-time sinc-squared estimate gives a positive broadened mass.

The structure below is an explicit hypothesis.  This module does not construct
it from qualitative six-site positivity or from extensive total collision
mass.
-/

open scoped Topology ENNReal

namespace ArchonPhysics.CanonicalDecayAnnealedLinearSmallBallLowerBridge

open ArchonPhysics
open ArchonPhysics.BroadenedResonanceMeasure
open ArchonPhysics.CanonicalCollisionMeasureWeakLimit
open ArchonPhysics.CanonicalOnShellInverseTimeSmallBallLower
open ArchonPhysics.CanonicalRankFrequencyMarkedAnnealedMismatchBridge
open ArchonPhysics.CanonicalRankFrequencyMarkedBroadenedMarginal
open ArchonPhysics.CanonicalRankFrequencyMarkedFiniteMeasureWeakLimit
open ArchonPhysics.CanonicalRankFrequencyMarkedMeasure
open ArchonPhysics.FiniteMeasureClosedSmallBallLowerWeakLimit
open ArchonPhysics.RandomMassThreeWaveCollisionNetwork
open ArchonPhysics.RepeatedParentChildMismatchSmallBall
open Filter MeasureTheory Set

noncomputable section

/-- The precise uniform finite-volume source estimate still required from the
random-mass model.  The same positive slope works for every volume and every
window width up to one, while the additive error vanishes with volume. -/
structure CanonicalDecayAnnealedLinearSmallBallLower where
  constant : Real
  constant_pos : 0 < constant
  error : Nat → Real
  error_nonneg : ∀ n, 0 ≤ error n
  error_tendsto_zero : Tendsto error atTop (nhds 0)
  bound : ∀ n : Nat, ∀ delta : Real,
    0 < delta → delta ≤ 1 →
    constant * delta - error n ≤
      ((canonicalMarkedMismatchAnnealedPerSiteFiniteMeasure
          decayInteractionSign n : Measure Real)
        (absoluteMismatchSublevel delta)).toReal

/-- A genuine canonical annealed `c * delta - error n` estimate passes to the
marked deterministic decay mismatch limit. -/
theorem canonicalDecayMarkedMismatchPerSiteLimit_absoluteMismatchSublevel_toReal_ge
    (smallBall : CanonicalDecayAnnealedLinearSmallBallLower)
    {delta : Real} (hdelta : 0 < delta) (hdeltaOne : delta ≤ 1) :
    smallBall.constant * delta ≤
      ((canonicalMarkedMismatchPerSiteLimitFiniteMeasure
          decayInteractionSign : Measure Real)
        (absoluteMismatchSublevel delta)).toReal := by
  exact
    finiteMeasure_absoluteMismatchSublevel_toReal_ge_of_linearLower_with_vanishingError
      (canonicalMarkedMismatchAnnealedPerSiteFiniteMeasure
        decayInteractionSign)
      (canonicalMarkedMismatchPerSiteLimitFiniteMeasure
        decayInteractionSign)
      (canonicalMarkedMismatchAnnealedPerSiteFiniteMeasure_tendsto
        decayInteractionSign)
      smallBall.constant smallBall.constant_pos.le
      smallBall.error smallBall.error_tendsto_zero smallBall.bound
      delta hdelta hdeltaOne

/-- Equivalent scalar collision-limit form of the canonical decay lower
small-ball estimate. -/
theorem canonicalDecayCollisionPerSiteMeasureLimit_absoluteMismatchSublevel_toReal_ge
    (smallBall : CanonicalDecayAnnealedLinearSmallBallLower)
    {delta : Real} (hdelta : 0 < delta) (hdeltaOne : delta ≤ 1) :
    smallBall.constant * delta ≤
      ((canonicalCollisionPerSiteMeasureLimit
          canonicalIIDMassPhaseEnsemble decayInteractionSign : Measure Real)
        (absoluteMismatchSublevel delta)).toReal := by
  have hmarked :=
    canonicalDecayMarkedMismatchPerSiteLimit_absoluteMismatchSublevel_toReal_ge
      smallBall hdelta hdeltaOne
  simpa only [canonicalMarkedMismatchPerSiteLimitFiniteMeasure,
    map_canonicalRankFrequencyMarkedPerSiteMeasureLimit_eq_collision] using
    hmarked

/-- At every time `T ≥ 1/4`, the conditional canonical linear small-ball
estimate supplies the inverse-time lower bound with slope `constant / 4`.
Consequently the canonical broadened collision mass is at least
`(constant / 4) / (4 * pi)`, equivalently `constant / (16 * pi)`. -/
theorem constant_div_four_div_four_pi_le_canonicalDecayBroadenedMass
    (smallBall : CanonicalDecayAnnealedLinearSmallBallLower)
    {T : Real} (hT : 0 < T) (hTquarter : (1 : Real) / 4 ≤ T) :
    (smallBall.constant / 4) / (4 * Real.pi) ≤
      ((canonicalBroadenedCollisionPerSiteMeasureLimit
          canonicalIIDMassPhaseEnsemble decayInteractionSign T hT).mass :
        Real) := by
  have hdelta : 0 < 1 / (4 * T) := by positivity
  have hfourT : 1 ≤ 4 * T := by nlinarith
  have hdeltaOne : 1 / (4 * T) ≤ 1 :=
    (div_le_one (by positivity)).2 hfourT
  have hwindow :=
    canonicalDecayCollisionPerSiteMeasureLimit_absoluteMismatchSublevel_toReal_ge
      smallBall hdelta hdeltaOne
  have hsmallBall :
      (smallBall.constant / 4) / T ≤
        (canonicalCollisionPerSiteMeasureLimit
          canonicalIIDMassPhaseEnsemble decayInteractionSign : Measure Real).real
          (absoluteMismatchSublevel (1 / (4 * T))) := by
    calc
      (smallBall.constant / 4) / T =
          smallBall.constant * (1 / (4 * T)) := by
        field_simp
      _ ≤ _ := hwindow
  simpa [canonicalBroadenedCollisionPerSiteMeasureLimit] using
    slope_div_four_pi_le_broadenedResonanceMeasure_mass
      (canonicalCollisionPerSiteMeasureLimit
        canonicalIIDMassPhaseEnsemble decayInteractionSign)
      hT hsmallBall

/-- In particular, the same transparent source estimate makes every
large-time canonical broadened decay mass strictly positive. -/
theorem canonicalDecayBroadenedMass_pos
    (smallBall : CanonicalDecayAnnealedLinearSmallBallLower)
    {T : Real} (hT : 0 < T) (hTquarter : (1 : Real) / 4 ≤ T) :
    0 <
      ((canonicalBroadenedCollisionPerSiteMeasureLimit
          canonicalIIDMassPhaseEnsemble decayInteractionSign T hT).mass :
        Real) := by
  have hlower :=
    constant_div_four_div_four_pi_le_canonicalDecayBroadenedMass
      smallBall hT hTquarter
  have hquarter : 0 < smallBall.constant / 4 := by
    exact div_pos smallBall.constant_pos (by norm_num)
  have hfourPi : 0 < 4 * Real.pi := by positivity
  exact lt_of_lt_of_le (div_pos hquarter hfourPi) hlower

end

end ArchonPhysics.CanonicalDecayAnnealedLinearSmallBallLowerBridge
