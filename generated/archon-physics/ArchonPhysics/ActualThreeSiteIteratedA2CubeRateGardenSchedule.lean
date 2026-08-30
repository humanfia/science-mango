import ArchonPhysics.ActualThreeSiteIteratedA2OuterGlobalSmallBallRate
import ArchonPhysics.PhyslibFPUTExceptionalEventHigherOrderRPACriterion
import ArchonPhysics.PhyslibFPUTGardenPowerScheduleHigherOrderRPA

/-!
# A sextic garden cutoff matched to the three-site cube-rate small ball

The global three-site outer estimate has the explicit Hölder form

`P(|mismatch| <= rho^3) <= 840 rho`.

It is therefore not a linear small-ball law in the mismatch width.  At the
denominator cutoff `gamma(g) = |g|^6`, however, the exceptional probability
is at most `840 |g|^2`.  This is `o(|g|)`, exactly the bad-set scale required
by the quadratic kinetic-time RPA criterion.

The smaller denominator cutoff changes the regular-good power bookkeeping.
After `order` inverse denominators, sufficient numerator powers are

* `6 * order + 2` in the quadratic channel;
* `6 * order + 1` in the quartic channel.

This file proves that scalar schedule and connects its exceptional budget to
the actual iid three-mass mismatch law.  It does not prove that the complete
Hamiltonian garden expansion supplies these numerator powers, nor does it
extend the fixed three-site estimate uniformly in the lattice volume.
-/

namespace ArchonPhysics.ActualThreeSiteIteratedA2CubeRateGardenSchedule

open Filter Topology
open ArchonPhysics
open ArchonPhysics.ActualThreeSiteIteratedA2OuterGlobalSmallBallRate
open ArchonPhysics.ActualThreeSiteIteratedA2OuterQuantitativeSmallBall
open ArchonPhysics.PhyslibFPUTExceptionalEventHigherOrderRPACriterion
open ArchonPhysics.PhyslibFPUTGardenPowerScheduleHigherOrderRPA
open ArchonPhysics.RandomEnsemble
open ArchonPhysics.ThreeParameterSpectralAveragingDensity
open MeasureTheory
open scoped ENNReal

noncomputable section

/-- The denominator cutoff dictated by the proved cube-rate small-ball law. -/
def sexticCouplingCutoff (g : Real) : Real :=
  |g| ^ 6

/-- The real exceptional probability at the sextic mismatch cutoff. -/
def threeSiteOuterSexticCutoffBadBudget (g : Real) : Real :=
  (iidMassTripleLaw
    (threeSiteOuterNearMismatchEvent (sexticCouplingCutoff g))).toReal

/-- Direct substitution `rho = |g|^2` in the proved cube-rate endpoint. -/
theorem iidMassTripleLaw_threeSiteOuterNearMismatchEvent_sextic_le
    {g : Real} (hg : g ≠ 0) :
    iidMassTripleLaw
        (threeSiteOuterNearMismatchEvent (sexticCouplingCutoff g)) <=
      840 * ENNReal.ofReal (squareCouplingCutoff g) := by
  have habs : 0 < |g| := abs_pos.mpr hg
  have hrho : 0 < |g| ^ 2 := pow_pos habs 2
  have h := iidMassTripleLaw_threeSiteOuterNearMismatchEvent_cube_le hrho
  have hpower : (|g| ^ 2) ^ 3 = |g| ^ 6 := by ring
  rw [hpower] at h
  simpa [sexticCouplingCutoff, squareCouplingCutoff] using h

theorem threeSiteOuterSexticCutoffBadBudget_nonneg (g : Real) :
    0 <= threeSiteOuterSexticCutoffBadBudget g :=
  ENNReal.toReal_nonneg

/-- Real-valued form consumed by the existing exceptional-event RPA API. -/
theorem threeSiteOuterSexticCutoffBadBudget_le
    {g : Real} (hg : g ≠ 0) :
    threeSiteOuterSexticCutoffBadBudget g <=
      840 * squareCouplingCutoff g := by
  have hENN :=
    iidMassTripleLaw_threeSiteOuterNearMismatchEvent_sextic_le hg
  have hfinite :
      (840 * ENNReal.ofReal (squareCouplingCutoff g) : ENNReal) ≠ ∞ := by
    finiteness
  have hreal := ENNReal.toReal_mono hfinite hENN
  rw [ENNReal.toReal_mul, ENNReal.toReal_ofNat,
    ENNReal.toReal_ofReal (by
      unfold squareCouplingCutoff
      positivity)] at hreal
  exact hreal

/-- Regular-good quadratic envelope for the sextic denominator cutoff. -/
def cubeRateQuadraticGardenGoodEnvelope
    (order : Nat) (coefficient g : Real) : Real :=
  coefficient * |g| ^ (6 * order + 2) /
    sexticCouplingCutoff g ^ order

/-- Regular-good quartic envelope for the sextic denominator cutoff. -/
def cubeRateQuarticGardenGoodEnvelope
    (order : Nat) (coefficient g : Real) : Real :=
  coefficient * |g| ^ (6 * order + 1) /
    sexticCouplingCutoff g ^ order

/-- The effective exceptional scale `|g|^2` is `o(|g|)`. -/
theorem squareCouplingCutoff_div_abs_cubeRate
    {g : Real} (hg : g ≠ 0) :
    squareCouplingCutoff g / |g| = |g| :=
  squareCouplingCutoff_div_abs hg

/-- After paying the kinetic quadratic deficit, the regular-good envelope
has one positive coupling power left. -/
theorem cubeRateQuadraticGardenGoodEnvelope_div_abs
    (order : Nat) (coefficient : Real) {g : Real} (hg : g ≠ 0) :
    cubeRateQuadraticGardenGoodEnvelope order coefficient g / |g| =
      coefficient * |g| := by
  have habsg : |g| ≠ 0 := abs_ne_zero.mpr hg
  unfold cubeRateQuadraticGardenGoodEnvelope sexticCouplingCutoff
  rw [pow_add, pow_mul]
  field_simp [habsg]

/-- The quartic regular-good envelope itself retains one positive coupling
power. -/
theorem cubeRateQuarticGardenGoodEnvelope_eq
    (order : Nat) (coefficient : Real) {g : Real} (hg : g ≠ 0) :
    cubeRateQuarticGardenGoodEnvelope order coefficient g =
      coefficient * |g| := by
  have habsg : |g| ≠ 0 := abs_ne_zero.mpr hg
  unfold cubeRateQuarticGardenGoodEnvelope sexticCouplingCutoff
  rw [pow_add, pow_mul]
  field_simp [habsg]

theorem sexticCouplingCutoff_tendsto_zero
    (g : Nat -> Real) (hg : Tendsto g atTop (nhds 0)) :
    Tendsto (fun n => sexticCouplingCutoff (g n))
      atTop (nhds 0) := by
  simpa [sexticCouplingCutoff] using hg.abs.pow 6

theorem squareCouplingCutoff_div_abs_cubeRate_tendsto_zero
    (g : Nat -> Real) (hg : Tendsto g atTop (nhds 0))
    (hg0 : forall n, g n ≠ 0) :
    Tendsto (fun n => squareCouplingCutoff (g n) / |g n|)
      atTop (nhds 0) :=
  squareCouplingCutoff_div_abs_tendsto_zero g hg hg0

theorem squareCouplingCutoff_cubeRate_tendsto_zero
    (g : Nat -> Real) (hg : Tendsto g atTop (nhds 0)) :
    Tendsto (fun n => squareCouplingCutoff (g n))
      atTop (nhds 0) :=
  squareCouplingCutoff_tendsto_zero g hg

theorem cubeRateQuadraticGardenGoodEnvelope_div_abs_tendsto_zero
    (order : Nat) (coefficient : Real)
    (g : Nat -> Real) (hg : Tendsto g atTop (nhds 0))
    (hg0 : forall n, g n ≠ 0) :
    Tendsto (fun n =>
      cubeRateQuadraticGardenGoodEnvelope order coefficient (g n) /
        |g n|) atTop (nhds 0) := by
  have habs : Tendsto (fun n => |g n|) atTop (nhds 0) := by
    simpa only [abs_zero] using hg.abs
  have heq : (fun n =>
      cubeRateQuadraticGardenGoodEnvelope order coefficient (g n) /
        |g n|) = fun n => coefficient * |g n| := by
    funext n
    exact cubeRateQuadraticGardenGoodEnvelope_div_abs
      order coefficient (hg0 n)
  rw [heq]
  simpa using
    (tendsto_const_nhds.mul habs :
      Tendsto (fun n : Nat => coefficient * |g n|)
        atTop (nhds (coefficient * 0)))

theorem cubeRateQuarticGardenGoodEnvelope_tendsto_zero
    (order : Nat) (coefficient : Real)
    (g : Nat -> Real) (hg : Tendsto g atTop (nhds 0))
    (hg0 : forall n, g n ≠ 0) :
    Tendsto (fun n =>
      cubeRateQuarticGardenGoodEnvelope order coefficient (g n))
        atTop (nhds 0) := by
  have habs : Tendsto (fun n => |g n|) atTop (nhds 0) := by
    simpa only [abs_zero] using hg.abs
  have heq : (fun n =>
      cubeRateQuarticGardenGoodEnvelope order coefficient (g n)) =
        fun n => coefficient * |g n| := by
    funext n
    exact cubeRateQuarticGardenGoodEnvelope_eq
      order coefficient (hg0 n)
  rw [heq]
  simpa using
    (tendsto_const_nhds.mul habs :
      Tendsto (fun n : Nat => coefficient * |g n|)
        atTop (nhds (coefficient * 0)))

/-- End-to-end scalar RPA schedule matched to a cube-rate small-ball law.
The bad-event hypotheses use the proved effective scale `|g|^2`; the
regular-good hypotheses retain the genuine sextic denominator cutoff through
the `6r+2` and `6r+1` envelopes. -/
theorem coupling_channel_budget_tendsto_zero_at_kineticTime_cubeRate
    (quadraticOrder quarticOrder : Nat)
    (g quadraticBudget quarticBudget quadraticBad quarticBad : Nat -> Real)
    (kappa beta tau : Real)
    (quadraticGoodCoefficient quarticGoodCoefficient : Real)
    (quadraticGlobal quarticGlobal : Real)
    (quadraticSmallBallCoefficient quarticSmallBallCoefficient : Real)
    (hg : Tendsto g atTop (nhds 0))
    (hg0 : forall n, g n ≠ 0)
    (hquadraticBudget0 : forall n, 0 <= quadraticBudget n)
    (hquarticBudget0 : forall n, 0 <= quarticBudget n)
    (hquadraticBad0 : forall n, 0 <= quadraticBad n)
    (hquarticBad0 : forall n, 0 <= quarticBad n)
    (hquadraticBudget : forall n,
      quadraticBudget n <=
        cubeRateQuadraticGardenGoodEnvelope quadraticOrder
            quadraticGoodCoefficient (g n) +
          quadraticGlobal * quadraticBad n)
    (hquarticBudget : forall n,
      quarticBudget n <=
        cubeRateQuarticGardenGoodEnvelope quarticOrder
            quarticGoodCoefficient (g n) +
          quarticGlobal * quarticBad n)
    (hquadraticSmallBall : forall n,
      quadraticBad n <=
        quadraticSmallBallCoefficient * squareCouplingCutoff (g n))
    (hquarticSmallBall : forall n,
      quarticBad n <=
        quarticSmallBallCoefficient * squareCouplingCutoff (g n)) :
    Tendsto (fun n =>
      (|kappa * g n| * quadraticBudget n +
        |beta * (g n) ^ 2| * quarticBudget n) *
          |tau / (g n) ^ 2|) atTop (nhds 0) := by
  exact
    coupling_channel_budget_tendsto_zero_at_kineticTime_of_good_bad
      g quadraticBudget quarticBudget
      (fun n => cubeRateQuadraticGardenGoodEnvelope quadraticOrder
        quadraticGoodCoefficient (g n))
      (fun n => cubeRateQuarticGardenGoodEnvelope quarticOrder
        quarticGoodCoefficient (g n))
      quadraticBad quarticBad
      (fun n => squareCouplingCutoff (g n))
      (fun n => squareCouplingCutoff (g n))
      kappa beta tau quadraticGlobal quarticGlobal
      quadraticSmallBallCoefficient quarticSmallBallCoefficient hg0
      hquadraticBudget0 hquarticBudget0 hquadraticBad0 hquarticBad0
      hquadraticBudget hquarticBudget hquadraticSmallBall hquarticSmallBall
      (cubeRateQuadraticGardenGoodEnvelope_div_abs_tendsto_zero
        quadraticOrder quadraticGoodCoefficient g hg hg0)
      (cubeRateQuarticGardenGoodEnvelope_tendsto_zero
        quarticOrder quarticGoodCoefficient g hg hg0)
      (squareCouplingCutoff_div_abs_cubeRate_tendsto_zero g hg hg0)
      (squareCouplingCutoff_cubeRate_tendsto_zero g hg)

end

end ArchonPhysics.ActualThreeSiteIteratedA2CubeRateGardenSchedule
