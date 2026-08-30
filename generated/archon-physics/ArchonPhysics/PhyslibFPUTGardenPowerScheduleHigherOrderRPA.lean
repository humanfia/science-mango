import ArchonPhysics.PhyslibFPUTExceptionalEventHigherOrderRPACriterion

/-!
# A concrete garden power schedule for higher-order RPA closure

A linear small-ball law forces the quadratic exceptional probability to be
`o(|g|)`.  The explicit schedule `cutoff = |g|^2` achieves this.  If a
regular garden term loses `r` inverse denominators, then the following
coupling powers are sufficient:

* quadratic channel: `|g|^(2*r+2) / cutoff^r`;
* quartic channel: `|g|^(2*r+1) / cutoff^r`.

After division by the quadratic target scale `|g|`, respectively without
division in the quartic channel, both envelopes are exactly a constant times
`|g|`.  This is an algebraic/asymptotic closure theorem, not a proof that
the actual FPUT garden remainder has these powers.  That model-specific
cancellation and recollision estimate remains an explicit premise.
-/

namespace ArchonPhysics.PhyslibFPUTGardenPowerScheduleHigherOrderRPA

open Filter
open Topology
open ArchonPhysics.PhyslibFPUTExceptionalEventHigherOrderRPACriterion

noncomputable section

/-- The common small-denominator cutoff schedule. -/
def squareCouplingCutoff (g : Real) : Real :=
  |g| ^ 2

/-- Good-set envelope for a quadratic source channel with `r` inverse-gap
losses and the sufficient `2*r+2` coupling powers. -/
def quadraticGardenGoodEnvelope
    (order : Nat) (coefficient g : Real) : Real :=
  coefficient * |g| ^ (2 * order + 2) /
    squareCouplingCutoff g ^ order

/-- Good-set envelope for a quartic source channel with `r` inverse-gap
losses and the sufficient `2*r+1` coupling powers. -/
def quarticGardenGoodEnvelope
    (order : Nat) (coefficient g : Real) : Real :=
  coefficient * |g| ^ (2 * order + 1) /
    squareCouplingCutoff g ^ order

theorem squareCouplingCutoff_div_abs
    {g : Real} (hg : g ≠ 0) :
    squareCouplingCutoff g / |g| = |g| := by
  have habsg : |g| ≠ 0 := abs_ne_zero.mpr hg
  unfold squareCouplingCutoff
  field_simp [habsg]

theorem quadraticGardenGoodEnvelope_div_abs
    (order : Nat) (coefficient : Real) {g : Real} (hg : g ≠ 0) :
    quadraticGardenGoodEnvelope order coefficient g / |g| =
      coefficient * |g| := by
  have habsg : |g| ≠ 0 := abs_ne_zero.mpr hg
  unfold quadraticGardenGoodEnvelope squareCouplingCutoff
  rw [pow_add, pow_mul]
  field_simp [habsg]

theorem quarticGardenGoodEnvelope_eq
    (order : Nat) (coefficient : Real) {g : Real} (hg : g ≠ 0) :
    quarticGardenGoodEnvelope order coefficient g =
      coefficient * |g| := by
  have habsg : |g| ≠ 0 := abs_ne_zero.mpr hg
  unfold quarticGardenGoodEnvelope squareCouplingCutoff
  rw [pow_add, pow_mul]
  field_simp [habsg]

theorem squareCouplingCutoff_tendsto_zero
    (g : Nat -> Real)
    (hg : Tendsto g atTop (nhds 0)) :
    Tendsto (fun n => squareCouplingCutoff (g n))
      atTop (nhds 0) := by
  simpa [squareCouplingCutoff] using hg.abs.pow 2

theorem squareCouplingCutoff_div_abs_tendsto_zero
    (g : Nat -> Real)
    (hg : Tendsto g atTop (nhds 0))
    (hg0 : forall n, g n ≠ 0) :
    Tendsto (fun n => squareCouplingCutoff (g n) / |g n|)
      atTop (nhds 0) := by
  have heq : (fun n => squareCouplingCutoff (g n) / |g n|) =
      fun n => |g n| := by
    funext n
    exact squareCouplingCutoff_div_abs (hg0 n)
  rw [heq]
  simpa using hg.abs

theorem quadraticGardenGoodEnvelope_div_abs_tendsto_zero
    (order : Nat) (coefficient : Real)
    (g : Nat -> Real)
    (hg : Tendsto g atTop (nhds 0))
    (hg0 : forall n, g n ≠ 0) :
    Tendsto (fun n =>
      quadraticGardenGoodEnvelope order coefficient (g n) / |g n|)
        atTop (nhds 0) := by
  have habs : Tendsto (fun n => |g n|) atTop (nhds 0) := by
    simpa only [abs_zero] using hg.abs
  have heq : (fun n =>
      quadraticGardenGoodEnvelope order coefficient (g n) / |g n|) =
      fun n => coefficient * |g n| := by
    funext n
    exact quadraticGardenGoodEnvelope_div_abs
      order coefficient (hg0 n)
  rw [heq]
  simpa using
    (tendsto_const_nhds.mul habs :
      Tendsto (fun n : Nat => coefficient * |g n|)
        atTop (nhds (coefficient * 0)))

theorem quarticGardenGoodEnvelope_tendsto_zero
    (order : Nat) (coefficient : Real)
    (g : Nat -> Real)
    (hg : Tendsto g atTop (nhds 0))
    (hg0 : forall n, g n ≠ 0) :
    Tendsto (fun n =>
      quarticGardenGoodEnvelope order coefficient (g n))
        atTop (nhds 0) := by
  have habs : Tendsto (fun n => |g n|) atTop (nhds 0) := by
    simpa only [abs_zero] using hg.abs
  have heq : (fun n =>
      quarticGardenGoodEnvelope order coefficient (g n)) =
      fun n => coefficient * |g n| := by
    funext n
    exact quarticGardenGoodEnvelope_eq order coefficient (hg0 n)
  rw [heq]
  simpa using
    (tendsto_const_nhds.mul habs :
      Tendsto (fun n : Nat => coefficient * |g n|)
        atTop (nhds (coefficient * 0)))

/-- Concrete square-cutoff closure.  The only model-specific inputs left are
upper bounds of the actual channel budgets by the displayed regular-garden
envelopes plus a bounded cost times the corresponding exceptional
probability, and linear small-ball bounds for those probabilities. -/
theorem coupling_channel_budget_tendsto_zero_at_kineticTime_squareCutoff
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
        quadraticGardenGoodEnvelope quadraticOrder
            quadraticGoodCoefficient (g n) +
          quadraticGlobal * quadraticBad n)
    (hquarticBudget : forall n,
      quarticBudget n <=
        quarticGardenGoodEnvelope quarticOrder
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
      (fun n => quadraticGardenGoodEnvelope quadraticOrder
        quadraticGoodCoefficient (g n))
      (fun n => quarticGardenGoodEnvelope quarticOrder
        quarticGoodCoefficient (g n))
      quadraticBad quarticBad
      (fun n => squareCouplingCutoff (g n))
      (fun n => squareCouplingCutoff (g n))
      kappa beta tau quadraticGlobal quarticGlobal
      quadraticSmallBallCoefficient quarticSmallBallCoefficient hg0
      hquadraticBudget0 hquarticBudget0 hquadraticBad0 hquarticBad0
      hquadraticBudget hquarticBudget hquadraticSmallBall
      hquarticSmallBall
      (quadraticGardenGoodEnvelope_div_abs_tendsto_zero
        quadraticOrder quadraticGoodCoefficient g hg hg0)
      (quarticGardenGoodEnvelope_tendsto_zero
        quarticOrder quarticGoodCoefficient g hg hg0)
      (squareCouplingCutoff_div_abs_tendsto_zero g hg hg0)
      (squareCouplingCutoff_tendsto_zero g hg)

end

end ArchonPhysics.PhyslibFPUTGardenPowerScheduleHigherOrderRPA
