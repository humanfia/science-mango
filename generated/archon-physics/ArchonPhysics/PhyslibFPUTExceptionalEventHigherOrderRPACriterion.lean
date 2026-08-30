import ArchonPhysics.PhyslibFPUTHigherOrderKineticRPACriterion

/-!
# Exceptional-event closure of the higher-order kinetic RPA criterion

The actual alpha-beta source hierarchy reduces kinetic-time factorization to
two unit-channel budgets:

* the quadratic unit budget must be `o(|g|)`;
* the quartic unit budget must be `o(1)`.

This file turns ordinary good/bad-event estimates into exactly those two
limits.  For a linear small-ball law `bad <= B * cutoff`, the quadratic
channel therefore needs `cutoff / |g| -> 0`, whereas the quartic channel only
needs `cutoff -> 0`.  The good-set remainders have the analogous scales.

No small-ball estimate, Jacobian noncancellation, garden cancellation,
recollision estimate, RPA renewal, or kinetic equation is assumed implicitly:
all such inputs remain explicit premises of the final theorem.
-/

namespace ArchonPhysics.PhyslibFPUTExceptionalEventHigherOrderRPACriterion

open Filter
open Topology
open ArchonPhysics.PhyslibFPUTHigherOrderKineticRPACriterion

noncomputable section

/-- A linear small-ball estimate with cutoff `o(|g|)` makes the exceptional
probability `o(|g|)`. -/
theorem badBudget_div_abs_tendsto_zero_of_linearSmallBall
    (g cutoff bad : Nat -> Real) (coefficient : Real)
    (hbad0 : forall n, 0 <= bad n)
    (hbad : forall n, bad n <= coefficient * cutoff n)
    (hcutoff : Tendsto (fun n => cutoff n / |g n|)
      atTop (nhds 0)) :
    Tendsto (fun n => bad n / |g n|) atTop (nhds 0) := by
  apply squeeze_zero
  · intro n
    exact div_nonneg (hbad0 n) (abs_nonneg _)
  · intro n
    calc
      bad n / |g n| <= (coefficient * cutoff n) / |g n| :=
        div_le_div_of_nonneg_right (hbad n) (abs_nonneg _)
      _ = coefficient * (cutoff n / |g n|) := by ring
  · simpa using
      (tendsto_const_nhds.mul hcutoff :
        Tendsto (fun n : Nat => coefficient * (cutoff n / |g n|))
          atTop (nhds (coefficient * 0)))

/-- A linear small-ball estimate with a vanishing cutoff makes the exceptional
probability vanish. -/
theorem badBudget_tendsto_zero_of_linearSmallBall
    (cutoff bad : Nat -> Real) (coefficient : Real)
    (hbad0 : forall n, 0 <= bad n)
    (hbad : forall n, bad n <= coefficient * cutoff n)
    (hcutoff : Tendsto cutoff atTop (nhds 0)) :
    Tendsto bad atTop (nhds 0) := by
  apply squeeze_zero
  · intro n
    exact hbad0 n
  · intro n
    exact hbad n
  · simpa using
      (tendsto_const_nhds.mul hcutoff :
        Tendsto (fun n : Nat => coefficient * cutoff n)
          atTop (nhds (coefficient * 0)))

/-- Good/bad decomposition at the quadratic scale.  A bounded global bad-set
cost is represented by the constant `globalBound`. -/
theorem budget_div_abs_tendsto_zero_of_good_bad
    (g budget good bad : Nat -> Real) (globalBound : Real)
    (hbudget0 : forall n, 0 <= budget n)
    (hbudget : forall n,
      budget n <= good n + globalBound * bad n)
    (hgood : Tendsto (fun n => good n / |g n|)
      atTop (nhds 0))
    (hbad : Tendsto (fun n => bad n / |g n|)
      atTop (nhds 0)) :
    Tendsto (fun n => budget n / |g n|) atTop (nhds 0) := by
  apply squeeze_zero
  · intro n
    exact div_nonneg (hbudget0 n) (abs_nonneg _)
  · intro n
    calc
      budget n / |g n| <=
          (good n + globalBound * bad n) / |g n| :=
        div_le_div_of_nonneg_right (hbudget n) (abs_nonneg _)
      _ = good n / |g n| +
          globalBound * (bad n / |g n|) := by ring
  · simpa using hgood.add
      (tendsto_const_nhds.mul hbad :
        Tendsto (fun n : Nat =>
          globalBound * (bad n / |g n|))
          atTop (nhds (globalBound * 0)))

/-- Good/bad decomposition at the quartic scale. -/
theorem budget_tendsto_zero_of_good_bad
    (budget good bad : Nat -> Real) (globalBound : Real)
    (hbudget0 : forall n, 0 <= budget n)
    (hbudget : forall n,
      budget n <= good n + globalBound * bad n)
    (hgood : Tendsto good atTop (nhds 0))
    (hbad : Tendsto bad atTop (nhds 0)) :
    Tendsto budget atTop (nhds 0) := by
  apply squeeze_zero
  · intro n
    exact hbudget0 n
  · intro n
    exact hbudget n
  · simpa using hgood.add
      (tendsto_const_nhds.mul hbad :
        Tendsto (fun n : Nat => globalBound * bad n)
          atTop (nhds (globalBound * 0)))

/-- Linear small-ball estimates plus good-set errors imply the exact pair of
unit-channel limits consumed by the kinetic-time coupling theorem. -/
theorem higherOrder_channel_criteria_of_linearSmallBall
    (g quadraticBudget quarticBudget : Nat -> Real)
    (quadraticGood quarticGood : Nat -> Real)
    (quadraticBad quarticBad : Nat -> Real)
    (quadraticCutoff quarticCutoff : Nat -> Real)
    (quadraticGlobal quarticGlobal : Real)
    (quadraticSmallBallCoefficient quarticSmallBallCoefficient : Real)
    (hquadraticBudget0 : forall n, 0 <= quadraticBudget n)
    (hquarticBudget0 : forall n, 0 <= quarticBudget n)
    (hquadraticBad0 : forall n, 0 <= quadraticBad n)
    (hquarticBad0 : forall n, 0 <= quarticBad n)
    (hquadraticBudget : forall n,
      quadraticBudget n <=
        quadraticGood n + quadraticGlobal * quadraticBad n)
    (hquarticBudget : forall n,
      quarticBudget n <=
        quarticGood n + quarticGlobal * quarticBad n)
    (hquadraticSmallBall : forall n,
      quadraticBad n <=
        quadraticSmallBallCoefficient * quadraticCutoff n)
    (hquarticSmallBall : forall n,
      quarticBad n <=
        quarticSmallBallCoefficient * quarticCutoff n)
    (hquadraticGood : Tendsto
      (fun n => quadraticGood n / |g n|) atTop (nhds 0))
    (hquarticGood : Tendsto quarticGood atTop (nhds 0))
    (hquadraticCutoff : Tendsto
      (fun n => quadraticCutoff n / |g n|) atTop (nhds 0))
    (hquarticCutoff : Tendsto quarticCutoff atTop (nhds 0)) :
    Tendsto (fun n => quadraticBudget n / |g n|)
        atTop (nhds 0) /\
      Tendsto quarticBudget atTop (nhds 0) := by
  have hquadraticBad :
      Tendsto (fun n => quadraticBad n / |g n|)
        atTop (nhds 0) :=
    badBudget_div_abs_tendsto_zero_of_linearSmallBall
      g quadraticCutoff quadraticBad quadraticSmallBallCoefficient
        hquadraticBad0 hquadraticSmallBall hquadraticCutoff
  have hquarticBad :
      Tendsto quarticBad atTop (nhds 0) :=
    badBudget_tendsto_zero_of_linearSmallBall
      quarticCutoff quarticBad quarticSmallBallCoefficient
        hquarticBad0 hquarticSmallBall hquarticCutoff
  exact
    ⟨budget_div_abs_tendsto_zero_of_good_bad
        g quadraticBudget quadraticGood quadraticBad quadraticGlobal
          hquadraticBudget0 hquadraticBudget hquadraticGood hquadraticBad,
      budget_tendsto_zero_of_good_bad
        quarticBudget quarticGood quarticBad quarticGlobal
          hquarticBudget0 hquarticBudget hquarticGood hquarticBad⟩

/-- End-to-end scalar closure: once the displayed good-set and linear
small-ball estimates hold, the actual coupling-weighted higher-order source
budget vanishes at time `tau / g^2`. -/
theorem coupling_channel_budget_tendsto_zero_at_kineticTime_of_good_bad
    (g quadraticBudget quarticBudget : Nat -> Real)
    (quadraticGood quarticGood : Nat -> Real)
    (quadraticBad quarticBad : Nat -> Real)
    (quadraticCutoff quarticCutoff : Nat -> Real)
    (kappa beta tau quadraticGlobal quarticGlobal : Real)
    (quadraticSmallBallCoefficient quarticSmallBallCoefficient : Real)
    (hg : forall n, g n ≠ 0)
    (hquadraticBudget0 : forall n, 0 <= quadraticBudget n)
    (hquarticBudget0 : forall n, 0 <= quarticBudget n)
    (hquadraticBad0 : forall n, 0 <= quadraticBad n)
    (hquarticBad0 : forall n, 0 <= quarticBad n)
    (hquadraticBudget : forall n,
      quadraticBudget n <=
        quadraticGood n + quadraticGlobal * quadraticBad n)
    (hquarticBudget : forall n,
      quarticBudget n <=
        quarticGood n + quarticGlobal * quarticBad n)
    (hquadraticSmallBall : forall n,
      quadraticBad n <=
        quadraticSmallBallCoefficient * quadraticCutoff n)
    (hquarticSmallBall : forall n,
      quarticBad n <=
        quarticSmallBallCoefficient * quarticCutoff n)
    (hquadraticGood : Tendsto
      (fun n => quadraticGood n / |g n|) atTop (nhds 0))
    (hquarticGood : Tendsto quarticGood atTop (nhds 0))
    (hquadraticCutoff : Tendsto
      (fun n => quadraticCutoff n / |g n|) atTop (nhds 0))
    (hquarticCutoff : Tendsto quarticCutoff atTop (nhds 0)) :
    Tendsto (fun n =>
      (|kappa * g n| * quadraticBudget n +
        |beta * (g n) ^ 2| * quarticBudget n) *
          |tau / (g n) ^ 2|) atTop (nhds 0) := by
  obtain ⟨hquadratic, hquartic⟩ :=
    higherOrder_channel_criteria_of_linearSmallBall
      g quadraticBudget quarticBudget quadraticGood quarticGood
        quadraticBad quarticBad quadraticCutoff quarticCutoff
        quadraticGlobal quarticGlobal quadraticSmallBallCoefficient
        quarticSmallBallCoefficient hquadraticBudget0 hquarticBudget0
        hquadraticBad0 hquarticBad0 hquadraticBudget hquarticBudget
        hquadraticSmallBall hquarticSmallBall hquadraticGood hquarticGood
        hquadraticCutoff hquarticCutoff
  exact coupling_channel_budget_tendsto_zero_at_kineticTime
    g quadraticBudget quarticBudget kappa beta tau hg
      hquadratic hquartic

end

end ArchonPhysics.PhyslibFPUTExceptionalEventHigherOrderRPACriterion
