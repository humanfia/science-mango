import ArchonPhysics.PhyslibFPUTActualBranchingA1SquareCutoffBudget

/-!
# Actual branching A1 adapter for the garden power schedule

For a fixed actual branching tree and a fixed family of heterogeneous
compact-atlas certificates, this module uses the genuine fiber-law bad-event
probability as both exceptional budgets in the quadratic and quartic source
channels.  The square-cutoff estimate proved in the preceding module
discharges both abstract linear-small-ball premises of the garden schedule.

The good-garden estimates remain explicit hypotheses.  In particular, this
adapter does not prove the model-specific coupling powers on the good set,
does not control recollisions, and does not establish Markov/RPA renewal.
The common scalar-path compatibility, cumulative Jacobian lower bounds used
to construct the supplied certificates, and compact-tail estimate are not
hidden.
-/

namespace ArchonPhysics.PhyslibFPUTActualBranchingA1GardenScheduleAdapter

open Filter Topology
open ArchonPhysics
open ArchonPhysics.PhyslibFPUTActualBranchingA1CompactSmallBall
open ArchonPhysics.PhyslibFPUTActualBranchingA1IntervalSelector
open ArchonPhysics.PhyslibFPUTActualBranchingA1SquareCutoffBudget
open ArchonPhysics.PhyslibFPUTArbitraryGardenCompactSmallBall
open ArchonPhysics.PhyslibFPUTBinaryInteractionTreeCouples
open ArchonPhysics.PhyslibFPUTGardenPowerScheduleHigherOrderRPA
open ArchonPhysics.RandomEnsemble
open MeasureTheory Set

noncomputable section

/-- Fixed-tree actual A1 adapter for the kinetic-time weighted source budget.
The same genuine bad-event probability is used in both source channels.
Only the two abstract small-ball premises are discharged; the displayed
good-garden budget bounds remain model-specific inputs. -/
theorem coupling_channel_budget_tendsto_zero_at_kineticTime_actualA1Branching
    {N : Nat} [NeZero N]
    (tree : RandomEigenmodeBinaryTree (Lattice.Site N))
    (fiber : ActualA1BranchingOccurrenceFiberFamily tree)
    (certificate : ∀ index : ActualA1BranchingIntervalIndex tree,
      OrdinaryGardenCoordinateCompactAtlas
        (actualA1BranchingOccurrenceFiberCoordinate tree fiber index))
    (K : ActualA1BranchingIntervalIndex tree → Set Real)
    (hcompact : ∀ index, (certificate index).compactSet = K index)
    (quadraticOrder quarticOrder : Nat)
    (g quadraticBudget quarticBudget : Nat → Real)
    (kappa beta tau : Real)
    (quadraticGoodCoefficient quarticGoodCoefficient : Real)
    (quadraticGlobal quarticGlobal : Real)
    (Btail : Real)
    (htail : ∀ n, actualA1BranchingCompactTailBudget tree K ≤
      Btail * squareCouplingCutoff (g n))
    (hg : Tendsto g atTop (nhds 0))
    (hg0 : ∀ n, g n ≠ 0)
    (hquadraticBudget0 : ∀ n, 0 ≤ quadraticBudget n)
    (hquarticBudget0 : ∀ n, 0 ≤ quarticBudget n)
    (hquadraticBudget : ∀ n,
      quadraticBudget n ≤
        quadraticGardenGoodEnvelope quadraticOrder
            quadraticGoodCoefficient (g n) +
          quadraticGlobal *
            actualA1BranchingSquareCutoffBadBudget tree fiber (g n))
    (hquarticBudget : ∀ n,
      quarticBudget n ≤
        quarticGardenGoodEnvelope quarticOrder
            quarticGoodCoefficient (g n) +
          quarticGlobal *
            actualA1BranchingSquareCutoffBadBudget tree fiber (g n)) :
    Tendsto (fun n =>
      (|kappa * g n| * quadraticBudget n +
        |beta * (g n) ^ 2| * quarticBudget n) *
          |tau / (g n) ^ 2|) atTop (nhds 0) := by
  let bad : Nat → Real := fun n =>
    actualA1BranchingSquareCutoffBadBudget tree fiber (g n)
  have hbad0 : ∀ n, 0 ≤ bad n := by
    intro n
    exact actualA1BranchingSquareCutoffBadBudget_nonneg
      tree fiber (g n)
  have hsmall : ∀ n, bad n ≤
      (actualA1BranchingFactorialSquareRealCoefficient
          tree fiber certificate + Btail) *
        squareCouplingCutoff (g n) := by
    intro n
    exact actualA1BranchingSquareCutoffBadBudget_le_of_compactTail
      tree fiber certificate K hcompact Btail (g n) (htail n)
  exact
    coupling_channel_budget_tendsto_zero_at_kineticTime_squareCutoff
      quadraticOrder quarticOrder g quadraticBudget quarticBudget bad bad
      kappa beta tau quadraticGoodCoefficient quarticGoodCoefficient
      quadraticGlobal quarticGlobal
      (actualA1BranchingFactorialSquareRealCoefficient
        tree fiber certificate + Btail)
      (actualA1BranchingFactorialSquareRealCoefficient
        tree fiber certificate + Btail)
      hg hg0 hquadraticBudget0 hquarticBudget0 hbad0 hbad0
      (by simpa only [bad] using hquadraticBudget)
      (by simpa only [bad] using hquarticBudget)
      hsmall hsmall

/-- Null compact exception specialization.  It removes the tail coefficient
without changing any of the still-explicit good-garden hypotheses. -/
theorem coupling_channel_budget_tendsto_zero_at_kineticTime_actualA1Branching_of_compactTail_zero
    {N : Nat} [NeZero N]
    (tree : RandomEigenmodeBinaryTree (Lattice.Site N))
    (fiber : ActualA1BranchingOccurrenceFiberFamily tree)
    (certificate : ∀ index : ActualA1BranchingIntervalIndex tree,
      OrdinaryGardenCoordinateCompactAtlas
        (actualA1BranchingOccurrenceFiberCoordinate tree fiber index))
    (K : ActualA1BranchingIntervalIndex tree → Set Real)
    (hcompact : ∀ index, (certificate index).compactSet = K index)
    (htail :
      massCoordinateLaw
        (actualA1BranchingOccurrenceCompactBadEvent tree K) = 0)
    (quadraticOrder quarticOrder : Nat)
    (g quadraticBudget quarticBudget : Nat → Real)
    (kappa beta tau : Real)
    (quadraticGoodCoefficient quarticGoodCoefficient : Real)
    (quadraticGlobal quarticGlobal : Real)
    (hg : Tendsto g atTop (nhds 0))
    (hg0 : ∀ n, g n ≠ 0)
    (hquadraticBudget0 : ∀ n, 0 ≤ quadraticBudget n)
    (hquarticBudget0 : ∀ n, 0 ≤ quarticBudget n)
    (hquadraticBudget : ∀ n,
      quadraticBudget n ≤
        quadraticGardenGoodEnvelope quadraticOrder
            quadraticGoodCoefficient (g n) +
          quadraticGlobal *
            actualA1BranchingSquareCutoffBadBudget tree fiber (g n))
    (hquarticBudget : ∀ n,
      quarticBudget n ≤
        quarticGardenGoodEnvelope quarticOrder
            quarticGoodCoefficient (g n) +
          quarticGlobal *
            actualA1BranchingSquareCutoffBadBudget tree fiber (g n)) :
    Tendsto (fun n =>
      (|kappa * g n| * quadraticBudget n +
        |beta * (g n) ^ 2| * quarticBudget n) *
          |tau / (g n) ^ 2|) atTop (nhds 0) := by
  apply coupling_channel_budget_tendsto_zero_at_kineticTime_actualA1Branching
    tree fiber certificate K hcompact quadraticOrder quarticOrder
    g quadraticBudget quarticBudget kappa beta tau
    quadraticGoodCoefficient quarticGoodCoefficient
    quadraticGlobal quarticGlobal 0
  · intro n
    simp [actualA1BranchingCompactTailBudget, htail]
  · exact hg
  · exact hg0
  · exact hquadraticBudget0
  · exact hquarticBudget0
  · exact hquadraticBudget
  · exact hquarticBudget

end

end ArchonPhysics.PhyslibFPUTActualBranchingA1GardenScheduleAdapter
