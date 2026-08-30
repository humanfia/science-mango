import ArchonPhysics.PhyslibFPUTActualBinaryHigherOrderKineticCriterion
import ArchonPhysics.PhyslibFPUTGardenPowerScheduleHigherOrderRPA
import ArchonPhysics.PhyslibFPUTUniformMomentDecoherencePropagation

/-!
# Actual square-cutoff RPA convergence with uniformly bounded moments

This module closes the finite-order algebraic chain without assuming that
each block moment has norm at most one.  For every prefix/next-cluster split,
the actual alpha--beta source is estimated by its unit quadratic and quartic
slot budgets.  A square small-denominator cutoff makes the corresponding
kinetic-time binary defect vanish.  The ordered telescope then upgrades all
binary limits to any fixed finite cluster order, using only uniform bounds on
the individual block moments.

The garden power estimates and linear small-ball bounds remain explicit
premises.  In particular, this theorem does not manufacture the microscopic
recollision cancellation or Jacobian noncancellation estimates.
-/

namespace ArchonPhysics.PhyslibFPUTActualGardenPowerScheduleRPAConvergence

open Filter
open Topology

open ArchonPhysics
open ArchonPhysics.CoerciveHamiltonianPhyslib
open ArchonPhysics.FinitePhaseMonomials
open ArchonPhysics.MassWeightedHamiltonianDynamics
open ArchonPhysics.ModalPhaseMismatch
open ArchonPhysics.PhyslibFPUTActualBinaryHigherOrderKineticCriterion
open ArchonPhysics.PhyslibFPUTActualSourceSlotPotentialSplit
open ArchonPhysics.PhyslibFPUTArbitraryClusterDecoherencePropagation
open ArchonPhysics.PhyslibFPUTGardenPowerScheduleHigherOrderRPA
open ArchonPhysics.PhyslibFPUTHigherOrderClusterFactorizationPropagation
open ArchonPhysics.PhyslibFPUTPositiveTimeCumulantHierarchy
open ArchonPhysics.PhyslibFPUTUniformMomentDecoherencePropagation

noncomputable section

variable {I Omega : Type*}
  [Fintype I] [DecidableEq I] [Nonempty I]
  [Fintype Omega] [DecidableEq Omega]

/-- Unit source-slot budget for one binary split, one system and one
interaction channel. -/
def indexedBinaryUnitSlotBudget
    (cluster : Nat -> Finset I)
    (leftBound rightBound : Nat -> Nat -> I -> Real)
    (system level : Nat) : Real :=
  binaryUnitSlotBudget
    (orderedClusterUnion cluster level) (cluster level)
    (leftBound system level) (rightBound system level)

/-- End-to-end actual finite-order RPA conclusion at kinetic time, with
probability normalization and uniformly bounded fixed-block moments in place
of the stronger pointwise `norm <= 1` assumption. -/
theorem actualFiniteCoerciveOrderedClusterFactorizationDefect_tendsto_zero_squareCutoff_of_uniformMomentBound
    {N : Nat} [NeZero N]
    (weight : Omega -> Real)
    (mass : Omega -> Lattice.PositiveMassConfig N)
    (kappa beta tau : Real)
    (g : Nat -> Real)
    (entry : I -> PhaseSign × Lattice.Site N)
    (p q : Nat -> Omega -> Time -> HilbertConfiguration N)
    (hp : forall system omega,
      Differentiable Real (p system omega))
    (hq : forall system omega,
      Differentiable Real (q system omega))
    (hHamilton : forall system omega,
      SatisfiesHamiltonEquations (mass omega) kappa beta (g system)
        (p system omega) (q system omega))
    (homega : forall omega i,
      0 < modeFrequency (mass omega) (entry i).2)
    (hweight : ∑ omega, weight omega = 1)
    (cluster : Nat -> Finset I)
    (hindex : forall level,
      Disjoint (orderedClusterUnion cluster level) (cluster level))
    (hzero : forall system level,
      actualFiniteCoerciveClusterFactorizationDefect
        weight mass entry (p system) (q system)
          (orderedClusterUnion cluster level) (cluster level) 0 = 0)
    (leftQuadratic leftQuartic rightQuadratic rightQuartic :
      Nat -> Nat -> I -> Real)
    (hleftQuadratic : forall system level,
      ∀ s ∈ Set.uIcc 0 (tau / (g system) ^ 2),
      ∀ slot ∈ orderedClusterUnion cluster level,
        ‖actualLeftQuadraticSourceSlotFactorizationDefect
          weight mass 1 1 entry (p system) (q system)
            (orderedClusterUnion cluster level) (cluster level) slot s‖ <=
          leftQuadratic system level slot)
    (hleftQuartic : forall system level,
      ∀ s ∈ Set.uIcc 0 (tau / (g system) ^ 2),
      ∀ slot ∈ orderedClusterUnion cluster level,
        ‖actualLeftQuarticSourceSlotFactorizationDefect
          weight mass 1 1 entry (p system) (q system)
            (orderedClusterUnion cluster level) (cluster level) slot s‖ <=
          leftQuartic system level slot)
    (hrightQuadratic : forall system level,
      ∀ s ∈ Set.uIcc 0 (tau / (g system) ^ 2),
      ∀ slot ∈ cluster level,
        ‖actualRightQuadraticSourceSlotFactorizationDefect
          weight mass 1 1 entry (p system) (q system)
            (orderedClusterUnion cluster level) (cluster level) slot s‖ <=
          rightQuadratic system level slot)
    (hrightQuartic : forall system level,
      ∀ s ∈ Set.uIcc 0 (tau / (g system) ^ 2),
      ∀ slot ∈ cluster level,
        ‖actualRightQuarticSourceSlotFactorizationDefect
          weight mass 1 1 entry (p system) (q system)
            (orderedClusterUnion cluster level) (cluster level) slot s‖ <=
          rightQuartic system level slot)
    (hleftQuadraticNonneg : forall system level slot,
      slot ∈ orderedClusterUnion cluster level ->
        0 <= leftQuadratic system level slot)
    (hleftQuarticNonneg : forall system level slot,
      slot ∈ orderedClusterUnion cluster level ->
        0 <= leftQuartic system level slot)
    (hrightQuadraticNonneg : forall system level slot,
      slot ∈ cluster level -> 0 <= rightQuadratic system level slot)
    (hrightQuarticNonneg : forall system level slot,
      slot ∈ cluster level -> 0 <= rightQuartic system level slot)
    (quadraticOrder quarticOrder : Nat -> Nat)
    (quadraticBad quarticBad : Nat -> Nat -> Real)
    (quadraticGoodCoefficient quarticGoodCoefficient : Nat -> Real)
    (quadraticGlobal quarticGlobal : Nat -> Real)
    (quadraticSmallBallCoefficient quarticSmallBallCoefficient : Nat -> Real)
    (hg : Tendsto g atTop (nhds 0))
    (hg0 : forall system, g system ≠ 0)
    (hquadraticBad0 : forall system level,
      0 <= quadraticBad system level)
    (hquarticBad0 : forall system level,
      0 <= quarticBad system level)
    (hquadraticBudget : forall system level,
      indexedBinaryUnitSlotBudget cluster
          leftQuadratic rightQuadratic system level <=
        quadraticGardenGoodEnvelope (quadraticOrder level)
            (quadraticGoodCoefficient level) (g system) +
          quadraticGlobal level * quadraticBad system level)
    (hquarticBudget : forall system level,
      indexedBinaryUnitSlotBudget cluster
          leftQuartic rightQuartic system level <=
        quarticGardenGoodEnvelope (quarticOrder level)
            (quarticGoodCoefficient level) (g system) +
          quarticGlobal level * quarticBad system level)
    (hquadraticSmallBall : forall system level,
      quadraticBad system level <=
        quadraticSmallBallCoefficient level *
          squareCouplingCutoff (g system))
    (hquarticSmallBall : forall system level,
      quarticBad system level <=
        quarticSmallBallCoefficient level *
          squareCouplingCutoff (g system))
    (hmoment : forall level, exists bound : Real, forall system,
      ‖actualFiniteCubicEnsembleBlockMoment
        weight mass entry (p system) (q system) (cluster level)
          (tau / (g system) ^ 2)‖ <= bound)
    (count : Nat) :
    Tendsto (fun system =>
      ‖actualFiniteCoerciveOrderedClusterFactorizationDefect
        weight mass entry (p system) (q system) cluster count
          (tau / (g system) ^ 2)‖) atTop (nhds 0) := by
  have hbinaryNorm : forall level, Tendsto (fun system =>
      ‖actualFiniteCoerciveClusterFactorizationDefect
        weight mass entry (p system) (q system)
          (orderedClusterUnion cluster level) (cluster level)
          (tau / (g system) ^ 2)‖) atTop (nhds 0) := by
    intro level
    let quadraticBudget : Nat -> Real := fun system =>
      indexedBinaryUnitSlotBudget cluster
        leftQuadratic rightQuadratic system level
    let quarticBudget : Nat -> Real := fun system =>
      indexedBinaryUnitSlotBudget cluster
        leftQuartic rightQuartic system level
    have hquadraticBudget0 : forall system,
        0 <= quadraticBudget system := by
      intro system
      exact binaryUnitSlotBudget_nonneg
        (orderedClusterUnion cluster level) (cluster level)
        (leftQuadratic system level) (rightQuadratic system level)
        (hleftQuadraticNonneg system level)
        (hrightQuadraticNonneg system level)
    have hquarticBudget0 : forall system,
        0 <= quarticBudget system := by
      intro system
      exact binaryUnitSlotBudget_nonneg
        (orderedClusterUnion cluster level) (cluster level)
        (leftQuartic system level) (rightQuartic system level)
        (hleftQuarticNonneg system level)
        (hrightQuarticNonneg system level)
    have hupper : Tendsto (fun system =>
        (|kappa * g system| * quadraticBudget system +
          |beta * (g system) ^ 2| * quarticBudget system) *
            |tau / (g system) ^ 2|) atTop (nhds 0) := by
      exact coupling_channel_budget_tendsto_zero_at_kineticTime_squareCutoff
        (quadraticOrder level) (quarticOrder level)
        g quadraticBudget quarticBudget
        (fun system => quadraticBad system level)
        (fun system => quarticBad system level)
        kappa beta tau
        (quadraticGoodCoefficient level) (quarticGoodCoefficient level)
        (quadraticGlobal level) (quarticGlobal level)
        (quadraticSmallBallCoefficient level)
        (quarticSmallBallCoefficient level)
        hg hg0 hquadraticBudget0 hquarticBudget0
        (fun system => hquadraticBad0 system level)
        (fun system => hquarticBad0 system level)
        (fun system => by
          simpa only [quadraticBudget] using hquadraticBudget system level)
        (fun system => by
          simpa only [quarticBudget] using hquarticBudget system level)
        (fun system => hquadraticSmallBall system level)
        (fun system => hquarticSmallBall system level)
    apply squeeze_zero
    · intro system
      exact norm_nonneg _
    · intro system
      exact norm_actualFiniteCoerciveClusterFactorizationDefect_le_binary_channels
        weight mass kappa beta (g system) entry
        (p system) (q system) (hp system) (hq system)
        (hHamilton system) homega
        (orderedClusterUnion cluster level) (cluster level)
        (hindex level) (hzero system level)
        (tau / (g system) ^ 2)
        (leftQuadratic system level) (leftQuartic system level)
        (rightQuadratic system level) (rightQuartic system level)
        (hleftQuadratic system level) (hleftQuartic system level)
        (hrightQuadratic system level) (hrightQuartic system level)
        (hleftQuadraticNonneg system level)
        (hleftQuarticNonneg system level)
        (hrightQuadraticNonneg system level)
        (hrightQuarticNonneg system level)
    · exact hupper
  have hbinary : forall level, Tendsto
      (fun system => actualFiniteCoerciveClusterFactorizationDefect
        weight mass entry (p system) (q system)
          (orderedClusterUnion cluster level) (cluster level)
          (tau / (g system) ^ 2)) atTop (nhds 0) := by
    intro level
    exact tendsto_zero_iff_norm_tendsto_zero.mpr (hbinaryNorm level)
  have hraw :=
    actualFiniteCoerciveOrderedClusterFactorizationDefect_tendsto_zero_of_uniformMomentBound
      weight mass entry p q hweight cluster
      (fun system => tau / (g system) ^ 2)
      hbinary hmoment count
  simpa using hraw.norm

end

end ArchonPhysics.PhyslibFPUTActualGardenPowerScheduleRPAConvergence
