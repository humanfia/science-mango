import ArchonPhysics.PhyslibFPUTGardenPowerScheduleHigherOrderRPA

/-!
# Actual Hamiltonian square-cutoff higher-order RPA closure

This module combines three previously separate verified layers:

1. the exact alpha-beta Hamiltonian source-slot decomposition;
2. arbitrary finite-cluster factorization-defect propagation;
3. the square-cutoff garden power schedule.

For a sequence of genuine Hamiltonian trajectories with `g_n -> 0`, the
conclusion is convergence of the actual ordered cluster factorization defect
at kinetic time `tau / g_n^2`.

The remaining inputs are displayed pointwise: unit-coupling source-slot
bounds, their good/bad garden estimates, and linear small-ball bounds.  In
particular this theorem does not construct the `2*r+2` / `2*r+1` coupling
gains, Jacobian noncancellation, or recollision decay.
-/

namespace ArchonPhysics.PhyslibFPUTActualGardenPowerScheduleRPAClosure

open Filter
open Topology
open ArchonPhysics
open ArchonPhysics.CoerciveHamiltonianPhyslib
open ArchonPhysics.FinitePhaseMonomials
open ArchonPhysics.MassWeightedHamiltonianDynamics
open ArchonPhysics.ModalPhaseMismatch
open ArchonPhysics.PhyslibFPUTActualSourceSlotPotentialSplit
open ArchonPhysics.PhyslibFPUTArbitraryClusterDecoherencePropagation
open ArchonPhysics.PhyslibFPUTGardenPowerScheduleHigherOrderRPA
open ArchonPhysics.PhyslibFPUTHigherOrderClusterFactorizationPropagation
open ArchonPhysics.PhyslibFPUTHigherOrderKineticRPACriterion
open ArchonPhysics.PhyslibFPUTPositiveTimeCumulantHierarchy

noncomputable section

variable {I Omega : Type*}
  [Fintype I] [DecidableEq I] [Nonempty I]
  [Fintype Omega] [DecidableEq Omega]

/-- Unit-slot budget for one member of a sequence of Hamiltonian systems. -/
def indexedOrderedUnitSlotBudget
    (cluster : Nat -> Finset I)
    (leftError rightError : Nat -> Nat -> I -> Real)
    (count system : Nat) : Real :=
  orderedUnitSlotBudget cluster
    (leftError system) (rightError system) count

omit [Fintype I] [Nonempty I] in
theorem indexedOrderedUnitSlotBudget_nonneg
    (cluster : Nat -> Finset I)
    (leftError rightError : Nat -> Nat -> I -> Real)
    (hleft : forall system level slot,
      0 <= leftError system level slot)
    (hright : forall system level slot,
      0 <= rightError system level slot)
    (count system : Nat) :
    0 <= indexedOrderedUnitSlotBudget
      cluster leftError rightError count system := by
  exact orderedUnitSlotBudget_nonneg
    cluster (leftError system) (rightError system)
      (hleft system) (hright system) count

/-- End-to-end conditional closure for an actual alpha-beta Hamiltonian
sequence and any fixed finite ordered cluster family. -/
theorem actualFiniteCoerciveOrderedClusterFactorizationDefect_tendsto_zero_squareCutoff
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
    (hempty : forall system,
      actualFiniteCubicEnsembleBlockMoment
        weight mass entry (p system) (q system) ∅
          (tau / (g system) ^ 2) = 1)
    (hmoment : forall system level,
      ‖actualFiniteCubicEnsembleBlockMoment
        weight mass entry (p system) (q system) (cluster level)
          (tau / (g system) ^ 2)‖ <= 1)
    (hleftQuadraticNonneg : forall system level slot,
      0 <= leftQuadratic system level slot)
    (hleftQuarticNonneg : forall system level slot,
      0 <= leftQuartic system level slot)
    (hrightQuadraticNonneg : forall system level slot,
      0 <= rightQuadratic system level slot)
    (hrightQuarticNonneg : forall system level slot,
      0 <= rightQuartic system level slot)
    (count quadraticOrder quarticOrder : Nat)
    (quadraticBad quarticBad : Nat -> Real)
    (quadraticGoodCoefficient quarticGoodCoefficient : Real)
    (quadraticGlobal quarticGlobal : Real)
    (quadraticSmallBallCoefficient quarticSmallBallCoefficient : Real)
    (hg : Tendsto g atTop (nhds 0))
    (hg0 : forall system, g system ≠ 0)
    (hquadraticBad0 : forall system, 0 <= quadraticBad system)
    (hquarticBad0 : forall system, 0 <= quarticBad system)
    (hquadraticBudget : forall system,
      indexedOrderedUnitSlotBudget cluster
          leftQuadratic rightQuadratic count system <=
        quadraticGardenGoodEnvelope quadraticOrder
            quadraticGoodCoefficient (g system) +
          quadraticGlobal * quadraticBad system)
    (hquarticBudget : forall system,
      indexedOrderedUnitSlotBudget cluster
          leftQuartic rightQuartic count system <=
        quarticGardenGoodEnvelope quarticOrder
            quarticGoodCoefficient (g system) +
          quarticGlobal * quarticBad system)
    (hquadraticSmallBall : forall system,
      quadraticBad system <=
        quadraticSmallBallCoefficient * squareCouplingCutoff (g system))
    (hquarticSmallBall : forall system,
      quarticBad system <=
        quarticSmallBallCoefficient * squareCouplingCutoff (g system)) :
    Tendsto (fun system =>
      ‖actualFiniteCoerciveOrderedClusterFactorizationDefect
        weight mass entry (p system) (q system) cluster count
          (tau / (g system) ^ 2)‖) atTop (nhds 0) := by
  let quadraticBudget : Nat -> Real := fun system =>
    indexedOrderedUnitSlotBudget cluster
      leftQuadratic rightQuadratic count system
  let quarticBudget : Nat -> Real := fun system =>
    indexedOrderedUnitSlotBudget cluster
      leftQuartic rightQuartic count system
  have hquadraticBudget0 : forall system, 0 <= quadraticBudget system := by
    intro system
    exact indexedOrderedUnitSlotBudget_nonneg
      cluster leftQuadratic rightQuadratic
        hleftQuadraticNonneg hrightQuadraticNonneg count system
  have hquarticBudget0 : forall system, 0 <= quarticBudget system := by
    intro system
    exact indexedOrderedUnitSlotBudget_nonneg
      cluster leftQuartic rightQuartic
        hleftQuarticNonneg hrightQuarticNonneg count system
  have hupper : Tendsto (fun system =>
      (|kappa * g system| * quadraticBudget system +
        |beta * (g system) ^ 2| * quarticBudget system) *
          |tau / (g system) ^ 2|) atTop (nhds 0) := by
    exact
      coupling_channel_budget_tendsto_zero_at_kineticTime_squareCutoff
        quadraticOrder quarticOrder g quadraticBudget quarticBudget
        quadraticBad quarticBad kappa beta tau
        quadraticGoodCoefficient quarticGoodCoefficient
        quadraticGlobal quarticGlobal quadraticSmallBallCoefficient
        quarticSmallBallCoefficient hg hg0 hquadraticBudget0
        hquarticBudget0 hquadraticBad0 hquarticBad0
        (by simpa only [quadraticBudget] using hquadraticBudget)
        (by simpa only [quarticBudget] using hquarticBudget)
        hquadraticSmallBall hquarticSmallBall
  apply squeeze_zero
  · intro system
    exact norm_nonneg _
  · intro system
    exact
      norm_actualFiniteCoerciveOrderedClusterFactorizationDefect_le_channels
        weight mass kappa beta (g system) entry
        (p system) (q system) (hp system) (hq system)
        (hHamilton system) homega cluster hindex (hzero system)
        (tau / (g system) ^ 2)
        (leftQuadratic system) (leftQuartic system)
        (rightQuadratic system) (rightQuartic system)
        (hleftQuadratic system) (hleftQuartic system)
        (hrightQuadratic system) (hrightQuartic system)
        (hempty system) (hmoment system)
        (hleftQuadraticNonneg system)
        (hleftQuarticNonneg system)
        (hrightQuadraticNonneg system)
        (hrightQuarticNonneg system) count
  · exact hupper

end

end ArchonPhysics.PhyslibFPUTActualGardenPowerScheduleRPAClosure
