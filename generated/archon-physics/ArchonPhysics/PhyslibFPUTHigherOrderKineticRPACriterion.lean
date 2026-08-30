import ArchonPhysics.PhyslibFPUTActualSourceSlotCouplingScaling

/-!
# Coupling-resolved higher-order RPA criterion at kinetic time

The actual arbitrary-cluster propagation estimate is combined with the exact
`kappa * g` / `beta * g^2` source-slot scaling.  The unresolved inputs are now
unit-coupling quadratic and quartic factorization defects on the same actual
Hamiltonian trajectories.

For kinetic time `tau / g^2`, the resulting scalar criterion is explicit:

* the total unit quadratic slot budget divided by `|g|` tends to zero;
* the total unit quartic slot budget tends to zero.

Equivalently, the two physical source channels are `o(g^2)` together.  This
module proves the reduction and limit algebra; it does not assume or prove
the garden/recollision estimates supplying those two limits.
-/

namespace ArchonPhysics.PhyslibFPUTHigherOrderKineticRPACriterion

open Filter
open Topology
open ArchonPhysics
open ArchonPhysics.CoerciveHamiltonianPhyslib
open ArchonPhysics.FinitePhaseMonomials
open ArchonPhysics.MassWeightedHamiltonianDynamics
open ArchonPhysics.ModalPhaseMismatch
open ArchonPhysics.PhyslibFPUTActualClusterSourceSlotClosure
open ArchonPhysics.PhyslibFPUTActualSourceSlotCouplingScaling
open ArchonPhysics.PhyslibFPUTActualSourceSlotPotentialSplit
open ArchonPhysics.PhyslibFPUTArbitraryClusterDecoherencePropagation
open ArchonPhysics.PhyslibFPUTHigherOrderClusterFactorizationPropagation
open ArchonPhysics.PhyslibFPUTPositiveTimeCumulantHierarchy

noncomputable section

variable {I Omega : Type*}
  [Fintype I] [DecidableEq I] [Nonempty I]
  [Fintype Omega] [DecidableEq Omega]

/-- Coupling-weighted error assigned to one nonlinear source slot. -/
def couplingWeightedSlotError
    (kappa beta g quadraticError quarticError : Real) : Real :=
  |kappa * g| * quadraticError + |beta * g ^ 2| * quarticError

theorem couplingWeightedSlotError_nonneg
    {kappa beta g quadraticError quarticError : Real}
    (hquadratic : 0 ≤ quadraticError) (hquartic : 0 ≤ quarticError) :
    0 ≤ couplingWeightedSlotError
      kappa beta g quadraticError quarticError := by
  exact add_nonneg
    (mul_nonneg (abs_nonneg _) hquadratic)
    (mul_nonneg (abs_nonneg _) hquartic)

/-- Fixed-order sum of unit-coupling slot budgets over all prefix splits. -/
def orderedUnitSlotBudget
    (cluster : Nat → Finset I)
    (leftError rightError : Nat → I → Real)
    (count : Nat) : Real :=
  ∑ n ∈ Finset.range count,
    ((∑ slot ∈ orderedClusterUnion cluster n, leftError n slot) +
      ∑ slot ∈ cluster n, rightError n slot)

omit [Fintype I] [Nonempty I] in
/-- A finite unit-slot budget is nonnegative when every slot error is. -/
theorem orderedUnitSlotBudget_nonneg
    (cluster : Nat → Finset I)
    (leftError rightError : Nat → I → Real)
    (hleft : ∀ n slot, 0 ≤ leftError n slot)
    (hright : ∀ n slot, 0 ≤ rightError n slot)
    (count : Nat) :
    0 ≤ orderedUnitSlotBudget cluster leftError rightError count := by
  unfold orderedUnitSlotBudget
  apply Finset.sum_nonneg
  intro n hn
  exact add_nonneg
    (Finset.sum_nonneg fun slot hslot => hleft n slot)
    (Finset.sum_nonneg fun slot hslot => hright n slot)

omit [Fintype I] [Nonempty I] in
/-- The finite sum of coupling-weighted slot errors separates exactly into
the physical quadratic and quartic prefactors. -/
theorem ordered_couplingWeightedSlotError_eq_channels
    (kappa beta g : Real)
    (cluster : Nat → Finset I)
    (leftQuadratic leftQuartic rightQuadratic rightQuartic :
      Nat → I → Real)
    (count : Nat) :
    (∑ n ∈ Finset.range count,
      ((∑ slot ∈ orderedClusterUnion cluster n,
          couplingWeightedSlotError kappa beta g
            (leftQuadratic n slot) (leftQuartic n slot)) +
        ∑ slot ∈ cluster n,
          couplingWeightedSlotError kappa beta g
            (rightQuadratic n slot) (rightQuartic n slot))) =
      |kappa * g| *
          orderedUnitSlotBudget cluster leftQuadratic rightQuadratic count +
        |beta * g ^ 2| *
          orderedUnitSlotBudget cluster leftQuartic rightQuartic count := by
  unfold couplingWeightedSlotError orderedUnitSlotBudget
  simp_rw [Finset.sum_add_distrib]
  simp_rw [← Finset.mul_sum]
  ring

/-- Actual arbitrary-cluster propagation from separate unit-coupling
quadratic and quartic source-slot bounds. -/
theorem norm_actualFiniteCoerciveOrderedClusterFactorizationDefect_le_channels
    {N : Nat} [NeZero N]
    (weight : Omega → Real)
    (mass : Omega → Lattice.PositiveMassConfig N)
    (kappa beta g : Real)
    (entry : I → PhaseSign × Lattice.Site N)
    (p q : Omega → Time → HilbertConfiguration N)
    (hp : ∀ omega, Differentiable Real (p omega))
    (hq : ∀ omega, Differentiable Real (q omega))
    (hHamilton : ∀ omega,
      SatisfiesHamiltonEquations (mass omega) kappa beta g
        (p omega) (q omega))
    (homega : ∀ omega i,
      0 < modeFrequency (mass omega) (entry i).2)
    (cluster : Nat → Finset I)
    (hindex : ∀ n,
      Disjoint (orderedClusterUnion cluster n) (cluster n))
    (hzero : ∀ n,
      actualFiniteCoerciveClusterFactorizationDefect
        weight mass entry p q
          (orderedClusterUnion cluster n) (cluster n) 0 = 0)
    (time : Real)
    (leftQuadratic leftQuartic rightQuadratic rightQuartic :
      Nat → I → Real)
    (hleftQuadratic : ∀ n, ∀ s ∈ Set.uIcc 0 time,
      ∀ slot ∈ orderedClusterUnion cluster n,
        ‖actualLeftQuadraticSourceSlotFactorizationDefect
          weight mass 1 1 entry p q
            (orderedClusterUnion cluster n) (cluster n) slot s‖ ≤
          leftQuadratic n slot)
    (hleftQuartic : ∀ n, ∀ s ∈ Set.uIcc 0 time,
      ∀ slot ∈ orderedClusterUnion cluster n,
        ‖actualLeftQuarticSourceSlotFactorizationDefect
          weight mass 1 1 entry p q
            (orderedClusterUnion cluster n) (cluster n) slot s‖ ≤
          leftQuartic n slot)
    (hrightQuadratic : ∀ n, ∀ s ∈ Set.uIcc 0 time,
      ∀ slot ∈ cluster n,
        ‖actualRightQuadraticSourceSlotFactorizationDefect
          weight mass 1 1 entry p q
            (orderedClusterUnion cluster n) (cluster n) slot s‖ ≤
          rightQuadratic n slot)
    (hrightQuartic : ∀ n, ∀ s ∈ Set.uIcc 0 time,
      ∀ slot ∈ cluster n,
        ‖actualRightQuarticSourceSlotFactorizationDefect
          weight mass 1 1 entry p q
            (orderedClusterUnion cluster n) (cluster n) slot s‖ ≤
          rightQuartic n slot)
    (hempty : actualFiniteCubicEnsembleBlockMoment
      weight mass entry p q ∅ time = 1)
    (hmoment : ∀ n,
      ‖actualFiniteCubicEnsembleBlockMoment
        weight mass entry p q (cluster n) time‖ ≤ 1)
    (hleftQuadraticNonneg : ∀ n slot, 0 ≤ leftQuadratic n slot)
    (hleftQuarticNonneg : ∀ n slot, 0 ≤ leftQuartic n slot)
    (hrightQuadraticNonneg : ∀ n slot, 0 ≤ rightQuadratic n slot)
    (hrightQuarticNonneg : ∀ n slot, 0 ≤ rightQuartic n slot)
    (count : Nat) :
    ‖actualFiniteCoerciveOrderedClusterFactorizationDefect
        weight mass entry p q cluster count time‖ ≤
      (|kappa * g| *
          orderedUnitSlotBudget cluster leftQuadratic rightQuadratic count +
        |beta * g ^ 2| *
          orderedUnitSlotBudget cluster leftQuartic rightQuartic count) *
        |time| := by
  apply le_trans
    (norm_actualFiniteCoerciveOrderedClusterFactorizationDefect_le_slotErrors
      weight mass kappa beta g entry p q hp hq hHamilton homega
        cluster hindex hzero time
        (fun n slot ↦ couplingWeightedSlotError kappa beta g
          (leftQuadratic n slot) (leftQuartic n slot))
        (fun n slot ↦ couplingWeightedSlotError kappa beta g
          (rightQuadratic n slot) (rightQuartic n slot))
        ?_ ?_ hempty hmoment ?_ ?_ count)
  · rw [ordered_couplingWeightedSlotError_eq_channels]
  · intro n s hs slot hslot
    apply (norm_actualLeftSourceSlotFactorizationDefect_le_coupling_channels
      weight mass kappa beta g entry p q
        (orderedClusterUnion cluster n) (cluster n) slot s).trans
    exact add_le_add
      (mul_le_mul_of_nonneg_left
        (hleftQuadratic n s hs slot hslot) (abs_nonneg _))
      (mul_le_mul_of_nonneg_left
        (hleftQuartic n s hs slot hslot) (abs_nonneg _))
  · intro n s hs slot hslot
    apply (norm_actualRightSourceSlotFactorizationDefect_le_coupling_channels
      weight mass kappa beta g entry p q
        (orderedClusterUnion cluster n) (cluster n) slot s).trans
    exact add_le_add
      (mul_le_mul_of_nonneg_left
        (hrightQuadratic n s hs slot hslot) (abs_nonneg _))
      (mul_le_mul_of_nonneg_left
        (hrightQuartic n s hs slot hslot) (abs_nonneg _))
  · intro n slot
    exact couplingWeightedSlotError_nonneg
      (hleftQuadraticNonneg n slot) (hleftQuarticNonneg n slot)
  · intro n slot
    exact couplingWeightedSlotError_nonneg
      (hrightQuadraticNonneg n slot) (hrightQuarticNonneg n slot)

/-! ## Scalar kinetic-time criterion -/

/-- Exact cancellation of the physical powers against kinetic time. -/
theorem coupling_channel_budget_mul_kineticTime
    (kappa beta g tau quadraticBudget quarticBudget : Real)
    (hg : g ≠ 0) :
    (|kappa * g| * quadraticBudget +
        |beta * g ^ 2| * quarticBudget) * |tau / g ^ 2| =
      |kappa| * |tau| * (quadraticBudget / |g|) +
        |beta| * |tau| * quarticBudget := by
  have habsg : |g| ≠ 0 := abs_ne_zero.mpr hg
  simp only [abs_mul, abs_div, abs_pow]
  field_simp [habsg]

/-- The precise asymptotic higher-order RPA criterion: the quadratic unit
budget is `o(|g|)` and the quartic unit budget is `o(1)`. -/
theorem coupling_channel_budget_tendsto_zero_at_kineticTime
    (g quadraticBudget quarticBudget : Nat → Real)
    (kappa beta tau : Real)
    (hg : ∀ n, g n ≠ 0)
    (hquadratic : Tendsto
      (fun n ↦ quadraticBudget n / |g n|) atTop (nhds 0))
    (hquartic : Tendsto quarticBudget atTop (nhds 0)) :
    Tendsto (fun n ↦
      (|kappa * g n| * quadraticBudget n +
        |beta * (g n) ^ 2| * quarticBudget n) *
          |tau / (g n) ^ 2|) atTop (nhds 0) := by
  have heq : (fun n ↦
      (|kappa * g n| * quadraticBudget n +
        |beta * (g n) ^ 2| * quarticBudget n) *
          |tau / (g n) ^ 2|) =
      fun n ↦ |kappa| * |tau| *
          (quadraticBudget n / |g n|) +
        |beta| * |tau| * quarticBudget n := by
    funext n
    exact coupling_channel_budget_mul_kineticTime
      kappa beta (g n) tau (quadraticBudget n) (quarticBudget n) (hg n)
  rw [heq]
  have hquadraticTerm : Tendsto
      (fun n ↦ (|kappa| * |tau|) *
        (quadraticBudget n / |g n|)) atTop (nhds 0) := by
    simpa using (tendsto_const_nhds.mul hquadratic)
  have hquarticTerm : Tendsto
      (fun n ↦ (|beta| * |tau|) * quarticBudget n)
        atTop (nhds 0) := by
    simpa using (tendsto_const_nhds.mul hquartic)
  simpa using hquadraticTerm.add hquarticTerm

end

end ArchonPhysics.PhyslibFPUTHigherOrderKineticRPACriterion
