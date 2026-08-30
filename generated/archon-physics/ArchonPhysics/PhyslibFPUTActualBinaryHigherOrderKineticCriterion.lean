import ArchonPhysics.PhyslibFPUTActualSourceSlotCouplingScaling

/-!
# A binary actual FPUT higher-order factorization criterion

For one fixed pair of disjoint finite mode blocks, this file combines three
already verified facts:

* the actual alpha--beta Hamiltonian differentiates the block-factorization
  defect into its source defect;
* that source defect is the sum of the individual left and right source-slot
  defects;
* quadratic and quartic source slots carry the exact factors `kappa * g` and
  `beta * g^2`.

Consequently, unit-coupling bounds on every displayed slot give the direct
single-split estimate

`‖defect(t)‖ ≤ (|kappa*g| * Q + |beta*g^2| * C) * |t|`,

where `Q` and `C` are the corresponding left-plus-right finite slot sums.
This is only a finite-time factorization-defect criterion.  No RPA closure,
decay, kinetic limit, or re-randomization is asserted.
-/

namespace ArchonPhysics.PhyslibFPUTActualBinaryHigherOrderKineticCriterion

open ArchonPhysics
open ArchonPhysics.CoerciveHamiltonianPhyslib
open ArchonPhysics.FinitePhaseMonomials
open ArchonPhysics.MassWeightedHamiltonianDynamics
open ArchonPhysics.ModalPhaseMismatch
open ArchonPhysics.PhyslibFPUTActualClusterSourceSlotClosure
open ArchonPhysics.PhyslibFPUTActualSourceSlotCouplingScaling
open ArchonPhysics.PhyslibFPUTActualSourceSlotPotentialSplit
open ArchonPhysics.PhyslibFPUTHigherOrderClusterFactorizationPropagation

noncomputable section

variable {I Omega : Type*}
  [Fintype I] [DecidableEq I] [Nonempty I]
  [Fintype Omega] [DecidableEq Omega]

/-- The unit-coupling budget on one fixed left/right block split. -/
def binaryUnitSlotBudget
    (left right : Finset I)
    (leftBound rightBound : I → Real) : Real :=
  (∑ slot ∈ left, leftBound slot) +
    ∑ slot ∈ right, rightBound slot

omit [Fintype I] [DecidableEq I] [Nonempty I] in
/-- A binary slot budget is nonnegative when its displayed slot bounds are
nonnegative. -/
theorem binaryUnitSlotBudget_nonneg
    (left right : Finset I)
    (leftBound rightBound : I → Real)
    (hleft : ∀ slot ∈ left, 0 ≤ leftBound slot)
    (hright : ∀ slot ∈ right, 0 ≤ rightBound slot) :
    0 ≤ binaryUnitSlotBudget left right leftBound rightBound := by
  exact add_nonneg
    (Finset.sum_nonneg fun slot hslot => hleft slot hslot)
    (Finset.sum_nonneg fun slot hslot => hright slot hslot)

omit [Fintype I] [DecidableEq I] [Nonempty I] in
/-- The finite sum of coupling-weighted binary slot bounds separates exactly
into its quadratic and quartic channel budgets. -/
theorem binary_couplingWeightedSlotSum_eq_channels
    (kappa beta g : Real) (left right : Finset I)
    (leftQuadratic leftQuartic rightQuadratic rightQuartic :
      I → Real) :
    ((∑ slot ∈ left,
        (|kappa * g| * leftQuadratic slot +
          |beta * g ^ 2| * leftQuartic slot)) +
      ∑ slot ∈ right,
        (|kappa * g| * rightQuadratic slot +
          |beta * g ^ 2| * rightQuartic slot)) =
      |kappa * g| * binaryUnitSlotBudget
        left right leftQuadratic rightQuadratic +
      |beta * g ^ 2| * binaryUnitSlotBudget
        left right leftQuartic rightQuartic := by
  unfold binaryUnitSlotBudget
  simp_rw [Finset.sum_add_distrib]
  simp_rw [← Finset.mul_sum]
  ring

/-- Fixed-left/right actual alpha--beta factorization-defect estimate from
nonnegative unit quadratic and quartic source-slot bounds. -/
theorem norm_actualFiniteCoerciveClusterFactorizationDefect_le_binary_channels
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
    (left right : Finset I) (hindex : Disjoint left right)
    (hzero : actualFiniteCoerciveClusterFactorizationDefect
      weight mass entry p q left right 0 = 0)
    (time : Real)
    (leftQuadratic leftQuartic rightQuadratic rightQuartic :
      I → Real)
    (hleftQuadratic : ∀ s ∈ Set.uIcc 0 time, ∀ slot ∈ left,
      ‖actualLeftQuadraticSourceSlotFactorizationDefect
        weight mass 1 1 entry p q left right slot s‖ ≤
          leftQuadratic slot)
    (hleftQuartic : ∀ s ∈ Set.uIcc 0 time, ∀ slot ∈ left,
      ‖actualLeftQuarticSourceSlotFactorizationDefect
        weight mass 1 1 entry p q left right slot s‖ ≤
          leftQuartic slot)
    (hrightQuadratic : ∀ s ∈ Set.uIcc 0 time, ∀ slot ∈ right,
      ‖actualRightQuadraticSourceSlotFactorizationDefect
        weight mass 1 1 entry p q left right slot s‖ ≤
          rightQuadratic slot)
    (hrightQuartic : ∀ s ∈ Set.uIcc 0 time, ∀ slot ∈ right,
      ‖actualRightQuarticSourceSlotFactorizationDefect
        weight mass 1 1 entry p q left right slot s‖ ≤
          rightQuartic slot)
    (hleftQuadraticNonneg : ∀ slot ∈ left,
      0 ≤ leftQuadratic slot)
    (hleftQuarticNonneg : ∀ slot ∈ left,
      0 ≤ leftQuartic slot)
    (hrightQuadraticNonneg : ∀ slot ∈ right,
      0 ≤ rightQuadratic slot)
    (hrightQuarticNonneg : ∀ slot ∈ right,
      0 ≤ rightQuartic slot) :
    ‖actualFiniteCoerciveClusterFactorizationDefect
        weight mass entry p q left right time‖ ≤
      (|kappa * g| * binaryUnitSlotBudget
          left right leftQuadratic rightQuadratic +
        |beta * g ^ 2| * binaryUnitSlotBudget
          left right leftQuartic rightQuartic) * |time| := by
  have hquadraticBudgetNonneg :
      0 ≤ binaryUnitSlotBudget
        left right leftQuadratic rightQuadratic :=
    binaryUnitSlotBudget_nonneg left right
      leftQuadratic rightQuadratic
      hleftQuadraticNonneg hrightQuadraticNonneg
  have hquarticBudgetNonneg :
      0 ≤ binaryUnitSlotBudget
        left right leftQuartic rightQuartic :=
    binaryUnitSlotBudget_nonneg left right
      leftQuartic rightQuartic
      hleftQuarticNonneg hrightQuarticNonneg
  have hchannelNonneg : 0 ≤
      |kappa * g| * binaryUnitSlotBudget
          left right leftQuadratic rightQuadratic +
        |beta * g ^ 2| * binaryUnitSlotBudget
          left right leftQuartic rightQuartic :=
    add_nonneg
      (mul_nonneg (abs_nonneg _) hquadraticBudgetNonneg)
      (mul_nonneg (abs_nonneg _) hquarticBudgetNonneg)
  apply norm_actualFiniteCoerciveClusterFactorizationDefect_le
    weight mass kappa beta g entry p q hp hq hHamilton homega
      left right hzero time
      (|kappa * g| * binaryUnitSlotBudget
          left right leftQuadratic rightQuadratic +
        |beta * g ^ 2| * binaryUnitSlotBudget
          left right leftQuartic rightQuartic)
  intro s hs
  apply (norm_actualFiniteCoerciveClusterFactorizationDefectSource_le_slotSums
    weight mass kappa beta g entry p q hp hq hHamilton homega
      hindex s).trans
  calc
    (∑ slot ∈ left,
        ‖actualLeftSourceSlotFactorizationDefect
          weight mass kappa beta g entry p q left right slot s‖) +
      ∑ slot ∈ right,
        ‖actualRightSourceSlotFactorizationDefect
          weight mass kappa beta g entry p q left right slot s‖ ≤
      (∑ slot ∈ left,
        (|kappa * g| * leftQuadratic slot +
          |beta * g ^ 2| * leftQuartic slot)) +
      ∑ slot ∈ right,
        (|kappa * g| * rightQuadratic slot +
          |beta * g ^ 2| * rightQuartic slot) := by
        apply add_le_add
        · apply Finset.sum_le_sum
          intro slot hslot
          apply (norm_actualLeftSourceSlotFactorizationDefect_le_coupling_channels
            weight mass kappa beta g entry p q
              left right slot s).trans
          exact add_le_add
            (mul_le_mul_of_nonneg_left
              (hleftQuadratic s hs slot hslot) (abs_nonneg _))
            (mul_le_mul_of_nonneg_left
              (hleftQuartic s hs slot hslot) (abs_nonneg _))
        · apply Finset.sum_le_sum
          intro slot hslot
          apply (norm_actualRightSourceSlotFactorizationDefect_le_coupling_channels
            weight mass kappa beta g entry p q
              left right slot s).trans
          exact add_le_add
            (mul_le_mul_of_nonneg_left
              (hrightQuadratic s hs slot hslot) (abs_nonneg _))
            (mul_le_mul_of_nonneg_left
              (hrightQuartic s hs slot hslot) (abs_nonneg _))
    _ = |kappa * g| * binaryUnitSlotBudget
          left right leftQuadratic rightQuadratic +
        |beta * g ^ 2| * binaryUnitSlotBudget
          left right leftQuartic rightQuartic :=
      binary_couplingWeightedSlotSum_eq_channels
        kappa beta g left right leftQuadratic leftQuartic
          rightQuadratic rightQuartic

end

end ArchonPhysics.PhyslibFPUTActualBinaryHigherOrderKineticCriterion
