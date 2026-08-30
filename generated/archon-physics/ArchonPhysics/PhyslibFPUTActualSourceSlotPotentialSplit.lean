import ArchonPhysics.PhyslibFPUTActualClusterSourceSlotClosure

/-!
# Quadratic/quartic split of actual coercive FPUT source-slot defects

Every full coercive alpha-beta source insertion is resolved into the
quadratic-force channel and the quartic-force channel.  Since a
factorization defect is linear in either displayed observable, the actual
slot defects split exactly, before taking norms or limits.

This is finite-volume Hamiltonian algebra.  It does not discard either
channel and does not assume random phases, a Markov approximation, a kinetic
equation, or decay of the resulting correlations.
-/

namespace ArchonPhysics.PhyslibFPUTActualSourceSlotPotentialSplit

open ArchonPhysics
open ArchonPhysics.FinitePhaseMonomials
open ArchonPhysics.PhyslibFPUTActualClusterSourceSlotClosure
open ArchonPhysics.PhyslibFPUTCoercivePositiveTimeCumulantHierarchy
open ArchonPhysics.PhyslibFPUTPositiveTimeCumulantHierarchy
open ArchonPhysics.PhyslibFPUTSourceInsertionClusterExpansion

noncomputable section

variable {I Omega : Type*}
  [Fintype I] [DecidableEq I] [Nonempty I]
  [Fintype Omega] [DecidableEq Omega]

/-! ## Generic linearity identities -/

/-- A finite weighted factorization defect is additive in its left
observable. -/
theorem finiteWeightedObservableFactorizationDefect_add_left
    (weight : Omega → Real)
    (left₁ left₂ right : Omega → Complex) :
    finiteWeightedObservableFactorizationDefect weight
        (fun omega ↦ left₁ omega + left₂ omega) right =
      finiteWeightedObservableFactorizationDefect weight left₁ right +
        finiteWeightedObservableFactorizationDefect weight left₂ right := by
  unfold finiteWeightedObservableFactorizationDefect
    finiteWeightedObservableMoment
  simp only [add_mul, mul_add, Finset.sum_add_distrib]
  ring

/-- A finite weighted factorization defect is additive in its right
observable. -/
theorem finiteWeightedObservableFactorizationDefect_add_right
    (weight : Omega → Real)
    (left right₁ right₂ : Omega → Complex) :
    finiteWeightedObservableFactorizationDefect weight left
        (fun omega ↦ right₁ omega + right₂ omega) =
      finiteWeightedObservableFactorizationDefect weight left right₁ +
        finiteWeightedObservableFactorizationDefect weight left right₂ := by
  unfold finiteWeightedObservableFactorizationDefect
    finiteWeightedObservableMoment
  simp only [mul_add, Finset.sum_add_distrib]
  ring

/-- Source insertion is pointwise additive in the inserted source. -/
theorem sourceInsertedBlockObservable_add_source
    (path source₁ source₂ : Omega → I → Real → Complex)
    (block : Finset I) (slot : I) (time : Real) :
    sourceInsertedBlockObservable path
        (fun omega i s ↦ source₁ omega i s + source₂ omega i s)
        block slot time =
      fun omega ↦
        sourceInsertedBlockObservable path source₁ block slot time omega +
          sourceInsertedBlockObservable path source₂ block slot time omega := by
  funext omega
  unfold sourceInsertedBlockObservable
  ring

/-! ## Actual quadratic and quartic source channels -/

/-- Signed quartic-force source for the same actual finite ensemble. -/
def actualFiniteQuarticEnsembleSource
    {N : Nat} [NeZero N]
    (mass : Omega → Lattice.PositiveMassConfig N)
    (beta g : Real)
    (entry : I → PhaseSign × Lattice.Site N)
    (q : Omega → Time →
      CoerciveHamiltonianPhyslib.HilbertConfiguration N) :
    Omega → I → Real → Complex :=
  fun omega i ↦ signedPhyslibQuarticForceRotatedSource
    (mass omega) beta g (entry i).1 (entry i).2 (q omega)

/-- Pointwise exact split of the actual full ensemble source. -/
theorem actualFiniteCoerciveEnsembleSource_eq_quadratic_add_quartic
    {N : Nat} [NeZero N]
    (mass : Omega → Lattice.PositiveMassConfig N)
    (kappa beta g : Real)
    (entry : I → PhaseSign × Lattice.Site N)
    (q : Omega → Time →
      CoerciveHamiltonianPhyslib.HilbertConfiguration N) :
    actualFiniteCoerciveEnsembleSource mass kappa beta g entry q =
      fun omega i time ↦
        actualFiniteCubicEnsembleSource mass kappa g entry q omega i time +
          actualFiniteQuarticEnsembleSource mass beta g entry q omega i time := by
  funext omega i time
  exact signedPhyslibCoerciveRotatedSource_eq_quadratic_add_quarticForce
    (mass omega) kappa beta g (entry i).1 (entry i).2 (q omega) time

/-- Left source-slot defect containing only the quadratic-force channel. -/
def actualLeftQuadraticSourceSlotFactorizationDefect
    {N : Nat} [NeZero N]
    (weight : Omega → Real)
    (mass : Omega → Lattice.PositiveMassConfig N)
    (kappa g : Real)
    (entry : I → PhaseSign × Lattice.Site N)
    (p q : Omega → Time →
      CoerciveHamiltonianPhyslib.HilbertConfiguration N)
    (left right : Finset I) (slot : I) (time : Real) : Complex :=
  finiteWeightedObservableFactorizationDefect weight
    (sourceInsertedBlockObservable
      (actualFiniteCubicEnsemblePath mass entry p q)
      (actualFiniteCubicEnsembleSource mass kappa g entry q)
      left slot time)
    (pathBlockObservable
      (actualFiniteCubicEnsemblePath mass entry p q) right time)

/-- Left source-slot defect containing only the quartic-force channel. -/
def actualLeftQuarticSourceSlotFactorizationDefect
    {N : Nat} [NeZero N]
    (weight : Omega → Real)
    (mass : Omega → Lattice.PositiveMassConfig N)
    (beta g : Real)
    (entry : I → PhaseSign × Lattice.Site N)
    (p q : Omega → Time →
      CoerciveHamiltonianPhyslib.HilbertConfiguration N)
    (left right : Finset I) (slot : I) (time : Real) : Complex :=
  finiteWeightedObservableFactorizationDefect weight
    (sourceInsertedBlockObservable
      (actualFiniteCubicEnsemblePath mass entry p q)
      (actualFiniteQuarticEnsembleSource mass beta g entry q)
      left slot time)
    (pathBlockObservable
      (actualFiniteCubicEnsemblePath mass entry p q) right time)

/-- Right source-slot defect containing only the quadratic-force channel. -/
def actualRightQuadraticSourceSlotFactorizationDefect
    {N : Nat} [NeZero N]
    (weight : Omega → Real)
    (mass : Omega → Lattice.PositiveMassConfig N)
    (kappa g : Real)
    (entry : I → PhaseSign × Lattice.Site N)
    (p q : Omega → Time →
      CoerciveHamiltonianPhyslib.HilbertConfiguration N)
    (left right : Finset I) (slot : I) (time : Real) : Complex :=
  finiteWeightedObservableFactorizationDefect weight
    (pathBlockObservable
      (actualFiniteCubicEnsemblePath mass entry p q) left time)
    (sourceInsertedBlockObservable
      (actualFiniteCubicEnsemblePath mass entry p q)
      (actualFiniteCubicEnsembleSource mass kappa g entry q)
      right slot time)

/-- Right source-slot defect containing only the quartic-force channel. -/
def actualRightQuarticSourceSlotFactorizationDefect
    {N : Nat} [NeZero N]
    (weight : Omega → Real)
    (mass : Omega → Lattice.PositiveMassConfig N)
    (beta g : Real)
    (entry : I → PhaseSign × Lattice.Site N)
    (p q : Omega → Time →
      CoerciveHamiltonianPhyslib.HilbertConfiguration N)
    (left right : Finset I) (slot : I) (time : Real) : Complex :=
  finiteWeightedObservableFactorizationDefect weight
    (pathBlockObservable
      (actualFiniteCubicEnsemblePath mass entry p q) left time)
    (sourceInsertedBlockObservable
      (actualFiniteCubicEnsemblePath mass entry p q)
      (actualFiniteQuarticEnsembleSource mass beta g entry q)
      right slot time)

/-! ## Exact slot splits and norm bounds -/

theorem actualLeftSourceSlotFactorizationDefect_eq_quadratic_add_quartic
    {N : Nat} [NeZero N]
    (weight : Omega → Real)
    (mass : Omega → Lattice.PositiveMassConfig N)
    (kappa beta g : Real)
    (entry : I → PhaseSign × Lattice.Site N)
    (p q : Omega → Time →
      CoerciveHamiltonianPhyslib.HilbertConfiguration N)
    (left right : Finset I) (slot : I) (time : Real) :
    actualLeftSourceSlotFactorizationDefect
        weight mass kappa beta g entry p q left right slot time =
      actualLeftQuadraticSourceSlotFactorizationDefect
          weight mass kappa g entry p q left right slot time +
        actualLeftQuarticSourceSlotFactorizationDefect
          weight mass beta g entry p q left right slot time := by
  unfold actualLeftSourceSlotFactorizationDefect
    actualLeftQuadraticSourceSlotFactorizationDefect
    actualLeftQuarticSourceSlotFactorizationDefect
  rw [actualFiniteCoerciveEnsembleSource_eq_quadratic_add_quartic]
  rw [sourceInsertedBlockObservable_add_source]
  exact finiteWeightedObservableFactorizationDefect_add_left _ _ _ _

theorem actualRightSourceSlotFactorizationDefect_eq_quadratic_add_quartic
    {N : Nat} [NeZero N]
    (weight : Omega → Real)
    (mass : Omega → Lattice.PositiveMassConfig N)
    (kappa beta g : Real)
    (entry : I → PhaseSign × Lattice.Site N)
    (p q : Omega → Time →
      CoerciveHamiltonianPhyslib.HilbertConfiguration N)
    (left right : Finset I) (slot : I) (time : Real) :
    actualRightSourceSlotFactorizationDefect
        weight mass kappa beta g entry p q left right slot time =
      actualRightQuadraticSourceSlotFactorizationDefect
          weight mass kappa g entry p q left right slot time +
        actualRightQuarticSourceSlotFactorizationDefect
          weight mass beta g entry p q left right slot time := by
  unfold actualRightSourceSlotFactorizationDefect
    actualRightQuadraticSourceSlotFactorizationDefect
    actualRightQuarticSourceSlotFactorizationDefect
  rw [actualFiniteCoerciveEnsembleSource_eq_quadratic_add_quartic]
  rw [sourceInsertedBlockObservable_add_source]
  exact finiteWeightedObservableFactorizationDefect_add_right _ _ _ _

theorem norm_actualLeftSourceSlotFactorizationDefect_le_channels
    {N : Nat} [NeZero N]
    (weight : Omega → Real)
    (mass : Omega → Lattice.PositiveMassConfig N)
    (kappa beta g : Real)
    (entry : I → PhaseSign × Lattice.Site N)
    (p q : Omega → Time →
      CoerciveHamiltonianPhyslib.HilbertConfiguration N)
    (left right : Finset I) (slot : I) (time : Real) :
    ‖actualLeftSourceSlotFactorizationDefect
        weight mass kappa beta g entry p q left right slot time‖ ≤
      ‖actualLeftQuadraticSourceSlotFactorizationDefect
        weight mass kappa g entry p q left right slot time‖ +
      ‖actualLeftQuarticSourceSlotFactorizationDefect
        weight mass beta g entry p q left right slot time‖ := by
  rw [actualLeftSourceSlotFactorizationDefect_eq_quadratic_add_quartic]
  exact norm_add_le _ _

theorem norm_actualRightSourceSlotFactorizationDefect_le_channels
    {N : Nat} [NeZero N]
    (weight : Omega → Real)
    (mass : Omega → Lattice.PositiveMassConfig N)
    (kappa beta g : Real)
    (entry : I → PhaseSign × Lattice.Site N)
    (p q : Omega → Time →
      CoerciveHamiltonianPhyslib.HilbertConfiguration N)
    (left right : Finset I) (slot : I) (time : Real) :
    ‖actualRightSourceSlotFactorizationDefect
        weight mass kappa beta g entry p q left right slot time‖ ≤
      ‖actualRightQuadraticSourceSlotFactorizationDefect
        weight mass kappa g entry p q left right slot time‖ +
      ‖actualRightQuarticSourceSlotFactorizationDefect
        weight mass beta g entry p q left right slot time‖ := by
  rw [actualRightSourceSlotFactorizationDefect_eq_quadratic_add_quartic]
  exact norm_add_le _ _

end

end ArchonPhysics.PhyslibFPUTActualSourceSlotPotentialSplit
