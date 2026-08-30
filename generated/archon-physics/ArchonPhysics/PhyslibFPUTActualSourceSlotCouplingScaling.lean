import ArchonPhysics.PhyslibFPUTActualSourceSlotPotentialSplit

/-!
# Explicit coupling scaling of actual coercive FPUT source-slot defects

The quadratic and quartic source channels carry the exact real couplings
`kappa * g` and `beta * g^2`.  This module pulls those scalars through the
phase/conjugate action, source insertion, finite expectation, and
factorization defect.  Consequently every full source-slot defect is bounded
by

`|kappa * g| * (unit quadratic defect) +
  |beta * g^2| * (unit quartic defect)`.

The unit-coupling defects remain correlations of the actual Hamiltonian
trajectory.  No decay or random-phase closure is asserted.
-/

namespace ArchonPhysics.PhyslibFPUTActualSourceSlotCouplingScaling

open ArchonPhysics
open ArchonPhysics.FinitePhaseMonomials
open ArchonPhysics.ForcedComplexModeDuhamel
open ArchonPhysics.ModalNonlinearForce
open ArchonPhysics.PhyslibFPUTActualClusterSourceSlotClosure
open ArchonPhysics.PhyslibFPUTActualSourceSlotPotentialSplit
open ArchonPhysics.PhyslibFPUTCoercivePositiveTimeCumulantHierarchy
open ArchonPhysics.PhyslibFPUTFirstPicardDecomposition
open ArchonPhysics.PhyslibFPUTPositiveTimeCumulantHierarchy
open ArchonPhysics.PhyslibFPUTSourceInsertionClusterExpansion
open ArchonPhysics.PhyslibFPUTBinaryInteractionTreeCouples
open ArchonPhysics.PhyslibHamiltonDuhamel

noncomputable section

variable {I Omega : Type*}
  [Fintype I] [DecidableEq I] [Nonempty I]
  [Fintype Omega] [DecidableEq Omega]

/-! ## Physical source scaling -/

/-- The quadratic rotated source contains exactly one factor `kappa * g`. -/
theorem physlibQuadraticRotatedSource_eq_coupling_mul_unit
    {N : Nat} [NeZero N]
    (m : Lattice.PositiveMassConfig N) (kappa g : Real)
    (mode : Lattice.Site N)
    (q : Time → CoerciveHamiltonianPhyslib.HilbertConfiguration N)
    (time : Real) :
    physlibQuadraticRotatedSource m kappa g mode q time =
      ((kappa * g : Real) : Complex) *
        physlibQuadraticRotatedSource m 1 1 mode q time := by
  unfold physlibQuadraticRotatedSource physlibModeRotatedSource
    physlibModeTensorForce tensorNonlinearForce forcedModeSource
  push_cast
  ring

/-- The quartic-force rotated source contains exactly one factor
`beta * g^2`. -/
theorem physlibQuarticForceRotatedSource_eq_coupling_mul_unit
    {N : Nat} [NeZero N]
    (m : Lattice.PositiveMassConfig N) (beta g : Real)
    (mode : Lattice.Site N)
    (q : Time → CoerciveHamiltonianPhyslib.HilbertConfiguration N)
    (time : Real) :
    physlibQuarticForceRotatedSource m beta g mode q time =
      ((beta * g ^ 2 : Real) : Complex) *
        physlibQuarticForceRotatedSource m 1 1 mode q time := by
  unfold physlibQuarticForceRotatedSource physlibCubicRotatedSource
    physlibModeRotatedSource physlibModeTensorForce tensorNonlinearForce
    forcedModeSource
  push_cast
  ring

/-- Both phase-sign branches preserve the real quadratic coupling. -/
theorem signedPhyslibCubicLeadingQuadraticSource_eq_coupling_mul_unit
    {N : Nat} [NeZero N]
    (m : Lattice.PositiveMassConfig N) (kappa g : Real)
    (sign : PhaseSign) (mode : Lattice.Site N)
    (q : Time → CoerciveHamiltonianPhyslib.HilbertConfiguration N)
    (time : Real) :
    signedPhyslibCubicLeadingQuadraticSource
        m kappa g sign mode q time =
      ((kappa * g : Real) : Complex) *
        signedPhyslibCubicLeadingQuadraticSource
          m 1 1 sign mode q time := by
  unfold signedPhyslibCubicLeadingQuadraticSource
  change phaseSignActComplex sign
      (physlibQuadraticRotatedSource m kappa g mode q time) =
    ((kappa * g : Real) : Complex) * phaseSignActComplex sign
      (physlibQuadraticRotatedSource m 1 1 mode q time)
  rw [physlibQuadraticRotatedSource_eq_coupling_mul_unit]
  cases sign <;> simp [phaseSignActComplex]

/-- Both phase-sign branches preserve the real quartic coupling. -/
theorem signedPhyslibQuarticForceRotatedSource_eq_coupling_mul_unit
    {N : Nat} [NeZero N]
    (m : Lattice.PositiveMassConfig N) (beta g : Real)
    (sign : PhaseSign) (mode : Lattice.Site N)
    (q : Time → CoerciveHamiltonianPhyslib.HilbertConfiguration N)
    (time : Real) :
    signedPhyslibQuarticForceRotatedSource
        m beta g sign mode q time =
      ((beta * g ^ 2 : Real) : Complex) *
        signedPhyslibQuarticForceRotatedSource
          m 1 1 sign mode q time := by
  unfold signedPhyslibQuarticForceRotatedSource
  rw [physlibQuarticForceRotatedSource_eq_coupling_mul_unit]
  cases sign <;> simp [phaseSignActComplex]

/-- Pointwise scaling of the actual finite quadratic ensemble source. -/
theorem actualFiniteCubicEnsembleSource_eq_coupling_mul_unit
    {N : Nat} [NeZero N]
    (mass : Omega → Lattice.PositiveMassConfig N)
    (kappa g : Real)
    (entry : I → PhaseSign × Lattice.Site N)
    (q : Omega → Time →
      CoerciveHamiltonianPhyslib.HilbertConfiguration N) :
    actualFiniteCubicEnsembleSource mass kappa g entry q =
      fun omega i time ↦ ((kappa * g : Real) : Complex) *
        actualFiniteCubicEnsembleSource mass 1 1 entry q omega i time := by
  funext omega i time
  exact signedPhyslibCubicLeadingQuadraticSource_eq_coupling_mul_unit
    (mass omega) kappa g (entry i).1 (entry i).2 (q omega) time

/-- Pointwise scaling of the actual finite quartic ensemble source. -/
theorem actualFiniteQuarticEnsembleSource_eq_coupling_mul_unit
    {N : Nat} [NeZero N]
    (mass : Omega → Lattice.PositiveMassConfig N)
    (beta g : Real)
    (entry : I → PhaseSign × Lattice.Site N)
    (q : Omega → Time →
      CoerciveHamiltonianPhyslib.HilbertConfiguration N) :
    actualFiniteQuarticEnsembleSource mass beta g entry q =
      fun omega i time ↦ ((beta * g ^ 2 : Real) : Complex) *
        actualFiniteQuarticEnsembleSource mass 1 1 entry q omega i time := by
  funext omega i time
  exact signedPhyslibQuarticForceRotatedSource_eq_coupling_mul_unit
    (mass omega) beta g (entry i).1 (entry i).2 (q omega) time

/-! ## Scalar linearity through source-slot defects -/

theorem finiteWeightedObservableMoment_const_mul
    (weight : Omega → Real) (c : Complex)
    (observable : Omega → Complex) :
    finiteWeightedObservableMoment weight
        (fun omega ↦ c * observable omega) =
      c * finiteWeightedObservableMoment weight observable := by
  unfold finiteWeightedObservableMoment
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro omega _
  ring

theorem finiteWeightedObservableFactorizationDefect_const_mul_left
    (weight : Omega → Real) (c : Complex)
    (left right : Omega → Complex) :
    finiteWeightedObservableFactorizationDefect weight
        (fun omega ↦ c * left omega) right =
      c * finiteWeightedObservableFactorizationDefect weight left right := by
  have hjoint :
      finiteWeightedObservableMoment weight
          (fun omega ↦ (c * left omega) * right omega) =
        c * finiteWeightedObservableMoment weight
          (fun omega ↦ left omega * right omega) := by
    rw [show (fun omega ↦ (c * left omega) * right omega) =
        (fun omega ↦ c * (left omega * right omega)) by
      funext omega
      ring]
    exact finiteWeightedObservableMoment_const_mul weight c _
  unfold finiteWeightedObservableFactorizationDefect
  rw [hjoint, finiteWeightedObservableMoment_const_mul]
  ring

theorem finiteWeightedObservableFactorizationDefect_const_mul_right
    (weight : Omega → Real) (c : Complex)
    (left right : Omega → Complex) :
    finiteWeightedObservableFactorizationDefect weight left
        (fun omega ↦ c * right omega) =
      c * finiteWeightedObservableFactorizationDefect weight left right := by
  have hjoint :
      finiteWeightedObservableMoment weight
          (fun omega ↦ left omega * (c * right omega)) =
        c * finiteWeightedObservableMoment weight
          (fun omega ↦ left omega * right omega) := by
    rw [show (fun omega ↦ left omega * (c * right omega)) =
        (fun omega ↦ c * (left omega * right omega)) by
      funext omega
      ring]
    exact finiteWeightedObservableMoment_const_mul weight c _
  unfold finiteWeightedObservableFactorizationDefect
  rw [hjoint, finiteWeightedObservableMoment_const_mul]
  ring

theorem sourceInsertedBlockObservable_const_mul_source
    (path source : Omega → I → Real → Complex) (c : Complex)
    (block : Finset I) (slot : I) (time : Real) :
    sourceInsertedBlockObservable path
        (fun omega i s ↦ c * source omega i s) block slot time =
      fun omega ↦ c *
        sourceInsertedBlockObservable path source block slot time omega := by
  funext omega
  unfold sourceInsertedBlockObservable
  ring

/-! ## Exact scaling of every actual source-slot defect -/

theorem actualLeftQuadraticSourceSlotFactorizationDefect_eq_coupling_mul_unit
    {N : Nat} [NeZero N]
    (weight : Omega → Real)
    (mass : Omega → Lattice.PositiveMassConfig N)
    (kappa g : Real)
    (entry : I → PhaseSign × Lattice.Site N)
    (p q : Omega → Time →
      CoerciveHamiltonianPhyslib.HilbertConfiguration N)
    (left right : Finset I) (slot : I) (time : Real) :
    actualLeftQuadraticSourceSlotFactorizationDefect
        weight mass kappa g entry p q left right slot time =
      ((kappa * g : Real) : Complex) *
        actualLeftQuadraticSourceSlotFactorizationDefect
          weight mass 1 1 entry p q left right slot time := by
  unfold actualLeftQuadraticSourceSlotFactorizationDefect
  rw [actualFiniteCubicEnsembleSource_eq_coupling_mul_unit]
  rw [sourceInsertedBlockObservable_const_mul_source]
  exact finiteWeightedObservableFactorizationDefect_const_mul_left _ _ _ _

theorem actualLeftQuarticSourceSlotFactorizationDefect_eq_coupling_mul_unit
    {N : Nat} [NeZero N]
    (weight : Omega → Real)
    (mass : Omega → Lattice.PositiveMassConfig N)
    (beta g : Real)
    (entry : I → PhaseSign × Lattice.Site N)
    (p q : Omega → Time →
      CoerciveHamiltonianPhyslib.HilbertConfiguration N)
    (left right : Finset I) (slot : I) (time : Real) :
    actualLeftQuarticSourceSlotFactorizationDefect
        weight mass beta g entry p q left right slot time =
      ((beta * g ^ 2 : Real) : Complex) *
        actualLeftQuarticSourceSlotFactorizationDefect
          weight mass 1 1 entry p q left right slot time := by
  unfold actualLeftQuarticSourceSlotFactorizationDefect
  rw [actualFiniteQuarticEnsembleSource_eq_coupling_mul_unit]
  rw [sourceInsertedBlockObservable_const_mul_source]
  exact finiteWeightedObservableFactorizationDefect_const_mul_left _ _ _ _

theorem actualRightQuadraticSourceSlotFactorizationDefect_eq_coupling_mul_unit
    {N : Nat} [NeZero N]
    (weight : Omega → Real)
    (mass : Omega → Lattice.PositiveMassConfig N)
    (kappa g : Real)
    (entry : I → PhaseSign × Lattice.Site N)
    (p q : Omega → Time →
      CoerciveHamiltonianPhyslib.HilbertConfiguration N)
    (left right : Finset I) (slot : I) (time : Real) :
    actualRightQuadraticSourceSlotFactorizationDefect
        weight mass kappa g entry p q left right slot time =
      ((kappa * g : Real) : Complex) *
        actualRightQuadraticSourceSlotFactorizationDefect
          weight mass 1 1 entry p q left right slot time := by
  unfold actualRightQuadraticSourceSlotFactorizationDefect
  rw [actualFiniteCubicEnsembleSource_eq_coupling_mul_unit]
  rw [sourceInsertedBlockObservable_const_mul_source]
  exact finiteWeightedObservableFactorizationDefect_const_mul_right _ _ _ _

theorem actualRightQuarticSourceSlotFactorizationDefect_eq_coupling_mul_unit
    {N : Nat} [NeZero N]
    (weight : Omega → Real)
    (mass : Omega → Lattice.PositiveMassConfig N)
    (beta g : Real)
    (entry : I → PhaseSign × Lattice.Site N)
    (p q : Omega → Time →
      CoerciveHamiltonianPhyslib.HilbertConfiguration N)
    (left right : Finset I) (slot : I) (time : Real) :
    actualRightQuarticSourceSlotFactorizationDefect
        weight mass beta g entry p q left right slot time =
      ((beta * g ^ 2 : Real) : Complex) *
        actualRightQuarticSourceSlotFactorizationDefect
          weight mass 1 1 entry p q left right slot time := by
  unfold actualRightQuarticSourceSlotFactorizationDefect
  rw [actualFiniteQuarticEnsembleSource_eq_coupling_mul_unit]
  rw [sourceInsertedBlockObservable_const_mul_source]
  exact finiteWeightedObservableFactorizationDefect_const_mul_right _ _ _ _

/-! ## Full source-slot bounds with explicit physical powers -/

theorem norm_actualLeftSourceSlotFactorizationDefect_le_coupling_channels
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
      |kappa * g| *
          ‖actualLeftQuadraticSourceSlotFactorizationDefect
            weight mass 1 1 entry p q left right slot time‖ +
        |beta * g ^ 2| *
          ‖actualLeftQuarticSourceSlotFactorizationDefect
            weight mass 1 1 entry p q left right slot time‖ := by
  apply (norm_actualLeftSourceSlotFactorizationDefect_le_channels
    weight mass kappa beta g entry p q left right slot time).trans
  rw [actualLeftQuadraticSourceSlotFactorizationDefect_eq_coupling_mul_unit,
    actualLeftQuarticSourceSlotFactorizationDefect_eq_coupling_mul_unit]
  simp only [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_mul]
  exact le_rfl

theorem norm_actualRightSourceSlotFactorizationDefect_le_coupling_channels
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
      |kappa * g| *
          ‖actualRightQuadraticSourceSlotFactorizationDefect
            weight mass 1 1 entry p q left right slot time‖ +
        |beta * g ^ 2| *
          ‖actualRightQuarticSourceSlotFactorizationDefect
            weight mass 1 1 entry p q left right slot time‖ := by
  apply (norm_actualRightSourceSlotFactorizationDefect_le_channels
    weight mass kappa beta g entry p q left right slot time).trans
  rw [actualRightQuadraticSourceSlotFactorizationDefect_eq_coupling_mul_unit,
    actualRightQuarticSourceSlotFactorizationDefect_eq_coupling_mul_unit]
  simp only [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_mul]
  exact le_rfl

end

end ArchonPhysics.PhyslibFPUTActualSourceSlotCouplingScaling
