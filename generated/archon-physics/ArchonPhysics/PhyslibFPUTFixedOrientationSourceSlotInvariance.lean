import ArchonPhysics.PhyslibFPUTSourceInsertionClusterExpansion

/-!
# Fixed-orientation invariance of finite source-slot defects

At fixed mass, the change from a Physlib eigenbasis to the measurable ordered
signed eigenbasis multiplies every mode by a deterministic sign.  This module
records the purely algebraic consequence needed by the quenched hierarchy:
path blocks, source-inserted blocks, and their factorization defects change by
one explicit block-orientation factor.  If the individual orientations have
unit norm, the defect norm is unchanged.

The orientation is deliberately independent of the finite ensemble sample.
Thus these statements apply directly to a fixed-mass (quenched) phase
ensemble.  They do not claim that a mass-dependent orientation can be pulled
through an annealed mass expectation.
-/

namespace ArchonPhysics.PhyslibFPUTFixedOrientationSourceSlotInvariance

open scoped BigOperators

open ArchonPhysics
open ArchonPhysics.PhyslibFPUTPositiveTimeCumulantHierarchy
open ArchonPhysics.PhyslibFPUTSourceInsertionClusterExpansion

noncomputable section

variable {I Omega : Type*}
  [Fintype I] [DecidableEq I] [Nonempty I]
  [Fintype Omega] [DecidableEq Omega]

/-- Multiply every modal path or source slot by a fixed orientation. -/
def orientedField
    (orientation : I -> Complex)
    (field : Omega -> I -> Real -> Complex) :
    Omega -> I -> Real -> Complex :=
  fun omega i time => orientation i * field omega i time

/-- Product orientation carried by a finite modal block. -/
def blockOrientation
    (orientation : I -> Complex) (block : Finset I) : Complex :=
  ∏ i ∈ block, orientation i

/-- An oriented path block carries exactly its block orientation. -/
theorem pathBlockObservable_orientedField
    (orientation : I -> Complex)
    (path : Omega -> I -> Real -> Complex)
    (block : Finset I) (time : Real) (omega : Omega) :
    pathBlockObservable (orientedField orientation path) block time omega =
      blockOrientation orientation block *
        pathBlockObservable path block time omega := by
  unfold pathBlockObservable signedBlockMonomial orientedField blockOrientation
  rw [Finset.prod_mul_distrib]

/-- If the displayed slot lies in the block, an oriented source-inserted block
carries the orientation of the whole block, including the source slot. -/
theorem sourceInsertedBlockObservable_orientedField
    (orientation : I -> Complex)
    (path source : Omega -> I -> Real -> Complex)
    (block : Finset I) (slot : I) (hslot : slot ∈ block)
    (time : Real) (omega : Omega) :
    sourceInsertedBlockObservable
        (orientedField orientation path)
        (orientedField orientation source) block slot time omega =
      blockOrientation orientation block *
        sourceInsertedBlockObservable path source block slot time omega := by
  unfold sourceInsertedBlockObservable orientedField blockOrientation
  rw [Finset.prod_mul_distrib]
  rw [← Finset.prod_erase_mul block orientation hslot]
  ring

/-- A sample-independent scalar can be pulled through the finite weighted
observable moment. -/
theorem finiteWeightedObservableMoment_const_mul
    (weight : Omega -> Real) (observable : Omega -> Complex) (c : Complex) :
    finiteWeightedObservableMoment weight (fun omega => c * observable omega) =
      c * finiteWeightedObservableMoment weight observable := by
  unfold finiteWeightedObservableMoment
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro omega _
  ring

/-- Scaling the two observables by sample-independent constants scales their
factorization defect by the product constant. -/
theorem finiteWeightedObservableFactorizationDefect_const_mul
    (weight : Omega -> Real) (left right : Omega -> Complex)
    (cLeft cRight : Complex) :
    finiteWeightedObservableFactorizationDefect weight
        (fun omega => cLeft * left omega)
        (fun omega => cRight * right omega) =
      (cLeft * cRight) *
        finiteWeightedObservableFactorizationDefect weight left right := by
  unfold finiteWeightedObservableFactorizationDefect
  have hproduct :
      (fun omega =>
        (cLeft * left omega) * (cRight * right omega)) =
        (fun omega => (cLeft * cRight) * (left omega * right omega)) := by
    funext omega
    ring
  rw [hproduct,
    finiteWeightedObservableMoment_const_mul,
    finiteWeightedObservableMoment_const_mul,
    finiteWeightedObservableMoment_const_mul]
  ring

/-- A left source-slot defect in the oriented frame equals the original
fixed-frame defect times the left and right block orientations. -/
theorem leftSourceSlotFactorizationDefect_orientedField
    (weight : Omega -> Real)
    (orientation : I -> Complex)
    (path source : Omega -> I -> Real -> Complex)
    (left right : Finset I) (slot : I) (hslot : slot ∈ left)
    (time : Real) :
    finiteWeightedObservableFactorizationDefect weight
        (sourceInsertedBlockObservable
          (orientedField orientation path)
          (orientedField orientation source) left slot time)
        (pathBlockObservable
          (orientedField orientation path) right time) =
      (blockOrientation orientation left * blockOrientation orientation right) *
        finiteWeightedObservableFactorizationDefect weight
          (sourceInsertedBlockObservable path source left slot time)
          (pathBlockObservable path right time) := by
  have hleft :
      sourceInsertedBlockObservable
          (orientedField orientation path)
          (orientedField orientation source) left slot time =
        fun omega => blockOrientation orientation left *
          sourceInsertedBlockObservable path source left slot time omega := by
    funext omega
    exact sourceInsertedBlockObservable_orientedField
      orientation path source left slot hslot time omega
  have hright :
      pathBlockObservable (orientedField orientation path) right time =
        fun omega => blockOrientation orientation right *
          pathBlockObservable path right time omega := by
    funext omega
    exact pathBlockObservable_orientedField
      orientation path right time omega
  rw [hleft, hright]
  exact finiteWeightedObservableFactorizationDefect_const_mul
    weight
      (sourceInsertedBlockObservable path source left slot time)
      (pathBlockObservable path right time)
      (blockOrientation orientation left)
      (blockOrientation orientation right)

/-- The symmetric right source-slot defect obeys the same exact orientation
law. -/
theorem rightSourceSlotFactorizationDefect_orientedField
    (weight : Omega -> Real)
    (orientation : I -> Complex)
    (path source : Omega -> I -> Real -> Complex)
    (left right : Finset I) (slot : I) (hslot : slot ∈ right)
    (time : Real) :
    finiteWeightedObservableFactorizationDefect weight
        (pathBlockObservable
          (orientedField orientation path) left time)
        (sourceInsertedBlockObservable
          (orientedField orientation path)
          (orientedField orientation source) right slot time) =
      (blockOrientation orientation left * blockOrientation orientation right) *
        finiteWeightedObservableFactorizationDefect weight
          (pathBlockObservable path left time)
          (sourceInsertedBlockObservable path source right slot time) := by
  have hleft :
      pathBlockObservable (orientedField orientation path) left time =
        fun omega => blockOrientation orientation left *
          pathBlockObservable path left time omega := by
    funext omega
    exact pathBlockObservable_orientedField
      orientation path left time omega
  have hright :
      sourceInsertedBlockObservable
          (orientedField orientation path)
          (orientedField orientation source) right slot time =
        fun omega => blockOrientation orientation right *
          sourceInsertedBlockObservable path source right slot time omega := by
    funext omega
    exact sourceInsertedBlockObservable_orientedField
      orientation path source right slot hslot time omega
  rw [hleft, hright]
  exact finiteWeightedObservableFactorizationDefect_const_mul
    weight
      (pathBlockObservable path left time)
      (sourceInsertedBlockObservable path source right slot time)
      (blockOrientation orientation left)
      (blockOrientation orientation right)

/-- A block made from unit-norm orientations again has unit norm. -/
theorem norm_blockOrientation
    (orientation : I -> Complex)
    (horientation : ∀ i, ‖orientation i‖ = 1)
    (block : Finset I) :
    ‖blockOrientation orientation block‖ = 1 := by
  unfold blockOrientation
  rw [norm_prod]
  simp [horientation]

/-- At fixed mass, unit orientations leave every left source-slot defect norm
exactly unchanged. -/
theorem norm_leftSourceSlotFactorizationDefect_orientedField
    (weight : Omega -> Real)
    (orientation : I -> Complex)
    (horientation : ∀ i, ‖orientation i‖ = 1)
    (path source : Omega -> I -> Real -> Complex)
    (left right : Finset I) (slot : I) (hslot : slot ∈ left)
    (time : Real) :
    ‖finiteWeightedObservableFactorizationDefect weight
        (sourceInsertedBlockObservable
          (orientedField orientation path)
          (orientedField orientation source) left slot time)
        (pathBlockObservable
          (orientedField orientation path) right time)‖ =
      ‖finiteWeightedObservableFactorizationDefect weight
        (sourceInsertedBlockObservable path source left slot time)
        (pathBlockObservable path right time)‖ := by
  rw [leftSourceSlotFactorizationDefect_orientedField
    weight orientation path source left right slot hslot time,
    norm_mul, norm_mul,
    norm_blockOrientation orientation horientation left,
    norm_blockOrientation orientation horientation right]
  simp

/-- At fixed mass, unit orientations also leave every right source-slot
defect norm exactly unchanged. -/
theorem norm_rightSourceSlotFactorizationDefect_orientedField
    (weight : Omega -> Real)
    (orientation : I -> Complex)
    (horientation : ∀ i, ‖orientation i‖ = 1)
    (path source : Omega -> I -> Real -> Complex)
    (left right : Finset I) (slot : I) (hslot : slot ∈ right)
    (time : Real) :
    ‖finiteWeightedObservableFactorizationDefect weight
        (pathBlockObservable
          (orientedField orientation path) left time)
        (sourceInsertedBlockObservable
          (orientedField orientation path)
          (orientedField orientation source) right slot time)‖ =
      ‖finiteWeightedObservableFactorizationDefect weight
        (pathBlockObservable path left time)
        (sourceInsertedBlockObservable path source right slot time)‖ := by
  rw [rightSourceSlotFactorizationDefect_orientedField
    weight orientation path source left right slot hslot time,
    norm_mul, norm_mul,
    norm_blockOrientation orientation horientation left,
    norm_blockOrientation orientation horientation right]
  simp

end

end ArchonPhysics.PhyslibFPUTFixedOrientationSourceSlotInvariance
