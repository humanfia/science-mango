import ArchonPhysics.PhyslibFPUTFixedOrientationSourceSlotInvariance

/-!
# Fixed-orientation invariance for Bochner source-slot defects

This is the measure-theoretic counterpart of the finite weighted identity.
It applies to an arbitrary phase probability space after the random mass has
been fixed: modal paths and nonlinear sources may be multiplied by fixed
unit-norm orientation factors without changing the norm of any Bochner
source-slot factorization defect.

No measurability or integrability premise is hidden in the algebraic scaling
identity.  Applications still have to establish that the concrete path and
source observables are legitimate Bochner integrands.  The orientation is
sample-independent, so the theorem is quenched rather than an invalid
annealed extraction of mass-dependent signs.
-/

namespace ArchonPhysics.PhyslibFPUTFixedOrientationBochnerInvariance

open scoped BigOperators

open ArchonPhysics
open MeasureTheory

noncomputable section

variable {I Omega : Type*} [DecidableEq I] [MeasurableSpace Omega]

/-- A modal field multiplied by a sample-independent orientation. -/
def orientedField
    (orientation : I -> Complex)
    (field : Omega -> I -> Real -> Complex) :
    Omega -> I -> Real -> Complex :=
  fun omega i time => orientation i * field omega i time

/-- Product orientation of one finite block. -/
def blockOrientation
    (orientation : I -> Complex) (block : Finset I) : Complex :=
  ∏ i ∈ block, orientation i

/-- A finite block observable on an arbitrary measure space. -/
def bochnerPathBlockObservable
    (path : Omega -> I -> Real -> Complex)
    (block : Finset I) (time : Real) (omega : Omega) : Complex :=
  ∏ i ∈ block, path omega i time

/-- One finite block with a displayed slot replaced by its source. -/
def bochnerSourceInsertedBlockObservable
    (path source : Omega -> I -> Real -> Complex)
    (block : Finset I) (slot : I) (time : Real) (omega : Omega) : Complex :=
  (∏ j ∈ block.erase slot, path omega j time) * source omega slot time

/-- Bochner factorization defect of two arbitrary complex observables. -/
def bochnerObservableFactorizationDefect
    (mu : Measure Omega) (left right : Omega -> Complex) : Complex :=
  (∫ omega, left omega * right omega ∂mu) -
    (∫ omega, left omega ∂mu) * (∫ omega, right omega ∂mu)

/-- An oriented path block carries exactly its deterministic block factor. -/
theorem bochnerPathBlockObservable_orientedField
    (orientation : I -> Complex)
    (path : Omega -> I -> Real -> Complex)
    (block : Finset I) (time : Real) (omega : Omega) :
    bochnerPathBlockObservable (orientedField orientation path)
        block time omega =
      blockOrientation orientation block *
        bochnerPathBlockObservable path block time omega := by
  unfold bochnerPathBlockObservable orientedField blockOrientation
  rw [Finset.prod_mul_distrib]

/-- An oriented source insertion carries the orientation of the full block. -/
theorem bochnerSourceInsertedBlockObservable_orientedField
    (orientation : I -> Complex)
    (path source : Omega -> I -> Real -> Complex)
    (block : Finset I) (slot : I) (hslot : slot ∈ block)
    (time : Real) (omega : Omega) :
    bochnerSourceInsertedBlockObservable
        (orientedField orientation path)
        (orientedField orientation source) block slot time omega =
      blockOrientation orientation block *
        bochnerSourceInsertedBlockObservable
          path source block slot time omega := by
  unfold bochnerSourceInsertedBlockObservable orientedField blockOrientation
  rw [Finset.prod_mul_distrib]
  rw [← Finset.prod_erase_mul block orientation hslot]
  ring

/-- Sample-independent scaling of both observables factors out of the
Bochner covariance defect. -/
theorem bochnerObservableFactorizationDefect_const_mul
    (mu : Measure Omega) (left right : Omega -> Complex)
    (cLeft cRight : Complex) :
    bochnerObservableFactorizationDefect mu
        (fun omega => cLeft * left omega)
        (fun omega => cRight * right omega) =
      (cLeft * cRight) *
        bochnerObservableFactorizationDefect mu left right := by
  unfold bochnerObservableFactorizationDefect
  have hproduct :
      (fun omega =>
        (cLeft * left omega) * (cRight * right omega)) =
        (fun omega => (cLeft * cRight) * (left omega * right omega)) := by
    funext omega
    ring
  rw [hproduct, integral_const_mul, integral_const_mul, integral_const_mul]
  ring

/-- Exact orientation law for a left Bochner source-slot defect. -/
theorem leftBochnerSourceSlotFactorizationDefect_orientedField
    (mu : Measure Omega)
    (orientation : I -> Complex)
    (path source : Omega -> I -> Real -> Complex)
    (left right : Finset I) (slot : I) (hslot : slot ∈ left)
    (time : Real) :
    bochnerObservableFactorizationDefect mu
        (bochnerSourceInsertedBlockObservable
          (orientedField orientation path)
          (orientedField orientation source) left slot time)
        (bochnerPathBlockObservable
          (orientedField orientation path) right time) =
      (blockOrientation orientation left * blockOrientation orientation right) *
        bochnerObservableFactorizationDefect mu
          (bochnerSourceInsertedBlockObservable path source left slot time)
          (bochnerPathBlockObservable path right time) := by
  have hleft :
      bochnerSourceInsertedBlockObservable
          (orientedField orientation path)
          (orientedField orientation source) left slot time =
        fun omega => blockOrientation orientation left *
          bochnerSourceInsertedBlockObservable
            path source left slot time omega := by
    funext omega
    exact bochnerSourceInsertedBlockObservable_orientedField
      orientation path source left slot hslot time omega
  have hright :
      bochnerPathBlockObservable
          (orientedField orientation path) right time =
        fun omega => blockOrientation orientation right *
          bochnerPathBlockObservable path right time omega := by
    funext omega
    exact bochnerPathBlockObservable_orientedField
      orientation path right time omega
  rw [hleft, hright]
  exact bochnerObservableFactorizationDefect_const_mul mu
    (bochnerSourceInsertedBlockObservable path source left slot time)
    (bochnerPathBlockObservable path right time)
    (blockOrientation orientation left)
    (blockOrientation orientation right)

/-- Exact orientation law for a right Bochner source-slot defect. -/
theorem rightBochnerSourceSlotFactorizationDefect_orientedField
    (mu : Measure Omega)
    (orientation : I -> Complex)
    (path source : Omega -> I -> Real -> Complex)
    (left right : Finset I) (slot : I) (hslot : slot ∈ right)
    (time : Real) :
    bochnerObservableFactorizationDefect mu
        (bochnerPathBlockObservable
          (orientedField orientation path) left time)
        (bochnerSourceInsertedBlockObservable
          (orientedField orientation path)
          (orientedField orientation source) right slot time) =
      (blockOrientation orientation left * blockOrientation orientation right) *
        bochnerObservableFactorizationDefect mu
          (bochnerPathBlockObservable path left time)
          (bochnerSourceInsertedBlockObservable path source right slot time) := by
  have hleft :
      bochnerPathBlockObservable
          (orientedField orientation path) left time =
        fun omega => blockOrientation orientation left *
          bochnerPathBlockObservable path left time omega := by
    funext omega
    exact bochnerPathBlockObservable_orientedField
      orientation path left time omega
  have hright :
      bochnerSourceInsertedBlockObservable
          (orientedField orientation path)
          (orientedField orientation source) right slot time =
        fun omega => blockOrientation orientation right *
          bochnerSourceInsertedBlockObservable
            path source right slot time omega := by
    funext omega
    exact bochnerSourceInsertedBlockObservable_orientedField
      orientation path source right slot hslot time omega
  rw [hleft, hright]
  exact bochnerObservableFactorizationDefect_const_mul mu
    (bochnerPathBlockObservable path left time)
    (bochnerSourceInsertedBlockObservable path source right slot time)
    (blockOrientation orientation left)
    (blockOrientation orientation right)

/-- Unit-norm orientations have a unit-norm block product. -/
theorem norm_blockOrientation
    (orientation : I -> Complex)
    (horientation : ∀ i, ‖orientation i‖ = 1)
    (block : Finset I) :
    ‖blockOrientation orientation block‖ = 1 := by
  unfold blockOrientation
  rw [norm_prod]
  simp [horientation]

/-- A fixed unit orientation leaves a left Bochner source-slot defect norm
unchanged. -/
theorem norm_leftBochnerSourceSlotFactorizationDefect_orientedField
    (mu : Measure Omega)
    (orientation : I -> Complex)
    (horientation : ∀ i, ‖orientation i‖ = 1)
    (path source : Omega -> I -> Real -> Complex)
    (left right : Finset I) (slot : I) (hslot : slot ∈ left)
    (time : Real) :
    ‖bochnerObservableFactorizationDefect mu
        (bochnerSourceInsertedBlockObservable
          (orientedField orientation path)
          (orientedField orientation source) left slot time)
        (bochnerPathBlockObservable
          (orientedField orientation path) right time)‖ =
      ‖bochnerObservableFactorizationDefect mu
        (bochnerSourceInsertedBlockObservable path source left slot time)
        (bochnerPathBlockObservable path right time)‖ := by
  rw [leftBochnerSourceSlotFactorizationDefect_orientedField
    mu orientation path source left right slot hslot time,
    norm_mul, norm_mul,
    norm_blockOrientation orientation horientation left,
    norm_blockOrientation orientation horientation right]
  simp

/-- A fixed unit orientation leaves a right Bochner source-slot defect norm
unchanged. -/
theorem norm_rightBochnerSourceSlotFactorizationDefect_orientedField
    (mu : Measure Omega)
    (orientation : I -> Complex)
    (horientation : ∀ i, ‖orientation i‖ = 1)
    (path source : Omega -> I -> Real -> Complex)
    (left right : Finset I) (slot : I) (hslot : slot ∈ right)
    (time : Real) :
    ‖bochnerObservableFactorizationDefect mu
        (bochnerPathBlockObservable
          (orientedField orientation path) left time)
        (bochnerSourceInsertedBlockObservable
          (orientedField orientation path)
          (orientedField orientation source) right slot time)‖ =
      ‖bochnerObservableFactorizationDefect mu
        (bochnerPathBlockObservable path left time)
        (bochnerSourceInsertedBlockObservable path source right slot time)‖ := by
  rw [rightBochnerSourceSlotFactorizationDefect_orientedField
    mu orientation path source left right slot hslot time,
    norm_mul, norm_mul,
    norm_blockOrientation orientation horientation left,
    norm_blockOrientation orientation horientation right]
  simp

end

end ArchonPhysics.PhyslibFPUTFixedOrientationBochnerInvariance
