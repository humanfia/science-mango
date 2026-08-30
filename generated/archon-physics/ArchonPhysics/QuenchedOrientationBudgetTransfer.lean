import ArchonPhysics.PhyslibFPUTFixedOrientationBochnerInvariance
import ArchonPhysics.QuenchedToAnnealedProbabilityTransfer

/-!
# Quenched orientation budgets under the mass law

The ordered eigenvector orientation may depend on the frozen mass and hence
cannot be pulled through the full annealed covariance.  It is nevertheless
constant on each conditional phase space.  We therefore first form the
Bochner factorization defect at fixed mass, use unit-orientation invariance
there, and only afterwards average its norm or its bad-mass event over the
mass law.

This is the legal two-stage replacement for an invalid extraction of a
mass-dependent sign from an annealed expectation.  It is an exact algebraic
transfer, not a decay, measurability, RPA, or kinetic-limit theorem.
-/

namespace ArchonPhysics.QuenchedOrientationBudgetTransfer

open ArchonPhysics
open ArchonPhysics.PhyslibFPUTFixedOrientationBochnerInvariance
open MeasureTheory Set

noncomputable section

variable {I Mass Phase : Type*}
  [DecidableEq I] [MeasurableSpace Mass] [MeasurableSpace Phase]

/-- Left source-slot factorization defect after freezing the mass and
integrating only over the phase law. -/
def quenchedLeftSourceSlotDefect
    (phaseLaw : Measure Phase)
    (path source : Mass -> Phase -> I -> Real -> Complex)
    (mass : Mass) (left right : Finset I) (slot : I) (time : Real) : Complex :=
  bochnerObservableFactorizationDefect phaseLaw
    (bochnerSourceInsertedBlockObservable
      (path mass) (source mass) left slot time)
    (bochnerPathBlockObservable (path mass) right time)

/-- The same left quenched defect in a mass-dependent oriented frame.  The
orientation is fixed while the phase integral is taken. -/
def orientedQuenchedLeftSourceSlotDefect
    (phaseLaw : Measure Phase)
    (orientation : Mass -> I -> Complex)
    (path source : Mass -> Phase -> I -> Real -> Complex)
    (mass : Mass) (left right : Finset I) (slot : I) (time : Real) : Complex :=
  bochnerObservableFactorizationDefect phaseLaw
    (bochnerSourceInsertedBlockObservable
      (orientedField (orientation mass) (path mass))
      (orientedField (orientation mass) (source mass)) left slot time)
    (bochnerPathBlockObservable
      (orientedField (orientation mass) (path mass)) right time)

/-- Right source-slot factorization defect after freezing the mass. -/
def quenchedRightSourceSlotDefect
    (phaseLaw : Measure Phase)
    (path source : Mass -> Phase -> I -> Real -> Complex)
    (mass : Mass) (left right : Finset I) (slot : I) (time : Real) : Complex :=
  bochnerObservableFactorizationDefect phaseLaw
    (bochnerPathBlockObservable (path mass) left time)
    (bochnerSourceInsertedBlockObservable
      (path mass) (source mass) right slot time)

/-- The right quenched defect in a mass-dependent oriented frame. -/
def orientedQuenchedRightSourceSlotDefect
    (phaseLaw : Measure Phase)
    (orientation : Mass -> I -> Complex)
    (path source : Mass -> Phase -> I -> Real -> Complex)
    (mass : Mass) (left right : Finset I) (slot : I) (time : Real) : Complex :=
  bochnerObservableFactorizationDefect phaseLaw
    (bochnerPathBlockObservable
      (orientedField (orientation mass) (path mass)) left time)
    (bochnerSourceInsertedBlockObservable
      (orientedField (orientation mass) (path mass))
      (orientedField (orientation mass) (source mass)) right slot time)

/-- For each frozen mass, a unit orientation leaves the left quenched defect
norm exactly unchanged. -/
theorem norm_orientedQuenchedLeftSourceSlotDefect_eq
    (phaseLaw : Measure Phase)
    (orientation : Mass -> I -> Complex)
    (horientation : ∀ mass i, ‖orientation mass i‖ = 1)
    (path source : Mass -> Phase -> I -> Real -> Complex)
    (mass : Mass) (left right : Finset I) (slot : I)
    (hslot : slot ∈ left) (time : Real) :
    ‖orientedQuenchedLeftSourceSlotDefect phaseLaw orientation
        path source mass left right slot time‖ =
      ‖quenchedLeftSourceSlotDefect phaseLaw
        path source mass left right slot time‖ := by
  unfold orientedQuenchedLeftSourceSlotDefect quenchedLeftSourceSlotDefect
  exact norm_leftBochnerSourceSlotFactorizationDefect_orientedField
    phaseLaw (orientation mass) (horientation mass)
      (path mass) (source mass) left right slot hslot time

/-- The symmetric fixed-mass norm identity for a right source slot. -/
theorem norm_orientedQuenchedRightSourceSlotDefect_eq
    (phaseLaw : Measure Phase)
    (orientation : Mass -> I -> Complex)
    (horientation : ∀ mass i, ‖orientation mass i‖ = 1)
    (path source : Mass -> Phase -> I -> Real -> Complex)
    (mass : Mass) (left right : Finset I) (slot : I)
    (hslot : slot ∈ right) (time : Real) :
    ‖orientedQuenchedRightSourceSlotDefect phaseLaw orientation
        path source mass left right slot time‖ =
      ‖quenchedRightSourceSlotDefect phaseLaw
        path source mass left right slot time‖ := by
  unfold orientedQuenchedRightSourceSlotDefect quenchedRightSourceSlotDefect
  exact norm_rightBochnerSourceSlotFactorizationDefect_orientedField
    phaseLaw (orientation mass) (horientation mass)
      (path mass) (source mass) left right slot hslot time

/-- Averaging the norm of the left quenched defect over the mass law is
orientation invariant, even though the orientation itself depends on mass. -/
theorem integral_norm_orientedQuenchedLeftSourceSlotDefect_eq
    (massLaw : Measure Mass) (phaseLaw : Measure Phase)
    (orientation : Mass -> I -> Complex)
    (horientation : ∀ mass i, ‖orientation mass i‖ = 1)
    (path source : Mass -> Phase -> I -> Real -> Complex)
    (left right : Finset I) (slot : I) (hslot : slot ∈ left)
    (time : Real) :
    (∫ mass,
      ‖orientedQuenchedLeftSourceSlotDefect phaseLaw orientation
        path source mass left right slot time‖ ∂massLaw) =
      ∫ mass,
        ‖quenchedLeftSourceSlotDefect phaseLaw
          path source mass left right slot time‖ ∂massLaw := by
  apply integral_congr_ae
  filter_upwards with mass
  exact norm_orientedQuenchedLeftSourceSlotDefect_eq
    phaseLaw orientation horientation path source
      mass left right slot hslot time

/-- The same post-conditioning mass-average identity for a right source
slot. -/
theorem integral_norm_orientedQuenchedRightSourceSlotDefect_eq
    (massLaw : Measure Mass) (phaseLaw : Measure Phase)
    (orientation : Mass -> I -> Complex)
    (horientation : ∀ mass i, ‖orientation mass i‖ = 1)
    (path source : Mass -> Phase -> I -> Real -> Complex)
    (left right : Finset I) (slot : I) (hslot : slot ∈ right)
    (time : Real) :
    (∫ mass,
      ‖orientedQuenchedRightSourceSlotDefect phaseLaw orientation
        path source mass left right slot time‖ ∂massLaw) =
      ∫ mass,
        ‖quenchedRightSourceSlotDefect phaseLaw
          path source mass left right slot time‖ ∂massLaw := by
  apply integral_congr_ae
  filter_upwards with mass
  exact norm_orientedQuenchedRightSourceSlotDefect_eq
    phaseLaw orientation horientation path source
      mass left right slot hslot time

/-- Every threshold bad-mass set for a left quenched defect is exactly
orientation invariant. -/
theorem orientedQuenchedLeftBadMassSet_eq
    (phaseLaw : Measure Phase)
    (orientation : Mass -> I -> Complex)
    (horientation : ∀ mass i, ‖orientation mass i‖ = 1)
    (path source : Mass -> Phase -> I -> Real -> Complex)
    (left right : Finset I) (slot : I) (hslot : slot ∈ left)
    (time threshold : Real) :
    {mass | threshold <
      ‖orientedQuenchedLeftSourceSlotDefect phaseLaw orientation
        path source mass left right slot time‖} =
      {mass | threshold <
        ‖quenchedLeftSourceSlotDefect phaseLaw
          path source mass left right slot time‖} := by
  ext mass
  simp only [Set.mem_setOf_eq]
  rw [norm_orientedQuenchedLeftSourceSlotDefect_eq
    phaseLaw orientation horientation path source
      mass left right slot hslot time]

/-- Hence any mass law assigns the same probability to the two left
quenched bad-mass events. -/
theorem measure_orientedQuenchedLeftBadMassSet_eq
    (massLaw : Measure Mass) (phaseLaw : Measure Phase)
    (orientation : Mass -> I -> Complex)
    (horientation : ∀ mass i, ‖orientation mass i‖ = 1)
    (path source : Mass -> Phase -> I -> Real -> Complex)
    (left right : Finset I) (slot : I) (hslot : slot ∈ left)
    (time threshold : Real) :
    massLaw {mass | threshold <
      ‖orientedQuenchedLeftSourceSlotDefect phaseLaw orientation
        path source mass left right slot time‖} =
      massLaw {mass | threshold <
        ‖quenchedLeftSourceSlotDefect phaseLaw
          path source mass left right slot time‖} := by
  rw [orientedQuenchedLeftBadMassSet_eq
    phaseLaw orientation horientation path source
      left right slot hslot time threshold]

/-- Right quenched threshold sets are likewise exactly invariant. -/
theorem orientedQuenchedRightBadMassSet_eq
    (phaseLaw : Measure Phase)
    (orientation : Mass -> I -> Complex)
    (horientation : ∀ mass i, ‖orientation mass i‖ = 1)
    (path source : Mass -> Phase -> I -> Real -> Complex)
    (left right : Finset I) (slot : I) (hslot : slot ∈ right)
    (time threshold : Real) :
    {mass | threshold <
      ‖orientedQuenchedRightSourceSlotDefect phaseLaw orientation
        path source mass left right slot time‖} =
      {mass | threshold <
        ‖quenchedRightSourceSlotDefect phaseLaw
          path source mass left right slot time‖} := by
  ext mass
  simp only [Set.mem_setOf_eq]
  rw [norm_orientedQuenchedRightSourceSlotDefect_eq
    phaseLaw orientation horientation path source
      mass left right slot hslot time]

/-- Any mass law gives equal probability to the oriented and unoriented right
quenched bad-mass events. -/
theorem measure_orientedQuenchedRightBadMassSet_eq
    (massLaw : Measure Mass) (phaseLaw : Measure Phase)
    (orientation : Mass -> I -> Complex)
    (horientation : ∀ mass i, ‖orientation mass i‖ = 1)
    (path source : Mass -> Phase -> I -> Real -> Complex)
    (left right : Finset I) (slot : I) (hslot : slot ∈ right)
    (time threshold : Real) :
    massLaw {mass | threshold <
      ‖orientedQuenchedRightSourceSlotDefect phaseLaw orientation
        path source mass left right slot time‖} =
      massLaw {mass | threshold <
        ‖quenchedRightSourceSlotDefect phaseLaw
          path source mass left right slot time‖} := by
  rw [orientedQuenchedRightBadMassSet_eq
    phaseLaw orientation horientation path source
      left right slot hslot time threshold]

end

end ArchonPhysics.QuenchedOrientationBudgetTransfer
