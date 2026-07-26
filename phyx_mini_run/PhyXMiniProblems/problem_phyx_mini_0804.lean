import Mathlib
import Physlib.Units.Examples

noncomputable section

namespace PhyXMiniProblems.ProblemPhyXMini0804

open Dimension

/-!
# Force exerted by a tray on a milk carton

A hand pushes a `1.00 kg` cafeteria tray horizontally with a constant `9.0 N`
force.  The tray is in contact with a `0.50 kg` milk carton, and both bodies
slide together on a horizontal surface whose friction is negligible.  The
horizontal axis below is oriented in the direction of the applied push.

Masses, horizontal force components, and horizontal acceleration components
are represented by unit-independent Physlib quantities.  Real numbers appear
only as coherent-unit readouts and answer-choice values.  In particular, the
tray-on-carton contact force is an independent field of the setup and is not
defined from the recorded answer.
-/

/-! ## Dimensionful physical quantities and coherent-unit readouts -/

/-- The physical dimension `L T⁻²` of an acceleration component. -/
def accelerationDimension : Dimension :=
  L𝓭 * T𝓭⁻¹ * T𝓭⁻¹

/-- The physical dimension `M L T⁻²` of a force component. -/
def forceDimension : Dimension :=
  M𝓭 * L𝓭 * T𝓭⁻¹ * T𝓭⁻¹

/-- A unit-independent physical mass.  Positivity is imposed by the setup data. -/
abbrev MassQuantity : Type :=
  Dimensionful (WithDim M𝓭 ℝ)

/-- A signed, unit-independent horizontal acceleration component. -/
abbrev AccelerationComponentQuantity : Type :=
  Dimensionful (WithDim accelerationDimension ℝ)

/-- A signed, unit-independent horizontal force component. -/
abbrev ForceComponentQuantity : Type :=
  Dimensionful (WithDim forceDimension ℝ)

/-- Read a physical mass in a selected mass unit. -/
def massReadout (unit : MassUnit) (mass : MassQuantity) : ℝ :=
  (mass {UnitChoices.SI with mass := unit}).val

/-- Read a horizontal acceleration in coherent selected length and time units. -/
def accelerationComponentReadout
    (lengthUnit : LengthUnit) (timeUnit : TimeUnit)
    (acceleration : AccelerationComponentQuantity) : ℝ :=
  (acceleration {UnitChoices.SI with
    length := lengthUnit, time := timeUnit}).val

/-- Read a horizontal force component in the coherent unit induced by the
selected base units. -/
def forceComponentReadout
    (massUnit : MassUnit) (lengthUnit : LengthUnit) (timeUnit : TimeUnit)
    (force : ForceComponentQuantity) : ℝ :=
  (force {UnitChoices.SI with
    mass := massUnit, length := lengthUnit, time := timeUnit}).val

/-- Kilogram readout of a physical mass. -/
def massInKilograms (mass : MassQuantity) : ℝ :=
  massReadout MassUnit.kilograms mass

/-- Metre-per-second-squared readout of a horizontal acceleration component. -/
def accelerationInMetersPerSecondSquared
    (acceleration : AccelerationComponentQuantity) : ℝ :=
  accelerationComponentReadout LengthUnit.meters TimeUnit.seconds acceleration

/-- Newton readout of a horizontal force component. -/
def forceComponentInNewtons (force : ForceComponentQuantity) : ℝ :=
  forceComponentReadout
    MassUnit.kilograms LengthUnit.meters TimeUnit.seconds force

/-! ## Bodies, figure labels, and answer choices -/

/-- The two bodies whose horizontal force balances are used. -/
inductive BodyLabel where
  | tray
  | carton
  deriving DecidableEq, Fintype, Repr

/-- Literal physical labels shown in the supplied figure. -/
inductive FigureLabel where
  | trayMass_mT
  | cartonMass_mC
  | appliedForce_F
  deriving DecidableEq, Fintype, Repr

/-- Numeric label readouts printed in the figure, in the units indicated there. -/
structure FigureReadouts where
  trayMassLabelKilograms : ℝ
  cartonMassLabelKilograms : ℝ
  appliedForceLabelNewtons : ℝ

/-- The side of the tray on which a pictured object appears. -/
inductive TraySide where
  | left
  | right
  deriving DecidableEq, Repr

/-- Orientations relevant to the surface and force arrow in the figure. -/
inductive FigureOrientation where
  | horizontal
  | vertical
  deriving DecidableEq, Repr

/-- Geometric facts directly read from the supplied raster. -/
structure FigureGeometry where
  cartonSideOfTray : TraySide
  handSideOfTray : TraySide
  surfaceOrientation : FigureOrientation
  pushArrowOrientation : FigureOrientation
  cartonContactsTray : Bool
  positiveAxisFollowsPush : Bool

/-- The four displayed multiple-choice answers. -/
inductive AnswerChoice where
  | A
  | B
  | C
  | D
  deriving DecidableEq, Fintype, Repr

/-- Force value printed beside each answer choice, measured in newtons. -/
def displayedForceInNewtons : AnswerChoice → ℝ
  | .A => 4
  | .B => 3
  | .C => 6
  | .D => 2

/-! ## Physical setup and assumptions -/

/--
The physical quantities for the tray-carton experiment.  Horizontal components
are signed relative to an axis chosen along the applied push.  Both bodies use
one acceleration field because contact is maintained and they slide together.
-/
structure CafeteriaPushSetup where
  mass : BodyLabel → MassQuantity
  commonHorizontalAcceleration : AccelerationComponentQuantity
  appliedPushOnTray : ForceComponentQuantity
  trayForceOnCarton : ForceComponentQuantity
  cartonForceOnTray : ForceComponentQuantity
  surfaceFrictionOn : BodyLabel → ForceComponentQuantity
  netHorizontalForceOn : BodyLabel → ForceComponentQuantity
  figure : FigureReadouts
  geometry : FigureGeometry

/--
Figure-derived geometry and numerical data.  These premises record the raster
without assigning any value to the unknown tray-on-carton contact force.
-/
structure MatchesFigure (setup : CafeteriaPushSetup) : Prop where
  surfaceIsHorizontal : setup.geometry.surfaceOrientation = .horizontal
  cartonImmediatelyLeftOfTray : setup.geometry.cartonSideOfTray = .left
  handAtRightEdgeOfTray : setup.geometry.handSideOfTray = .right
  trayContactsCarton : setup.geometry.cartonContactsTray = true
  positiveAxisIsDirectionOfPush : setup.geometry.positiveAxisFollowsPush = true
  pushArrowIsHorizontal : setup.geometry.pushArrowOrientation = .horizontal
  trayMassPhysicalReadout :
    massInKilograms (setup.mass .tray) = setup.figure.trayMassLabelKilograms
  cartonMassPhysicalReadout :
    massInKilograms (setup.mass .carton) = setup.figure.cartonMassLabelKilograms
  appliedForcePhysicalReadout :
    forceComponentInNewtons setup.appliedPushOnTray =
      setup.figure.appliedForceLabelNewtons
  trayMassLabelIsOneKilogram :
    setup.figure.trayMassLabelKilograms = 1
  cartonMassLabelIsHalfKilogram :
    setup.figure.cartonMassLabelKilograms = 1 / 2
  appliedForceLabelIsNineNewtons :
    setup.figure.appliedForceLabelNewtons = 9
  trayMassPositive : 0 < massInKilograms (setup.mass .tray)
  cartonMassPositive : 0 < massInKilograms (setup.mass .carton)

/--
Frictionless one-dimensional Newtonian dynamics for the two-body system.

The force-accounting equations list the actual signed horizontal forces on
each body.  Newton's third law relates the two independently stored contact
forces, and `UnitExamples.NewtonsSecondWithDim` states `F = m a` with the
correct dimensions for every coherent choice of base units.
-/
structure SatisfiesFrictionlessNewtonianDynamics
    (setup : CafeteriaPushSetup) : Prop where
  negligibleFriction :
    ∀ body units, (setup.surfaceFrictionOn body units).val = 0
  trayForceAccounting :
    ∀ units,
      (setup.netHorizontalForceOn .tray units).val =
        (setup.appliedPushOnTray units).val +
          (setup.cartonForceOnTray units).val +
          (setup.surfaceFrictionOn .tray units).val
  cartonForceAccounting :
    ∀ units,
      (setup.netHorizontalForceOn .carton units).val =
        (setup.trayForceOnCarton units).val +
          (setup.surfaceFrictionOn .carton units).val
  contactActionReaction :
    ∀ units,
      (setup.trayForceOnCarton units).val =
        -(setup.cartonForceOnTray units).val
  newtonSecondLaw :
    ∀ body units,
      UnitExamples.NewtonsSecondWithDim
        (setup.mass body units)
        (setup.netHorizontalForceOn body units)
        (setup.commonHorizontalAcceleration units)

/-! ## Consequences and requested result -/

/--
The figure data and governing laws imply a common horizontal acceleration of
`6 m/s²`.  This is a derived intermediate result, not a setup assumption.
-/
lemma common_acceleration_is_six_meters_per_second_squared
    (setup : CafeteriaPushSetup)
    (_figure : MatchesFigure setup)
    (_dynamics : SatisfiesFrictionlessNewtonianDynamics setup) :
    accelerationInMetersPerSecondSquared
      setup.commonHorizontalAcceleration = 6 := by
  have h_tray_mass :
      massInKilograms (setup.mass .tray) = 1 :=
    _figure.trayMassPhysicalReadout.trans
      _figure.trayMassLabelIsOneKilogram
  have h_carton_mass :
      massInKilograms (setup.mass .carton) = 1 / 2 :=
    _figure.cartonMassPhysicalReadout.trans
      _figure.cartonMassLabelIsHalfKilogram
  have h_applied :
      forceComponentInNewtons setup.appliedPushOnTray = 9 :=
    _figure.appliedForcePhysicalReadout.trans
      _figure.appliedForceLabelIsNineNewtons
  have h_tray_friction :=
    _dynamics.negligibleFriction .tray UnitChoices.SI
  have h_carton_friction :=
    _dynamics.negligibleFriction .carton UnitChoices.SI
  have h_tray_forces :=
    _dynamics.trayForceAccounting UnitChoices.SI
  have h_carton_forces :=
    _dynamics.cartonForceAccounting UnitChoices.SI
  have h_action_reaction :=
    _dynamics.contactActionReaction UnitChoices.SI
  have h_newton_tray :=
    _dynamics.newtonSecondLaw .tray UnitChoices.SI
  have h_newton_carton :=
    _dynamics.newtonSecondLaw .carton UnitChoices.SI
  simp only [UnitExamples.NewtonsSecondWithDim] at h_newton_tray h_newton_carton
  simp only [massInKilograms, massReadout,
    forceComponentInNewtons, forceComponentReadout,
    accelerationInMetersPerSecondSquared, accelerationComponentReadout,
    UnitChoices.SI] at *
  nlinarith

/--
The tray exerts a horizontal force of `3 N` on the carton.

This declaration formalizes
`thm:physics:phyx_mini_0804:target` from the blueprint chapter.
-/
theorem tray_exerts_three_newtons_on_carton
    (setup : CafeteriaPushSetup)
    (_figure : MatchesFigure setup)
    (_dynamics : SatisfiesFrictionlessNewtonianDynamics setup) :
    forceComponentInNewtons setup.trayForceOnCarton = 3 := by
  have h_acceleration :
      accelerationInMetersPerSecondSquared
        setup.commonHorizontalAcceleration = 6 :=
    common_acceleration_is_six_meters_per_second_squared
      setup _figure _dynamics
  have h_carton_mass :
      massInKilograms (setup.mass .carton) = 1 / 2 :=
    _figure.cartonMassPhysicalReadout.trans
      _figure.cartonMassLabelIsHalfKilogram
  have h_carton_friction :=
    _dynamics.negligibleFriction .carton UnitChoices.SI
  have h_carton_forces :=
    _dynamics.cartonForceAccounting UnitChoices.SI
  have h_newton_carton :=
    _dynamics.newtonSecondLaw .carton UnitChoices.SI
  simp only [UnitExamples.NewtonsSecondWithDim] at h_newton_carton
  simp only [massInKilograms, massReadout,
    forceComponentInNewtons, forceComponentReadout,
    accelerationInMetersPerSecondSquared, accelerationComponentReadout,
    UnitChoices.SI] at *
  nlinarith

/-- Consequently, answer choice `B` is the displayed force that matches the
physical tray-on-carton force. -/
theorem answer_choice_B_matches
    (setup : CafeteriaPushSetup)
    (_figure : MatchesFigure setup)
    (_dynamics : SatisfiesFrictionlessNewtonianDynamics setup) :
    forceComponentInNewtons setup.trayForceOnCarton =
      displayedForceInNewtons .B := by
  simpa [displayedForceInNewtons] using
    tray_exerts_three_newtons_on_carton setup _figure _dynamics

end PhyXMiniProblems.ProblemPhyXMini0804
