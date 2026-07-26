import Mathlib
import Physlib.Units.WithDim.Energy
import Physlib.Units.WithDim.Speed

/- USER: The assigned source file did not exist when this autoformalization task began. -/

noncomputable section

namespace PhyXMiniProblems.ProblemPhyXMini0821

open Dimension

/-!
# Angular speed of a cylinder unwound by a falling block

A light, inextensible cable is wrapped around a solid cylinder of mass `M`
and radius `R`.  Its free end is tied to a block of mass `m`, initially a
height `h` above the floor.  The cylinder turns about a stationary horizontal
axis with negligible axle friction.  When released from rest, the block falls
and the cable unwinds without slipping.

The answer choices express the impact angular speed in terms of the block's
impact speed `v`.  The no-slip kinematics give the requested relation
`ω = v / R`, answer B.

Masses, lengths, speeds, angular speeds, acceleration, moment of inertia, and
energies are represented by unit-independent Physlib quantities.  Real
numbers below occur only in coherent-SI readouts and symbolic answer formulas.

Assumption/target split:

* governing laws: the solid-cylinder inertia formula, equality of block and
  cable speeds, the no-slip rim-speed relation, the standard potential and
  kinetic energy formulas, and conservation of mechanical energy;
* previous-part results: none; `v` is named here as the block's impact speed;
* figure/data readouts: cylinder, central axis, left-tangent cable, hanging
  block, floor, the radius arrow, height arrow, and labels `M`, `R`, `m`, `h`;
* current target: the coherent-SI angular-speed readout equals `v / R`, and
  hence corresponds to answer choice B.
-/

/-! ## Dimensionful physical quantities and coherent-SI readouts -/

/-- The physical dimension `L T⁻²` of gravitational acceleration. -/
def accelerationDimension : Dimension :=
  L𝓭 * T𝓭⁻¹ * T𝓭⁻¹

/-- The physical dimension `M L²` of an axial moment of inertia. -/
def momentOfInertiaDimension : Dimension :=
  M𝓭 * L𝓭 * L𝓭

/-- A nonnegative, unit-independent physical mass. -/
abbrev MassQuantity : Type :=
  Dimensionful (WithDim M𝓭 NNReal)

/-- A nonnegative, unit-independent physical length. -/
abbrev LengthQuantity : Type :=
  Dimensionful (WithDim L𝓭 NNReal)

/-- A nonnegative linear-speed magnitude. -/
abbrev SpeedQuantity : Type := DimSpeed

/-- A nonnegative angular-speed magnitude; radians are dimensionless. -/
abbrev AngularSpeedQuantity : Type :=
  Dimensionful (WithDim T𝓭⁻¹ NNReal)

/-- A nonnegative gravitational-acceleration magnitude. -/
abbrev AccelerationQuantity : Type :=
  Dimensionful (WithDim accelerationDimension NNReal)

/-- A nonnegative scalar moment of inertia about the cylinder axis. -/
abbrev MomentOfInertiaQuantity : Type :=
  Dimensionful (WithDim momentOfInertiaDimension NNReal)

/-- A physical energy, with dimension `M L² T⁻²`. -/
abbrev EnergyQuantity : Type := DimEnergy

/-- Read a nonnegative dimensionful quantity in coherent SI units. -/
def nonnegativeSIReadout {dimension : Dimension}
    (quantity : Dimensionful (WithDim dimension NNReal)) : ℝ :=
  ((quantity UnitChoices.SI).val : ℝ)

/-- Kilogram readout of a mass. -/
def massInKilograms (mass : MassQuantity) : ℝ :=
  nonnegativeSIReadout mass

/-- Metre readout of a length. -/
def lengthInMeters (length : LengthQuantity) : ℝ :=
  nonnegativeSIReadout length

/-- Metre-per-second readout of a linear speed. -/
def speedInMetersPerSecond (speed : SpeedQuantity) : ℝ :=
  nonnegativeSIReadout speed

/-- Radian-per-second readout of an angular-speed magnitude. -/
def angularSpeedInRadiansPerSecond (speed : AngularSpeedQuantity) : ℝ :=
  nonnegativeSIReadout speed

/-- Metre-per-second-squared readout of an acceleration magnitude. -/
def accelerationInMetersPerSecondSquared
    (acceleration : AccelerationQuantity) : ℝ :=
  nonnegativeSIReadout acceleration

/-- `kg m²` readout of a scalar moment of inertia. -/
def momentOfInertiaInKilogramMetersSquared
    (inertia : MomentOfInertiaQuantity) : ℝ :=
  nonnegativeSIReadout inertia

/-- Joule readout of an energy, calibrated by Physlib's joule. -/
def energyInJoules (energy : EnergyQuantity) : ℝ :=
  (energy UnitChoices.SI).val /
    (DimEnergy.joule UnitChoices.SI).val

/-! ## Primary-figure vocabulary -/

/-- Individually recognizable elements of the supplied bitmap. -/
inductive FigureElement where
  | solidCylinder
  | centralAxle
  | wrappedCable
  | hangingBlock
  | radiusArrow
  | heightArrow
  | floorLine
  | groundHatching
  deriving DecidableEq, Fintype, Repr

/-- Literal symbolic labels visible in the supplied bitmap. -/
inductive FigureLabel where
  | cylinderMassM
  | radiusR
  | blockMassm
  | releaseHeightH
  deriving DecidableEq, Fintype, Repr

/-- Side of the cylinder at which the pictured straight cable is tangent. -/
inductive CylinderSide where
  | left
  | right
  deriving DecidableEq, Repr

/-- Orientation of the straight cable segment drawn between cylinder and block. -/
inductive CableSegmentOrientation where
  | vertical
  | horizontal
  deriving DecidableEq, Repr

/-- Qualitative placement information transcribed from primary image `821.png`. -/
structure CylinderCableFigure where
  showsElement : FigureElement → Bool
  showsLabel : FigureLabel → Bool
  straightCableTangentSide : CylinderSide
  straightCableOrientation : CableSegmentOrientation
  blockDrawnBelowCylinder : Bool
  radiusArrowRunsFromRimToAxle : Bool
  heightArrowRunsFromFloorToBlock : Bool

/-! ## Physical apparatus and scenario assumptions -/

/-- The rigid body's mass-distribution idealization. -/
inductive CylinderMassModel where
  | uniformSolidCylinder
  deriving DecidableEq, Repr

/-- Orientation of the cylinder's rotation axis. -/
inductive AxisOrientation where
  | horizontal
  deriving DecidableEq, Repr

/-- Motion of the axis relative to the laboratory. -/
inductive AxisMotion where
  | stationary
  deriving DecidableEq, Repr

/-- Bearing-friction idealization used by the problem. -/
inductive AxleFrictionModel where
  | negligible
  deriving DecidableEq, Repr

/-- Cable-mass idealization represented by the word "light". -/
inductive CableMassModel where
  | negligible
  deriving DecidableEq, Repr

/-- Cable-extension idealization represented by "nonstretching". -/
inductive CableStretchModel where
  | inextensible
  deriving DecidableEq, Repr

/-- Contact behavior between the cable and cylinder. -/
inductive CableContactModel where
  | unwindsWithoutSlipping
  deriving DecidableEq, Repr

/-- Attachment of the cable's free end. -/
inductive CableAttachment where
  | tiedToBlock
  deriving DecidableEq, Repr

/-!
Independent quantities and qualitative data of the cylinder-cable-block
system.  In particular, the impact angular speed is an unconstrained physical
quantity here and is not defined from an answer choice.
-/
structure CylinderCableSetup where
  figure : CylinderCableFigure
  cylinderMassModel : CylinderMassModel
  axisOrientation : AxisOrientation
  axisMotion : AxisMotion
  axleFrictionModel : AxleFrictionModel
  cableMassModel : CableMassModel
  cableStretchModel : CableStretchModel
  cableContactModel : CableContactModel
  cableAttachment : CableAttachment
  cylinderMassM : MassQuantity
  cylinderRadiusR : LengthQuantity
  blockMassm : MassQuantity
  releaseHeightH : LengthQuantity
  fallDistanceAtImpact : LengthQuantity
  gravitationalAcceleration : AccelerationQuantity
  cylinderMomentOfInertia : MomentOfInertiaQuantity
  initialBlockSpeed : SpeedQuantity
  initialCylinderAngularSpeed : AngularSpeedQuantity
  blockSpeedAtImpactV : SpeedQuantity
  cableSpeedAtImpact : SpeedQuantity
  cylinderAngularSpeedAtImpact : AngularSpeedQuantity
  initialGravitationalPotentialEnergy : EnergyQuantity
  blockKineticEnergyAtImpact : EnergyQuantity
  cylinderRotationalEnergyAtImpact : EnergyQuantity

/-- Literal graphical evidence from the primary raster. -/
structure MatchesPrimaryFigure (setup : CylinderCableSetup) : Prop where
  allElementsShown :
    ∀ element : FigureElement, setup.figure.showsElement element = true
  allLabelsShown :
    ∀ label : FigureLabel, setup.figure.showsLabel label = true
  cableIsTangentOnLeft :
    setup.figure.straightCableTangentSide = .left
  straightCableIsVertical :
    setup.figure.straightCableOrientation = .vertical
  blockIsBelowCylinder : setup.figure.blockDrawnBelowCylinder = true
  radiusArrowJoinsRimAndAxle :
    setup.figure.radiusArrowRunsFromRimToAxle = true
  heightArrowJoinsFloorAndBlock :
    setup.figure.heightArrowRunsFromFloorToBlock = true

/-- Qualitative assumptions and initial/impact conditions stated in the prose. -/
structure MatchesProblemDescription (setup : CylinderCableSetup) : Prop where
  cylinderIsUniformAndSolid :
    setup.cylinderMassModel = .uniformSolidCylinder
  rotationAxisIsHorizontal : setup.axisOrientation = .horizontal
  rotationAxisIsStationary : setup.axisMotion = .stationary
  axleFrictionIsNegligible : setup.axleFrictionModel = .negligible
  cableMassIsNegligible : setup.cableMassModel = .negligible
  cableIsInextensible : setup.cableStretchModel = .inextensible
  cableUnwindsWithoutSlipping :
    setup.cableContactModel = .unwindsWithoutSlipping
  freeEndIsTiedToBlock : setup.cableAttachment = .tiedToBlock
  blockReleasedFromRest :
    speedInMetersPerSecond setup.initialBlockSpeed = 0
  cylinderInitiallyAtRest :
    angularSpeedInRadiansPerSecond setup.initialCylinderAngularSpeed = 0
  blockFallsTheReleaseHeight :
    setup.fallDistanceAtImpact = setup.releaseHeightH

/-- Positivity and nondegeneracy of the physical parameters. -/
structure HasPhysicalParameters (setup : CylinderCableSetup) : Prop where
  cylinderMassPositive : 0 < massInKilograms setup.cylinderMassM
  cylinderRadiusPositive : 0 < lengthInMeters setup.cylinderRadiusR
  blockMassPositive : 0 < massInKilograms setup.blockMassm
  releaseHeightPositive : 0 < lengthInMeters setup.releaseHeightH
  gravityPositive :
    0 < accelerationInMetersPerSecondSquared
      setup.gravitationalAcceleration

/-!
Governing mechanics for the ideal system.  The no-slip condition is kept in
its physical rim-speed form through an independently represented cable speed;
the requested solved relation `ω = v / R` does not occur in this structure.
-/
structure SatisfiesCylinderCableLaws (setup : CylinderCableSetup) : Prop where
  solidCylinderMomentOfInertia :
    momentOfInertiaInKilogramMetersSquared
        setup.cylinderMomentOfInertia =
      (1 / 2 : ℝ) * massInKilograms setup.cylinderMassM *
        lengthInMeters setup.cylinderRadiusR ^ 2
  blockMovesWithCableAtImpact :
    speedInMetersPerSecond setup.blockSpeedAtImpactV =
      speedInMetersPerSecond setup.cableSpeedAtImpact
  noSlipRimSpeedAtImpact :
    speedInMetersPerSecond setup.cableSpeedAtImpact =
      lengthInMeters setup.cylinderRadiusR *
        angularSpeedInRadiansPerSecond
          setup.cylinderAngularSpeedAtImpact
  initialPotentialEnergyFormula :
    energyInJoules setup.initialGravitationalPotentialEnergy =
      massInKilograms setup.blockMassm *
        accelerationInMetersPerSecondSquared
          setup.gravitationalAcceleration *
        lengthInMeters setup.releaseHeightH
  blockKineticEnergyFormula :
    energyInJoules setup.blockKineticEnergyAtImpact =
      (1 / 2 : ℝ) * massInKilograms setup.blockMassm *
        speedInMetersPerSecond setup.blockSpeedAtImpactV ^ 2
  cylinderRotationalEnergyFormula :
    energyInJoules setup.cylinderRotationalEnergyAtImpact =
      (1 / 2 : ℝ) *
        momentOfInertiaInKilogramMetersSquared
          setup.cylinderMomentOfInertia *
        angularSpeedInRadiansPerSecond
          setup.cylinderAngularSpeedAtImpact ^ 2
  mechanicalEnergyConservedAtImpact :
    energyInJoules setup.initialGravitationalPotentialEnergy =
      energyInJoules setup.blockKineticEnergyAtImpact +
        energyInJoules setup.cylinderRotationalEnergyAtImpact

/-! ## Derived kinematics and answer metadata -/

/-- The cable constraints combine to identify the block speed with rim speed. -/
lemma blockImpactSpeed_eq_radius_mul_angularSpeed
    (setup : CylinderCableSetup)
    (_laws : SatisfiesCylinderCableLaws setup) :
    speedInMetersPerSecond setup.blockSpeedAtImpactV =
      lengthInMeters setup.cylinderRadiusR *
        angularSpeedInRadiansPerSecond
          setup.cylinderAngularSpeedAtImpact := by
  exact
    _laws.blockMovesWithCableAtImpact.trans
      _laws.noSlipRimSpeedAtImpact

/-- Labels of the four formulas printed as answer choices. -/
inductive AnswerChoice where
  | A
  | B
  | C
  | D
  deriving DecidableEq, Fintype, Repr

/-- Dataset metadata recording the supplied answer label. -/
def recordedAnswerChoice : AnswerChoice := .B

/-!
At floor impact, the cylinder's angular speed is the block speed `v` divided
by cylinder radius `R`.  This is formula B in the problem statement.

This formalizes blueprint label `thm:physics:phyx_mini_0821:target`.
-/
theorem angularSpeedAtImpact_eq_blockSpeed_div_radius
    (setup : CylinderCableSetup)
    (_figure : MatchesPrimaryFigure setup)
    (_description : MatchesProblemDescription setup)
    (_physical : HasPhysicalParameters setup)
    (_laws : SatisfiesCylinderCableLaws setup) :
    angularSpeedInRadiansPerSecond
        setup.cylinderAngularSpeedAtImpact =
      speedInMetersPerSecond setup.blockSpeedAtImpactV /
        lengthInMeters setup.cylinderRadiusR := by
  have radius_ne :
      lengthInMeters setup.cylinderRadiusR ≠ 0 :=
    ne_of_gt _physical.cylinderRadiusPositive
  apply (eq_div_iff radius_ne).2
  rw [mul_comm]
  exact
    (blockImpactSpeed_eq_radius_mul_angularSpeed setup _laws).symm

end PhyXMiniProblems.ProblemPhyXMini0821
