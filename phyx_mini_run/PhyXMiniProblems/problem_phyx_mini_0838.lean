import Mathlib
import Physlib.Electromagnetism.Basic
import Physlib.Electromagnetism.Charge.ChargeUnit
import Physlib.Units.WithDim.Energy

/- USER: The assigned source file did not exist when this autoformalization task began. -/

noncomputable section

namespace PhyXMiniProblems.ProblemPhyXMini0838

open Dimension

/-!
# Ninety-degree turn of an electron beam in a parallel-plate capacitor

An electron enters and leaves through two holes in the same perforated plate.
The holes are `1.0 cm` apart along that plate, while the uniform field and the
electron acceleration are normal to the plates.  The entry and exit velocity
directions differ by ninety degrees.

The written question asks for electric-field strength, whereas the supplied
answer choices all have units of length and the primary figure labels the
plate spacing by `d`.  This file therefore keeps both physically meaningful
conclusions separate:

* the electric-field strength required by the written question;
* the minimum plate clearance `d`, whose ideal value is `2.5 mm` and matches
  recorded choice D.

Assumption/target split:

* governing laws: constant-acceleration kinematics in coordinates tangent and
  normal to the plates, `K = m |v|^2 / 2`, and `m |a| = |q| E`;
* previous-part results: none;
* figure/data readouts: initial kinetic energy `3.0e-17 J`, hole separation
  `1.0 cm`, the label `d`, parallel plates, two holes in the same plate, the
  upward-to-rightward path, and the elementary-charge calibration;
* current target conclusions: `E = 2 K / (|q| L)`, its numerical SI value,
  existence of a minimum adequate spacing denoted by the figure label `d`,
  `d = L/4 = 2.5 mm`, and unique selection of displayed choice D.

All basic physical quantities below are dimensionful Physlib quantities.
Real numbers occur only as explicitly named coherent-unit readouts, figure
coordinates, or displayed multiple-choice values.
-/

/-! ## Dimensionful quantities and coherent-unit readouts -/

/-- The physical dimension `L T⁻¹` of a signed velocity component. -/
def velocityDimension : Dimension := L𝓭 * T𝓭⁻¹

/-- The physical dimension `L T⁻²` of a signed acceleration component. -/
def accelerationDimension : Dimension := L𝓭 * T𝓭⁻¹ * T𝓭⁻¹

/-- The physical dimension `M L T⁻² C⁻¹` of electric-field strength. -/
def electricFieldStrengthDimension : Dimension :=
  M𝓭 * L𝓭 * T𝓭⁻¹ * T𝓭⁻¹ * C𝓭⁻¹

/-- A nonnegative physical length such as a separation or plate clearance. -/
abbrev LengthQuantity : Type := Dimensionful (WithDim L𝓭 NNReal)

/-- A signed physical coordinate measured along or normal to a plate. -/
abbrev SignedLengthQuantity : Type := Dimensionful (WithDim L𝓭 ℝ)

/-- A nonnegative physical elapsed time. -/
abbrev TimeQuantity : Type := Dimensionful (WithDim T𝓭 NNReal)

/-- A signed physical velocity component. -/
abbrev VelocityQuantity : Type :=
  Dimensionful (WithDim velocityDimension ℝ)

/-- A signed physical acceleration component. -/
abbrev AccelerationQuantity : Type :=
  Dimensionful (WithDim accelerationDimension ℝ)

/-- A nonnegative physical mass. -/
abbrev MassQuantity : Type := Dimensionful (WithDim M𝓭 NNReal)

/-- A nonnegative magnitude of electric charge. -/
abbrev ChargeMagnitudeQuantity : Type :=
  Dimensionful (WithDim C𝓭 NNReal)

/-- A nonnegative magnitude of electric-field strength. -/
abbrev ElectricFieldStrengthQuantity : Type :=
  Dimensionful (WithDim electricFieldStrengthDimension NNReal)

/-- Read a nonnegative physical length in a selected Physlib length unit. -/
def lengthReadout (unit : LengthUnit) (length : LengthQuantity) : ℝ :=
  ((length {UnitChoices.SI with length := unit}).val : ℝ)

/-- Metre readout of a physical length. -/
def lengthInMeters (length : LengthQuantity) : ℝ :=
  lengthReadout LengthUnit.meters length

/-- Centimetre readout used for the separation of the two holes. -/
def lengthInCentimeters (length : LengthQuantity) : ℝ :=
  lengthReadout LengthUnit.centimeters length

/-- Millimetre readout used by the four displayed choices. -/
def lengthInMillimeters (length : LengthQuantity) : ℝ :=
  lengthReadout LengthUnit.millimeters length

/-- SI-metre readout of a signed plate-adapted coordinate. -/
def signedLengthInMeters (length : SignedLengthQuantity) : ℝ :=
  (length UnitChoices.SI).val

/-- SI-second readout of a physical time. -/
def timeInSeconds (time : TimeQuantity) : ℝ :=
  ((time UnitChoices.SI).val : ℝ)

/-- SI-metres-per-second readout of a signed velocity component. -/
def velocityInMetersPerSecond (velocity : VelocityQuantity) : ℝ :=
  (velocity UnitChoices.SI).val

/-- SI-metres-per-second-squared readout of a signed acceleration. -/
def accelerationInMetersPerSecondSquared
    (acceleration : AccelerationQuantity) : ℝ :=
  (acceleration UnitChoices.SI).val

/-- SI-kilogram readout of a nonnegative physical mass. -/
def massInKilograms (mass : MassQuantity) : ℝ :=
  ((mass UnitChoices.SI).val : ℝ)

/-- Read a charge magnitude in a selected Physlib charge unit. -/
def chargeMagnitudeReadout
    (unit : ChargeUnit) (charge : ChargeMagnitudeQuantity) : ℝ :=
  ((charge {UnitChoices.SI with charge := unit}).val : ℝ)

/-- SI-coulomb readout of a physical charge magnitude. -/
def chargeMagnitudeInCoulombs (charge : ChargeMagnitudeQuantity) : ℝ :=
  chargeMagnitudeReadout ChargeUnit.coulombs charge

/-- Coherent-SI joule readout of a Physlib energy. -/
def energyInJoules (energy : DimEnergy) : ℝ :=
  (energy UnitChoices.SI).val

/-- Coherent-SI readout of electric-field strength in newtons per coulomb. -/
def fieldStrengthInNewtonsPerCoulomb
    (strength : ElectricFieldStrengthQuantity) : ℝ :=
  ((strength UnitChoices.SI).val : ℝ)

/-!
Physlib's exact elementary-charge unit, expressed as a scalar number of
coulombs.  The electron charge stored below remains a dimensionful quantity.
-/
def physlibElementaryChargeInCoulombs : ℝ :=
  ((ChargeUnit.elementaryCharge / ChargeUnit.coulombs : NNReal) : ℝ)

/-! ## Primary-figure vocabulary -/

/-- The two physical plates, distinguished by whether the beam holes occur in it. -/
inductive CapacitorPlate where
  | solid
  | perforated
  deriving DecidableEq, Fintype, Repr

/-- The two holes used by the beam in its order of travel. -/
inductive BeamHole where
  | entrance
  | exit
  deriving DecidableEq, Fintype, Repr

/-- Absolute page directions of the blue trajectory arrows in the raster. -/
inductive FigureDirection where
  | upward
  | rightward
  deriving DecidableEq, Repr

/-- The sole symbolic distance label visible in the primary figure. -/
inductive FigureDistanceLabel where
  | d
  deriving DecidableEq, Repr

/-!
Literal qualitative content transcribed from image 838.  This structure has
no numerical plate spacing and contains no requested field-strength result.
-/
structure ParallelPlateTurnFigure where
  plateShown : CapacitorPlate → Bool
  platesAreParallel : Bool
  holePlate : BeamHole → CapacitorPlate
  distanceLabel : FigureDistanceLabel
  distanceArrowIsNormalToPlates : Bool
  beamLabel : String
  incomingArrowDirection : FigureDirection
  outgoingArrowDirection : FigureDirection
  pathBendsBetweenPlates : Bool

/-! ## Independent physical setup -/

/-!
The coordinate system is adapted to the plates.  `alongPlatePosition` and
`normalPosition` are dimensionful trajectory components.  The separate
`Electromagnetism.ElectricField` field retains Physlib's spacetime-dependent
electric-field role; its displayed two-dimensional SI component vector is
connected to the dimensionful strength by the governing-law structure below.

Neither the field strength nor the plate spacing is defined from an answer.
-/
structure ElectronBeamTurnSetup where
  initialKineticEnergy : DimEnergy
  electronMass : MassQuantity
  electronChargeMagnitude : ChargeMagnitudeQuantity
  holeSeparation : LengthQuantity
  requiredFieldStrength : ElectricFieldStrengthQuantity
  electricField : Electromagnetism.ElectricField 2
  uniformFieldVectorNewtonsPerCoulomb : EuclideanSpace ℝ (Fin 2)
  entranceTime : TimeQuantity
  exitTime : TimeQuantity
  alongPlatePosition : TimeQuantity → SignedLengthQuantity
  normalPosition : TimeQuantity → SignedLengthQuantity
  alongPlateVelocity : TimeQuantity → VelocityQuantity
  normalVelocity : TimeQuantity → VelocityQuantity
  normalAcceleration : AccelerationQuantity
  figure : ParallelPlateTurnFigure

/-! ## Scenario, data, and figure readouts -/

/-- The prose and primary-image object identifications. -/
structure MatchesElectronTurnScenario (setup : ElectronBeamTurnSetup) : Prop where
  solidPlateShown : setup.figure.plateShown .solid = true
  perforatedPlateShown : setup.figure.plateShown .perforated = true
  parallelPlates : setup.figure.platesAreParallel = true
  entranceInPerforatedPlate :
    setup.figure.holePlate .entrance = .perforated
  exitInSamePerforatedPlate : setup.figure.holePlate .exit = .perforated
  plateSpacingLabelIsD : setup.figure.distanceLabel = .d
  spacingArrowNormalToPlates :
    setup.figure.distanceArrowIsNormalToPlates = true
  electronLabelShown : setup.figure.beamLabel = "Electrons"
  incomingPathPointsUp :
    setup.figure.incomingArrowDirection = .upward
  outgoingPathPointsRight :
    setup.figure.outgoingArrowDirection = .rightward
  pathBendsInsideCapacitor : setup.figure.pathBendsBetweenPlates = true

/-!
Numerical source data and the standard charge calibration.  The source gives
no numerical field-strength readout here, and the figure's symbolic spacing
`d` is introduced only as the quantity solved for in the target conclusion.
-/
structure MatchesProblemData (setup : ElectronBeamTurnSetup) : Prop where
  kineticEnergyReadout :
    energyInJoules setup.initialKineticEnergy = 3 * 10 ^ (-17 : ℤ)
  holeSeparationReadout : lengthInCentimeters setup.holeSeparation = 1
  elementaryChargeCalibration :
    chargeMagnitudeInCoulombs setup.electronChargeMagnitude =
      physlibElementaryChargeInCoulombs

/-- Positivity and nondegeneracy conditions for the physical apparatus. -/
structure HasPhysicalElectronTurnParameters
    (setup : ElectronBeamTurnSetup) : Prop where
  positiveKineticEnergy : 0 < energyInJoules setup.initialKineticEnergy
  positiveElectronMass : 0 < massInKilograms setup.electronMass
  positiveChargeMagnitude :
    0 < chargeMagnitudeInCoulombs setup.electronChargeMagnitude
  positiveHoleSeparation : 0 < lengthInMeters setup.holeSeparation
  positiveRequiredFieldStrength :
    0 < fieldStrengthInNewtonsPerCoulomb setup.requiredFieldStrength
  positiveTransitTime :
    timeInSeconds setup.entranceTime < timeInSeconds setup.exitTime

/-! ## Governing electric-force and kinematics laws -/

/-!
The field is uniform, the electric force is normal to the plates, and motion
has constant normal acceleration and zero tangential acceleration.  All
equations are expressed at an explicit coherent-SI readout boundary.

The laws are general: they do not mention `2 K / (q L)`, `L/4`, `2.5 mm`, or
any displayed answer choice.
-/
structure SatisfiesUniformFieldKinematics
    (setup : ElectronBeamTurnSetup) : Prop where
  electricFieldIsUniform : ∀ time position,
    setup.electricField time position =
      setup.uniformFieldVectorNewtonsPerCoulomb
  strengthMatchesUniformFieldVector :
    fieldStrengthInNewtonsPerCoulomb setup.requiredFieldStrength =
      ‖setup.uniformFieldVectorNewtonsPerCoulomb‖
  fieldHasNoTangentialComponent :
    setup.uniformFieldVectorNewtonsPerCoulomb (0 : Fin 2) = 0
  signedElectronForceRelation :
    massInKilograms setup.electronMass *
        accelerationInMetersPerSecondSquared setup.normalAcceleration =
      -chargeMagnitudeInCoulombs setup.electronChargeMagnitude *
        setup.uniformFieldVectorNewtonsPerCoulomb (1 : Fin 2)
  kineticEnergyRelation :
    energyInJoules setup.initialKineticEnergy =
      massInKilograms setup.electronMass / 2 *
        (velocityInMetersPerSecond
              (setup.alongPlateVelocity setup.entranceTime) ^ 2 +
          velocityInMetersPerSecond
              (setup.normalVelocity setup.entranceTime) ^ 2)
  electricForceRelation :
    massInKilograms setup.electronMass *
        |accelerationInMetersPerSecondSquared setup.normalAcceleration| =
      chargeMagnitudeInCoulombs setup.electronChargeMagnitude *
        fieldStrengthInNewtonsPerCoulomb setup.requiredFieldStrength
  alongPlateVelocityIsConstant : ∀ time,
    velocityInMetersPerSecond (setup.alongPlateVelocity time) =
      velocityInMetersPerSecond
        (setup.alongPlateVelocity setup.entranceTime)
  normalVelocityLaw : ∀ time,
    velocityInMetersPerSecond (setup.normalVelocity time) =
      velocityInMetersPerSecond
          (setup.normalVelocity setup.entranceTime) +
        accelerationInMetersPerSecondSquared setup.normalAcceleration *
          (timeInSeconds time - timeInSeconds setup.entranceTime)
  alongPlatePositionLaw : ∀ time,
    signedLengthInMeters (setup.alongPlatePosition time) =
      signedLengthInMeters
          (setup.alongPlatePosition setup.entranceTime) +
        velocityInMetersPerSecond
            (setup.alongPlateVelocity setup.entranceTime) *
          (timeInSeconds time - timeInSeconds setup.entranceTime)
  normalPositionLaw : ∀ time,
    signedLengthInMeters (setup.normalPosition time) =
      signedLengthInMeters (setup.normalPosition setup.entranceTime) +
        velocityInMetersPerSecond
            (setup.normalVelocity setup.entranceTime) *
          (timeInSeconds time - timeInSeconds setup.entranceTime) +
        (1 / 2 : ℝ) *
          accelerationInMetersPerSecondSquared setup.normalAcceleration *
          (timeInSeconds time - timeInSeconds setup.entranceTime) ^ 2

/-!
Boundary conditions for the desired ninety-degree turn.  The dot-product
equation is the requested right-angle condition in the orthonormal
plate-tangent/plate-normal frame.  It is a design condition, not the requested
field magnitude or plate clearance.
-/
structure SatisfiesNinetyDegreeTurnBoundaryConditions
    (setup : ElectronBeamTurnSetup) : Prop where
  entranceAlongCoordinateIsZero :
    signedLengthInMeters
      (setup.alongPlatePosition setup.entranceTime) = 0
  entranceNormalCoordinateIsZero :
    signedLengthInMeters (setup.normalPosition setup.entranceTime) = 0
  exitAlongCoordinateIsHoleSeparation :
    signedLengthInMeters (setup.alongPlatePosition setup.exitTime) =
      lengthInMeters setup.holeSeparation
  exitReturnsToPerforatedPlate :
    signedLengthInMeters (setup.normalPosition setup.exitTime) = 0
  entryMovesForwardAndIntoGap :
    0 < velocityInMetersPerSecond
          (setup.alongPlateVelocity setup.entranceTime) ∧
      0 < velocityInMetersPerSecond
          (setup.normalVelocity setup.entranceTime)
  exitMovesForwardAndTowardPlate :
    0 < velocityInMetersPerSecond
          (setup.alongPlateVelocity setup.exitTime) ∧
      velocityInMetersPerSecond (setup.normalVelocity setup.exitTime) < 0
  entryAndExitVelocitiesArePerpendicular :
    velocityInMetersPerSecond
          (setup.alongPlateVelocity setup.entranceTime) *
        velocityInMetersPerSecond
          (setup.alongPlateVelocity setup.exitTime) +
      velocityInMetersPerSecond
          (setup.normalVelocity setup.entranceTime) *
        velocityInMetersPerSecond
          (setup.normalVelocity setup.exitTime) = 0

/-! ## Minimum-clearance predicate and displayed choices -/

/-- A physical time lies between entrance and exit, inclusive. -/
def IsDuringTransit (setup : ElectronBeamTurnSetup) (time : TimeQuantity) : Prop :=
  timeInSeconds setup.entranceTime ≤ timeInSeconds time ∧
    timeInSeconds time ≤ timeInSeconds setup.exitTime

/-!
A candidate plate spacing is adequate when the whole ideal trajectory remains
between the perforated plate (`normal = 0`) and the opposite plate.  This is a
geometric clearance predicate, not a formula for its minimum.
-/
def IsAdequatePlateSpacing
    (setup : ElectronBeamTurnSetup) (spacing : LengthQuantity) : Prop :=
  0 < lengthInMeters spacing ∧
    ∀ time, IsDuringTransit setup time →
      0 ≤ signedLengthInMeters (setup.normalPosition time) ∧
        signedLengthInMeters (setup.normalPosition time) ≤
          lengthInMeters spacing

/-- A spacing is the least positive spacing adequate for the trajectory. -/
def IsMinimumAdequatePlateSpacing
    (setup : ElectronBeamTurnSetup) (spacing : LengthQuantity) : Prop :=
  IsAdequatePlateSpacing setup spacing ∧
    ∀ alternative, IsAdequatePlateSpacing setup alternative →
      lengthInMeters spacing ≤ lengthInMeters alternative

/-- Labels attached to the four length-valued choices in the supplied source. -/
inductive AnswerChoice where
  | A
  | B
  | C
  | D
  deriving DecidableEq, Fintype, Repr

/-- Millimetre value printed next to each answer label. -/
def displayedPlateSpacingInMillimeters : AnswerChoice → ℝ
  | .A => 13 / 10
  | .B => 53 / 10
  | .C => 1
  | .D => 5 / 2

/-- The answer label recorded by the dataset. -/
def recordedDatasetAnswer : AnswerChoice := .D

/-- A physical spacing exactly matches the value printed beside a choice. -/
def MatchesDisplayedPlateSpacing
    (spacing : LengthQuantity) (choice : AnswerChoice) : Prop :=
  lengthInMillimeters spacing =
    displayedPlateSpacingInMillimeters choice

/-- A displayed choice is the unique exact match for a physical spacing. -/
def IsUniqueMatchingDisplayedPlateSpacing
    (spacing : LengthQuantity) (choice : AnswerChoice) : Prop :=
  MatchesDisplayedPlateSpacing spacing choice ∧
    ∀ alternative,
      MatchesDisplayedPlateSpacing spacing alternative →
        alternative = choice

/-! ## Derived relations and final target -/

/-!
The uniform-field laws and ninety-degree boundary conditions imply the field
strength requested by the prose: `E = 2 K / (|q| L)`.
-/
private lemma requiredFieldStrength_eq_energyFormula
    (setup : ElectronBeamTurnSetup)
    (hPhysical : HasPhysicalElectronTurnParameters setup)
    (hKinematics : SatisfiesUniformFieldKinematics setup)
    (hTurn : SatisfiesNinetyDegreeTurnBoundaryConditions setup) :
    fieldStrengthInNewtonsPerCoulomb setup.requiredFieldStrength =
      2 * energyInJoules setup.initialKineticEnergy /
        (chargeMagnitudeInCoulombs setup.electronChargeMagnitude *
          lengthInMeters setup.holeSeparation) := by
  let t₀ := timeInSeconds setup.entranceTime
  let t₁ := timeInSeconds setup.exitTime
  let Δt := t₁ - t₀
  let u :=
    velocityInMetersPerSecond
      (setup.alongPlateVelocity setup.entranceTime)
  let w :=
    velocityInMetersPerSecond
      (setup.normalVelocity setup.entranceTime)
  let a :=
    accelerationInMetersPerSecondSquared setup.normalAcceleration
  let m := massInKilograms setup.electronMass
  let q := chargeMagnitudeInCoulombs setup.electronChargeMagnitude
  let E :=
    fieldStrengthInNewtonsPerCoulomb setup.requiredFieldStrength
  let K := energyInJoules setup.initialKineticEnergy
  let L := lengthInMeters setup.holeSeparation
  have hΔt : 0 < Δt := by
    simpa [Δt, t₀, t₁] using hPhysical.positiveTransitTime
  have hu : 0 < u := by
    simpa [u] using hTurn.entryMovesForwardAndIntoGap.1
  have hw : 0 < w := by
    simpa [w] using hTurn.entryMovesForwardAndIntoGap.2
  have hm : 0 < m := by
    simpa [m] using hPhysical.positiveElectronMass
  have hq : 0 < q := by
    simpa [q] using hPhysical.positiveChargeMagnitude
  have hLpos : 0 < L := by
    simpa [L] using hPhysical.positiveHoleSeparation
  have hL : L = u * Δt := by
    have h :=
      hKinematics.alongPlatePositionLaw setup.exitTime
    simpa [L, u, Δt, t₀, t₁,
      hTurn.entranceAlongCoordinateIsZero,
      hTurn.exitAlongCoordinateIsHoleSeparation] using h
  have hNormalDisplacement :
      0 = w * Δt + (1 / 2 : ℝ) * a * Δt ^ 2 := by
    have h := hKinematics.normalPositionLaw setup.exitTime
    simpa [w, a, Δt, t₀, t₁,
      hTurn.entranceNormalCoordinateIsZero,
      hTurn.exitReturnsToPerforatedPlate] using h
  have hNormalFactor : Δt * (2 * w + a * Δt) = 0 := by
    nlinarith [hNormalDisplacement]
  have hΔt_ne : Δt ≠ 0 := ne_of_gt hΔt
  have hAccelerationTime : a * Δt = -2 * w := by
    have h :=
      (mul_eq_zero.mp hNormalFactor).resolve_left hΔt_ne
    linarith
  have hPerpendicular :
      u * u + w * (w + a * Δt) = 0 := by
    have h := hTurn.entryAndExitVelocitiesArePerpendicular
    rw [hKinematics.alongPlateVelocityIsConstant setup.exitTime,
      hKinematics.normalVelocityLaw setup.exitTime] at h
    simpa [u, w, a, Δt, t₀, t₁] using h
  have huw : u = w := by
    nlinarith [hPerpendicular, hAccelerationTime]
  have hK : K = m * u ^ 2 := by
    have h := hKinematics.kineticEnergyRelation
    change K = m / 2 * (u ^ 2 + w ^ 2) at h
    rw [← huw] at h
    nlinarith
  have ha : a < 0 := by
    nlinarith [hAccelerationTime]
  have habs : |a| = -a := abs_of_neg ha
  have hForce : m * |a| = q * E := by
    simpa [m, q, E, a] using hKinematics.electricForceRelation
  have hNegativeAccelerationTime : (-a) * Δt = 2 * u := by
    rw [huw]
    nlinarith [hAccelerationTime]
  have hCross : q * E * L = 2 * K := by
    calc
      q * E * L = (m * |a|) * L := by rw [hForce]
      _ = m * u * ((-a) * Δt) := by rw [habs, hL]; ring
      _ = m * u * (2 * u) := by rw [hNegativeAccelerationTime]
      _ = 2 * K := by rw [hK]; ring
  apply (eq_div_iff (mul_ne_zero (ne_of_gt hq) (ne_of_gt hLpos))).2
  nlinarith [hCross]

/-!
For the given source data, the required field is the exact SI expression below
(approximately `3.7449e4 N/C`).  This answers the dimensionally consistent
written question without conflating it with the millimetre choices.
-/
private lemma requiredFieldStrength_numeric
    (setup : ElectronBeamTurnSetup)
    (hData : MatchesProblemData setup)
    (hPhysical : HasPhysicalElectronTurnParameters setup)
    (hKinematics : SatisfiesUniformFieldKinematics setup)
    (hTurn : SatisfiesNinetyDegreeTurnBoundaryConditions setup) :
    fieldStrengthInNewtonsPerCoulomb setup.requiredFieldStrength =
      (2 * (3 * 10 ^ (-17 : ℤ))) /
        (physlibElementaryChargeInCoulombs * (1 / 100 : ℝ)) := by
  have centimeters_eq_meters (length : LengthQuantity) :
      lengthInCentimeters length = 100 * lengthInMeters length := by
    have hunit := length.2
      ({ UnitChoices.SI with length := LengthUnit.meters } : UnitChoices)
      ({ UnitChoices.SI with length := LengthUnit.centimeters } : UnitChoices)
    have hval := congrArg WithDim.val hunit
    have hval_real := congrArg (fun value : NNReal => (value : ℝ)) hval
    norm_num [lengthInCentimeters, lengthInMeters, lengthReadout,
      UnitChoices.dimScale, LengthUnit.meters, LengthUnit.centimeters,
      LengthUnit.scale, LengthUnit.div_eq_val, NNReal.smul_def] at hval_real ⊢
    exact hval_real
  have hLengthMeters :
      lengthInMeters setup.holeSeparation = (1 / 100 : ℝ) := by
    nlinarith [hData.holeSeparationReadout,
      centimeters_eq_meters setup.holeSeparation]
  rw [requiredFieldStrength_eq_energyFormula setup hPhysical hKinematics hTurn,
    hData.kineticEnergyReadout, hData.elementaryChargeCalibration,
    hLengthMeters]

/-!
The normal component of the parabolic trajectory reaches its maximum halfway
through the transit.  For a right-angle turn between holes a distance `L`
apart on the same plate, the least clearance is `L/4`.
-/
private lemma minimumPlateSpacing_eq_oneFourthHoleSeparation
    (setup : ElectronBeamTurnSetup)
    (hPhysical : HasPhysicalElectronTurnParameters setup)
    (hKinematics : SatisfiesUniformFieldKinematics setup)
    (hTurn : SatisfiesNinetyDegreeTurnBoundaryConditions setup) :
    ∃ figurePlateSpacingD : LengthQuantity,
      IsMinimumAdequatePlateSpacing setup figurePlateSpacingD ∧
        lengthInMeters figurePlateSpacingD =
          lengthInMeters setup.holeSeparation / 4 := by
  let t₀ := timeInSeconds setup.entranceTime
  let t₁ := timeInSeconds setup.exitTime
  let Δt := t₁ - t₀
  let u :=
    velocityInMetersPerSecond
      (setup.alongPlateVelocity setup.entranceTime)
  let w :=
    velocityInMetersPerSecond
      (setup.normalVelocity setup.entranceTime)
  let a :=
    accelerationInMetersPerSecondSquared setup.normalAcceleration
  let L := lengthInMeters setup.holeSeparation
  have hΔt : 0 < Δt := by
    simpa [Δt, t₀, t₁] using hPhysical.positiveTransitTime
  have hΔt_ne : Δt ≠ 0 := ne_of_gt hΔt
  have hu : 0 < u := by
    simpa [u] using hTurn.entryMovesForwardAndIntoGap.1
  have hw : 0 < w := by
    simpa [w] using hTurn.entryMovesForwardAndIntoGap.2
  have hLpos : 0 < L := by
    simpa [L] using hPhysical.positiveHoleSeparation
  have hL : L = u * Δt := by
    have h :=
      hKinematics.alongPlatePositionLaw setup.exitTime
    simpa [L, u, Δt, t₀, t₁,
      hTurn.entranceAlongCoordinateIsZero,
      hTurn.exitAlongCoordinateIsHoleSeparation] using h
  have hNormalDisplacement :
      0 = w * Δt + (1 / 2 : ℝ) * a * Δt ^ 2 := by
    have h := hKinematics.normalPositionLaw setup.exitTime
    simpa [w, a, Δt, t₀, t₁,
      hTurn.entranceNormalCoordinateIsZero,
      hTurn.exitReturnsToPerforatedPlate] using h
  have hNormalFactor : Δt * (2 * w + a * Δt) = 0 := by
    nlinarith [hNormalDisplacement]
  have hAccelerationTime : a * Δt = -2 * w := by
    have h :=
      (mul_eq_zero.mp hNormalFactor).resolve_left hΔt_ne
    linarith
  have hPerpendicular :
      u * u + w * (w + a * Δt) = 0 := by
    have h := hTurn.entryAndExitVelocitiesArePerpendicular
    rw [hKinematics.alongPlateVelocityIsConstant setup.exitTime,
      hKinematics.normalVelocityLaw setup.exitTime] at h
    simpa [u, w, a, Δt, t₀, t₁] using h
  have huw : u = w := by
    nlinarith [hPerpendicular, hAccelerationTime]
  have ha : a = -2 * w / Δt := by
    apply (eq_div_iff hΔt_ne).2
    exact hAccelerationTime
  have hTrajectory (time : TimeQuantity) :
      signedLengthInMeters (setup.normalPosition time) =
        w * (timeInSeconds time - t₀) *
          (Δt - (timeInSeconds time - t₀)) / Δt := by
    calc
      signedLengthInMeters (setup.normalPosition time) =
          w * (timeInSeconds time - t₀) +
            (1 / 2 : ℝ) * a *
              (timeInSeconds time - t₀) ^ 2 := by
        simpa [w, a, t₀, hTurn.entranceNormalCoordinateIsZero] using
          hKinematics.normalPositionLaw time
      _ = w * (timeInSeconds time - t₀) *
            (Δt - (timeInSeconds time - t₀)) / Δt := by
        rw [ha]
        field_simp [hΔt_ne]
        ring
  let figurePlateSpacingD : LengthQuantity :=
    CarriesDimension.toDimensionful UnitChoices.SI
      ⟨⟨L / 4, (div_nonneg hLpos.le (by norm_num))⟩⟩
  have hSpacingMeters :
      lengthInMeters figurePlateSpacingD = L / 4 := by
    have hUnit :
        ({ UnitChoices.SI with length := LengthUnit.meters } :
            UnitChoices) = UnitChoices.SI := by
      ext <;> rfl
    dsimp only [figurePlateSpacingD, lengthInMeters, lengthReadout]
    rw [hUnit]
    simp only [CarriesDimension.toDimensionful_apply_apply,
      UnitChoices.dimScale_self, one_smul]
    rfl
  have hAdequate : IsAdequatePlateSpacing setup figurePlateSpacingD := by
    constructor
    · rw [hSpacingMeters]
      positivity
    · intro time hDuring
      let s := timeInSeconds time - t₀
      have hs_nonnegative : 0 ≤ s := by
        have h := hDuring.1
        change t₀ ≤ timeInSeconds time at h
        dsimp [s]
        linarith
      have hs_le : s ≤ Δt := by
        have h := hDuring.2
        change timeInSeconds time ≤ t₁ at h
        dsimp [s, Δt]
        linarith
      have hPosition :
          signedLengthInMeters (setup.normalPosition time) =
            w * s * (Δt - s) / Δt := by
        simpa [s] using hTrajectory time
      constructor
      · rw [hPosition]
        positivity
      · rw [hSpacingMeters, hPosition, hL, huw]
        have hSquare : 0 ≤ w * (Δt - 2 * s) ^ 2 := by
          positivity
        have hIdentity :
            w * Δt / 4 - w * s * (Δt - s) / Δt =
              w * (Δt - 2 * s) ^ 2 / (4 * Δt) := by
          field_simp [hΔt_ne]
          ring
        rw [← sub_nonneg]
        rw [hIdentity]
        positivity
  have ht₀_nonnegative : 0 ≤ t₀ := by
    dsimp [t₀, timeInSeconds]
    positivity
  have ht₁_nonnegative : 0 ≤ t₁ := by
    dsimp [t₁, timeInSeconds]
    positivity
  let midpointTime : TimeQuantity :=
    CarriesDimension.toDimensionful UnitChoices.SI
      ⟨⟨(t₀ + t₁) / 2,
        (div_nonneg (add_nonneg ht₀_nonnegative ht₁_nonnegative)
          (by norm_num))⟩⟩
  have hMidpointReadout :
      timeInSeconds midpointTime = (t₀ + t₁) / 2 := by
    dsimp only [midpointTime, timeInSeconds]
    simp only [CarriesDimension.toDimensionful_apply_apply,
      UnitChoices.dimScale_self, one_smul]
    rfl
  have hMidpointDuring : IsDuringTransit setup midpointTime := by
    constructor
    · rw [hMidpointReadout]
      change t₀ ≤ (t₀ + t₁) / 2
      linarith
    · rw [hMidpointReadout]
      change (t₀ + t₁) / 2 ≤ t₁
      linarith
  have hMidpointElapsed :
      timeInSeconds midpointTime - t₀ = Δt / 2 := by
    rw [hMidpointReadout]
    dsimp [Δt]
    ring
  have hMidpointHeight :
      signedLengthInMeters (setup.normalPosition midpointTime) = L / 4 := by
    rw [hTrajectory midpointTime, hMidpointElapsed, hL, huw]
    field_simp [hΔt_ne]
    ring
  refine ⟨figurePlateSpacingD, ⟨hAdequate, ?_⟩, hSpacingMeters⟩
  intro alternative hAlternative
  have hUpperAtMidpoint :=
    (hAlternative.2 midpointTime hMidpointDuring).2
  rw [hMidpointHeight] at hUpperAtMidpoint
  rw [hSpacingMeters]
  exact hUpperAtMidpoint

/-!
Formalization of `thm:physics:phyx_mini_0838:target`.

It preserves the source's mismatch explicitly: the first conjunct answers the
electric-field question, while the existential conclusion explains the
length-valued answer list and recorded choice D.
-/
theorem problem_phyx_mini_0838
    (setup : ElectronBeamTurnSetup)
    (hScenario : MatchesElectronTurnScenario setup)
    (hData : MatchesProblemData setup)
    (hPhysical : HasPhysicalElectronTurnParameters setup)
    (hKinematics : SatisfiesUniformFieldKinematics setup)
    (hTurn : SatisfiesNinetyDegreeTurnBoundaryConditions setup) :
    fieldStrengthInNewtonsPerCoulomb setup.requiredFieldStrength =
        (2 * (3 * 10 ^ (-17 : ℤ))) /
          (physlibElementaryChargeInCoulombs * (1 / 100 : ℝ)) ∧
      ∃ figurePlateSpacingD : LengthQuantity,
        IsMinimumAdequatePlateSpacing setup figurePlateSpacingD ∧
          lengthInMeters figurePlateSpacingD =
            lengthInMeters setup.holeSeparation / 4 ∧
          lengthInMillimeters figurePlateSpacingD = 5 / 2 ∧
          IsUniqueMatchingDisplayedPlateSpacing
            figurePlateSpacingD recordedDatasetAnswer := by
  refine
    ⟨requiredFieldStrength_numeric setup hData hPhysical hKinematics hTurn,
      ?_⟩
  rcases
      minimumPlateSpacing_eq_oneFourthHoleSeparation
        setup hPhysical hKinematics hTurn with
    ⟨figurePlateSpacingD, hMinimum, hSpacingMeters⟩
  have centimeters_eq_meters (length : LengthQuantity) :
      lengthInCentimeters length = 100 * lengthInMeters length := by
    have hunit := length.2
      ({ UnitChoices.SI with length := LengthUnit.meters } : UnitChoices)
      ({ UnitChoices.SI with length := LengthUnit.centimeters } : UnitChoices)
    have hval := congrArg WithDim.val hunit
    have hval_real := congrArg (fun value : NNReal => (value : ℝ)) hval
    norm_num [lengthInCentimeters, lengthInMeters, lengthReadout,
      UnitChoices.dimScale, LengthUnit.meters, LengthUnit.centimeters,
      LengthUnit.scale, LengthUnit.div_eq_val, NNReal.smul_def] at hval_real ⊢
    exact hval_real
  have millimeters_eq_meters (length : LengthQuantity) :
      lengthInMillimeters length = 1000 * lengthInMeters length := by
    have hunit := length.2
      ({ UnitChoices.SI with length := LengthUnit.meters } : UnitChoices)
      ({ UnitChoices.SI with length := LengthUnit.millimeters } : UnitChoices)
    have hval := congrArg WithDim.val hunit
    have hval_real := congrArg (fun value : NNReal => (value : ℝ)) hval
    norm_num [lengthInMillimeters, lengthInMeters, lengthReadout,
      UnitChoices.dimScale, LengthUnit.meters, LengthUnit.millimeters,
      LengthUnit.scale, LengthUnit.div_eq_val, NNReal.smul_def] at hval_real ⊢
    exact hval_real
  have hHoleSeparationMeters :
      lengthInMeters setup.holeSeparation = (1 / 100 : ℝ) := by
    nlinarith [hData.holeSeparationReadout,
      centimeters_eq_meters setup.holeSeparation]
  have hSpacingMillimeters :
      lengthInMillimeters figurePlateSpacingD = 5 / 2 := by
    rw [millimeters_eq_meters, hSpacingMeters, hHoleSeparationMeters]
    norm_num
  have hUnique :
      IsUniqueMatchingDisplayedPlateSpacing
        figurePlateSpacingD recordedDatasetAnswer := by
    constructor
    · change
        lengthInMillimeters figurePlateSpacingD =
          displayedPlateSpacingInMillimeters recordedDatasetAnswer
      rw [hSpacingMillimeters]
      norm_num [recordedDatasetAnswer,
        displayedPlateSpacingInMillimeters]
    · intro alternative hAlternative
      change
        lengthInMillimeters figurePlateSpacingD =
          displayedPlateSpacingInMillimeters alternative at hAlternative
      rw [hSpacingMillimeters] at hAlternative
      cases alternative with
      | A =>
          norm_num [displayedPlateSpacingInMillimeters] at hAlternative
      | B =>
          norm_num [displayedPlateSpacingInMillimeters] at hAlternative
      | C =>
          norm_num [displayedPlateSpacingInMillimeters] at hAlternative
      | D =>
          rfl
  exact
    ⟨figurePlateSpacingD, hMinimum, hSpacingMeters,
      hSpacingMillimeters, hUnique⟩

end PhyXMiniProblems.ProblemPhyXMini0838
