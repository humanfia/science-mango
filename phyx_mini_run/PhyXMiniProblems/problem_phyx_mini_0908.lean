import Mathlib
import Physlib.Electromagnetism.Basic
import Physlib.Electromagnetism.Charge.ChargeUnit
import Physlib.SpaceAndTime.Space.LengthUnit
import Physlib.Units.WithDim.Basic
import Physlib.Units.WithDim.Speed

noncomputable section

namespace PhyXMiniProblems.ProblemPhyXMini0908

open Dimension

/-!
# Speed of an electron crossing charged circular electrodes

The primary image `908.png` shows two parallel circular electrodes.  The
negative electrode is on the left, the positive electrode is on the right,
their diameter is labelled `2R = 6.0 cm`, and their separation is labelled
`d = 5.0 mm`.  Field arrows point from the positive electrode toward the
negative electrode.  An electron starts at the negative electrode, and its
acceleration arrow points toward the positive electrode.

The electrodes are charged by transferring `10^11` electrons from the
positive electrode to the negative electrode.  The model below keeps all
lengths, areas, charges, masses, capacitances, potentials, field strengths,
accelerations, permittivities, and speeds as unit-independent Physlib
quantities.  Real scalars occur only at explicit coherent-SI or named-unit
readout boundaries and in the governing scalar laws.  In particular, the
impact speed is an independent observable; it is not defined from answer C.
-/

/-! ## Dimensionful physical quantities and unit readouts -/

/-- The physical dimension `L^2` of plate-face area. -/
def areaDimension : Dimension := L𝓭 * L𝓭

/-- The physical dimension `M L^2 T^-2` of energy. -/
def energyDimension : Dimension :=
  M𝓭 * L𝓭 * L𝓭 * T𝓭⁻¹ * T𝓭⁻¹

/-- The physical dimension of electric potential, energy per charge. -/
def electricPotentialDimension : Dimension :=
  energyDimension * C𝓭⁻¹

/-- The physical dimension `C^2 / J` of capacitance. -/
def capacitanceDimension : Dimension :=
  C𝓭 * C𝓭 * M𝓭⁻¹ * L𝓭⁻¹ * L𝓭⁻¹ * T𝓭 * T𝓭

/-- The physical dimension `N / C` of electric-field strength. -/
def electricFieldStrengthDimension : Dimension :=
  M𝓭 * L𝓭 * T𝓭⁻¹ * T𝓭⁻¹ * C𝓭⁻¹

/-- The physical dimension `C^2 / (N m^2)` of electric permittivity. -/
def electricPermittivityDimension : Dimension :=
  C𝓭 * C𝓭 * T𝓭 * T𝓭 * M𝓭⁻¹ * L𝓭⁻¹ * L𝓭⁻¹ * L𝓭⁻¹

/-- The physical dimension `L T^-2` of acceleration. -/
def accelerationDimension : Dimension :=
  L𝓭 * T𝓭⁻¹ * T𝓭⁻¹

/-- A nonnegative, unit-independent physical length. -/
abbrev LengthQuantity : Type :=
  Dimensionful (WithDim L𝓭 NNReal)

/-- A nonnegative, unit-independent physical area. -/
abbrev AreaQuantity : Type :=
  Dimensionful (WithDim areaDimension NNReal)

/-- A nonnegative, unit-independent physical mass. -/
abbrev MassQuantity : Type :=
  Dimensionful (WithDim M𝓭 NNReal)

/-- A nonnegative electric-charge magnitude. -/
abbrev ChargeMagnitudeQuantity : Type :=
  Dimensionful (WithDim C𝓭 NNReal)

/-- A signed electric charge. -/
abbrev SignedChargeQuantity : Type :=
  Dimensionful (WithDim C𝓭 ℝ)

/-- A signed electric potential after choosing a common zero. -/
abbrev ElectricPotentialQuantity : Type :=
  Dimensionful (WithDim electricPotentialDimension ℝ)

/-- A nonnegative potential difference between the two electrodes. -/
abbrev PotentialDifferenceQuantity : Type :=
  Dimensionful (WithDim electricPotentialDimension NNReal)

/-- A nonnegative physical capacitance. -/
abbrev CapacitanceQuantity : Type :=
  Dimensionful (WithDim capacitanceDimension NNReal)

/-- A nonnegative electric-field strength. -/
abbrev ElectricFieldStrengthQuantity : Type :=
  Dimensionful (WithDim electricFieldStrengthDimension NNReal)

/-- A nonnegative electric permittivity. -/
abbrev ElectricPermittivityQuantity : Type :=
  Dimensionful (WithDim electricPermittivityDimension NNReal)

/-- A nonnegative acceleration magnitude. -/
abbrev AccelerationQuantity : Type :=
  Dimensionful (WithDim accelerationDimension NNReal)

/-- A nonnegative physical speed, using Physlib's standard speed type. -/
abbrev SpeedQuantity : Type := DimSpeed

/-- Read a physical length in a selected Physlib length unit. -/
def lengthReadout (unit : LengthUnit) (length : LengthQuantity) : ℝ :=
  ((length {UnitChoices.SI with length := unit}).val : ℝ)

/-- Read a physical length in coherent-SI metres. -/
def lengthInMeters (length : LengthQuantity) : ℝ :=
  lengthReadout LengthUnit.meters length

/-- Read a physical length in centimetres. -/
def lengthInCentimeters (length : LengthQuantity) : ℝ :=
  lengthReadout LengthUnit.centimeters length

/-- Read a physical length in millimetres. -/
def lengthInMillimeters (length : LengthQuantity) : ℝ :=
  lengthReadout LengthUnit.millimeters length

/-- Read plate-face area in coherent-SI square metres. -/
def areaInSquareMeters (area : AreaQuantity) : ℝ :=
  ((area UnitChoices.SI).val : ℝ)

/-- Read a mass in coherent-SI kilograms. -/
def massInKilograms (mass : MassQuantity) : ℝ :=
  ((mass UnitChoices.SI).val : ℝ)

/-- Read a nonnegative charge magnitude in coherent-SI coulombs. -/
def chargeMagnitudeInCoulombs (charge : ChargeMagnitudeQuantity) : ℝ :=
  ((charge UnitChoices.SI).val : ℝ)

/-- Read a signed electric charge in coherent-SI coulombs. -/
def signedChargeInCoulombs (charge : SignedChargeQuantity) : ℝ :=
  (charge UnitChoices.SI).val

/-- Read a signed electric potential in coherent-SI volts. -/
def electricPotentialInVolts (potential : ElectricPotentialQuantity) : ℝ :=
  (potential UnitChoices.SI).val

/-- Read a nonnegative potential difference in coherent-SI volts. -/
def potentialDifferenceInVolts
    (potentialDifference : PotentialDifferenceQuantity) : ℝ :=
  ((potentialDifference UnitChoices.SI).val : ℝ)

/-- Read capacitance in coherent-SI farads. -/
def capacitanceInFarads (capacitance : CapacitanceQuantity) : ℝ :=
  ((capacitance UnitChoices.SI).val : ℝ)

/-- Read field strength in coherent SI newtons per coulomb. -/
def electricFieldStrengthInNewtonsPerCoulomb
    (strength : ElectricFieldStrengthQuantity) : ℝ :=
  ((strength UnitChoices.SI).val : ℝ)

/-- Read permittivity in coherent SI `C^2 / (N m^2)`. -/
def electricPermittivityInSI
    (permittivity : ElectricPermittivityQuantity) : ℝ :=
  ((permittivity UnitChoices.SI).val : ℝ)

/-- Read acceleration in coherent SI metres per second squared. -/
def accelerationInMetersPerSecondSquared
    (acceleration : AccelerationQuantity) : ℝ :=
  ((acceleration UnitChoices.SI).val : ℝ)

/-- Read a speed in coherent SI metres per second. -/
def speedInMetersPerSecond (speed : SpeedQuantity) : ℝ :=
  ((speed UnitChoices.SI).val : ℝ)

/-!
Physlib supplies the elementary charge as a `ChargeUnit`.  This is its
positive magnitude relative to the coulomb unit.
-/
def physlibElementaryChargeInCoulombs : ℝ :=
  ((ChargeUnit.elementaryCharge / ChargeUnit.coulombs : NNReal) : ℝ)

/-- Classical translational kinetic energy as a coherent-SI joule readout. -/
def classicalKineticEnergyInJoules
    (mass : MassQuantity) (speed : SpeedQuantity) : ℝ :=
  (1 / 2 : ℝ) * massInKilograms mass * speedInMetersPerSecond speed ^ 2

/-- Electrostatic potential energy `q V` as a coherent-SI joule readout. -/
def electrostaticPotentialEnergyInJoules
    (charge : SignedChargeQuantity)
    (potential : ElectricPotentialQuantity) : ℝ :=
  signedChargeInCoulombs charge * electricPotentialInVolts potential

/-! ## Named physical roles and primary-figure vocabulary -/

/-- The two electrodes, named by the signs printed in the image. -/
inductive ElectrodeLabel where
  | negative
  | positive
  deriving DecidableEq, Fintype, Repr

/-- Horizontal placement of an electrode in the side-view diagram. -/
inductive HorizontalSide where
  | left
  | right
  deriving DecidableEq, Repr

/-- Electrical polarity printed on an electrode. -/
inductive ElectrodePolarity where
  | negative
  | positive
  deriving DecidableEq, Repr

/-- Plate-face shape used by the elementary capacitance model. -/
inductive ElectrodeShape where
  | circular
  | other
  deriving DecidableEq, Repr

/-- Material filling the gap between the electrodes. -/
inductive GapMedium where
  | vacuum
  | material
  deriving DecidableEq, Repr

/-- Particle species distinguished by the problem. -/
inductive ParticleSpecies where
  | electron
  | other
  deriving DecidableEq, Repr

/-- Sign of the moving particle's electric charge. -/
inductive ChargeSign where
  | negative
  | positive
  deriving DecidableEq, Repr

/-- Horizontal directions needed to interpret the field and acceleration arrows. -/
inductive HorizontalDirection where
  | leftward
  | rightward
  deriving DecidableEq, Repr

/-- The release event and the later collision event. -/
inductive MotionEvent where
  | release
  | impact
  deriving DecidableEq, Fintype, Repr

/-!
Literal content transcribed from image `908.png`.  The diameter and gap
inscriptions are scalar named-unit readouts; calibration premises below tie
them to independent dimensionful lengths.
-/
structure ParallelCircularElectrodeFigure where
  electrodeShown : ElectrodeLabel → Bool
  electrodeSide : ElectrodeLabel → HorizontalSide
  electrodePolarity : ElectrodeLabel → ElectrodePolarity
  chargeLabelUsesQ : ElectrodeLabel → Bool
  electrodesDrawnParallel : Bool
  diameterArrowShown : Bool
  diameterLabelUsesTwoR : Bool
  printedDiameterCentimeters : ℝ
  separationArrowShown : Bool
  separationLabelUsesD : Bool
  printedSeparationMillimeters : ℝ
  electricFieldArrowsShown : Bool
  electricFieldVectorLabelShown : Bool
  electricFieldArrowDirection : HorizontalDirection
  electronMarkerShown : Bool
  electronTextShown : Bool
  electronMarkerAt : ElectrodeLabel
  accelerationArrowShown : Bool
  accelerationVectorLabelShown : Bool
  accelerationArrowDirection : HorizontalDirection

/-!
Independent physical quantities and observables of the experiment.  In
particular, `speedAt .impact` is stored as an unknown physical speed and is
not computed here from the recorded answer or from a closed-form formula.
-/
structure TransferredElectronCapacitorSetup where
  electrodeShape : ElectrodeShape
  plateDiameter : LengthQuantity
  plateRadius : LengthQuantity
  plateFaceArea : AreaQuantity
  plateSeparation : LengthQuantity
  transferredElectronCount : ℕ
  transferredChargeMagnitude : ChargeMagnitudeQuantity
  signedChargeOn : ElectrodeLabel → SignedChargeQuantity
  transferSource : ElectrodeLabel
  transferDestination : ElectrodeLabel
  gapMedium : GapMedium
  vacuumElectromagneticSystem : Electromagnetism.EMSystem
  vacuumPermittivity : ElectricPermittivityQuantity
  capacitance : CapacitanceQuantity
  electricPotentialAt : ElectrodeLabel → ElectricPotentialQuantity
  potentialDifference : PotentialDifferenceQuantity
  electricFieldStrength : ElectricFieldStrengthQuantity
  electricField : Electromagnetism.ElectricField 1
  observationTime : Time
  betweenElectrodes : Set (Time × Space 1)
  electricFieldDirection : HorizontalDirection
  particleSpecies : ParticleSpecies
  particleChargeSign : ChargeSign
  electronMass : MassQuantity
  electronChargeMagnitude : ChargeMagnitudeQuantity
  electronSignedCharge : SignedChargeQuantity
  electricAccelerationMagnitude : AccelerationQuantity
  electronAccelerationDirection : HorizontalDirection
  locationAt : MotionEvent → ElectrodeLabel
  speedAt : MotionEvent → SpeedQuantity
  figure : ParallelCircularElectrodeFigure

/-! ## Scenario, figure/data readouts, constants, geometry, and laws -/

/-- The prose scenario, without any assertion of the requested impact speed. -/
structure MatchesTransferredElectronCapacitorScenario
    (setup : TransferredElectronCapacitorSetup) : Prop where
  electrodesAreCircular : setup.electrodeShape = .circular
  gapIsVacuum : setup.gapMedium = .vacuum
  electronsRemovedFromPositiveElectrode :
    setup.transferSource = .positive
  electronsPlacedOnNegativeElectrode :
    setup.transferDestination = .negative
  movingParticleIsElectron : setup.particleSpecies = .electron
  movingParticleChargeIsNegative : setup.particleChargeSign = .negative
  releasedAtNegativeElectrode : setup.locationAt .release = .negative
  collidesWithPositiveElectrode : setup.locationAt .impact = .positive
  fieldPointsFromPositiveToNegative :
    setup.electricFieldDirection = .leftward
  electronAccelerationOpposesField :
    setup.electronAccelerationDirection = .rightward

/-!
All qualitative and numerical evidence read from the primary raster.  No
impact speed or answer choice is printed in the image or asserted here.
-/
structure MatchesSuppliedParallelElectrodeFigure
    (setup : TransferredElectronCapacitorSetup) : Prop where
  bothElectrodesShown :
    setup.figure.electrodeShown .negative = true ∧
      setup.figure.electrodeShown .positive = true
  negativeElectrodeOnLeft :
    setup.figure.electrodeSide .negative = .left
  positiveElectrodeOnRight :
    setup.figure.electrodeSide .positive = .right
  negativePolarityPrinted :
    setup.figure.electrodePolarity .negative = .negative
  positivePolarityPrinted :
    setup.figure.electrodePolarity .positive = .positive
  bothChargeLabelsUseQ : ∀ electrode,
    setup.figure.chargeLabelUsesQ electrode = true
  electrodesAreDrawnParallel : setup.figure.electrodesDrawnParallel = true
  diameterArrowIsShown : setup.figure.diameterArrowShown = true
  diameterLabelUsesTwoR : setup.figure.diameterLabelUsesTwoR = true
  diameterLabelIsSixCentimeters :
    setup.figure.printedDiameterCentimeters = 6
  diameterLabelCalibratesPhysicalDiameter :
    lengthInCentimeters setup.plateDiameter =
      setup.figure.printedDiameterCentimeters
  separationArrowIsShown : setup.figure.separationArrowShown = true
  separationLabelUsesD : setup.figure.separationLabelUsesD = true
  separationLabelIsFiveMillimeters :
    setup.figure.printedSeparationMillimeters = 5
  separationLabelCalibratesPhysicalGap :
    lengthInMillimeters setup.plateSeparation =
      setup.figure.printedSeparationMillimeters
  fieldArrowsAreShown : setup.figure.electricFieldArrowsShown = true
  fieldVectorLabelIsShown :
    setup.figure.electricFieldVectorLabelShown = true
  fieldArrowsPointLeft :
    setup.figure.electricFieldArrowDirection = .leftward
  figureFieldAgreesWithPhysicalDirection :
    setup.figure.electricFieldArrowDirection = setup.electricFieldDirection
  electronMarkerIsShown : setup.figure.electronMarkerShown = true
  electronTextIsShown : setup.figure.electronTextShown = true
  electronIsDrawnAtNegativeElectrode :
    setup.figure.electronMarkerAt = .negative
  accelerationArrowIsShown : setup.figure.accelerationArrowShown = true
  accelerationVectorLabelIsShown :
    setup.figure.accelerationVectorLabelShown = true
  accelerationArrowPointsRight :
    setup.figure.accelerationArrowDirection = .rightward
  figureAccelerationAgreesWithPhysicalDirection :
    setup.figure.accelerationArrowDirection =
      setup.electronAccelerationDirection

/-!
Numerical information from the prose and its SI conversions.  The released
electron is at rest, while the impact speed remains unconstrained here.
-/
structure MatchesProblemReadouts
    (setup : TransferredElectronCapacitorSetup) : Prop where
  transferredElectronCount : setup.transferredElectronCount = 10 ^ 11
  diameterCentimeters : lengthInCentimeters setup.plateDiameter = 6
  diameterMeters : lengthInMeters setup.plateDiameter = 6 / 100
  separationMillimeters : lengthInMillimeters setup.plateSeparation = 5
  separationMeters : lengthInMeters setup.plateSeparation = 5 / 1000
  releasedFromRest : speedInMetersPerSecond (setup.speedAt .release) = 0

/-!
Electron reference data and the rounded vacuum permittivity used by the
introductory-physics arithmetic.  Physlib supplies the exact elementary
charge; the mass uses the usual `9.11 * 10^-31 kg` readout.  The rounded
`epsilon_0 = 9 * 10^-12` calibration accounts for the precision of the
two-significant-figure answer choices and states no impact-speed result.
-/
structure UsesTextbookElectronAndVacuumReferenceData
    (setup : TransferredElectronCapacitorSetup) : Prop where
  electronChargeMagnitudeCalibration :
    chargeMagnitudeInCoulombs setup.electronChargeMagnitude =
      physlibElementaryChargeInCoulombs
  electronSignedChargeCalibration :
    signedChargeInCoulombs setup.electronSignedCharge =
      -chargeMagnitudeInCoulombs setup.electronChargeMagnitude
  electronMassKilograms :
    massInKilograms setup.electronMass = 911 / (10 : ℝ) ^ 33
  dimensionfulPermittivityAgreesWithEMSystem :
    electricPermittivityInSI setup.vacuumPermittivity =
      setup.vacuumElectromagneticSystem.ε₀
  textbookRoundedVacuumPermittivity :
    setup.vacuumElectromagneticSystem.ε₀ = 9 / (10 : ℝ) ^ 12

/-! Circular-face geometry associated with the figure's `2R` label. -/
structure SatisfiesCircularElectrodeGeometry
    (setup : TransferredElectronCapacitorSetup) : Prop where
  diameterIsTwiceRadius :
    lengthInMeters setup.plateDiameter =
      2 * lengthInMeters setup.plateRadius
  circularFaceArea :
    areaInSquareMeters setup.plateFaceArea =
      Real.pi * lengthInMeters setup.plateRadius ^ 2

/-- Positivity and non-vacuity assumptions selecting the physical branch. -/
structure HasPhysicalCapacitorParameters
    (setup : TransferredElectronCapacitorSetup) : Prop where
  positiveRadius : 0 < lengthInMeters setup.plateRadius
  positiveSeparation : 0 < lengthInMeters setup.plateSeparation
  positiveFaceArea : 0 < areaInSquareMeters setup.plateFaceArea
  positiveTransferredCount : 0 < setup.transferredElectronCount
  positiveElectronChargeMagnitude :
    0 < chargeMagnitudeInCoulombs setup.electronChargeMagnitude
  positiveElectronMass : 0 < massInKilograms setup.electronMass
  positiveVacuumPermittivity :
    0 < electricPermittivityInSI setup.vacuumPermittivity
  positiveCapacitance : 0 < capacitanceInFarads setup.capacitance
  positivePotentialDifference :
    0 < potentialDifferenceInVolts setup.potentialDifference
  positiveFieldStrength :
    0 < electricFieldStrengthInNewtonsPerCoulomb
      setup.electricFieldStrength
  positiveAcceleration :
    0 < accelerationInMetersPerSecondSquared
      setup.electricAccelerationMagnitude
  plateGapRegionNonempty : setup.betweenElectrodes.Nonempty

/-!
The Physlib vector field has the stated constant magnitude throughout the
idealized gap.  Direction is retained separately by the scenario and figure
premises because the one-dimensional norm does not encode arrow orientation.
-/
structure HasUniformElectricFieldBetweenElectrodes
    (setup : TransferredElectronCapacitorSetup) : Prop where
  uniformMagnitude :
    ∀ time position, (time, position) ∈ setup.betweenElectrodes →
      ‖setup.electricField time position‖ =
        electricFieldStrengthInNewtonsPerCoulomb
          setup.electricFieldStrength

/-!
The governing ideal parallel-plate laws:

* transferring `N` electrons produces charge magnitude `Q = N e`;
* the two electrode charges are `-Q` and `+Q`;
* `C = epsilon_0 A / d`;
* `Delta V = Q / C = E d`;
* Newton's second law gives `m a = e E` for the acceleration magnitude.

These laws contain no solved impact speed, numerical speed interval, or
answer label.
-/
structure SatisfiesIdealParallelPlateElectrostaticLaws
    (setup : TransferredElectronCapacitorSetup) : Prop where
  transferredChargeMagnitudeLaw :
    chargeMagnitudeInCoulombs setup.transferredChargeMagnitude =
      (setup.transferredElectronCount : ℝ) *
        chargeMagnitudeInCoulombs setup.electronChargeMagnitude
  negativeElectrodeCharge :
    signedChargeInCoulombs (setup.signedChargeOn .negative) =
      -chargeMagnitudeInCoulombs setup.transferredChargeMagnitude
  positiveElectrodeCharge :
    signedChargeInCoulombs (setup.signedChargeOn .positive) =
      chargeMagnitudeInCoulombs setup.transferredChargeMagnitude
  parallelPlateCapacitanceLaw :
    capacitanceInFarads setup.capacitance =
      electricPermittivityInSI setup.vacuumPermittivity *
        areaInSquareMeters setup.plateFaceArea /
        lengthInMeters setup.plateSeparation
  potentialDifferenceFromChargeAndCapacitance :
    potentialDifferenceInVolts setup.potentialDifference =
      chargeMagnitudeInCoulombs setup.transferredChargeMagnitude /
        capacitanceInFarads setup.capacitance
  potentialDifferenceIsPositiveMinusNegative :
    potentialDifferenceInVolts setup.potentialDifference =
      electricPotentialInVolts (setup.electricPotentialAt .positive) -
        electricPotentialInVolts (setup.electricPotentialAt .negative)
  uniformFieldPotentialDrop :
    potentialDifferenceInVolts setup.potentialDifference =
      electricFieldStrengthInNewtonsPerCoulomb
          setup.electricFieldStrength *
        lengthInMeters setup.plateSeparation
  electricForceAccelerationLaw :
    massInKilograms setup.electronMass *
        accelerationInMetersPerSecondSquared
          setup.electricAccelerationMagnitude =
      chargeMagnitudeInCoulombs setup.electronChargeMagnitude *
        electricFieldStrengthInNewtonsPerCoulomb
          setup.electricFieldStrength

/-!
Classical mechanical energy is conserved from release at the negative
electrode to impact at the positive electrode.  This is the governing
work-energy law `K + qV = constant`; it does not solve for the impact speed.
-/
structure SatisfiesElectrostaticMechanicalEnergyConservation
    (setup : TransferredElectronCapacitorSetup) : Prop where
  energyConserved :
    classicalKineticEnergyInJoules
          setup.electronMass (setup.speedAt .release) +
        electrostaticPotentialEnergyInJoules
          setup.electronSignedCharge
          (setup.electricPotentialAt (setup.locationAt .release)) =
      classicalKineticEnergyInJoules
          setup.electronMass (setup.speedAt .impact) +
        electrostaticPotentialEnergyInJoules
          setup.electronSignedCharge
          (setup.electricPotentialAt (setup.locationAt .impact))

/-! ## Displayed answers and current target conclusions -/

/-- Labels of the four speeds printed with the problem. -/
inductive AnswerChoice where
  | A
  | B
  | C
  | D
  deriving DecidableEq, Fintype, Repr

/-- Speed printed beside each choice, in metres per second. -/
def AnswerChoice.displayedSpeedInMetersPerSecond : AnswerChoice → ℝ
  | .A => 13 * 10 ^ 6
  | .B => 53 * 10 ^ 6
  | .C => 33 * 10 ^ 6
  | .D => 35 * 10 ^ 6

/-!
Half of one unit in the final significant place of the displayed speeds.
This is a reporting tolerance, not an assumption about the impact speed.
-/
def displayedSpeedRoundingTolerance : ℝ := 5 * 10 ^ 5

/-- The source dataset records answer C; this is metadata, not a premise. -/
def recordedDatasetAnswer : AnswerChoice := .C

/-- A choice is the ordinary two-significant-figure rounding match. -/
def MatchesDisplayedImpactSpeed
    (setup : TransferredElectronCapacitorSetup)
    (choice : AnswerChoice) : Prop :=
  |speedInMetersPerSecond (setup.speedAt .impact) -
      choice.displayedSpeedInMetersPerSecond| <
    displayedSpeedRoundingTolerance

/-- Exactly one displayed choice matches the physical impact speed. -/
def IsUniqueMatchingDisplayedImpactSpeed
    (setup : TransferredElectronCapacitorSetup)
    (choice : AnswerChoice) : Prop :=
  MatchesDisplayedImpactSpeed setup choice ∧
    ∀ other : AnswerChoice,
      MatchesDisplayedImpactSpeed setup other → other = choice

/-!
The circular-plate geometry and capacitor laws give the potential difference
directly from the transferred electron count, elementary charge, radius, gap,
and vacuum permittivity.
-/
lemma platePotentialDifference_eq_closedForm
    (setup : TransferredElectronCapacitorSetup)
    (hGeometry : SatisfiesCircularElectrodeGeometry setup)
    (hPhysical : HasPhysicalCapacitorParameters setup)
    (hLaws : SatisfiesIdealParallelPlateElectrostaticLaws setup) :
    potentialDifferenceInVolts setup.potentialDifference =
      (setup.transferredElectronCount : ℝ) *
          chargeMagnitudeInCoulombs setup.electronChargeMagnitude *
          lengthInMeters setup.plateSeparation /
        (electricPermittivityInSI setup.vacuumPermittivity *
          Real.pi * lengthInMeters setup.plateRadius ^ 2) := by
  rw [hLaws.potentialDifferenceFromChargeAndCapacitance,
    hLaws.transferredChargeMagnitudeLaw,
    hLaws.parallelPlateCapacitanceLaw, hGeometry.circularFaceArea]
  field_simp [ne_of_gt hPhysical.positiveSeparation,
    ne_of_gt hPhysical.positiveVacuumPermittivity,
    Real.pi_ne_zero, ne_of_gt hPhysical.positiveRadius]

/-!
Combining the voltage formula with `K + qV` conservation and release from
rest gives the nonnegative classical impact-speed square root.  This derived
formula is a conclusion, not a premise field or local definition.
-/
lemma impactSpeed_eq_closedForm
    (setup : TransferredElectronCapacitorSetup)
    (hScenario : MatchesTransferredElectronCapacitorScenario setup)
    (hReadouts : MatchesProblemReadouts setup)
    (hReference : UsesTextbookElectronAndVacuumReferenceData setup)
    (hGeometry : SatisfiesCircularElectrodeGeometry setup)
    (hPhysical : HasPhysicalCapacitorParameters setup)
    (hLaws : SatisfiesIdealParallelPlateElectrostaticLaws setup)
    (hEnergy : SatisfiesElectrostaticMechanicalEnergyConservation setup) :
    speedInMetersPerSecond (setup.speedAt .impact) =
      Real.sqrt
        (2 * (setup.transferredElectronCount : ℝ) *
          chargeMagnitudeInCoulombs setup.electronChargeMagnitude ^ 2 *
          lengthInMeters setup.plateSeparation /
          (massInKilograms setup.electronMass *
            electricPermittivityInSI setup.vacuumPermittivity *
            Real.pi * lengthInMeters setup.plateRadius ^ 2)) := by
  have hPotential := platePotentialDifference_eq_closedForm setup hGeometry hPhysical hLaws
  have hConservation := hEnergy.energyConserved
  rw [hScenario.releasedAtNegativeElectrode,
    hScenario.collidesWithPositiveElectrode] at hConservation
  simp only [classicalKineticEnergyInJoules,
    electrostaticPotentialEnergyInJoules] at hConservation
  rw [hReadouts.releasedFromRest,
    hReference.electronSignedChargeCalibration] at hConservation
  norm_num at hConservation
  have hKinetic :
      (1 / 2 : ℝ) * massInKilograms setup.electronMass *
          speedInMetersPerSecond (setup.speedAt .impact) ^ 2 =
        chargeMagnitudeInCoulombs setup.electronChargeMagnitude *
          potentialDifferenceInVolts setup.potentialDifference := by
    rw [hLaws.potentialDifferenceIsPositiveMinusNegative]
    nlinarith [hConservation]
  rw [hPotential] at hKinetic
  have hSpeedSquared :
      speedInMetersPerSecond (setup.speedAt .impact) ^ 2 =
        2 * (setup.transferredElectronCount : ℝ) *
          chargeMagnitudeInCoulombs setup.electronChargeMagnitude ^ 2 *
          lengthInMeters setup.plateSeparation /
          (massInKilograms setup.electronMass *
            electricPermittivityInSI setup.vacuumPermittivity *
            Real.pi * lengthInMeters setup.plateRadius ^ 2) := by
    field_simp [ne_of_gt hPhysical.positiveElectronMass,
      ne_of_gt hPhysical.positiveVacuumPermittivity,
      Real.pi_ne_zero, ne_of_gt hPhysical.positiveRadius] at hKinetic ⊢
    ring_nf at hKinetic ⊢
    nlinarith [hKinetic]
  rw [← hSpeedSquared, Real.sqrt_sq]
  exact NNReal.coe_nonneg _

/-!
With the problem data and textbook reference calibration, the impact speed
lies in the rounding interval centered at `3.3 * 10^7 m/s` and matches no
other printed choice.
-/
lemma impactSpeed_uniquely_matches_answerC
    (setup : TransferredElectronCapacitorSetup)
    (hScenario : MatchesTransferredElectronCapacitorScenario setup)
    (hReadouts : MatchesProblemReadouts setup)
    (hReference : UsesTextbookElectronAndVacuumReferenceData setup)
    (hGeometry : SatisfiesCircularElectrodeGeometry setup)
    (hPhysical : HasPhysicalCapacitorParameters setup)
    (hLaws : SatisfiesIdealParallelPlateElectrostaticLaws setup)
    (hEnergy : SatisfiesElectrostaticMechanicalEnergyConservation setup) :
    (325 * 10 ^ 5 : ℝ) <
        speedInMetersPerSecond (setup.speedAt .impact) ∧
      speedInMetersPerSecond (setup.speedAt .impact) <
        (335 * 10 ^ 5 : ℝ) ∧
      IsUniqueMatchingDisplayedImpactSpeed setup .C := by
  have hRadius : lengthInMeters setup.plateRadius = 3 / 100 := by
    nlinarith [hGeometry.diameterIsTwiceRadius, hReadouts.diameterMeters]
  have hSpeed := impactSpeed_eq_closedForm setup hScenario hReadouts hReference
    hGeometry hPhysical hLaws hEnergy
  rw [hReadouts.transferredElectronCount,
    hReference.electronChargeMagnitudeCalibration,
    hReadouts.separationMeters, hReference.electronMassKilograms,
    hReference.dimensionfulPermittivityAgreesWithEMSystem,
    hReference.textbookRoundedVacuumPermittivity, hRadius] at hSpeed
  have hElementary :
      physlibElementaryChargeInCoulombs = (1.602176634e-19 : ℝ) := by
    simp [physlibElementaryChargeInCoulombs, ChargeUnit.elementaryCharge]
    rfl
  have hImpactLower :
      (325 * 10 ^ 5 : ℝ) <
        speedInMetersPerSecond (setup.speedAt .impact) := by
    rw [hSpeed]
    apply Real.lt_sqrt_of_sq_lt
    rw [hElementary]
    have hDenominator :
        0 < (911 / (10 : ℝ) ^ 33) * (9 / (10 : ℝ) ^ 12) *
          Real.pi * (3 / 100) ^ 2 := by
      positivity
    rw [lt_div_iff₀ hDenominator]
    norm_num
    nlinarith [Real.pi_lt_d2]
  have hImpactUpper :
      speedInMetersPerSecond (setup.speedAt .impact) <
        (335 * 10 ^ 5 : ℝ) := by
    rw [hSpeed]
    apply (Real.sqrt_lt' (by norm_num)).2
    rw [hElementary]
    have hDenominator :
        0 < (911 / (10 : ℝ) ^ 33) * (9 / (10 : ℝ) ^ 12) *
          Real.pi * (3 / 100) ^ 2 := by
      positivity
    rw [div_lt_iff₀ hDenominator]
    norm_num
    nlinarith [Real.pi_gt_d2]
  refine ⟨hImpactLower, hImpactUpper, ?_, ?_⟩
  · rw [MatchesDisplayedImpactSpeed, AnswerChoice.displayedSpeedInMetersPerSecond,
      displayedSpeedRoundingTolerance, abs_lt]
    norm_num
    constructor <;> nlinarith
  · intro other hOther
    cases other with
    | A =>
        simp only [MatchesDisplayedImpactSpeed,
          AnswerChoice.displayedSpeedInMetersPerSecond,
          displayedSpeedRoundingTolerance, abs_lt] at hOther
        norm_num at hOther
        exfalso
        nlinarith
    | B =>
        simp only [MatchesDisplayedImpactSpeed,
          AnswerChoice.displayedSpeedInMetersPerSecond,
          displayedSpeedRoundingTolerance, abs_lt] at hOther
        norm_num at hOther
        exfalso
        nlinarith
    | C => rfl
    | D =>
        simp only [MatchesDisplayedImpactSpeed,
          AnswerChoice.displayedSpeedInMetersPerSecond,
          displayedSpeedRoundingTolerance, abs_lt] at hOther
        norm_num at hOther
        exfalso
        nlinarith

/-!
Transferring `10^11` electrons gives `Q = N e`.  For circular plates of
radius `3.0 cm` separated by `5.0 mm`, the ideal parallel-plate laws give

`Delta V = N e d / (epsilon_0 pi R^2)`.

Mechanical-energy conservation for the electron released from rest then
gives

`v = sqrt (2 N e^2 d / (m_e epsilon_0 pi R^2))`.

Under the standard electron calibration and the textbook-rounded vacuum
permittivity, this lies between `3.25 * 10^7` and `3.35 * 10^7 m/s`, uniquely
selecting `3.3 * 10^7 m/s`, answer C.

This declaration formalizes `thm:physics:phyx_mini_0908:target`.  No premise
states the voltage closed form, solved impact speed, numerical speed interval,
or matching answer choice.
-/
theorem problem_phyx_mini_0908
    (setup : TransferredElectronCapacitorSetup)
    (hScenario : MatchesTransferredElectronCapacitorScenario setup)
    (hFigure : MatchesSuppliedParallelElectrodeFigure setup)
    (hReadouts : MatchesProblemReadouts setup)
    (hReference : UsesTextbookElectronAndVacuumReferenceData setup)
    (hGeometry : SatisfiesCircularElectrodeGeometry setup)
    (hPhysical : HasPhysicalCapacitorParameters setup)
    (hUniformField : HasUniformElectricFieldBetweenElectrodes setup)
    (hLaws : SatisfiesIdealParallelPlateElectrostaticLaws setup)
    (hEnergy : SatisfiesElectrostaticMechanicalEnergyConservation setup) :
    potentialDifferenceInVolts setup.potentialDifference =
        (setup.transferredElectronCount : ℝ) *
            chargeMagnitudeInCoulombs setup.electronChargeMagnitude *
            lengthInMeters setup.plateSeparation /
          (electricPermittivityInSI setup.vacuumPermittivity *
            Real.pi * lengthInMeters setup.plateRadius ^ 2) ∧
      speedInMetersPerSecond (setup.speedAt .impact) =
        Real.sqrt
          (2 * (setup.transferredElectronCount : ℝ) *
            chargeMagnitudeInCoulombs setup.electronChargeMagnitude ^ 2 *
            lengthInMeters setup.plateSeparation /
            (massInKilograms setup.electronMass *
              electricPermittivityInSI setup.vacuumPermittivity *
              Real.pi * lengthInMeters setup.plateRadius ^ 2)) ∧
      (325 * 10 ^ 5 : ℝ) <
        speedInMetersPerSecond (setup.speedAt .impact) ∧
      speedInMetersPerSecond (setup.speedAt .impact) <
        (335 * 10 ^ 5 : ℝ) ∧
      IsUniqueMatchingDisplayedImpactSpeed setup .C := by
  refine ⟨platePotentialDifference_eq_closedForm setup hGeometry hPhysical hLaws,
    impactSpeed_eq_closedForm setup hScenario hReadouts hReference hGeometry
      hPhysical hLaws hEnergy, ?_⟩
  exact impactSpeed_uniquely_matches_answerC setup hScenario hReadouts hReference
    hGeometry hPhysical hLaws hEnergy

end PhyXMiniProblems.ProblemPhyXMini0908
