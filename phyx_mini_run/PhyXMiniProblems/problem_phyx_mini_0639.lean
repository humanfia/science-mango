import Mathlib
import Physlib.Electromagnetism.Basic
import Physlib.Units.WithDim.Speed

noncomputable section

namespace PhyXMiniProblems.ProblemPhyXMini0639

open Dimension

/-!
# Undeflected electrons between charged parallel electrodes

The primary figure shows an electron moving left between two horizontal,
parallel electrodes. A `200 V` source makes the upper electrode positive and
the lower electrode negative. The plate separation is `8.0 mm`, their shown
length is `4.0 cm`, and the electron speed is `5.0 * 10^6 m/s`. A magnetic
field, confined to the plate gap, is chosen so that its force on the electron
cancels the electric force.

Lengths, speed, charge magnitude, potential difference, and field strengths
are represented by unit-independent Physlib quantities. Real numbers occur
only as calibrated readouts in stated units. Physlib's spacetime-dependent
electric and magnetic fields retain the vector-field role of the applied
fields; the scalar school-physics laws below relate their uniform magnitudes.
-/

/-! ## Dimensionful physical quantities and unit readouts -/

/-- The dimension `M L² T⁻² C⁻¹` of electric potential difference. -/
def potentialDifferenceDimension : Dimension :=
  M𝓭 * L𝓭 * L𝓭 * T𝓭⁻¹ * T𝓭⁻¹ * C𝓭⁻¹

/-- The dimension `M L T⁻² C⁻¹` of electric-field strength. -/
def electricFieldStrengthDimension : Dimension :=
  M𝓭 * L𝓭 * T𝓭⁻¹ * T𝓭⁻¹ * C𝓭⁻¹

/-- The dimension `M T⁻¹ C⁻¹` of magnetic-field strength. -/
def magneticFieldStrengthDimension : Dimension :=
  M𝓭 * T𝓭⁻¹ * C𝓭⁻¹

/-- A nonnegative, unit-independent physical length. -/
abbrev LengthQuantity : Type := Dimensionful (WithDim L𝓭 NNReal)

/-- A nonnegative, unit-independent speed. -/
abbrev SpeedQuantity : Type := DimSpeed

/-- A nonnegative electric-charge magnitude. -/
abbrev ChargeMagnitudeQuantity : Type :=
  Dimensionful (WithDim C𝓭 NNReal)

/-- A nonnegative potential-difference magnitude. -/
abbrev PotentialDifferenceQuantity : Type :=
  Dimensionful (WithDim potentialDifferenceDimension NNReal)

/-- A nonnegative electric-field magnitude. -/
abbrev ElectricFieldStrengthQuantity : Type :=
  Dimensionful (WithDim electricFieldStrengthDimension NNReal)

/-- A nonnegative magnetic-field magnitude. -/
abbrev MagneticFieldStrengthQuantity : Type :=
  Dimensionful (WithDim magneticFieldStrengthDimension NNReal)

/-- Read a physical length in a selected length unit. -/
def lengthReadout (unit : LengthUnit) (length : LengthQuantity) : ℝ :=
  ((length {UnitChoices.SI with length := unit}).val : ℝ)

/-- Read a speed in coherent selected length and time units. -/
def speedReadout
    (lengthUnit : LengthUnit) (timeUnit : TimeUnit)
    (speed : SpeedQuantity) : ℝ :=
  ((speed {UnitChoices.SI with
    length := lengthUnit, time := timeUnit}).val : ℝ)

/-- SI readout of an electric-charge magnitude, in coulombs. -/
def chargeInCoulombs (charge : ChargeMagnitudeQuantity) : ℝ :=
  ((charge UnitChoices.SI).val : ℝ)

/-- SI readout of a potential difference, in volts. -/
def potentialDifferenceInVolts
    (potentialDifference : PotentialDifferenceQuantity) : ℝ :=
  ((potentialDifference UnitChoices.SI).val : ℝ)

/-- SI readout of electric-field strength, in volts per metre. -/
def electricFieldStrengthInVoltsPerMeter
    (strength : ElectricFieldStrengthQuantity) : ℝ :=
  ((strength UnitChoices.SI).val : ℝ)

/-- SI readout of magnetic-field strength, in teslas. -/
def magneticFieldStrengthInTeslas
    (strength : MagneticFieldStrengthQuantity) : ℝ :=
  ((strength UnitChoices.SI).val : ℝ)

/-- Read magnetic-field strength in milliteslas. -/
def magneticFieldStrengthInMilliteslas
    (strength : MagneticFieldStrengthQuantity) : ℝ :=
  1000 * magneticFieldStrengthInTeslas strength

/-! ## Named objects, directions, and primary-figure content -/

/-- Particle species distinguished in this problem. -/
inductive ParticleSpecies where
  | electron
  | other
  deriving DecidableEq, Repr

/-- Sign of a particle's electric charge. -/
inductive ChargeSign where
  | positive
  | negative
  deriving DecidableEq, Repr

/-- The two horizontal electrodes visible in the supplied image. -/
inductive ElectrodeLabel where
  | upper
  | lower
  deriving DecidableEq, Repr

/-- Electrical polarity shown for an electrode. -/
inductive ElectrodePolarity where
  | positive
  | negative
  deriving DecidableEq, Repr

/-- The relative geometry of the two electrodes. -/
inductive ElectrodeArrangement where
  | parallel
  | nonparallel
  deriving DecidableEq, Repr

/-- Named Cartesian directions needed to interpret the side-view figure. -/
inductive SpatialDirection where
  | right
  | left
  | upward
  | downward
  | intoPage
  | outOfPage
  deriving DecidableEq, Repr

/-!
Typed content of the supplied raster figure. The three dimensionful label
fields are physical labels, not bare scalar stand-ins. Their numerical unit
readouts are imposed separately by `MatchesProblemAndFigureReadouts`.
-/
structure ParallelElectrodeFigure where
  showsBattery : Bool
  showsElectrode : ElectrodeLabel → Bool
  electrodePolarity : ElectrodeLabel → ElectrodePolarity
  electrodeArrangement : ElectrodeArrangement
  voltageLabel : PotentialDifferenceQuantity
  separationLabel : LengthQuantity
  plateLengthLabel : LengthQuantity
  particleMarker : ParticleSpecies
  particleArrowDirection : SpatialDirection

/-!
The physical apparatus and its independent observables. In particular,
`magneticFieldStrength` is not defined from an answer choice or from the
desired `5 mT` value.
-/
structure ParallelPlateElectronSetup where
  particleSpecies : ParticleSpecies
  particleChargeSign : ChargeSign
  particleChargeMagnitude : ChargeMagnitudeQuantity
  particleSpeed : SpeedQuantity
  plateSeparation : LengthQuantity
  plateLength : LengthQuantity
  potentialDifference : PotentialDifferenceQuantity
  electricFieldStrength : ElectricFieldStrengthQuantity
  magneticFieldStrength : MagneticFieldStrengthQuantity
  electricField : Electromagnetism.ElectricField 3
  magneticField : Electromagnetism.MagneticField 3
  betweenElectrodes : Set (Time × Space 3)
  velocityDirection : SpatialDirection
  electricFieldDirection : SpatialDirection
  magneticFieldDirection : SpatialDirection
  electricForceDirection : SpatialDirection
  magneticForceDirection : SpatialDirection
  figure : ParallelElectrodeFigure

/-! ## Assumptions: source data, field support, and governing laws -/

/-!
Problem-statement and primary-image evidence. The two equivalent separation
readouts keep both the printed `8.0 mm` label and its SI calibration available
to the later plate-field law. No magnetic-field value or answer label occurs
in these data.
-/
structure MatchesProblemAndFigureReadouts
    (setup : ParallelPlateElectronSetup) : Prop where
  particleIsElectron : setup.particleSpecies = .electron
  electronChargeIsNegative : setup.particleChargeSign = .negative
  speedMetersPerSecond :
    speedReadout LengthUnit.meters TimeUnit.seconds setup.particleSpeed =
      5 * 10 ^ 6
  batteryIsShown : setup.figure.showsBattery = true
  bothElectrodesShown :
    setup.figure.showsElectrode .upper = true ∧
      setup.figure.showsElectrode .lower = true
  platesAreParallel : setup.figure.electrodeArrangement = .parallel
  upperPlateIsPositive :
    setup.figure.electrodePolarity .upper = .positive
  lowerPlateIsNegative :
    setup.figure.electrodePolarity .lower = .negative
  voltageLabelIsPhysicalVoltage :
    setup.figure.voltageLabel = setup.potentialDifference
  separationLabelIsPhysicalSeparation :
    setup.figure.separationLabel = setup.plateSeparation
  lengthLabelIsPhysicalPlateLength :
    setup.figure.plateLengthLabel = setup.plateLength
  potentialDifferenceVolts :
    potentialDifferenceInVolts setup.potentialDifference = 200
  separationMillimeters :
    lengthReadout LengthUnit.millimeters setup.plateSeparation = 8
  separationMeters :
    lengthReadout LengthUnit.meters setup.plateSeparation = 8 / 1000
  plateLengthCentimeters :
    lengthReadout LengthUnit.centimeters setup.plateLength = 4
  plateLengthMeters :
    lengthReadout LengthUnit.meters setup.plateLength = 4 / 100
  figureParticleIsElectron : setup.figure.particleMarker = .electron
  figureArrowPointsLeft : setup.figure.particleArrowDirection = .left
  electronMovesLeft : setup.velocityDirection = .left

/-- Positivity and non-vacuity conditions for the physical experiment. -/
structure HasPhysicalParameters (setup : ParallelPlateElectronSetup) : Prop where
  chargeMagnitudePositive :
    0 < chargeInCoulombs setup.particleChargeMagnitude
  speedPositive :
    0 < speedReadout LengthUnit.meters TimeUnit.seconds setup.particleSpeed
  separationPositive :
    0 < lengthReadout LengthUnit.meters setup.plateSeparation
  plateLengthPositive :
    0 < lengthReadout LengthUnit.meters setup.plateLength
  potentialDifferencePositive :
    0 < potentialDifferenceInVolts setup.potentialDifference
  electricFieldStrengthPositive :
    0 < electricFieldStrengthInVoltsPerMeter setup.electricFieldStrength
  magneticFieldStrengthPositive :
    0 < magneticFieldStrengthInTeslas setup.magneticFieldStrength
  plateGapRegionNonempty : setup.betweenElectrodes.Nonempty

/-- A spacetime-dependent vector field vanishes outside a specified region. -/
def FieldIsConfinedTo
    (region : Set (Time × Space 3))
    (field : Time → Space 3 → EuclideanSpace ℝ (Fin 3)) : Prop :=
  ∀ time position, (time, position) ∉ region → field time position = 0

/-!
The problem's explicit support assumption: the magnetic field vanishes away
from the region between the electrodes.
-/
def MagneticFieldIsConfinedToPlateGap
    (setup : ParallelPlateElectronSetup) : Prop :=
  FieldIsConfinedTo setup.betweenElectrodes setup.magneticField

/-!
The scalar strengths stored in the setup are the uniform norms of the Physlib
vector fields within the plate gap.
-/
structure FieldsHaveUniformMagnitudeInPlateGap
    (setup : ParallelPlateElectronSetup) : Prop where
  electricMagnitude :
    ∀ time position, (time, position) ∈ setup.betweenElectrodes →
      ‖setup.electricField time position‖ =
        electricFieldStrengthInVoltsPerMeter setup.electricFieldStrength
  magneticMagnitude :
    ∀ time position, (time, position) ∈ setup.betweenElectrodes →
      ‖setup.magneticField time position‖ =
        magneticFieldStrengthInTeslas setup.magneticFieldStrength

/-!
Uniform parallel-plate electrostatics: the field points from the positive
upper plate to the negative lower plate and has magnitude `E = ΔV / d`.
This law contains no magnetic-field result.
-/
structure SatisfiesParallelPlateElectricFieldLaw
    (setup : ParallelPlateElectronSetup) : Prop where
  fieldPointsDownward : setup.electricFieldDirection = .downward
  strengthFromVoltageAndSeparation :
    electricFieldStrengthInVoltsPerMeter setup.electricFieldStrength =
      potentialDifferenceInVolts setup.potentialDifference /
        lengthReadout LengthUnit.meters setup.plateSeparation

/-!
For the negatively charged, left-moving electron, a magnetic field directed
out of the page gives a downward magnetic force, opposite the upward electric
force. An undeflected path therefore has equal force magnitudes
`q E = q v B`. This is the general Lorentz-force balance, not the requested
numerical value of `B`.
-/
structure SatisfiesUndeflectedLorentzForceBalance
    (setup : ParallelPlateElectronSetup) : Prop where
  magneticFieldPointsOutOfPage : setup.magneticFieldDirection = .outOfPage
  electricForcePointsUpward : setup.electricForceDirection = .upward
  magneticForcePointsDownward : setup.magneticForceDirection = .downward
  zeroNetTransverseForce :
    chargeInCoulombs setup.particleChargeMagnitude *
        electricFieldStrengthInVoltsPerMeter setup.electricFieldStrength =
      chargeInCoulombs setup.particleChargeMagnitude *
        speedReadout LengthUnit.meters TimeUnit.seconds setup.particleSpeed *
          magneticFieldStrengthInTeslas setup.magneticFieldStrength

/-! ## Displayed answers and conclusions -/

/-- Labels of the four magnetic-field choices printed in the question. -/
inductive AnswerChoice where
  | A
  | B
  | C
  | D
  deriving DecidableEq, Repr

/-- Magnetic-field strength, in milliteslas, displayed beside each choice. -/
def answerStrengthInMilliteslas : AnswerChoice → ℝ
  | .A => 4
  | .B => 5
  | .C => 6
  | .D => 7

/-- The answer label recorded in the source dataset. -/
def recordedDatasetAnswer : AnswerChoice := .B

/-!
A displayed choice matches the independently modeled physical magnetic-field
strength when their millitesla readouts agree.
-/
def AnswerMatchesMagneticField
    (setup : ParallelPlateElectronSetup) (choice : AnswerChoice) : Prop :=
  magneticFieldStrengthInMilliteslas setup.magneticFieldStrength =
    answerStrengthInMilliteslas choice

/-- The `200 V` potential difference across `8.0 mm` gives `25000 V/m`. -/
lemma electricFieldStrength_eq_twentyFiveThousand_voltsPerMeter
    (setup : ParallelPlateElectronSetup)
    (hData : MatchesProblemAndFigureReadouts setup)
    (hFieldLaw : SatisfiesParallelPlateElectricFieldLaw setup) :
    electricFieldStrengthInVoltsPerMeter setup.electricFieldStrength = 25000 := by
  rw [hFieldLaw.strengthFromVoltageAndSeparation,
    hData.potentialDifferenceVolts, hData.separationMeters]
  norm_num

/-!
The plate-field law and zero-force condition give
`B = E / v = 25000 / (5 * 10^6) = 5 * 10^-3 T`.
-/
lemma requiredMagneticFieldStrength_eq_fiveMilliteslas
    (setup : ParallelPlateElectronSetup)
    (hData : MatchesProblemAndFigureReadouts setup)
    (hPhysical : HasPhysicalParameters setup)
    (hFieldLaw : SatisfiesParallelPlateElectricFieldLaw setup)
    (hLorentz : SatisfiesUndeflectedLorentzForceBalance setup) :
    magneticFieldStrengthInTeslas setup.magneticFieldStrength = 5 / 1000 := by
  have hE := electricFieldStrength_eq_twentyFiveThousand_voltsPerMeter
    setup hData hFieldLaw
  have hBalance := hLorentz.zeroNetTransverseForce
  rw [hE, hData.speedMetersPerSecond] at hBalance
  have hChargeNe :
      chargeInCoulombs setup.particleChargeMagnitude ≠ 0 :=
    ne_of_gt hPhysical.chargeMagnitudePositive
  have hCancelled : (25000 : ℝ) =
      (5 * 10 ^ 6) *
        magneticFieldStrengthInTeslas setup.magneticFieldStrength := by
    apply mul_left_cancel₀ hChargeNe
    simpa [mul_assoc] using hBalance
  norm_num at hCancelled ⊢
  linarith

/-!
The uniform electric field is `25000 V/m`; canceling its force on an electron
moving at `5.0 * 10^6 m/s` requires an out-of-page field of
`5.0 * 10^-3 T = 5.0 mT`. This is displayed as answer B.

This declaration formalizes `thm:physics:phyx_mini_0639:target`. Neither the
`5 mT` value nor the matching answer appears in any premise.
-/
theorem problem_phyx_mini_0639
    (setup : ParallelPlateElectronSetup)
    (hData : MatchesProblemAndFigureReadouts setup)
    (hPhysical : HasPhysicalParameters setup)
    (hConfined : MagneticFieldIsConfinedToPlateGap setup)
    (hUniform : FieldsHaveUniformMagnitudeInPlateGap setup)
    (hFieldLaw : SatisfiesParallelPlateElectricFieldLaw setup)
    (hLorentz : SatisfiesUndeflectedLorentzForceBalance setup) :
    magneticFieldStrengthInTeslas setup.magneticFieldStrength = 5 / 1000 ∧
      AnswerMatchesMagneticField setup recordedDatasetAnswer := by
  have hB := requiredMagneticFieldStrength_eq_fiveMilliteslas
    setup hData hPhysical hFieldLaw hLorentz
  constructor
  · exact hB
  · norm_num [AnswerMatchesMagneticField, recordedDatasetAnswer,
      answerStrengthInMilliteslas, magneticFieldStrengthInMilliteslas, hB]

end PhyXMiniProblems.ProblemPhyXMini0639
