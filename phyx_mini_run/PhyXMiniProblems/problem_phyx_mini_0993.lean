import Mathlib
import Physlib.Electromagnetism.Basic
import Physlib.Electromagnetism.Charge.ChargeUnit
import Physlib.SpaceAndTime.Time.TimeUnit
import Physlib.Units.WithDim.Basic

/- USER: The assigned Lean file did not exist when this autoformalization task began. -/

noncomputable section

namespace PhyXMiniProblems.ProblemPhyXMini0993

open Dimension

/-!
# Electron travel time between parallel plates

The primary raster shows parallel conducting plates separated by `1.0 cm` and
connected to a `100 V` battery.  The lower plate is positive, the upper plate
is negative, and the nearly uniform electric field points upward.  The
pictured particle carries a minus sign, and its force arrow points downward
with the label `F = -e E`.

The coordinate convention in the image has positive `x` to the right and
positive `y` downward.  Consequently the field has negative `y` component,
whereas the force and acceleration of the electron have positive `y`
components.

The source asks for a travel time but does not state an initial velocity.  The
recorded answer `3.4 * 10^-9 s` is the value for an electron released from
rest at the upper-plate level.  That necessary scenario completion is exposed
as the separate premise `ReleasedFromRestAtUpperPlate`, rather than hidden in
a definition or governing-law structure.

Assumption/target split:

* governing laws: `|V| = |E| d` for the ideal parallel plates, spatially and
  temporally uniform field, `F = q E`, `F = m a`, and constant-acceleration
  position/velocity updates;
* previous-part results: none;
* figure readouts: `100 V`, `1.0 cm`, plate signs and battery connections,
  upward field arrows, downward `F = -e E`, the electron glyph, and the `x`,
  `y`, and `O` labels;
* source-prose and calibrated data: `1.00 * 10^4 N/C`, the corresponding
  physical `100 V` and `1.0 cm` readouts, and `1.0 cm = 10^-2 m`;
* current target conclusions: the positive travel time equals the derived
  square-root prediction, agrees with `3.4 * 10^-9 s` at its displayed
  precision, and makes answer B uniquely closest.

No premise contains the square-root travel-time formula, its numerical value,
or a selected answer choice.
-/

/-! ## Dimensionful physical quantities and coherent-unit readouts -/

/-- Cartesian component vectors in the plane of the supplied figure. -/
abbrev PlanarVector : Type := EuclideanSpace ℝ (Fin 2)

/-- The physical dimension `L T⁻¹` of velocity. -/
def velocityDimension : Dimension := L𝓭 * T𝓭⁻¹

/-- The physical dimension `L T⁻²` of acceleration. -/
def accelerationDimension : Dimension := L𝓭 * T𝓭⁻¹ * T𝓭⁻¹

/-- The physical dimension `M L T⁻²` of force. -/
def forceDimension : Dimension := M𝓭 * L𝓭 * T𝓭⁻¹ * T𝓭⁻¹

/-- The physical dimension `M L² T⁻² C⁻¹` of electric potential. -/
def electricPotentialDimension : Dimension :=
  M𝓭 * L𝓭 * L𝓭 * T𝓭⁻¹ * T𝓭⁻¹ * C𝓭⁻¹

/-- The physical dimension `M L T⁻² C⁻¹` of electric-field strength. -/
def electricFieldDimension : Dimension :=
  M𝓭 * L𝓭 * T𝓭⁻¹ * T𝓭⁻¹ * C𝓭⁻¹

/-- A nonnegative, unit-independent physical length. -/
abbrev LengthQuantity : Type :=
  Dimensionful (WithDim L𝓭 NNReal)

/-- A nonnegative, unit-independent elapsed time. -/
abbrev DurationQuantity : Type :=
  Dimensionful (WithDim T𝓭 NNReal)

/-- A nonnegative, unit-independent particle mass. -/
abbrev MassQuantity : Type :=
  Dimensionful (WithDim M𝓭 NNReal)

/-- A signed, unit-independent electric charge. -/
abbrev SignedChargeQuantity : Type :=
  Dimensionful (WithDim C𝓭 ℝ)

/-- A nonnegative, unit-independent electric-potential magnitude. -/
abbrev ElectricPotentialMagnitudeQuantity : Type :=
  Dimensionful (WithDim electricPotentialDimension NNReal)

/-- A nonnegative, unit-independent electric-field magnitude. -/
abbrev ElectricFieldMagnitudeQuantity : Type :=
  Dimensionful (WithDim electricFieldDimension NNReal)

/-- A unit-independent position vector in the diagram plane. -/
abbrev PlanarPositionQuantity : Type :=
  Dimensionful (WithDim L𝓭 PlanarVector)

/-- A unit-independent velocity vector in the diagram plane. -/
abbrev PlanarVelocityQuantity : Type :=
  Dimensionful (WithDim velocityDimension PlanarVector)

/-- A unit-independent acceleration vector in the diagram plane. -/
abbrev PlanarAccelerationQuantity : Type :=
  Dimensionful (WithDim accelerationDimension PlanarVector)

/-- A unit-independent force vector in the diagram plane. -/
abbrev PlanarForceQuantity : Type :=
  Dimensionful (WithDim forceDimension PlanarVector)

/-- A unit-independent electric-field vector in the diagram plane. -/
abbrev PlanarElectricFieldQuantity : Type :=
  Dimensionful (WithDim electricFieldDimension PlanarVector)

/-- Coordinate `0`, positive toward the right in the image. -/
def xAxis : Fin 2 := 0

/-- Coordinate `1`, positive downward in the image. -/
def yAxis : Fin 2 := 1

/-- Coherent units whose time readout is in nanoseconds. -/
def nanosecondUnitChoices : UnitChoices :=
  { UnitChoices.SI with time := TimeUnit.nanoseconds }

/-- Coherent-SI readout of length in metres. -/
def lengthInMeters (length : LengthQuantity) : ℝ :=
  ((length UnitChoices.SI).val : ℝ)

/-- Readout of length in the centimetres printed in the raster. -/
def lengthInCentimeters (length : LengthQuantity) : ℝ :=
  ((length {UnitChoices.SI with length := LengthUnit.centimeters}).val : ℝ)

/-- Coherent-SI readout of duration in seconds. -/
def durationInSeconds (duration : DurationQuantity) : ℝ :=
  ((duration UnitChoices.SI).val : ℝ)

/-- Readout of duration in nanoseconds. -/
def durationInNanoseconds (duration : DurationQuantity) : ℝ :=
  ((duration nanosecondUnitChoices).val : ℝ)

/-- Coherent-SI readout of mass in kilograms. -/
def massInKilograms (mass : MassQuantity) : ℝ :=
  ((mass UnitChoices.SI).val : ℝ)

/-- Coherent-SI readout of signed charge in coulombs. -/
def chargeInCoulombs (charge : SignedChargeQuantity) : ℝ :=
  (charge UnitChoices.SI).val

/-- Charge readout in Physlib's exact elementary-charge unit. -/
def chargeInElementaryCharges (charge : SignedChargeQuantity) : ℝ :=
  (charge {UnitChoices.SI with charge := ChargeUnit.elementaryCharge}).val

/-- Readout of an electric-potential magnitude in volts. -/
def potentialMagnitudeInVolts
    (potential : ElectricPotentialMagnitudeQuantity) : ℝ :=
  ((potential UnitChoices.SI).val : ℝ)

/-- Readout of an electric-field magnitude in newtons per coulomb. -/
def fieldMagnitudeInNewtonsPerCoulomb
    (field : ElectricFieldMagnitudeQuantity) : ℝ :=
  ((field UnitChoices.SI).val : ℝ)

/-- Readout of a position vector in metres. -/
def positionVectorInMeters (position : PlanarPositionQuantity) : PlanarVector :=
  (position UnitChoices.SI).val

/-- Readout of a velocity vector in metres per second. -/
def velocityVectorInMetersPerSecond
    (velocity : PlanarVelocityQuantity) : PlanarVector :=
  (velocity UnitChoices.SI).val

/-- Readout of an acceleration vector in metres per second squared. -/
def accelerationVectorInMetersPerSecondSquared
    (acceleration : PlanarAccelerationQuantity) : PlanarVector :=
  (acceleration UnitChoices.SI).val

/-- Readout of a force vector in newtons. -/
def forceVectorInNewtons (force : PlanarForceQuantity) : PlanarVector :=
  (force UnitChoices.SI).val

/-- Readout of an electric-field vector in newtons per coulomb. -/
def electricFieldVectorInNewtonsPerCoulomb
    (field : PlanarElectricFieldQuantity) : PlanarVector :=
  (field UnitChoices.SI).val

/-! ## Primary-figure vocabulary and physical setup -/

/-- The two parallel conducting plates in image `993.png`. -/
inductive Plate where
  | upper
  | lower
  deriving DecidableEq, Fintype, Repr

/-- Charge signs printed on plates and on the blue particle. -/
inductive ChargeSign where
  | positive
  | negative
  deriving DecidableEq, Repr

/-- The two terminals of the depicted battery. -/
inductive BatteryTerminal where
  | positive
  | negative
  deriving DecidableEq, Repr

/-- Qualitative directions relevant to the raster. -/
inductive FigureDirection where
  | rightward
  | upward
  | downward
  deriving DecidableEq, Repr

/-- The two coordinate axes printed through `O`. -/
inductive CoordinateAxis where
  | x
  | y
  deriving DecidableEq, Fintype, Repr

/-- The particle species implied by the minus glyph and `-e` force label. -/
inductive ParticleSpecies where
  | electron
  deriving DecidableEq, Repr

/-- The idealized field model described in the problem prose. -/
inductive ElectricFieldModel where
  | nearlyUniformBetweenParallelPlates
  deriving DecidableEq, Repr

/-!
Literal presentation information transcribed from the primary raster.  The
real fields are unit-labelled printed readouts, not definitions of the
independent physical quantities below.
-/
structure ParallelPlateFigure where
  platesDrawnParallel : Bool
  plateSign : Plate → ChargeSign
  connectedBatteryTerminal : Plate → BatteryTerminal
  printedBatteryVoltageVolts : ℝ
  printedPlateSeparationCentimeters : ℝ
  thinFieldArrowsShown : Bool
  fieldArrowsRepresentUniformField : Bool
  fieldArrowDirection : FigureDirection
  electronSphereShown : Bool
  particleSign : ChargeSign
  downwardForceArrowShown : Bool
  forceArrowDirection : FigureDirection
  printedForceFormula : String
  axisLabel : CoordinateAxis → String
  positiveAxisDirection : CoordinateAxis → FigureDirection
  printedOriginLabel : String

/-!
Independent physical quantities and trajectory observables.  The trajectory
argument is explicitly a coherent-SI time readout in seconds.  The travel
duration is an unknown physical quantity and is not defined from the answer
table.
-/
structure ElectronPlateTraversalSetup where
  figure : ParallelPlateFigure
  particleSpecies : ParticleSpecies
  fieldModel : ElectricFieldModel
  plateSeparation : LengthQuantity
  batteryPotentialMagnitude : ElectricPotentialMagnitudeQuantity
  electronMass : MassQuantity
  electronCharge : SignedChargeQuantity
  electricFieldMagnitude : ElectricFieldMagnitudeQuantity
  uniformElectricFieldVector : PlanarElectricFieldQuantity
  physlibElectricField : Electromagnetism.ElectricField 2
  electronForce : PlanarForceQuantity
  electronAcceleration : PlanarAccelerationQuantity
  positionAtSeconds : ℝ → PlanarPositionQuantity
  velocityAtSeconds : ℝ → PlanarVelocityQuantity
  travelDuration : DurationQuantity
  downwardUnitDirection : PlanarVector

/-! ## Scenario, figure evidence, and physical input data -/

/-- The particle and idealized apparatus named or depicted in the source. -/
structure MatchesElectronParallelPlateScenario
    (setup : ElectronPlateTraversalSetup) : Prop where
  particleIsElectron : setup.particleSpecies = .electron
  fieldModelIsNearlyUniform :
    setup.fieldModel = .nearlyUniformBetweenParallelPlates

/-!
Direct transcription of image `993.png`.  Its two numerical labels are kept
as presentation data here; their calibration to independent dimensionful
quantities is stated separately below.  This premise contains no field-value
claim from the prose, travel-time value, or answer label.
-/
structure MatchesSuppliedParallelPlateFigure
    (setup : ElectronPlateTraversalSetup) : Prop where
  platesAreParallel : setup.figure.platesDrawnParallel = true
  upperPlateIsNegative : setup.figure.plateSign .upper = .negative
  lowerPlateIsPositive : setup.figure.plateSign .lower = .positive
  upperPlateConnectedToNegativeTerminal :
    setup.figure.connectedBatteryTerminal .upper = .negative
  lowerPlateConnectedToPositiveTerminal :
    setup.figure.connectedBatteryTerminal .lower = .positive
  batteryLabelIsOneHundredVolts :
    setup.figure.printedBatteryVoltageVolts = 100
  gapLabelIsOneCentimeter :
    setup.figure.printedPlateSeparationCentimeters = 1
  thinFieldArrowsAreShown : setup.figure.thinFieldArrowsShown = true
  arrowsAreLabelledUniform :
    setup.figure.fieldArrowsRepresentUniformField = true
  fieldArrowsPointUp : setup.figure.fieldArrowDirection = .upward
  electronSphereIsShown : setup.figure.electronSphereShown = true
  electronCarriesMinusGlyph : setup.figure.particleSign = .negative
  forceArrowIsShown : setup.figure.downwardForceArrowShown = true
  forceArrowPointsDown : setup.figure.forceArrowDirection = .downward
  forceFormulaIsPrinted : setup.figure.printedForceFormula = "F = -eE"
  xAxisLabel : setup.figure.axisLabel .x = "x"
  yAxisLabel : setup.figure.axisLabel .y = "y"
  xPositiveToRight :
    setup.figure.positiveAxisDirection .x = .rightward
  yPositiveDown : setup.figure.positiveAxisDirection .y = .downward
  originLabel : setup.figure.printedOriginLabel = "O"

/-!
Numerical physical data supplied by the problem statement.  In particular,
`1.00 * 10^4 N/C` is prose data rather than a label in the raster.  The metre
readout records the exact SI calibration of the displayed `1.0 cm`; none of
these fields constrain the requested travel duration.
-/
structure UsesStatedProblemData
    (setup : ElectronPlateTraversalSetup) : Prop where
  batteryPotentialIsOneHundredVolts :
    potentialMagnitudeInVolts setup.batteryPotentialMagnitude = 100
  plateSeparationIsOneCentimeter :
    lengthInCentimeters setup.plateSeparation = 1
  plateSeparationIsOneHundredthMeter :
    lengthInMeters setup.plateSeparation = 1e-2
  fieldMagnitudeIsOneTimesTenToTheFour :
    fieldMagnitudeInNewtonsPerCoulomb setup.electricFieldMagnitude =
      1 * (10 : ℝ) ^ 4

/-!
Standard reference data implicit in calling the depicted particle an
electron.  `ChargeUnit.elementaryCharge` is Physlib's exact SI-defined
elementary-charge unit.
-/
structure UsesStandardElectronReferenceData
    (setup : ElectronPlateTraversalSetup) : Prop where
  electronMassKilograms :
    massInKilograms setup.electronMass = 9.1093837015e-31
  electronChargeInElementaryCharges :
    chargeInElementaryCharges setup.electronCharge = -1
  electronSignedChargeCoulombs :
    chargeInCoulombs setup.electronCharge = -(1.602176634e-19)

/-! Positivity, charge sign, and the diagram's downward unit direction. -/
structure HasPhysicalElectronTraversalParameters
    (setup : ElectronPlateTraversalSetup) : Prop where
  positiveMass : 0 < massInKilograms setup.electronMass
  negativeCharge : chargeInCoulombs setup.electronCharge < 0
  positivePlateSeparation : 0 < lengthInMeters setup.plateSeparation
  positiveFieldMagnitude :
    0 < fieldMagnitudeInNewtonsPerCoulomb setup.electricFieldMagnitude
  downwardDirectionIsUnit : ‖setup.downwardUnitDirection‖ = 1
  downwardDirectionHasNoXComponent : setup.downwardUnitDirection xAxis = 0
  downwardDirectionHasPositiveYComponent :
    setup.downwardUnitDirection yAxis = 1

/-!
The source omits an initial velocity, although the recorded answer requires
one.  This premise makes the inferred textbook condition explicit: at time
zero the electron is at the upper-plate level and is released from rest.
-/
structure ReleasedFromRestAtUpperPlate
    (setup : ElectronPlateTraversalSetup) : Prop where
  initialVelocityIsZero :
    velocityVectorInMetersPerSecond (setup.velocityAtSeconds 0) = 0
  initialVerticalCoordinateIsZero :
    positionVectorInMeters (setup.positionAtSeconds 0) yAxis = 0

/-! ## Governing electrostatics, dynamics, and kinematics -/

/-!
For the ideal parallel-plate model the magnitudes obey `|V| = |E| d`.  This
is a general apparatus law; it does not constrain the travel duration.
-/
structure SatisfiesParallelPlateVoltageFieldLaw
    (setup : ElectronPlateTraversalSetup) : Prop where
  voltageEqualsFieldTimesSeparation :
    potentialMagnitudeInVolts setup.batteryPotentialMagnitude =
      fieldMagnitudeInNewtonsPerCoulomb setup.electricFieldMagnitude *
        lengthInMeters setup.plateSeparation

/-!
The Physlib field is constant throughout spacetime and its component values
are explicitly calibrated here to the dimensionful vector's coherent-SI
`N/C` readout.  The vector points upward (opposite the image's positive-`y`
direction), and the independent magnitude is its Euclidean norm.
-/
structure SatisfiesStaticUniformUpwardElectricField
    (setup : ElectronPlateTraversalSetup) : Prop where
  physlibFieldIsUniform : ∀ time position,
    setup.physlibElectricField time position =
      electricFieldVectorInNewtonsPerCoulomb
        setup.uniformElectricFieldVector
  fieldPointsUpward :
    electricFieldVectorInNewtonsPerCoulomb
        setup.uniformElectricFieldVector =
      (-fieldMagnitudeInNewtonsPerCoulomb setup.electricFieldMagnitude) •
        setup.downwardUnitDirection
  magnitudeAgreesWithVectorNorm :
    fieldMagnitudeInNewtonsPerCoulomb setup.electricFieldMagnitude =
      ‖electricFieldVectorInNewtonsPerCoulomb
        setup.uniformElectricFieldVector‖

/-!
The coherent-SI vector equations `F = q E` and `F = m a`.  Since `q < 0`
and `E` points upward, these laws derive rather than assume a downward force.
-/
structure SatisfiesElectronForceAndNewtonLaws
    (setup : ElectronPlateTraversalSetup) : Prop where
  electricForceLaw :
    forceVectorInNewtons setup.electronForce =
      chargeInCoulombs setup.electronCharge •
        electricFieldVectorInNewtonsPerCoulomb
          setup.uniformElectricFieldVector
  newtonSecondLaw :
    forceVectorInNewtons setup.electronForce =
      massInKilograms setup.electronMass •
        accelerationVectorInMetersPerSecondSquared
          setup.electronAcceleration

/-!
Constant-acceleration position and velocity updates, stated for every
nonnegative coherent-SI time.  They contain no plate distance or requested
travel time.
-/
structure SatisfiesConstantAccelerationKinematics
    (setup : ElectronPlateTraversalSetup) : Prop where
  positionUpdate : ∀ seconds : ℝ, 0 ≤ seconds →
    positionVectorInMeters (setup.positionAtSeconds seconds) -
        positionVectorInMeters (setup.positionAtSeconds 0) =
      seconds •
          velocityVectorInMetersPerSecond (setup.velocityAtSeconds 0) +
        (seconds ^ 2 / 2) •
          accelerationVectorInMetersPerSecondSquared
            setup.electronAcceleration
  velocityUpdate : ∀ seconds : ℝ, 0 ≤ seconds →
    velocityVectorInMetersPerSecond (setup.velocityAtSeconds seconds) =
      velocityVectorInMetersPerSecond (setup.velocityAtSeconds 0) +
        seconds •
          accelerationVectorInMetersPerSecondSquared
            setup.electronAcceleration

/-!
Semantic endpoint condition for “travel this distance”: at the independent
travel duration, the displacement is one plate separation downward.  It does
not supply a duration value.
-/
structure CompletesOnePlateGapTraversal
    (setup : ElectronPlateTraversalSetup) : Prop where
  endpointDisplacement :
    positionVectorInMeters
          (setup.positionAtSeconds (durationInSeconds setup.travelDuration)) -
        positionVectorInMeters (setup.positionAtSeconds 0) =
      lengthInMeters setup.plateSeparation • setup.downwardUnitDirection

/-! ## Derived travel time and displayed-answer semantics -/

/-!
The positive square-root prediction obtained by combining the plate distance,
electron reference data, electric force, Newton's law, and rest-to-distance
kinematics.  This definition depends only on physical inputs, not on an
answer choice.
-/
def predictedTravelTimeSeconds (setup : ElectronPlateTraversalSetup) : ℝ :=
  Real.sqrt
    (2 * massInKilograms setup.electronMass *
        lengthInMeters setup.plateSeparation /
      (|chargeInCoulombs setup.electronCharge| *
        fieldMagnitudeInNewtonsPerCoulomb setup.electricFieldMagnitude))

/-- Labels of the four displayed travel-time choices. -/
inductive AnswerChoice where
  | A
  | B
  | C
  | D
  deriving DecidableEq, Fintype, Repr

/-- Travel time in seconds printed beside each answer label. -/
def AnswerChoice.displayedTravelTimeSeconds : AnswerChoice → ℝ
  | .A => 3.4e-7
  | .B => 3.4e-9
  | .C => 1.7e-9
  | .D => 5.9e-9

/-- Half of one unit in the last printed decimal place. -/
def AnswerChoice.halfUnitInLastPlaceSeconds : AnswerChoice → ℝ
  | .A => 5e-9
  | .B => 5e-11
  | .C => 5e-11
  | .D => 5e-11

/-- Dataset answer label, kept on the conclusion side of the formalization. -/
def recordedDatasetAnswer : AnswerChoice := .B

/-- Agreement with a displayed answer at that answer's printed precision. -/
def MatchesDisplayedPrecision
    (actualSeconds : ℝ) (choice : AnswerChoice) : Prop :=
  |actualSeconds - choice.displayedTravelTimeSeconds| ≤
    choice.halfUnitInLastPlaceSeconds

/-- A choice is strictly closer to the physical duration than every rival. -/
def IsUniqueClosestTravelTimeChoice
    (actualSeconds : ℝ) (choice : AnswerChoice) : Prop :=
  ∀ alternative : AnswerChoice, alternative ≠ choice →
    |actualSeconds - choice.displayedTravelTimeSeconds| <
      |actualSeconds - alternative.displayedTravelTimeSeconds|

/-!
The governing laws and endpoint condition determine the positive duration by
the usual `sqrt (2 m d / (|q| E))` relation.  The formula is a derived
conclusion, not a law or setup field.
-/
lemma travel_time_eq_square_root_prediction
    (setup : ElectronPlateTraversalSetup)
    (_physical : HasPhysicalElectronTraversalParameters setup)
    (_released : ReleasedFromRestAtUpperPlate setup)
    (_uniformField : SatisfiesStaticUniformUpwardElectricField setup)
    (_dynamics : SatisfiesElectronForceAndNewtonLaws setup)
    (_kinematics : SatisfiesConstantAccelerationKinematics setup)
    (_traversal : CompletesOnePlateGapTraversal setup) :
    durationInSeconds setup.travelDuration =
      predictedTravelTimeSeconds setup := by
  let t := durationInSeconds setup.travelDuration
  let m := massInKilograms setup.electronMass
  let d := lengthInMeters setup.plateSeparation
  let q := chargeInCoulombs setup.electronCharge
  let E :=
    fieldMagnitudeInNewtonsPerCoulomb setup.electricFieldMagnitude
  let a :=
    accelerationVectorInMetersPerSecondSquared
      setup.electronAcceleration yAxis
  have ht : 0 ≤ t := by
    exact NNReal.coe_nonneg _
  have hm : 0 < m := by
    exact _physical.positiveMass
  have hd : 0 < d := by
    exact _physical.positivePlateSeparation
  have hq : q < 0 := by
    exact _physical.negativeCharge
  have hE : 0 < E := by
    exact _physical.positiveFieldMagnitude
  have hfieldY :
      electricFieldVectorInNewtonsPerCoulomb
          setup.uniformElectricFieldVector yAxis = -E := by
    rw [_uniformField.fieldPointsUpward]
    simp [E, _physical.downwardDirectionHasPositiveYComponent]
  have hforceY :
      forceVectorInNewtons setup.electronForce yAxis = q * (-E) := by
    have h :=
      congrArg (fun vector : PlanarVector => vector yAxis)
        _dynamics.electricForceLaw
    simpa [q, hfieldY] using h
  have hnewtonY :
      forceVectorInNewtons setup.electronForce yAxis = m * a := by
    have h :=
      congrArg (fun vector : PlanarVector => vector yAxis)
        _dynamics.newtonSecondLaw
    simpa [m, a] using h
  have hacc : m * a = |q| * E := by
    calc
      m * a = forceVectorInNewtons setup.electronForce yAxis :=
        hnewtonY.symm
      _ = q * (-E) := hforceY
      _ = |q| * E := by rw [abs_of_neg hq]; ring
  have hendY :
      (positionVectorInMeters
              (setup.positionAtSeconds t) -
            positionVectorInMeters (setup.positionAtSeconds 0)) yAxis =
        d := by
    have h :=
      congrArg (fun vector : PlanarVector => vector yAxis)
        _traversal.endpointDisplacement
    simpa [t, d, _physical.downwardDirectionHasPositiveYComponent] using h
  have hkinY :
      (positionVectorInMeters
              (setup.positionAtSeconds t) -
            positionVectorInMeters (setup.positionAtSeconds 0)) yAxis =
        t ^ 2 / 2 * a := by
    have h :=
      congrArg (fun vector : PlanarVector => vector yAxis)
        (_kinematics.positionUpdate t ht)
    simpa [a, _released.initialVelocityIsZero] using h
  have hdistance : d = t ^ 2 / 2 * a := by
    rw [← hendY]
    exact hkinY
  have hcross : (|q| * E) * t ^ 2 = 2 * m * d := by
    calc
      (|q| * E) * t ^ 2 = (m * a) * t ^ 2 := by rw [hacc]
      _ = 2 * m * (t ^ 2 / 2 * a) := by ring
      _ = 2 * m * d := by rw [← hdistance]
  have hden : 0 < |q| * E := by
    exact mul_pos (abs_pos.mpr (ne_of_lt hq)) hE
  have hsq : t ^ 2 = 2 * m * d / (|q| * E) := by
    apply (eq_div_iff (ne_of_gt hden)).2
    nlinarith [hcross]
  change t = Real.sqrt (2 * m * d / (|q| * E))
  calc
    t = |t| := (abs_of_nonneg ht).symm
    _ = Real.sqrt (t ^ 2) := (Real.sqrt_sq_eq_abs t).symm
    _ = Real.sqrt (2 * m * d / (|q| * E)) := by rw [hsq]

/-!
**Blueprint target:** `thm:physics:phyx_mini_0993:target`.

For a standard electron released from rest, the `1.0 cm`, `100 V`, and
`1.00 * 10^4 N/C` plate data give approximately `3.37 ns`.  This rounds to
`3.4 * 10^-9 s`, the value displayed by answer B, and is strictly closer to B
than to A, C, or D.
-/
theorem problem_phyx_mini_0993
    (setup : ElectronPlateTraversalSetup)
    (_scenario : MatchesElectronParallelPlateScenario setup)
    (_figure : MatchesSuppliedParallelPlateFigure setup)
    (_data : UsesStatedProblemData setup)
    (_reference : UsesStandardElectronReferenceData setup)
    (_physical : HasPhysicalElectronTraversalParameters setup)
    (_released : ReleasedFromRestAtUpperPlate setup)
    (_plateLaw : SatisfiesParallelPlateVoltageFieldLaw setup)
    (_uniformField : SatisfiesStaticUniformUpwardElectricField setup)
    (_dynamics : SatisfiesElectronForceAndNewtonLaws setup)
    (_kinematics : SatisfiesConstantAccelerationKinematics setup)
    (_traversal : CompletesOnePlateGapTraversal setup) :
    durationInSeconds setup.travelDuration =
        predictedTravelTimeSeconds setup ∧
      MatchesDisplayedPrecision
        (durationInSeconds setup.travelDuration) recordedDatasetAnswer ∧
      IsUniqueClosestTravelTimeChoice
        (durationInSeconds setup.travelDuration) recordedDatasetAnswer := by
  have htime :=
    travel_time_eq_square_root_prediction setup _physical _released
      _uniformField _dynamics _kinematics _traversal
  let r : ℝ :=
    2 * 9.1093837015e-31 * 1e-2 /
      (1.602176634e-19 * (1 * (10 : ℝ) ^ 4))
  let s : ℝ := Real.sqrt r
  have hr : 0 ≤ r := by
    dsimp [r]
    norm_num
  have hs_nonneg : 0 ≤ s := by
    exact Real.sqrt_nonneg r
  have hs_sq : s ^ 2 = r := by
    exact Real.sq_sqrt hr
  have hr_lower : (3.35e-9 : ℝ) ^ 2 < r := by
    dsimp [r]
    norm_num
  have hr_upper : r < (3.45e-9 : ℝ) ^ 2 := by
    dsimp [r]
    norm_num
  have hs_lower : (3.35e-9 : ℝ) < s := by
    apply (sq_lt_sq₀ (by norm_num) hs_nonneg).mp
    rw [hs_sq]
    exact hr_lower
  have hs_upper : s < (3.45e-9 : ℝ) := by
    apply (sq_lt_sq₀ hs_nonneg (by norm_num)).mp
    rw [hs_sq]
    exact hr_upper
  have hprediction : predictedTravelTimeSeconds setup = s := by
    unfold predictedTravelTimeSeconds
    rw [_reference.electronMassKilograms,
      _data.plateSeparationIsOneHundredthMeter,
      _reference.electronSignedChargeCoulombs,
      _data.fieldMagnitudeIsOneTimesTenToTheFour]
    congr 1
    dsimp [r, s]
    norm_num
  have htime_numeric :
      durationInSeconds setup.travelDuration = s := by
    rw [htime, hprediction]
  have hprecision : |s - 3.4e-9| ≤ (5e-11 : ℝ) := by
    rw [abs_le]
    constructor <;> nlinarith
  refine ⟨htime, ?_, ?_⟩
  · rw [htime_numeric]
    simpa [MatchesDisplayedPrecision, recordedDatasetAnswer,
      AnswerChoice.displayedTravelTimeSeconds,
      AnswerChoice.halfUnitInLastPlaceSeconds] using hprecision
  · rw [htime_numeric]
    intro alternative hne
    cases alternative with
    | A =>
        change |s - 3.4e-9| < |s - 3.4e-7|
        rw [abs_of_neg (by nlinarith : s - 3.4e-7 < 0)]
        nlinarith
    | B =>
        exact (hne rfl).elim
    | C =>
        change |s - 3.4e-9| < |s - 1.7e-9|
        rw [abs_of_pos (by nlinarith : 0 < s - 1.7e-9)]
        nlinarith
    | D =>
        change |s - 3.4e-9| < |s - 5.9e-9|
        rw [abs_of_neg (by nlinarith : s - 5.9e-9 < 0)]
        nlinarith

end PhyXMiniProblems.ProblemPhyXMini0993
