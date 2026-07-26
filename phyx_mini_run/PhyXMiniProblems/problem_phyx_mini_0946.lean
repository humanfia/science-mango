import Mathlib
import Physlib.Electromagnetism.Basic
import Physlib.Units.WithDim.Basic

/- USER: The assigned Lean file did not exist when this autoformalization task began. -/

noncomputable section

namespace PhyXMiniProblems.ProblemPhyXMini0946

open Dimension

/-!
# Extra weight supported by a current-carrying bar

The apparatus has a straight conducting bar bridging two vertical rails.  The
primary raster labels the active bar length by `L`, its diameter by `d`, the
rightward current by `I`, the into-page magnetic field by `B`, and the
battery emf by `ℰ`.  Thus the current and field are perpendicular and the
right-hand rule gives an upward magnetic force.

The prose also records the near-ground earth field (`0.50 G`, inclined
downward by about `45°`) before replacing it by a horizontal `1.0 T`
permanent-magnet field.  The requested setup uses a `10 cm` active bar length
and a `10 A` current.  These supplied data fix the magnetic lift at `1.0 N`.
The phrase “extra weight” requires subtracting the bar's own weight, but the
source supplies neither that weight nor the material and geometric data needed
to calculate it.  Consequently the source supports the relation
`extra weight = 1.0 N - bar weight`, not the recorded numerical answer `0.83 N`.

Physical magnitudes are unit-independent Physlib `Dimensionful` quantities.
Real numbers occur only as named coherent-SI or named conventional-unit
readouts, angles in degrees, and displayed answer-choice values.

Assumption/target split:

* governing laws: uniform-field calibration, the perpendicular straight-wire
  magnetic-force law `F = B I L`, its right-hand-rule direction, and threshold
  vertical force balance;
* previous-device results: none are linked by the source report;
* prose/figure readouts: earth-field data, the `1.0 T` magnet field, `10 cm`
  active length, `10 A` current, rails/bar/battery, labels `L,d,I,B,ℰ`,
  current to the right, and field crosses into the page;
* current target: the lift is `1.0 N` and the extra levitatable weight is
  `1.0 N` minus the unspecified bar self-weight.

The setup stores the extra weight as an independent physical observable.
Neither a setup field nor any premise states its requested numerical value or
the missing bar self-weight calibration.  Answer B is retained only as dataset
metadata below.
-/

/-! ## Physical dimensions and unit-independent magnitudes -/

/-- Magnetic flux density (tesla) has dimension `M T⁻¹ C⁻¹`. -/
def magneticFluxDensityDimension : Dimension :=
  M𝓭 * T𝓭⁻¹ * C𝓭⁻¹

/-- Electric current (ampere) has dimension `C T⁻¹`. -/
def electricCurrentDimension : Dimension :=
  C𝓭 * T𝓭⁻¹

/-- Electromotive force (volt) has dimension `M L² T⁻² C⁻¹`. -/
def electromotiveForceDimension : Dimension :=
  M𝓭 * L𝓭 * L𝓭 * T𝓭⁻¹ * T𝓭⁻¹ * C𝓭⁻¹

/-- Force and weight (newton) have dimension `M L T⁻²`. -/
def forceDimension : Dimension :=
  M𝓭 * L𝓭 * T𝓭⁻¹ * T𝓭⁻¹

/-- A nonnegative, unit-independent magnetic-flux-density magnitude. -/
abbrev MagneticFluxDensityMagnitude : Type :=
  Dimensionful (WithDim magneticFluxDensityDimension NNReal)

/-- A nonnegative, unit-independent physical length. -/
abbrev LengthMagnitude : Type :=
  Dimensionful (WithDim L𝓭 NNReal)

/-- A nonnegative, unit-independent electric-current magnitude. -/
abbrev ElectricCurrentMagnitude : Type :=
  Dimensionful (WithDim electricCurrentDimension NNReal)

/-- A nonnegative, unit-independent battery-emf magnitude. -/
abbrev ElectromotiveForceMagnitude : Type :=
  Dimensionful (WithDim electromotiveForceDimension NNReal)

/-- A nonnegative, unit-independent force or weight magnitude. -/
abbrev ForceMagnitude : Type :=
  Dimensionful (WithDim forceDimension NNReal)

/-! ## Named unit readouts -/

/-- Read a nonnegative dimensionful quantity in coherent SI units. -/
def nonnegativeSIReadout {d : Dimension}
    (quantity : Dimensionful (WithDim d NNReal)) : ℝ :=
  ((quantity UnitChoices.SI).val : ℝ)

/-- Read magnetic flux density in teslas. -/
def magneticFluxDensityInTeslas
    (field : MagneticFluxDensityMagnitude) : ℝ :=
  nonnegativeSIReadout field

/--
Read magnetic flux density in gauss.  This definition records
`1 G = 10⁻⁴ T`, equivalently one tesla is `10⁴ G`.
-/
def magneticFluxDensityInGauss
    (field : MagneticFluxDensityMagnitude) : ℝ :=
  10000 * magneticFluxDensityInTeslas field

/-- Read length in metres. -/
def lengthInMeters (length : LengthMagnitude) : ℝ :=
  nonnegativeSIReadout length

/-- Read length in centimetres. -/
def lengthInCentimeters (length : LengthMagnitude) : ℝ :=
  100 * lengthInMeters length

/-- Read current in amperes. -/
def currentInAmperes (current : ElectricCurrentMagnitude) : ℝ :=
  nonnegativeSIReadout current

/-- Read battery emf in volts. -/
def emfInVolts (emf : ElectromotiveForceMagnitude) : ℝ :=
  nonnegativeSIReadout emf

/-- Read a force or weight in newtons. -/
def forceInNewtons (force : ForceMagnitude) : ℝ :=
  nonnegativeSIReadout force

/-! ## Spatial roles and primary-raster vocabulary -/

/-- Page-relative directions needed for the current, field, lift, and weight. -/
inductive SpatialDirection where
  | rightward
  | leftward
  | upward
  | downward
  | intoPage
  | outOfPage
  deriving DecidableEq, Repr

/-- Orientations of the bar, rails, and applied field relative to gravity. -/
inductive PhysicalOrientation where
  | horizontal
  | vertical
  deriving DecidableEq, Repr

/-- The downward inclination convention used for the earth's field. -/
inductive FieldInclinationSense where
  | downwardFromHorizontal
  | upwardFromHorizontal
  deriving DecidableEq, Repr

/-- The field marker convention printed throughout the magnet gap. -/
inductive FieldMarkerKind where
  | cross
  | dot
  deriving DecidableEq, Repr

/-- Physical components visible in image `946.png`. -/
inductive FigureFeature where
  | leftRail
  | rightRail
  | conductingBar
  | connectingWires
  | battery
  | currentArrow
  | magneticFieldMarkers
  | lengthDimensionLine
  | diameterDimensionLine
  deriving DecidableEq, Fintype, Repr

/-- Quantity labels visible in the primary raster. -/
inductive FigureQuantityLabel where
  | activeBarLength
  | barDiameter
  | current
  | magneticField
  | batteryEmf
  deriving DecidableEq, Fintype, Repr

/-- The literal symbol printed for each figure quantity. -/
def expectedPrintedSymbol : FigureQuantityLabel → String
  | .activeBarLength => "L"
  | .barDiameter => "d"
  | .current => "I"
  | .magneticField => "B"
  | .batteryEmf => "ℰ"

/--
Literal presentation data from the primary raster.  In particular, the raster
shows that `L` spans the rails and `d` spans the bar thickness; it supplies
no numerical value for the diameter or battery emf.
-/
structure LevitationDeviceFigure where
  shows : FigureFeature → Bool
  quantityLabelShown : FigureQuantityLabel → Bool
  printedSymbol : FigureQuantityLabel → String
  railsAreParallel : Bool
  barBridgesRails : Bool
  circuitIsClosed : Bool
  railOrientationOnPage : PhysicalOrientation
  barOrientationOnPage : PhysicalOrientation
  lengthDimensionSpansRails : Bool
  diameterDimensionSpansBarThickness : Bool
  fieldMarkerKind : FieldMarkerKind
  fieldDirection : SpatialDirection
  currentDirection : SpatialDirection

/-! ## Independent apparatus state -/

/--
The physical state of the levitation apparatus.  The vector fields use
Physlib's spacetime-dependent magnetic-field type, while their calibrated
magnitudes and all mechanical forces remain unit-independent quantities.
-/
structure CurrentCarryingBarSetup where
  earthMagneticField : Electromagnetism.MagneticField 3
  permanentMagnetField : Electromagnetism.MagneticField 3
  nearGroundRegion : Set (Time × Space 3)
  permanentMagnetGap : Set (Time × Space 3)
  earthFieldMagnitude : MagneticFluxDensityMagnitude
  earthFieldInclinationDegrees : ℝ
  earthFieldInclinationSense : FieldInclinationSense
  permanentMagnetFieldMagnitude : MagneticFluxDensityMagnitude
  permanentMagnetFieldOrientation : PhysicalOrientation
  permanentMagnetFieldDirection : SpatialDirection
  activeBarLength : LengthMagnitude
  barDiameter : LengthMagnitude
  currentMagnitude : ElectricCurrentMagnitude
  currentDirection : SpatialDirection
  batteryEmf : ElectromotiveForceMagnitude
  magneticLiftForce : ForceMagnitude
  magneticLiftForceDirection : SpatialDirection
  barSelfWeight : ForceMagnitude
  barWeightDirection : SpatialDirection
  extraLevitatableWeight : ForceMagnitude
  figure : LevitationDeviceFigure

/-! ## Prose data, figure evidence, and governing laws -/

/--
Numerical and qualitative facts stated in the problem prose.  The earth-field
data are retained even though the requested estimate uses permanent magnets.
-/
structure MatchesPermanentMagnetLevitationDescription
    (setup : CurrentCarryingBarSetup) : Prop where
  earthFieldIsHalfGauss :
    magneticFluxDensityInGauss setup.earthFieldMagnitude = 1 / 2
  earthFieldInclinationIsFortyFiveDegrees :
    setup.earthFieldInclinationDegrees = 45
  earthFieldInclinesDownward :
    setup.earthFieldInclinationSense = .downwardFromHorizontal
  permanentMagnetFieldIsOneTesla :
    magneticFluxDensityInTeslas setup.permanentMagnetFieldMagnitude = 1
  permanentMagnetFieldIsHorizontal :
    setup.permanentMagnetFieldOrientation = .horizontal
  permanentMagnetFieldPointsIntoPage :
    setup.permanentMagnetFieldDirection = .intoPage
  activeBarLengthIsTenCentimeters :
    lengthInCentimeters setup.activeBarLength = 10
  currentMagnitudeIsTenAmperes :
    currentInAmperes setup.currentMagnitude = 10
  barIsHorizontal : setup.figure.barOrientationOnPage = .horizontal
  railsAreVertical : setup.figure.railOrientationOnPage = .vertical
  weightPointsDownward : setup.barWeightDirection = .downward

/--
Primary-image evidence.  The `L` dimension spans the rail separation and the
`d` dimension spans the bar diameter, correcting the auxiliary caption's
misidentification of `d` as the rail separation.
-/
structure MatchesPrimaryLevitationDeviceFigure
    (setup : CurrentCarryingBarSetup) : Prop where
  everyNamedFeatureIsShown :
    ∀ feature, setup.figure.shows feature = true
  everyQuantityLabelIsShown :
    ∀ label, setup.figure.quantityLabelShown label = true
  printedSymbolsMatch :
    ∀ label, setup.figure.printedSymbol label = expectedPrintedSymbol label
  railsAreParallel : setup.figure.railsAreParallel = true
  barBridgesBothRails : setup.figure.barBridgesRails = true
  batteryClosesCircuit : setup.figure.circuitIsClosed = true
  lengthMarkerSpansRails :
    setup.figure.lengthDimensionSpansRails = true
  diameterMarkerSpansBar :
    setup.figure.diameterDimensionSpansBarThickness = true
  crossesEncodeIntoPageField :
    setup.figure.fieldMarkerKind = .cross ∧
      setup.figure.fieldDirection = .intoPage
  currentArrowPointsRight :
    setup.figure.currentDirection = .rightward
  figureFieldAgreesWithApparatus :
    setup.figure.fieldDirection = setup.permanentMagnetFieldDirection
  figureCurrentAgreesWithApparatus :
    setup.figure.currentDirection = setup.currentDirection

/-- Positive magnitudes and nonempty regions select a nondegenerate setup. -/
structure HasPhysicalLevitationParameters
    (setup : CurrentCarryingBarSetup) : Prop where
  earthFieldPositive :
    0 < magneticFluxDensityInTeslas setup.earthFieldMagnitude
  permanentMagnetFieldPositive :
    0 < magneticFluxDensityInTeslas setup.permanentMagnetFieldMagnitude
  activeBarLengthPositive :
    0 < lengthInMeters setup.activeBarLength
  barDiameterPositive :
    0 < lengthInMeters setup.barDiameter
  currentPositive :
    0 < currentInAmperes setup.currentMagnitude
  batteryEmfPositive :
    0 < emfInVolts setup.batteryEmf
  barWeightPositive :
    0 < forceInNewtons setup.barSelfWeight
  nearGroundRegionNonempty : setup.nearGroundRegion.Nonempty
  permanentMagnetGapNonempty : setup.permanentMagnetGap.Nonempty

/--
Calibration of the two scalar flux-density magnitudes against the norms of the
corresponding Physlib vector fields in their stated regions.
-/
structure HasCalibratedMagneticFields
    (setup : CurrentCarryingBarSetup) : Prop where
  earthFieldMagnitudeCalibration : ∀ time position,
    (time, position) ∈ setup.nearGroundRegion →
      ‖setup.earthMagneticField time position‖ =
        magneticFluxDensityInTeslas setup.earthFieldMagnitude
  permanentFieldIsUniform : ∀ time position,
    (time, position) ∈ setup.permanentMagnetGap →
      ‖setup.permanentMagnetField time position‖ =
        magneticFluxDensityInTeslas setup.permanentMagnetFieldMagnitude

/--
Magnetic force on a straight active bar segment perpendicular to a uniform
field.  With current rightward and field into the page, the right-hand rule
selects the upward force direction.
-/
structure SatisfiesStraightBarMagneticForceLaw
    (setup : CurrentCarryingBarSetup) : Prop where
  currentPointsRight : setup.currentDirection = .rightward
  perpendicularDirections :
    setup.currentDirection = .rightward ∧
      setup.permanentMagnetFieldDirection = .intoPage
  perpendicularMagneticForceMagnitude :
    forceInNewtons setup.magneticLiftForce =
      magneticFluxDensityInTeslas setup.permanentMagnetFieldMagnitude *
        currentInAmperes setup.currentMagnitude *
          lengthInMeters setup.activeBarLength
  rightHandRuleGivesUpwardLift :
    setup.magneticLiftForceDirection = .upward

/--
At the maximum supported load, upward magnetic lift balances both the bar's
own downward weight and the independent extra load.  This generic balance does
not state the requested value of the extra load.
-/
structure SatisfiesThresholdLevitationBalance
    (setup : CurrentCarryingBarSetup) : Prop where
  verticalForceBalance :
    forceInNewtons setup.magneticLiftForce =
      forceInNewtons setup.barSelfWeight +
        forceInNewtons setup.extraLevitatableWeight

/-! ## Answer-choice data and formalization target -/

/-- The four displayed multiple-choice labels. -/
inductive AnswerChoice where
  | A
  | B
  | C
  | D
  deriving DecidableEq, Fintype, Repr

/-- Displayed extra-weight value, in newtons, attached to each answer choice. -/
def answerChoiceWeightInNewtons : AnswerChoice → ℝ
  | .A => 9 / 20
  | .B => 83 / 100
  | .C => 6 / 5
  | .D => 11 / 50

/-- The answer label recorded by the dataset, retained as metadata. -/
def recordedDatasetAnswer : AnswerChoice := .B

/--
With a `1.0 T` perpendicular permanent-magnet field, `10 A` current, and
`10 cm` active bar length, the supplied data determine a `1.0 N` magnetic
lift.  At threshold, the additional supported load is therefore `1.0 N`
minus the bar's own unspecified weight.  A numerical extra-load value cannot
be selected without a bar-weight calibration absent from the source.

Blueprint label: `thm:physics:phyx_mini_0946:target`.
-/
theorem supplied_data_determine_one_newton_lift
    (setup : CurrentCarryingBarSetup)
    (_description : MatchesPermanentMagnetLevitationDescription setup)
    (_figure : MatchesPrimaryLevitationDeviceFigure setup)
    (_physical : HasPhysicalLevitationParameters setup)
    (_fieldCalibration : HasCalibratedMagneticFields setup)
    (_magneticForceLaw : SatisfiesStraightBarMagneticForceLaw setup)
    (_forceBalance : SatisfiesThresholdLevitationBalance setup) :
    forceInNewtons setup.magneticLiftForce = 1 ∧
      forceInNewtons setup.extraLevitatableWeight =
        1 - forceInNewtons setup.barSelfWeight := by
  have hcentimeters := _description.activeBarLengthIsTenCentimeters
  unfold lengthInCentimeters at hcentimeters
  have hlength :
      lengthInMeters setup.activeBarLength = (1 : ℝ) / 10 := by
    linarith
  have hlift := _magneticForceLaw.perpendicularMagneticForceMagnitude
  rw [_description.permanentMagnetFieldIsOneTesla,
    _description.currentMagnitudeIsTenAmperes, hlength] at hlift
  norm_num at hlift
  constructor
  · exact hlift
  · linarith [_forceBalance.verticalForceBalance]

end PhyXMiniProblems.ProblemPhyXMini0946
