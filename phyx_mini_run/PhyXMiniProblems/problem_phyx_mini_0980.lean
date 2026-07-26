import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Physlib.Electromagnetism.Basic
import Physlib.Units.WithDim.Basic

noncomputable section

namespace PhyXMiniProblems.ProblemPhyXMini0980

open Dimension MeasureTheory

/-!
# Magnetic field reconstructed from an induced-current graph

A four-turn circular search coil is placed between the pole faces of a large
electromagnet.  Its plane is parallel to the pole faces, so the idealized
magnetic field is perpendicular to the coil.  The field starts at zero, and a
graph gives the magnitude of the current induced in the coil while the field
is increased.  The current keeps one circulation direction throughout the
measurement.

Physical magnitudes are represented by Physlib `Dimensionful` quantities.
Real numbers occur only as coherent-SI readouts, graph coordinates in the
units printed on the axes, and displayed answer values.  Physlib's
spacetime-dependent vector magnetic field is retained and calibrated to the
dimensionful scalar flux-density magnitude at the coil.

Assumption/target split:

* governing laws: circular-coil area, uniform perpendicular magnetic flux,
  integrated Faraday induction, and Ohm's law;
* previous-part results: none;
* figure/data readouts: four turns, radius `0.800 cm`, resistance `0.250 Ω`,
  zero initial field, the fixed induced-current direction, graph axes and its
  rising/constant/falling/zero segments, and observation time `6.00 s`;
* current target conclusion: the field value implied by the graph and laws,
  `3375 / (256 * π) T`.

The target conclusion does not occur in a premise or setup definition.
Recorded answer B is retained only as source-dataset metadata and is not
treated as a physical measurement or as part of the physical target.
-/

/-! ## Dimensionful physical quantities and coherent-SI readouts -/

/-- Area has physical dimension length squared. -/
def areaDimension : Dimension :=
  L𝓭 * L𝓭

/-- Electric current has physical dimension charge per time. -/
def electricCurrentDimension : Dimension :=
  C𝓭 * T𝓭⁻¹

/-- Magnetic flux density, measured in teslas, has dimension `M T⁻¹ C⁻¹`. -/
def magneticFluxDensityDimension : Dimension :=
  M𝓭 * T𝓭⁻¹ * C𝓭⁻¹

/-- Magnetic flux has dimension magnetic flux density times area. -/
def magneticFluxDimension : Dimension :=
  magneticFluxDensityDimension * areaDimension

/-- Electromotive force has dimension magnetic flux per time. -/
def electromotiveForceDimension : Dimension :=
  magneticFluxDimension * T𝓭⁻¹

/-- Electrical resistance has dimension electromotive force divided by current. -/
def electricalResistanceDimension : Dimension :=
  electromotiveForceDimension * electricCurrentDimension⁻¹

/-- A nonnegative, unit-independent physical length. -/
abbrev LengthMagnitude : Type :=
  Dimensionful (WithDim L𝓭 NNReal)

/-- A nonnegative, unit-independent physical time. -/
abbrev TimeMagnitude : Type :=
  Dimensionful (WithDim T𝓭 NNReal)

/-- A nonnegative, unit-independent physical area. -/
abbrev AreaMagnitude : Type :=
  Dimensionful (WithDim areaDimension NNReal)

/-- A nonnegative, unit-independent electric-current magnitude. -/
abbrev ElectricCurrentMagnitude : Type :=
  Dimensionful (WithDim electricCurrentDimension NNReal)

/-- A nonnegative, unit-independent magnetic-flux-density magnitude. -/
abbrev MagneticFluxDensityMagnitude : Type :=
  Dimensionful (WithDim magneticFluxDensityDimension NNReal)

/-- A nonnegative, unit-independent magnetic flux through one coil turn. -/
abbrev MagneticFluxMagnitude : Type :=
  Dimensionful (WithDim magneticFluxDimension NNReal)

/-- A nonnegative, unit-independent induced electromotive-force magnitude. -/
abbrev ElectromotiveForceMagnitude : Type :=
  Dimensionful (WithDim electromotiveForceDimension NNReal)

/-- A nonnegative, unit-independent electrical resistance. -/
abbrev ElectricalResistanceMagnitude : Type :=
  Dimensionful (WithDim electricalResistanceDimension NNReal)

/-- Coherent-SI readout of a nonnegative dimensionful quantity. -/
def nonnegativeSIReadout {dimension : Dimension}
    (quantity : Dimensionful (WithDim dimension NNReal)) : ℝ :=
  ((quantity UnitChoices.SI).val : ℝ)

/-- Read a length in metres. -/
def lengthInMeters (length : LengthMagnitude) : ℝ :=
  nonnegativeSIReadout length

/-- Read a length in centimetres. -/
def lengthInCentimeters (length : LengthMagnitude) : ℝ :=
  100 * lengthInMeters length

/-- Read a physical time in seconds. -/
def timeInSeconds (time : TimeMagnitude) : ℝ :=
  nonnegativeSIReadout time

/-- Read an area in square metres. -/
def areaInSquareMeters (area : AreaMagnitude) : ℝ :=
  nonnegativeSIReadout area

/-- Read an electric-current magnitude in amperes. -/
def currentInAmperes (current : ElectricCurrentMagnitude) : ℝ :=
  nonnegativeSIReadout current

/-- Read an electric-current magnitude in milliamperes. -/
def currentInMilliamperes (current : ElectricCurrentMagnitude) : ℝ :=
  1000 * currentInAmperes current

/-- Read a magnetic-flux-density magnitude in teslas. -/
def magneticFluxDensityInTeslas
    (density : MagneticFluxDensityMagnitude) : ℝ :=
  nonnegativeSIReadout density

/-- Read magnetic flux through one turn in webers. -/
def magneticFluxInWebers (flux : MagneticFluxMagnitude) : ℝ :=
  nonnegativeSIReadout flux

/-- Read an induced electromotive-force magnitude in volts. -/
def electromotiveForceInVolts
    (emf : ElectromotiveForceMagnitude) : ℝ :=
  nonnegativeSIReadout emf

/-- Read electrical resistance in ohms. -/
def resistanceInOhms (resistance : ElectricalResistanceMagnitude) : ℝ :=
  nonnegativeSIReadout resistance

/-! ## Apparatus, geometry, and primary-graph vocabulary -/

/-- The two coordinate axes visible in the supplied graph. -/
inductive PlotAxis where
  | horizontal
  | vertical
  deriving DecidableEq, Fintype, Repr

/-- Physical quantity and unit printed on a graph axis. -/
inductive PlotAxisRole where
  | timeInSeconds
  | inducedCurrentInMilliamperes
  deriving DecidableEq, Repr

/-- Color of the data-point markers in the primary raster. -/
inductive MarkerColor where
  | black
  | other
  deriving DecidableEq, Repr

/-- Relative orientation of the search-coil plane and the pole faces. -/
inductive PlanePoleFaceRelation where
  | parallel
  | notParallel
  deriving DecidableEq, Repr

/-- Relative orientation of the magnetic field and the coil plane. -/
inductive FieldCoilPlaneRelation where
  | perpendicular
  | oblique
  deriving DecidableEq, Repr

/-!
The actual circulation sense is not identified by the graph, but the prose
states that it never reverses.  These constructors distinguish the two
possible oriented senses without inventing a viewing-side convention.
-/
inductive OrientedCurrentSense where
  | reference
  | reverse
  deriving DecidableEq, Repr

/-!
Literal presentation data from image `980.png`.  The plotted values are scalar
coordinates in the units named by the axes; calibration to the physical
current is imposed separately.
-/
structure InducedCurrentGraphFigure where
  axisRole : PlotAxis → PlotAxisRole
  printedAxisLabel : PlotAxis → String
  timeAxisMinimumSeconds : ℝ
  timeAxisMaximumSeconds : ℝ
  currentAxisMinimumMilliamperes : ℝ
  currentAxisMaximumMilliamperes : ℝ
  plottedCurrentMilliamperesAtSecond : ℝ → ℝ
  markerColor : MarkerColor
  dataPointsMarked : Bool
  pointsFollowPiecewiseLinearTrace : Bool
  rectangularGridShown : Bool

/-!
Independent physical observables of the electromagnet and search coil.  The
time-indexed field magnitude, flux, emf, and induced current are not defined
from a solved formula or from an answer choice.
-/
structure ElectromagnetSearchCoilSetup where
  coilTurnCount : ℕ
  coilRadius : LengthMagnitude
  coilArea : AreaMagnitude
  coilResistance : ElectricalResistanceMagnitude
  coilPlaneRelativeToPoleFaces : PlanePoleFaceRelation
  fieldRelativeToCoilPlane : FieldCoilPlaneRelation
  ambientMagneticField : Electromagnetism.MagneticField 3
  coilSurfaceRegion : Set (Space 3)
  coilLocation : Space 3
  electromagnetWindingCurrentAtSecond : ℝ → ElectricCurrentMagnitude
  magneticFluxDensityMagnitudeAtSecond :
    ℝ → MagneticFluxDensityMagnitude
  magneticFluxThroughOneTurnAtSecond : ℝ → MagneticFluxMagnitude
  inducedEmfMagnitudeAtSecond : ℝ → ElectromotiveForceMagnitude
  inducedCurrentMagnitudeAtSecond : ℝ → ElectricCurrentMagnitude
  inducedCurrentSenseAtSecond : ℝ → OrientedCurrentSense
  referenceInducedCurrentSense : OrientedCurrentSense
  observationTime : TimeMagnitude
  figure : InducedCurrentGraphFigure

/-! ## Written scenario, figure evidence, and physical calibration -/

/-!
Numerical apparatus data and qualitative facts stated in the prose.  The
field and winding-current monotonicity preserve the description that the
field grows from zero as the electromagnet is energized.  The fixed-sense
condition records the stated absence of induced-current reversal.
-/
structure MatchesWrittenElectromagnetScenario
    (setup : ElectromagnetSearchCoilSetup) : Prop where
  fourTurnCoil : setup.coilTurnCount = 4
  radiusIsEightTenthsCentimeter :
    lengthInCentimeters setup.coilRadius = 4 / 5
  resistanceIsQuarterOhm :
    resistanceInOhms setup.coilResistance = 1 / 4
  coilPlaneParallelToPoleFaces :
    setup.coilPlaneRelativeToPoleFaces = .parallel
  fieldPerpendicularToCoilPlane :
    setup.fieldRelativeToCoilPlane = .perpendicular
  initialMagneticFieldIsZero :
    magneticFluxDensityInTeslas
        (setup.magneticFluxDensityMagnitudeAtSecond 0) = 0
  windingCurrentIsNondecreasing :
    MonotoneOn
      (fun t => currentInAmperes
        (setup.electromagnetWindingCurrentAtSecond t))
      (Set.Icc 0 7)
  magneticFieldMagnitudeIsNondecreasing :
    MonotoneOn
      (fun t => magneticFluxDensityInTeslas
        (setup.magneticFluxDensityMagnitudeAtSecond t))
      (Set.Icc 0 7)
  inducedCurrentKeepsOneSense : ∀ t : ℝ,
    t ∈ Set.Icc 0 7 →
      setup.inducedCurrentSenseAtSecond t =
        setup.referenceInducedCurrentSense
  observationAtSixSeconds : timeInSeconds setup.observationTime = 6

/-!
The image has a time axis from `0` to `7 s`, a current axis from `0` to
`3.50 mA`, black point markers, and a piecewise-linear trace.  Reading the
primary raster gives a linear rise from `(0,0)` to `(2,3)`, a plateau through
`5 s`, a linear fall to zero at `6 s`, and a final zero segment through `7 s`.
-/
structure MatchesPrimaryInducedCurrentGraph
    (setup : ElectromagnetSearchCoilSetup) : Prop where
  horizontalRole : setup.figure.axisRole .horizontal = .timeInSeconds
  verticalRole :
    setup.figure.axisRole .vertical = .inducedCurrentInMilliamperes
  horizontalAxisLabel :
    setup.figure.printedAxisLabel .horizontal = "t (s)"
  verticalAxisLabel :
    setup.figure.printedAxisLabel .vertical = "i (mA)"
  timeAxisStartsAtZero : setup.figure.timeAxisMinimumSeconds = 0
  timeAxisEndsAtSeven : setup.figure.timeAxisMaximumSeconds = 7
  currentAxisStartsAtZero :
    setup.figure.currentAxisMinimumMilliamperes = 0
  currentAxisEndsAtThreePointFive :
    setup.figure.currentAxisMaximumMilliamperes = 7 / 2
  blackMarkers : setup.figure.markerColor = .black
  dataPointsAreMarked : setup.figure.dataPointsMarked = true
  piecewiseLinearTrace :
    setup.figure.pointsFollowPiecewiseLinearTrace = true
  rectangularGrid : setup.figure.rectangularGridShown = true
  physicalCurrentCalibratedToPlot : ∀ t : ℝ,
    t ∈ Set.Icc 0 7 →
      currentInMilliamperes (setup.inducedCurrentMagnitudeAtSecond t) =
        setup.figure.plottedCurrentMilliamperesAtSecond t
  risingSegment : ∀ t : ℝ, 0 ≤ t → t ≤ 2 →
    setup.figure.plottedCurrentMilliamperesAtSecond t = 3 / 2 * t
  constantSegment : ∀ t : ℝ, 2 ≤ t → t ≤ 5 →
    setup.figure.plottedCurrentMilliamperesAtSecond t = 3
  fallingSegment : ∀ t : ℝ, 5 ≤ t → t ≤ 6 →
    setup.figure.plottedCurrentMilliamperesAtSecond t = 3 * (6 - t)
  finalZeroSegment : ∀ t : ℝ, 6 ≤ t → t ≤ 7 →
    setup.figure.plottedCurrentMilliamperesAtSecond t = 0

/-!
The Physlib vector field is uniform across the idealized small coil and its
norm at the coil location is calibrated to the dimensionful tesla readout.
-/
structure CalibratesMagneticFieldAtCoil
    (setup : ElectromagnetSearchCoilSetup) : Prop where
  coilLocationBelongsToSurface :
    setup.coilLocation ∈ setup.coilSurfaceRegion
  fieldUniformAcrossCoil : ∀ t : ℝ, t ∈ Set.Icc 0 7 →
    ∀ point, point ∈ setup.coilSurfaceRegion →
      setup.ambientMagneticField t point =
        setup.ambientMagneticField t setup.coilLocation
  vectorNormMatchesTeslaMagnitude : ∀ t : ℝ, t ∈ Set.Icc 0 7 →
    ‖setup.ambientMagneticField t setup.coilLocation‖ =
      magneticFluxDensityInTeslas
        (setup.magneticFluxDensityMagnitudeAtSecond t)

/-- Positivity and non-vacuity conditions for the physical apparatus. -/
structure HasPhysicalSearchCoilParameters
    (setup : ElectromagnetSearchCoilSetup) : Prop where
  turnCountPositive : 0 < setup.coilTurnCount
  radiusPositive : 0 < lengthInMeters setup.coilRadius
  areaPositive : 0 < areaInSquareMeters setup.coilArea
  resistancePositive : 0 < resistanceInOhms setup.coilResistance
  coilSurfaceNonempty : setup.coilSurfaceRegion.Nonempty

/-! ## Governing geometry, flux, induction, and circuit laws -/

/-- The ideal circular-coil area law `A = π r²`. -/
structure SatisfiesCircularCoilGeometry
    (setup : ElectromagnetSearchCoilSetup) : Prop where
  circularAreaLaw :
    areaInSquareMeters setup.coilArea =
      Real.pi * lengthInMeters setup.coilRadius ^ 2

/-!
For a uniform field perpendicular to the coil, the flux through one turn is
`Φ = B A`.  Turn multiplication belongs to Faraday's law below, so this field
does not conflate one-turn flux with flux linkage.
-/
structure SatisfiesUniformPerpendicularFluxLaw
    (setup : ElectromagnetSearchCoilSetup) : Prop where
  oneTurnFluxLaw : ∀ t : ℝ, t ∈ Set.Icc 0 7 →
    magneticFluxInWebers
        (setup.magneticFluxThroughOneTurnAtSecond t) =
      magneticFluxDensityInTeslas
          (setup.magneticFluxDensityMagnitudeAtSecond t) *
        areaInSquareMeters setup.coilArea

/-!
Ohm's law relates the independently modeled emf and current magnitudes.
Integrated Faraday induction relates the increase in one-turn flux to the
time integral of emf.  Because the flux is nondecreasing and the induced
current keeps one direction, magnitudes can be used without discarding a
sign reversal.
-/
structure SatisfiesFaradayAndOhmLaws
    (setup : ElectromagnetSearchCoilSetup) : Prop where
  currentIntegrableOnMeasurementInterval :
    IntervalIntegrable
      (fun t => currentInAmperes
        (setup.inducedCurrentMagnitudeAtSecond t)) volume 0 7
  emfIntegrableOnMeasurementInterval :
    IntervalIntegrable
      (fun t => electromotiveForceInVolts
        (setup.inducedEmfMagnitudeAtSecond t)) volume 0 7
  ohmsLaw : ∀ t : ℝ, t ∈ Set.Icc 0 7 →
    electromotiveForceInVolts (setup.inducedEmfMagnitudeAtSecond t) =
      currentInAmperes (setup.inducedCurrentMagnitudeAtSecond t) *
        resistanceInOhms setup.coilResistance
  integratedFaradayLaw : ∀ a b : ℝ,
    0 ≤ a → a ≤ b → b ≤ 7 →
      (setup.coilTurnCount : ℝ) *
          (magneticFluxInWebers
              (setup.magneticFluxThroughOneTurnAtSecond b) -
            magneticFluxInWebers
              (setup.magneticFluxThroughOneTurnAtSecond a)) =
        ∫ t in a..b,
          electromotiveForceInVolts
            (setup.inducedEmfMagnitudeAtSecond t)

/-! ## Figure consequence, answer metadata, and requested result -/

/-!
The signed area under the nonnegative induced-current graph from `0` through
`6 s` is `13.5 mA·s = 0.0135 A·s`.  This is a consequence of the figure alone,
not a magnetic-field answer.
-/
lemma inducedCurrentTimeAreaFromPrimaryGraph
    (setup : ElectromagnetSearchCoilSetup)
    (_figure : MatchesPrimaryInducedCurrentGraph setup) :
    (∫ t in (0 : ℝ)..6,
      currentInAmperes (setup.inducedCurrentMagnitudeAtSecond t)) =
        27 / 2000 := by
  let current : ℝ → ℝ :=
    fun t => currentInAmperes (setup.inducedCurrentMagnitudeAtSecond t)
  have h_rising (t : ℝ) (ht0 : 0 ≤ t) (ht2 : t ≤ 2) :
      current t = 3 / 2000 * t := by
    have hcal := _figure.physicalCurrentCalibratedToPlot t
      ⟨ht0, by linarith⟩
    have hplot := _figure.risingSegment t ht0 ht2
    rw [currentInMilliamperes, hplot] at hcal
    dsimp [current]
    linarith
  have h_constant (t : ℝ) (ht2 : 2 ≤ t) (ht5 : t ≤ 5) :
      current t = 3 / 1000 := by
    have hcal := _figure.physicalCurrentCalibratedToPlot t
      ⟨by linarith, by linarith⟩
    have hplot := _figure.constantSegment t ht2 ht5
    rw [currentInMilliamperes, hplot] at hcal
    dsimp [current]
    linarith
  have h_falling (t : ℝ) (ht5 : 5 ≤ t) (ht6 : t ≤ 6) :
      current t = 3 / 1000 * (6 - t) := by
    have hcal := _figure.physicalCurrentCalibratedToPlot t
      ⟨by linarith, by linarith⟩
    have hplot := _figure.fallingSegment t ht5 ht6
    rw [currentInMilliamperes, hplot] at hcal
    dsimp [current]
    linarith
  have h_integrable_rising : IntervalIntegrable current volume 0 2 := by
    apply
      ((show Continuous (fun t : ℝ => 3 / 2000 * t) by fun_prop).intervalIntegrable 0 2).congr
    intro t ht
    have hmem := Set.uIoc_subset_uIcc ht
    rw [Set.uIcc_of_le (by norm_num : (0 : ℝ) ≤ 2)] at hmem
    exact (h_rising t hmem.1 hmem.2).symm
  have h_integrable_constant : IntervalIntegrable current volume 2 5 := by
    apply
      ((show Continuous (fun _ : ℝ => (3 / 1000 : ℝ)) by fun_prop).intervalIntegrable 2 5).congr
    intro t ht
    have hmem := Set.uIoc_subset_uIcc ht
    rw [Set.uIcc_of_le (by norm_num : (2 : ℝ) ≤ 5)] at hmem
    exact (h_constant t hmem.1 hmem.2).symm
  have h_integrable_falling : IntervalIntegrable current volume 5 6 := by
    apply
      ((show Continuous (fun t : ℝ => 3 / 1000 * (6 - t)) by
          fun_prop).intervalIntegrable 5 6).congr
    intro t ht
    have hmem := Set.uIoc_subset_uIcc ht
    rw [Set.uIcc_of_le (by norm_num : (5 : ℝ) ≤ 6)] at hmem
    exact (h_falling t hmem.1 hmem.2).symm
  change (∫ t in (0 : ℝ)..6, current t) = 27 / 2000
  rw [← intervalIntegral.integral_add_adjacent_intervals
      (h_integrable_rising.trans h_integrable_constant) h_integrable_falling,
    ← intervalIntegral.integral_add_adjacent_intervals
      h_integrable_rising h_integrable_constant]
  have h_int_rising :
      (∫ t in (0 : ℝ)..2, current t) =
        ∫ t in (0 : ℝ)..2, 3 / 2000 * t := by
    apply intervalIntegral.integral_congr
    intro t ht
    rw [Set.uIcc_of_le (by norm_num : (0 : ℝ) ≤ 2)] at ht
    exact h_rising t ht.1 ht.2
  have h_int_constant :
      (∫ t in (2 : ℝ)..5, current t) =
        ∫ _t in (2 : ℝ)..5, 3 / 1000 := by
    apply intervalIntegral.integral_congr
    intro t ht
    rw [Set.uIcc_of_le (by norm_num : (2 : ℝ) ≤ 5)] at ht
    exact h_constant t ht.1 ht.2
  have h_int_falling :
      (∫ t in (5 : ℝ)..6, current t) =
        ∫ t in (5 : ℝ)..6, 3 / 1000 * (6 - t) := by
    apply intervalIntegral.integral_congr
    intro t ht
    rw [Set.uIcc_of_le (by norm_num : (5 : ℝ) ≤ 6)] at ht
    exact h_falling t ht.1 ht.2
  have h_rising_value :
      (∫ t in (0 : ℝ)..2, 3 / 2000 * t) = 3 / 1000 := by
    rw [intervalIntegral.integral_const_mul, integral_id]
    norm_num
  have h_constant_value :
      (∫ _t in (2 : ℝ)..5, (3 / 1000 : ℝ)) = 9 / 1000 := by
    norm_num
  have h_falling_value :
      (∫ t in (5 : ℝ)..6, 3 / 1000 * (6 - t)) = 3 / 2000 := by
    rw [intervalIntegral.integral_const_mul]
    rw [intervalIntegral.integral_sub]
    · rw [intervalIntegral.integral_const, integral_id]
      norm_num
    · exact continuous_const.intervalIntegrable 5 6
    · exact continuous_id.intervalIntegrable 5 6
  rw [h_int_rising, h_int_constant, h_int_falling,
    h_rising_value, h_constant_value, h_falling_value]
  norm_num

/-- Labels attached to the four displayed magnetic-field choices. -/
inductive AnswerChoice where
  | A
  | B
  | C
  | D
  deriving DecidableEq, Fintype, Repr

/-- Magnetic-flux-density magnitude in teslas printed beside an answer label. -/
def AnswerChoice.displayedMagneticFieldInTeslas : AnswerChoice → ℝ
  | .A => 4
  | .B => 37 / 10
  | .C => 3
  | .D => 9 / 4

/-- The source dataset records answer label B. -/
def recordedDatasetAnswer : AnswerChoice := .B

/-- Magnetic-field magnitude requested at the independently modeled time. -/
def observedMagneticFieldInTeslas
    (setup : ElectromagnetSearchCoilSetup) : ℝ :=
  magneticFluxDensityInTeslas
    (setup.magneticFluxDensityMagnitudeAtSecond
      (timeInSeconds setup.observationTime))

/-- A displayed choice agrees with the requested magnetic-field readout. -/
def AnswerMatchesObservedMagneticField
    (setup : ElectromagnetSearchCoilSetup)
    (choice : AnswerChoice) : Prop :=
  observedMagneticFieldInTeslas setup =
    choice.displayedMagneticFieldInTeslas

/-!
The primary graph has current-time area `0.0135 A·s`.  Together with the stated
coil data and governing laws, it implies the exact field
`3375 / (256 * π) T` at `t = 6.00 s`, approximately `4.196 T`.  Consequently
the source dataset's recorded answer B (`3.7 T`) does not agree with the
modeled experiment; that recorded answer is retained only as metadata.  This
declaration is the source-supported redraft of blueprint label
`thm:physics:phyx_mini_0980:target`.
-/
theorem problem_phyx_mini_0980
    (setup : ElectromagnetSearchCoilSetup)
    (_scenario : MatchesWrittenElectromagnetScenario setup)
    (_figure : MatchesPrimaryInducedCurrentGraph setup)
    (_fieldCalibration : CalibratesMagneticFieldAtCoil setup)
    (_physical : HasPhysicalSearchCoilParameters setup)
    (_geometry : SatisfiesCircularCoilGeometry setup)
    (_flux : SatisfiesUniformPerpendicularFluxLaw setup)
    (_laws : SatisfiesFaradayAndOhmLaws setup) :
    observedMagneticFieldInTeslas setup = 3375 / (256 * Real.pi) := by
  have h_radius : lengthInMeters setup.coilRadius = 1 / 125 := by
    have h := _scenario.radiusIsEightTenthsCentimeter
    rw [lengthInCentimeters] at h
    linarith
  have h_area : areaInSquareMeters setup.coilArea = Real.pi / 15625 := by
    calc
      areaInSquareMeters setup.coilArea =
          Real.pi * lengthInMeters setup.coilRadius ^ 2 :=
        _geometry.circularAreaLaw
      _ = Real.pi / 15625 := by rw [h_radius]; ring
  have h_flux_zero :
      magneticFluxInWebers
          (setup.magneticFluxThroughOneTurnAtSecond 0) = 0 := by
    rw [_flux.oneTurnFluxLaw 0 (by norm_num)]
    rw [_scenario.initialMagneticFieldIsZero]
    ring
  have h_flux_six :
      magneticFluxInWebers
          (setup.magneticFluxThroughOneTurnAtSecond 6) =
        magneticFluxDensityInTeslas
            (setup.magneticFluxDensityMagnitudeAtSecond 6) *
          (Real.pi / 15625) := by
    rw [_flux.oneTurnFluxLaw 6 (by norm_num), h_area]
  have h_emf_current :
      (∫ t in (0 : ℝ)..6,
        electromotiveForceInVolts
          (setup.inducedEmfMagnitudeAtSecond t)) =
        ∫ t in (0 : ℝ)..6,
          currentInAmperes
              (setup.inducedCurrentMagnitudeAtSecond t) *
            resistanceInOhms setup.coilResistance := by
    apply intervalIntegral.integral_congr
    intro t ht
    rw [Set.uIcc_of_le (by norm_num : (0 : ℝ) ≤ 6)] at ht
    exact _laws.ohmsLaw t ⟨ht.1, by linarith [ht.2]⟩
  have h_emf_area :
      (∫ t in (0 : ℝ)..6,
        electromotiveForceInVolts
          (setup.inducedEmfMagnitudeAtSecond t)) = 27 / 8000 := by
    rw [h_emf_current, intervalIntegral.integral_mul_const,
      inducedCurrentTimeAreaFromPrimaryGraph setup _figure,
      _scenario.resistanceIsQuarterOhm]
    norm_num
  have h_faraday :=
    _laws.integratedFaradayLaw 0 6 (by norm_num) (by norm_num) (by norm_num)
  rw [_scenario.fourTurnCoil, h_flux_zero, h_flux_six, h_emf_area] at h_faraday
  norm_num at h_faraday
  rw [observedMagneticFieldInTeslas, _scenario.observationAtSixSeconds]
  apply (eq_div_iff (mul_ne_zero (by norm_num) Real.pi_ne_zero)).2
  nlinarith

end PhyXMiniProblems.ProblemPhyXMini0980
