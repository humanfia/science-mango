import Mathlib
import Physlib.Units.WithDim.Basic

/- USER: The assigned Lean file did not exist when this autoformalization task began. -/

noncomputable section

namespace PhyXMiniProblems.ProblemPhyXMini0926

open Dimension

/-!
# Induced current in a circular loop in a decreasing magnetic field

A single circular conducting loop has diameter `10 cm` and resistance
`0.20 Ω`.  The primary raster shows uniformly spaced blue dots both inside
and outside the loop, encoding a magnetic field directed out of the page, and
prints `B decreasing at 0.50 T/s`.  For a fixed loop in a spatially uniform
perpendicular field, the changing flux induces an emf and hence an Ohmic
current.

Physical magnitudes are represented by Physlib's unit-covariant
`Dimensionful (WithDim ...)` quantities.  Real numbers occur only as explicitly
named coherent-SI readouts, displayed answer values, and dimensionless turn
counts.

Assumption/target split:

* governing laws: circular area, uniform perpendicular magnetic-flux change,
  Faraday's law for the emf magnitude, and Ohm's law for current magnitude;
* previous-part results: none;
* figure/data readouts: a brown circular single-turn loop, blue out-of-page
  dots inside and outside the loop, a spatially uniform perpendicular field,
  diameter `10 cm`, resistance `0.20 Ω`, and field magnitude decreasing at
  `0.50 T/s`;
* current targets: the exact induced current `25π/4 mA` (equivalently
  `π/160 A`) and the fact that answer choice B, `20 mA`, is uniquely nearest.

Neither target is a setup field definition or a premise of any figure,
geometry, or governing-law structure.
-/

/-! ## Physical dimensions and unit-independent quantities -/

/-- Area has physical dimension `L²`. -/
def areaDimension : Dimension :=
  L𝓭 * L𝓭

/-- Electric current has physical dimension `C T⁻¹`. -/
def electricCurrentDimension : Dimension :=
  C𝓭 * T𝓭⁻¹

/-- Electrical resistance has physical dimension `M L² T⁻¹ C⁻²`. -/
def electricalResistanceDimension : Dimension :=
  M𝓭 * L𝓭 * L𝓭 * T𝓭⁻¹ * C𝓭⁻¹ * C𝓭⁻¹

/-- Magnetic flux density (tesla) has physical dimension `M T⁻¹ C⁻¹`. -/
def magneticFluxDensityDimension : Dimension :=
  M𝓭 * T𝓭⁻¹ * C𝓭⁻¹

/-- A magnetic-flux-density change rate has dimension `M T⁻² C⁻¹`. -/
def magneticFluxDensityRateDimension : Dimension :=
  M𝓭 * T𝓭⁻¹ * T𝓭⁻¹ * C𝓭⁻¹

/-- Magnetic flux has the dimension of flux density times area. -/
def magneticFluxDimension : Dimension :=
  magneticFluxDensityDimension * areaDimension

/-- Magnetic-flux change rate has the volt dimension `M L² T⁻² C⁻¹`. -/
def magneticFluxRateDimension : Dimension :=
  magneticFluxDimension * T𝓭⁻¹

/-- Electromotive force has physical dimension `M L² T⁻² C⁻¹`. -/
def emfDimension : Dimension :=
  M𝓭 * L𝓭 * L𝓭 * T𝓭⁻¹ * T𝓭⁻¹ * C𝓭⁻¹

/-- A nonnegative, unit-independent physical length. -/
abbrev LengthMagnitude : Type :=
  Dimensionful (WithDim L𝓭 NNReal)

/-- A nonnegative, unit-independent physical area. -/
abbrev AreaMagnitude : Type :=
  Dimensionful (WithDim areaDimension NNReal)

/-- A nonnegative, unit-independent electrical resistance. -/
abbrev ResistanceMagnitude : Type :=
  Dimensionful (WithDim electricalResistanceDimension NNReal)

/-- A nonnegative, unit-independent magnetic-flux-density decrease rate. -/
abbrev MagneticFluxDensityRateMagnitude : Type :=
  Dimensionful (WithDim magneticFluxDensityRateDimension NNReal)

/-- A nonnegative, unit-independent magnetic-flux decrease rate. -/
abbrev MagneticFluxRateMagnitude : Type :=
  Dimensionful (WithDim magneticFluxRateDimension NNReal)

/-- A nonnegative, unit-independent induced-emf magnitude. -/
abbrev EmfMagnitude : Type :=
  Dimensionful (WithDim emfDimension NNReal)

/-- A nonnegative, unit-independent electric-current magnitude. -/
abbrev ElectricCurrentMagnitude : Type :=
  Dimensionful (WithDim electricCurrentDimension NNReal)

/-! ## Named coherent-SI readouts -/

/-- Read a nonnegative dimensionful quantity in coherent SI units. -/
def nonnegativeSIReadout {d : Dimension}
    (quantity : Dimensionful (WithDim d NNReal)) : ℝ :=
  ((quantity UnitChoices.SI).val : ℝ)

/-- Read a physical length in metres. -/
def lengthInMeters (length : LengthMagnitude) : ℝ :=
  nonnegativeSIReadout length

/-- Read the loop diameter in centimetres. -/
def lengthInCentimeters (length : LengthMagnitude) : ℝ :=
  100 * lengthInMeters length

/-- Read a physical area in square metres. -/
def areaInSquareMeters (area : AreaMagnitude) : ℝ :=
  nonnegativeSIReadout area

/-- Read an electrical resistance in ohms. -/
def resistanceInOhms (resistance : ResistanceMagnitude) : ℝ :=
  nonnegativeSIReadout resistance

/-- Read a magnetic-flux-density decrease rate in teslas per second. -/
def magneticFluxDensityRateInTeslasPerSecond
    (rate : MagneticFluxDensityRateMagnitude) : ℝ :=
  nonnegativeSIReadout rate

/-- Read a magnetic-flux decrease rate in webers per second. -/
def magneticFluxRateInWebersPerSecond
    (rate : MagneticFluxRateMagnitude) : ℝ :=
  nonnegativeSIReadout rate

/-- Read an induced-emf magnitude in volts. -/
def emfMagnitudeInVolts (emf : EmfMagnitude) : ℝ :=
  nonnegativeSIReadout emf

/-- Read an electric-current magnitude in amperes. -/
def currentMagnitudeInAmperes (current : ElectricCurrentMagnitude) : ℝ :=
  nonnegativeSIReadout current

/-- Read an electric-current magnitude in milliamperes. -/
def currentMagnitudeInMilliamperes
    (current : ElectricCurrentMagnitude) : ℝ :=
  1000 * currentMagnitudeInAmperes current

/-! ## Apparatus and primary-figure vocabulary -/

/-- Idealized topology and construction of the conducting loop. -/
inductive LoopConductorModel where
  | closedSingleTurnWire
  | other
  deriving DecidableEq, Repr

/-- Shape of the loop outline visible in the raster. -/
inductive LoopOutlineShape where
  | circular
  | other
  deriving DecidableEq, Repr

/-- Colors needed to transcribe the two visual components of image `926.png`. -/
inductive FigureColor where
  | brown
  | blue
  | other
  deriving DecidableEq, Repr

/-- Conventional marker used for a field normal to the page. -/
inductive FieldMarkerKind where
  | dot
  | cross
  deriving DecidableEq, Repr

/-- Page-normal direction encoded by a conventional field marker. -/
inductive PageNormalDirection where
  | outOfPage
  | intoPage
  deriving DecidableEq, Repr

/-- Temporal trend stated for the magnetic-flux-density magnitude. -/
inductive MagneticFieldTrend where
  | decreasing
  | increasing
  | constant
  deriving DecidableEq, Repr

/-- Spatial uniformity idealization of the applied field. -/
inductive FieldUniformity where
  | spatiallyUniform
  | nonuniform
  deriving DecidableEq, Repr

/-- Orientation of the applied field relative to the loop plane. -/
inductive FieldLoopOrientation where
  | perpendicularToLoopPlane
  | other
  deriving DecidableEq, Repr

/-!
Presentation facts transcribed from the primary raster.  The scalar rate is a
printed tesla-per-second readout and is calibrated to an independent physical
rate in `MatchesPrimaryInductionLoopFigure` below.
-/
structure InductionLoopFigure where
  loopOutlineShape : LoopOutlineShape
  loopOutlineColor : FigureColor
  fieldMarkerKind : FieldMarkerKind
  fieldMarkerColor : FigureColor
  fieldMarkerDirection : PageNormalDirection
  fieldDotsInsideLoopShown : Bool
  fieldDotsOutsideLoopShown : Bool
  fieldDotsUniformlySpaced : Bool
  printedMagneticFieldSymbol : String
  printedTrendWord : String
  displayedDecreaseRateTeslasPerSecond : ℝ

/-!
Independent physical quantities and observables of the induction experiment.
In particular, the area, flux-change rate, induced emf, and induced current are
not defined from their desired numerical values or from an answer choice.
-/
structure CircularInductionLoopSetup where
  loopModel : LoopConductorModel
  turnCount : ℕ
  fieldUniformity : FieldUniformity
  fieldOrientation : FieldLoopOrientation
  fieldDirection : PageNormalDirection
  fieldTrend : MagneticFieldTrend
  loopDiameter : LengthMagnitude
  loopArea : AreaMagnitude
  loopResistance : ResistanceMagnitude
  magneticFluxDensityDecreaseRate : MagneticFluxDensityRateMagnitude
  magneticFluxDecreaseRate : MagneticFluxRateMagnitude
  inducedEmfMagnitude : EmfMagnitude
  inducedCurrentMagnitude : ElectricCurrentMagnitude
  figure : InductionLoopFigure

/-! ## Problem data, figure evidence, and governing relations -/

/-- Prose data for the circular `10 cm`, `0.20 Ω`, single-turn loop. -/
structure MatchesInductionLoopDescription
    (setup : CircularInductionLoopSetup) : Prop where
  loopIsClosedSingleTurnWire :
    setup.loopModel = .closedSingleTurnWire
  exactlyOneTurn : setup.turnCount = 1
  diameterIsTenCentimeters :
    lengthInCentimeters setup.loopDiameter = 10
  resistanceIsPointTwoOhms :
    resistanceInOhms setup.loopResistance = 1 / 5

/-!
Facts supplied by image `926.png`.  Dot markers conventionally encode a field
out of the page.  Their regular placement both inside and outside the loop is
the figure-derived evidence for a spatially uniform field perpendicular to the
loop plane.  This structure contains no induced-current value.
-/
structure MatchesPrimaryInductionLoopFigure
    (setup : CircularInductionLoopSetup) : Prop where
  outlineIsCircular : setup.figure.loopOutlineShape = .circular
  outlineIsBrown : setup.figure.loopOutlineColor = .brown
  markersAreDots : setup.figure.fieldMarkerKind = .dot
  markersAreBlue : setup.figure.fieldMarkerColor = .blue
  dotsPointOutOfPage :
    setup.figure.fieldMarkerDirection = .outOfPage
  dotsAreShownInsideLoop :
    setup.figure.fieldDotsInsideLoopShown = true
  dotsAreShownOutsideLoop :
    setup.figure.fieldDotsOutsideLoopShown = true
  dotPatternIsUniform :
    setup.figure.fieldDotsUniformlySpaced = true
  printedFieldSymbolIsB :
    setup.figure.printedMagneticFieldSymbol = "B"
  printedTrendIsDecreasing :
    setup.figure.printedTrendWord = "decreasing"
  printedRateIsPointFiveTeslasPerSecond :
    setup.figure.displayedDecreaseRateTeslasPerSecond = 1 / 2
  physicalRateMatchesPrintedRate :
    magneticFluxDensityRateInTeslasPerSecond
        setup.magneticFluxDensityDecreaseRate =
      setup.figure.displayedDecreaseRateTeslasPerSecond
  physicalDirectionMatchesDots :
    setup.fieldDirection = setup.figure.fieldMarkerDirection
  fieldMagnitudeIsDecreasing :
    setup.fieldTrend = .decreasing
  fieldIsSpatiallyUniform :
    setup.fieldUniformity = .spatiallyUniform
  fieldIsPerpendicularToLoop :
    setup.fieldOrientation = .perpendicularToLoopPlane

/-- Positivity and nondegeneracy conditions selecting the physical branch. -/
structure HasPhysicalInductionLoopParameters
    (setup : CircularInductionLoopSetup) : Prop where
  diameterPositive : 0 < lengthInMeters setup.loopDiameter
  areaPositive : 0 < areaInSquareMeters setup.loopArea
  resistancePositive : 0 < resistanceInOhms setup.loopResistance
  decreaseRatePositive :
    0 < magneticFluxDensityRateInTeslasPerSecond
      setup.magneticFluxDensityDecreaseRate

/-!
The area of a circle is `π r²`, with radius one half of the independently
modeled loop diameter.  This is a geometric law, not a definition of the area
from the `10 cm` data.
-/
structure SatisfiesCircularLoopGeometry
    (setup : CircularInductionLoopSetup) : Prop where
  circularAreaLaw :
    areaInSquareMeters setup.loopArea =
      Real.pi * (lengthInMeters setup.loopDiameter / 2) ^ 2

/-!
Governing magnitude relations for the fixed loop:

* in a uniform field perpendicular to a fixed area, the magnetic-flux
  decrease rate is area times the flux-density decrease rate;
* Faraday's law gives emf magnitude as turn count times flux-change rate; and
* Ohm's law gives emf magnitude as current magnitude times resistance.

These general relations contain neither `25π/4 mA` nor answer choice B.
-/
structure SatisfiesCircularLoopInductionLaws
    (setup : CircularInductionLoopSetup) : Prop where
  uniformPerpendicularFluxChange :
    magneticFluxRateInWebersPerSecond setup.magneticFluxDecreaseRate =
      areaInSquareMeters setup.loopArea *
        magneticFluxDensityRateInTeslasPerSecond
          setup.magneticFluxDensityDecreaseRate
  faradayLawMagnitude :
    emfMagnitudeInVolts setup.inducedEmfMagnitude =
      (setup.turnCount : ℝ) *
        magneticFluxRateInWebersPerSecond setup.magneticFluxDecreaseRate
  ohmsLawMagnitude :
    emfMagnitudeInVolts setup.inducedEmfMagnitude =
      currentMagnitudeInAmperes setup.inducedCurrentMagnitude *
        resistanceInOhms setup.loopResistance

/-! ## Derived quantities and displayed answer selection -/

/-- The stated diameter and circular geometry give area `π/400 m²`. -/
lemma loopArea_eq_pi_div_four_hundred
    (setup : CircularInductionLoopSetup)
    (_description : MatchesInductionLoopDescription setup)
    (_geometry : SatisfiesCircularLoopGeometry setup) :
    areaInSquareMeters setup.loopArea = Real.pi / 400 := by
  have hdiameter :
      lengthInMeters setup.loopDiameter = (1 : ℝ) / 10 := by
    have h := _description.diameterIsTenCentimeters
    simp only [lengthInCentimeters] at h
    linarith
  calc
    areaInSquareMeters setup.loopArea =
        Real.pi * (lengthInMeters setup.loopDiameter / 2) ^ 2 :=
      _geometry.circularAreaLaw
    _ = Real.pi / 400 := by rw [hdiameter]; ring

/-- Faraday's law then gives the single-turn emf magnitude `π/800 V`. -/
lemma inducedEmf_eq_pi_div_eight_hundred
    (setup : CircularInductionLoopSetup)
    (_description : MatchesInductionLoopDescription setup)
    (_figure : MatchesPrimaryInductionLoopFigure setup)
    (_geometry : SatisfiesCircularLoopGeometry setup)
    (_laws : SatisfiesCircularLoopInductionLaws setup) :
    emfMagnitudeInVolts setup.inducedEmfMagnitude = Real.pi / 800 := by
  have harea :
      areaInSquareMeters setup.loopArea = Real.pi / 400 :=
    loopArea_eq_pi_div_four_hundred setup _description _geometry
  have hrate :
      magneticFluxDensityRateInTeslasPerSecond
          setup.magneticFluxDensityDecreaseRate = (1 : ℝ) / 2 := by
    calc
      magneticFluxDensityRateInTeslasPerSecond
          setup.magneticFluxDensityDecreaseRate =
          setup.figure.displayedDecreaseRateTeslasPerSecond :=
        _figure.physicalRateMatchesPrintedRate
      _ = (1 : ℝ) / 2 :=
        _figure.printedRateIsPointFiveTeslasPerSecond
  calc
    emfMagnitudeInVolts setup.inducedEmfMagnitude =
        (setup.turnCount : ℝ) *
          magneticFluxRateInWebersPerSecond
            setup.magneticFluxDecreaseRate :=
      _laws.faradayLawMagnitude
    _ = (setup.turnCount : ℝ) *
          (areaInSquareMeters setup.loopArea *
            magneticFluxDensityRateInTeslasPerSecond
              setup.magneticFluxDensityDecreaseRate) := by
      rw [_laws.uniformPerpendicularFluxChange]
    _ = Real.pi / 800 := by
      rw [_description.exactlyOneTurn, Nat.cast_one, harea, hrate]
      ring

/-- Labels of the four answer choices displayed in the problem. -/
inductive AnswerChoice where
  | A
  | B
  | C
  | D
  deriving DecidableEq, Fintype, Repr

/-- Current magnitude in milliamperes printed beside each answer label. -/
def AnswerChoice.currentInMilliamperes : AnswerChoice → ℝ
  | .A => 16
  | .B => 20
  | .C => 39
  | .D => 15

/-- The answer label recorded in the supplied dataset metadata. -/
def recordedDatasetAnswer : AnswerChoice := .B

/-!
A displayed choice is the unique nearest choice to a computed milliampere
readout when every differently labelled choice has strictly larger absolute
error.  This generic definition neither selects B nor prescribes a current.
-/
def IsUniqueNearestDisplayedCurrentChoice
    (computedMilliamperes : ℝ) (choice : AnswerChoice) : Prop :=
  ∀ other : AnswerChoice, other ≠ choice →
    |computedMilliamperes - choice.currentInMilliamperes| <
      |computedMilliamperes - other.currentInMilliamperes|

/-- A displayed answer agrees with the modeled induced-current magnitude. -/
def AnswerMatchesInducedCurrent
    (setup : CircularInductionLoopSetup) (choice : AnswerChoice) : Prop :=
  IsUniqueNearestDisplayedCurrentChoice
    (currentMagnitudeInMilliamperes setup.inducedCurrentMagnitude) choice

/-!
The loop area is `π(0.05 m)²`, so the flux changes at `π/800 Wb/s`.
Faraday's law and the `0.20 Ω` resistance give

`I = (π/800 V)/(1/5 Ω) = π/160 A = 25π/4 mA ≈ 19.6 mA`.

Consequently the unique nearest displayed value is `20 mA`, answer choice B.
This declaration formalizes `thm:physics:phyx_mini_0926:target`.
-/
theorem problem_phyx_mini_0926
    (setup : CircularInductionLoopSetup)
    (_description : MatchesInductionLoopDescription setup)
    (_figure : MatchesPrimaryInductionLoopFigure setup)
    (_physical : HasPhysicalInductionLoopParameters setup)
    (_geometry : SatisfiesCircularLoopGeometry setup)
    (_laws : SatisfiesCircularLoopInductionLaws setup) :
    currentMagnitudeInAmperes setup.inducedCurrentMagnitude =
        Real.pi / 160 ∧
      currentMagnitudeInMilliamperes setup.inducedCurrentMagnitude =
        25 * Real.pi / 4 ∧
      AnswerMatchesInducedCurrent setup recordedDatasetAnswer := by
  have hemf :
      emfMagnitudeInVolts setup.inducedEmfMagnitude = Real.pi / 800 :=
    inducedEmf_eq_pi_div_eight_hundred
      setup _description _figure _geometry _laws
  have hcurrent :
      currentMagnitudeInAmperes setup.inducedCurrentMagnitude =
        Real.pi / 160 := by
    have hohm := _laws.ohmsLawMagnitude
    rw [hemf, _description.resistanceIsPointTwoOhms] at hohm
    linarith
  have hmilliamperes :
      currentMagnitudeInMilliamperes setup.inducedCurrentMagnitude =
        25 * Real.pi / 4 := by
    rw [currentMagnitudeInMilliamperes, hcurrent]
    ring
  refine ⟨hcurrent, hmilliamperes, ?_⟩
  rw [AnswerMatchesInducedCurrent, recordedDatasetAnswer, hmilliamperes]
  intro other hother
  cases other with
  | A =>
      change |25 * Real.pi / 4 - 20| < |25 * Real.pi / 4 - 16|
      have hpositive :
          0 < 25 * Real.pi / 4 - 16 := by
        nlinarith [Real.pi_gt_three]
      rw [abs_of_pos hpositive]
      exact abs_lt.mpr
        ⟨by nlinarith [Real.pi_gt_three], by norm_num⟩
  | B =>
      exact (hother rfl).elim
  | C =>
      change |25 * Real.pi / 4 - 20| < |25 * Real.pi / 4 - 39|
      have hnegative :
          25 * Real.pi / 4 - 39 < 0 := by
        nlinarith [Real.pi_le_four]
      rw [abs_of_neg hnegative]
      exact abs_lt.mpr
        ⟨by norm_num, by nlinarith [Real.pi_le_four]⟩
  | D =>
      change |25 * Real.pi / 4 - 20| < |25 * Real.pi / 4 - 15|
      have hpositive :
          0 < 25 * Real.pi / 4 - 15 := by
        nlinarith [Real.pi_gt_three]
      rw [abs_of_pos hpositive]
      exact abs_lt.mpr
        ⟨by nlinarith [Real.pi_gt_three], by norm_num⟩

end PhyXMiniProblems.ProblemPhyXMini0926
