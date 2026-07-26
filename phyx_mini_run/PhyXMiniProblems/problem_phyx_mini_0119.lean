import Mathlib
import Physlib.Units.WithDim.Basic

noncomputable section

namespace PhyXMiniProblems.ProblemPhyXMini0119

open Dimension

/-!
# Laser wavelength from a reciprocal-slit-separation plot

Monochromatic laser light illuminates a succession of narrow double slits.
For each slit pair, the adjacent bright-fringe spacing `Δy` is measured near
the center of a screen `0.900 m` from the slits. The supplied graph plots the
measured `Δy`, in millimeters, against `1 / d`, in inverse millimeters, and
shows a magenta best-fit line through eight black observations.

Lengths are unit-independent Physlib quantities. Since the graph's vertical
coordinate has dimension length and its horizontal coordinate has dimension
inverse length, the fitted slope has dimension length squared. Real numbers
below are used only for calibrated scalar readouts and plot coordinates.
-/

/-- A unit-independent physical quantity carrying the dimension of length. -/
abbrev LengthQuantity : Type := Dimensionful (WithDim L𝓭 ℝ)

/-- A unit-independent signed quantity carrying the dimension of area. -/
abbrev AreaQuantity : Type := Dimensionful (WithDim (L𝓭 * L𝓭) ℝ)

/-- Scalar readout of a physical length in a selected length unit. -/
def lengthReadout (unit : LengthUnit) (length : LengthQuantity) : ℝ :=
  (length { UnitChoices.SI with length := unit }).val

/-- Scalar readout of a physical area in the square of a selected length unit. -/
def areaReadout (unit : LengthUnit) (area : AreaQuantity) : ℝ :=
  (area { UnitChoices.SI with length := unit }).val

/-- Meter readout used for the stated slit-to-screen distance. -/
def lengthInMeters (length : LengthQuantity) : ℝ :=
  lengthReadout LengthUnit.meters length

/-- Millimeter readout used on the graph's vertical axis. -/
def lengthInMillimeters (length : LengthQuantity) : ℝ :=
  lengthReadout LengthUnit.millimeters length

/-- Nanometer readout used by the wavelength answer choices. -/
def lengthInNanometers (length : LengthQuantity) : ℝ :=
  lengthReadout LengthUnit.nanometers length

/-- Square-millimeter readout appropriate to the fitted graph slope. -/
def areaInSquareMillimeters (area : AreaQuantity) : ℝ :=
  areaReadout LengthUnit.millimeters area

/-- The two optical planes whose axial separation is `0.900 m`. -/
inductive OpticalPlane where
  | doubleSlitPlane
  | screen
  deriving DecidableEq, Repr

/-- The illumination branch stated in the problem. -/
inductive IlluminationKind where
  | monochromaticLaser
  | broadband
  deriving DecidableEq, Repr

/-- Whether each pair of openings is modeled as narrow or finite-width. -/
inductive SlitRegime where
  | narrow
  | finiteWidth
  deriving DecidableEq, Repr

/-- The approximation used for central adjacent-fringe spacing. -/
inductive OpticalApproximation where
  | paraxialFraunhofer
  | exactFiniteAngle
  deriving DecidableEq, Repr

/-- Physical quantities named by the two axes of the supplied graph. -/
inductive PlotAxisQuantity where
  | reciprocalSlitSeparation
  | adjacentBrightFringeSpacing
  deriving DecidableEq, Repr

/-- Units printed beside the two graph axes. -/
inductive PlotAxisUnit where
  | inverseMillimeters
  | millimeters
  deriving DecidableEq, Repr

/-- Colors used for observations and the fitted line in the source image. -/
inductive PlotColor where
  | black
  | magenta
  deriving DecidableEq, Repr

/--
The eight plotted observations and the dimensionful fitted-line parameters.

The observed horizontal coordinates are scalar readouts in `mm⁻¹`, and the
observed vertical coordinates and fitted-line values are scalar readouts in
`mm`. The intercept is therefore a length and the slope is an area.
-/
structure ReciprocalSlitSeparationPlot where
  horizontalAxis : PlotAxisQuantity
  verticalAxis : PlotAxisQuantity
  horizontalUnit : PlotAxisUnit
  verticalUnit : PlotAxisUnit
  horizontalMinimumPerMillimeter : ℝ
  horizontalMaximumPerMillimeter : ℝ
  horizontalGridSpacingPerMillimeter : ℝ
  verticalMinimumMillimeters : ℝ
  verticalMaximumMillimeters : ℝ
  verticalGridSpacingMillimeters : ℝ
  reciprocalSlitSeparationPerMillimeter : Fin 8 → ℝ
  measuredFringeSpacingMillimeters : Fin 8 → ℝ
  observationColor : PlotColor
  bestFitLineColor : PlotColor
  hasGrid : Bool
  bestFitIntercept : LengthQuantity
  bestFitSlope : AreaQuantity
  bestFitLineValueMillimeters : ℝ → ℝ

/--
The laser, slit pairs, screen, and graph used by the wavelength experiment.

Measured and ideal fringe spacings are separate fields: the black points are
experimental observations and need not lie exactly on the paraxial prediction.
-/
structure DoubleSlitWavelengthExperiment where
  illumination : IlluminationKind
  slitRegime : SlitRegime
  approximation : OpticalApproximation
  axialCoordinate : OpticalPlane → LengthQuantity
  wavelengthLambda : LengthQuantity
  screenDistanceL : LengthQuantity
  slitSeparationD : Fin 8 → LengthQuantity
  idealAdjacentFringeSpacing : Fin 8 → LengthQuantity
  measuredAdjacentFringeSpacing : Fin 8 → LengthQuantity
  plot : ReciprocalSlitSeparationPlot

/--
The physical branch and positivity conditions of the experiment. Positivity
does not prescribe the unknown wavelength's numerical value.
-/
def HasPhysicalConfiguration
    (setup : DoubleSlitWavelengthExperiment) : Prop :=
  setup.illumination = .monochromaticLaser ∧
    setup.slitRegime = .narrow ∧
    setup.approximation = .paraxialFraunhofer ∧
    0 < lengthInMeters setup.wavelengthLambda ∧
    0 < lengthInMeters setup.screenDistanceL ∧
    (∀ i, 0 < lengthInMillimeters (setup.slitSeparationD i)) ∧
    (∀ i, 0 < lengthInMillimeters (setup.idealAdjacentFringeSpacing i)) ∧
    (∀ i, 0 < lengthInMillimeters (setup.measuredAdjacentFringeSpacing i))

/--
The stated `0.900 m` distance and its interpretation as the axial separation
between the slit plane and screen. No wavelength value is included.
-/
def MatchesProblemReadouts
    (setup : DoubleSlitWavelengthExperiment) : Prop :=
  lengthInMeters setup.screenDistanceL = 9 / 10 ∧
    lengthInMeters (setup.axialCoordinate .screen) -
        lengthInMeters (setup.axialCoordinate .doubleSlitPlane) =
      lengthInMeters setup.screenDistanceL

/--
Labels, ranges, grid spacings, colors, approximate marker-center readouts, and
the calibrated fitted-line slope read from the primary image.

The line's slope is `0.558 mm²`; its value is independent figure data, not a
wavelength assumption. The displayed marker coordinates retain experimental
scatter and are deliberately not asserted to lie exactly on the ideal line.
-/
def MatchesSuppliedPlot (plot : ReciprocalSlitSeparationPlot) : Prop :=
  plot.horizontalAxis = .reciprocalSlitSeparation ∧
    plot.verticalAxis = .adjacentBrightFringeSpacing ∧
    plot.horizontalUnit = .inverseMillimeters ∧
    plot.verticalUnit = .millimeters ∧
    plot.horizontalMinimumPerMillimeter = 0 ∧
    plot.horizontalMaximumPerMillimeter = 12 ∧
    plot.horizontalGridSpacingPerMillimeter = 2 ∧
    plot.verticalMinimumMillimeters = 0 ∧
    plot.verticalMaximumMillimeters = 6 ∧
    plot.verticalGridSpacingMillimeters = 1 ∧
    plot.observationColor = .black ∧
    plot.bestFitLineColor = .magenta ∧
    plot.hasGrid = true ∧
    plot.reciprocalSlitSeparationPerMillimeter 0 = 1 ∧
    plot.measuredFringeSpacingMillimeters 0 = 1 / 2 ∧
    plot.reciprocalSlitSeparationPerMillimeter 1 = 5 / 4 ∧
    plot.measuredFringeSpacingMillimeters 1 = 7 / 10 ∧
    plot.reciprocalSlitSeparationPerMillimeter 2 = 5 / 3 ∧
    plot.measuredFringeSpacingMillimeters 2 = 1 ∧
    plot.reciprocalSlitSeparationPerMillimeter 3 = 5 / 2 ∧
    plot.measuredFringeSpacingMillimeters 3 = 13 / 10 ∧
    plot.reciprocalSlitSeparationPerMillimeter 4 = 10 / 3 ∧
    plot.measuredFringeSpacingMillimeters 4 = 17 / 10 ∧
    plot.reciprocalSlitSeparationPerMillimeter 5 = 5 ∧
    plot.measuredFringeSpacingMillimeters 5 = 27 / 10 ∧
    plot.reciprocalSlitSeparationPerMillimeter 6 = 20 / 3 ∧
    plot.measuredFringeSpacingMillimeters 6 = 7 / 2 ∧
    plot.reciprocalSlitSeparationPerMillimeter 7 = 10 ∧
    plot.measuredFringeSpacingMillimeters 7 = 11 / 2 ∧
    areaInSquareMillimeters plot.bestFitSlope = 279 / 500

/--
Calibration connecting graph coordinates to the microscope and fringe-spacing
measurements, together with the equation of the displayed fitted line.
-/
structure SatisfiesMeasurementPlotCalibration
    (setup : DoubleSlitWavelengthExperiment) : Prop where
  horizontalCoordinatesAreReciprocalSeparationReadouts :
    ∀ i : Fin 8,
      setup.plot.reciprocalSlitSeparationPerMillimeter i =
        1 / lengthInMillimeters (setup.slitSeparationD i)
  verticalCoordinatesAreMeasuredFringeReadouts :
    ∀ i : Fin 8,
      setup.plot.measuredFringeSpacingMillimeters i =
        lengthInMillimeters (setup.measuredAdjacentFringeSpacing i)
  bestFitLineEquation :
    ∀ xPerMillimeter : ℝ,
      setup.plot.bestFitLineValueMillimeters xPerMillimeter =
        lengthInMillimeters setup.plot.bestFitIntercept +
          areaInSquareMillimeters setup.plot.bestFitSlope * xPerMillimeter

/--
The governing central-fringe law and its reciprocal-separation-plot form.

For narrow slits in the paraxial Fraunhofer regime,
`Δy = λ L / d`. Consequently a plot of `Δy` against `1 / d` has physical
slope `λ L`. Both relations are stated in every length unit and neither
assigns a problem-specific value to `λ`.
-/
structure SatisfiesParaxialDoubleSlitLaw
    (setup : DoubleSlitWavelengthExperiment) : Prop where
  adjacentBrightFringeLaw :
    ∀ (i : Fin 8) (unit : LengthUnit),
      lengthReadout unit (setup.idealAdjacentFringeSpacing i) =
        lengthReadout unit setup.wavelengthLambda *
            lengthReadout unit setup.screenDistanceL /
          lengthReadout unit (setup.slitSeparationD i)
  reciprocalPlotSlopeLaw :
    ∀ unit : LengthUnit,
      areaReadout unit setup.plot.bestFitSlope =
        lengthReadout unit setup.wavelengthLambda *
          lengthReadout unit setup.screenDistanceL

/-- Labels of the four wavelength choices printed with the question. -/
inductive AnswerChoice where
  | A
  | B
  | C
  | D
  deriving DecidableEq, Repr

/-- Wavelength readout in nanometers printed beside each answer label. -/
def displayedWavelengthNanometers : AnswerChoice → ℝ
  | .A => 620
  | .B => 619
  | .C => 631
  | .D => 618

/-- Agreement of a wavelength with a displayed whole-nanometer choice. -/
def MatchesAnswerToNearestNanometer
    (setup : DoubleSlitWavelengthExperiment) (choice : AnswerChoice) : Prop :=
  |lengthInNanometers setup.wavelengthLambda -
      displayedWavelengthNanometers choice| ≤ 1 / 2

/-- The stated `0.900 m` screen distance is `900 mm`. -/
lemma screenDistanceInMillimeters_eq_nine_hundred
    (setup : DoubleSlitWavelengthExperiment)
    (h_readouts : MatchesProblemReadouts setup) :
    lengthInMillimeters setup.screenDistanceL = 900 := by
  have h_units :
      lengthInMillimeters setup.screenDistanceL =
        1000 * lengthInMeters setup.screenDistanceL := by
    have h := congrArg WithDim.val
      (setup.screenDistanceL.2
        ({ UnitChoices.SI with length := LengthUnit.meters } : UnitChoices)
        ({ UnitChoices.SI with length := LengthUnit.millimeters } : UnitChoices))
    change lengthInMillimeters setup.screenDistanceL =
      _ * lengthInMeters setup.screenDistanceL at h
    norm_num [lengthInMillimeters, lengthInMeters, lengthReadout,
      UnitChoices.dimScale, LengthUnit.millimeters, LengthUnit.meters,
      LengthUnit.scale, LengthUnit.div_eq_val, NNReal.smul_def] at h ⊢
    exact h
  rw [h_units, h_readouts.1]
  norm_num

/--
The calibrated slope `0.558 mm²` and screen distance `900 mm`, combined with
`slope = λ L`, give the laser wavelength `620 nm`.
-/
lemma wavelengthInNanometers_eq_six_hundred_twenty
    (setup : DoubleSlitWavelengthExperiment)
    (h_physical : HasPhysicalConfiguration setup)
    (h_readouts : MatchesProblemReadouts setup)
    (h_plot : MatchesSuppliedPlot setup.plot)
    (h_law : SatisfiesParaxialDoubleSlitLaw setup) :
    lengthInNanometers setup.wavelengthLambda = 620 := by
  have h_screen_mm :
      lengthInMillimeters setup.screenDistanceL = 900 :=
    screenDistanceInMillimeters_eq_nine_hundred setup h_readouts
  have h_slope :
      areaInSquareMillimeters setup.plot.bestFitSlope = 279 / 500 := by
    simp only [MatchesSuppliedPlot] at h_plot
    aesop
  have h_slope_law :=
    h_law.reciprocalPlotSlopeLaw LengthUnit.millimeters
  change areaInSquareMillimeters setup.plot.bestFitSlope =
    lengthInMillimeters setup.wavelengthLambda *
      lengthInMillimeters setup.screenDistanceL at h_slope_law
  have h_wavelength_mm :
      lengthInMillimeters setup.wavelengthLambda = 31 / 50000 := by
    norm_num at h_slope h_slope_law ⊢
    nlinarith
  have h_units :
      lengthInNanometers setup.wavelengthLambda =
        1000000 * lengthInMillimeters setup.wavelengthLambda := by
    have h := congrArg WithDim.val
      (setup.wavelengthLambda.2
        ({ UnitChoices.SI with length := LengthUnit.millimeters } : UnitChoices)
        ({ UnitChoices.SI with length := LengthUnit.nanometers } : UnitChoices))
    change lengthInNanometers setup.wavelengthLambda =
      _ * lengthInMillimeters setup.wavelengthLambda at h
    norm_num [lengthInNanometers, lengthInMillimeters, lengthReadout,
      UnitChoices.dimScale, LengthUnit.nanometers, LengthUnit.millimeters,
      LengthUnit.meters, LengthUnit.scale, LengthUnit.div_eq_val,
      NNReal.smul_def] at h ⊢
    exact h
  rw [h_units, h_wavelength_mm]
  norm_num

/-!
The best-fit line has slope `0.558 mm²`; since `L = 900 mm` and the paraxial
double-slit law gives `slope = λ L`, the wavelength is `620 nm`, answer A.

This formalizes `thm:physics:phyx_mini_0119:target`. The numerical wavelength
and answer label occur only in the conclusion and answer-choice table, never
in the physical, problem-readout, plot-calibration, or governing-law premises.
-/
theorem problem_phyx_mini_0119
    (setup : DoubleSlitWavelengthExperiment)
    (h_physical : HasPhysicalConfiguration setup)
    (h_readouts : MatchesProblemReadouts setup)
    (h_plot : MatchesSuppliedPlot setup.plot)
    (h_calibration : SatisfiesMeasurementPlotCalibration setup)
    (h_law : SatisfiesParaxialDoubleSlitLaw setup) :
    lengthInNanometers setup.wavelengthLambda = 620 ∧
      MatchesAnswerToNearestNanometer setup .A := by
  have h_wavelength :=
    wavelengthInNanometers_eq_six_hundred_twenty
      setup h_physical h_readouts h_plot h_law
  constructor
  · exact h_wavelength
  · simp [MatchesAnswerToNearestNanometer, displayedWavelengthNanometers,
      h_wavelength]

end PhyXMiniProblems.ProblemPhyXMini0119
