import Mathlib.Algebra.Order.Round
import Physlib.ClassicalMechanics.Mass.MassUnit
import Physlib.QuantumMechanics.PlanckConstant
import Physlib.Units.WithDim.Speed

noncomputable section

namespace PhyXMiniProblems.ProblemPhyXMini0500

open Dimension

/-!
# Neutron speed from a double-slit interference trace

Neutrons pass through two slits separated by `0.10 nm`, and a detector is
`3.5 m` beyond the slit plane.  The supplied detector trace has an unlabeled
horizontal position axis, a vertical axis labeled "Neutron intensity", and a
`100 μm` scale bar.  Rounded image coordinates put adjacent central maxima
about `32` pixels apart and the scale bar endpoints `48` pixels apart.

All lengths, the neutron mass, Planck's action, and the neutron speed are
unit-independent physical quantities.  Real numbers occur only as calibrated
unit readouts, image-pixel coordinates, and displayed answer values.  In
particular, the neutron speed is an independent observable and is not defined
from the recorded answer.
-/

/-! ## Physical quantities and calibrated readouts -/

/-- A nonnegative, unit-independent physical quantity with length dimension. -/
abbrev LengthQuantity : Type := Dimensionful (WithDim L𝓭 NNReal)

/-- A nonnegative, unit-independent physical mass. -/
abbrev MassQuantity : Type := Dimensionful (WithDim M𝓭 NNReal)

/-- The dimension of action, `mass * length^2 / time`. -/
def actionDimension : Dimension := M𝓭 * L𝓭 * L𝓭 * T𝓭⁻¹

/-- A nonnegative, unit-independent physical action. -/
abbrev ActionQuantity : Type :=
  Dimensionful (WithDim actionDimension NNReal)

/-- Read a physical length as a real number in a selected length unit. -/
def lengthReadout (unit : LengthUnit) (length : LengthQuantity) : ℝ :=
  ((length {UnitChoices.SI with length := unit}).val : ℝ)

/-- Metre readout of a physical length. -/
def lengthInMeters (length : LengthQuantity) : ℝ :=
  lengthReadout LengthUnit.meters length

/-- Femtometre readout of a physical length. -/
def lengthInFemtometers (length : LengthQuantity) : ℝ :=
  lengthReadout LengthUnit.femtometers length

/-- Nanometre readout of a physical length. -/
def lengthInNanometers (length : LengthQuantity) : ℝ :=
  lengthReadout LengthUnit.nanometers length

/-- Micrometre readout of a physical length. -/
def lengthInMicrometers (length : LengthQuantity) : ℝ :=
  lengthReadout LengthUnit.micrometers length

/-- Kilogram readout of a physical mass. -/
def massInKilograms (mass : MassQuantity) : ℝ :=
  ((mass {UnitChoices.SI with mass := MassUnit.kilograms}).val : ℝ)

/-- Metre-per-second readout of a physical speed. -/
def speedInMetersPerSecond (speed : DimSpeed) : ℝ :=
  ((speed UnitChoices.SI).val : ℝ)

/-- SI readout of an action in joule-seconds. -/
def actionInJouleSeconds (action : ActionQuantity) : ℝ :=
  ((action UnitChoices.SI).val : ℝ)

/-! ## Experimental roles and primary-figure vocabulary -/

/-- The particle species sent through the slits. -/
inductive ParticleSpecies where
  | neutron
  | other
  deriving DecidableEq, Repr

/-- The aperture arrangement used by the experiment. -/
inductive SlitArrangement where
  | twoNarrowParallelSlits
  | other
  deriving DecidableEq, Repr

/-- Approximation regime used for the textbook calculation. -/
inductive PropagationRegime where
  | nonrelativisticParaxial
  | other
  deriving DecidableEq, Repr

/-- The two axes of the detector-output graph. -/
inductive PlotAxis where
  | horizontal
  | vertical
  deriving DecidableEq, Repr

/-- Physical role of an axis in the detector-output graph. -/
inductive PlotAxisRole where
  | transverseDetectorPosition
  | neutronIntensity
  deriving DecidableEq, Repr

/-- Horizontal landmarks measured in the supplied raster. -/
inductive FigureLandmark where
  | firstLeftIntensityMaximum
  | centralIntensityMaximum
  | firstRightIntensityMaximum
  | scaleBarLeftEndpoint
  | scaleBarRightEndpoint
  deriving DecidableEq, Fintype, Repr

/-!
Qualitative graph information and rounded horizontal pixel coordinates from
the primary image.  The `scaleBarLength` is a physical detector length; the
pixel coordinates are dimensionless raster readouts.
-/
structure NeutronDetectorFigure where
  axisRole : PlotAxis → PlotAxisRole
  axisHasPrintedLabel : PlotAxis → Bool
  horizontalPixelAt : FigureLandmark → ℝ
  scaleBarLength : LengthQuantity
  severalResolvedIntensityMaxima : Bool
  largestMaximumNearCenter : Bool
  approximatelySymmetricEnvelope : Bool
  peakAmplitudeFallsAwayFromCenter : Bool

/-!
Independent physical quantities of the experiment.  The inferred adjacent
fringe spacing, matter wavelength, and neutron speed are fields rather than
definitions; the calibration, interference, and de Broglie hypotheses below
relate them.
-/
structure NeutronDoubleSlitSetup where
  particleSpecies : ParticleSpecies
  slitArrangement : SlitArrangement
  regime : PropagationRegime
  slitSeparation : LengthQuantity
  slitToDetectorDistance : LengthQuantity
  adjacentBrightFringeSpacing : LengthQuantity
  matterWavelength : LengthQuantity
  particleMass : MassQuantity
  planckAction : ActionQuantity
  neutronSpeed : DimSpeed
  figure : NeutronDetectorFigure
  neutronsShotThroughSlits : Bool
  detectorRecordsTransmittedNeutrons : Bool

/-! ## Scenario, source data, figure readouts, and governing laws -/

/-- Qualitative physical scenario and approximation selected by the problem. -/
structure MatchesNeutronDoubleSlitScenario
    (setup : NeutronDoubleSlitSetup) : Prop where
  particleIsNeutron : setup.particleSpecies = .neutron
  usesTwoNarrowSlits : setup.slitArrangement = .twoNarrowParallelSlits
  neutronBeamPassesThroughSlits : setup.neutronsShotThroughSlits = true
  downstreamDetectorRecordsBeam :
    setup.detectorRecordsTransmittedNeutrons = true
  textbookRegime : setup.regime = .nonrelativisticParaxial

/-!
The two calibrated lengths stated in the prose.  This premise contains no
fringe spacing, wavelength, neutron speed, or answer choice.
-/
structure MatchesProblemLengthReadouts
    (setup : NeutronDoubleSlitSetup) : Prop where
  slitSeparationNanometers :
    lengthInNanometers setup.slitSeparation = 0.10
  detectorDistanceMeters :
    lengthInMeters setup.slitToDetectorDistance = 3.5

/-!
Rounded landmark coordinates measured from the `508 × 278` source raster and
the physical label on its scale bar.  The maxima used for calibration are
adjacent peaks near the center.  These are figure/data readouts, not a speed
or wavelength conclusion.
-/
structure MatchesSuppliedDetectorFigure
    (figure : NeutronDetectorFigure) : Prop where
  horizontalRole :
    figure.axisRole .horizontal = .transverseDetectorPosition
  verticalRole : figure.axisRole .vertical = .neutronIntensity
  horizontalAxisUnlabeled :
    figure.axisHasPrintedLabel .horizontal = false
  verticalAxisLabeled : figure.axisHasPrintedLabel .vertical = true
  leftAdjacentPeakPixel :
    figure.horizontalPixelAt .firstLeftIntensityMaximum = 223
  centralPeakPixel :
    figure.horizontalPixelAt .centralIntensityMaximum = 256
  rightAdjacentPeakPixel :
    figure.horizontalPixelAt .firstRightIntensityMaximum = 288
  scaleBarLeftPixel :
    figure.horizontalPixelAt .scaleBarLeftEndpoint = 385
  scaleBarRightPixel :
    figure.horizontalPixelAt .scaleBarRightEndpoint = 433
  scaleBarMicrometers : lengthInMicrometers figure.scaleBarLength = 100
  resolvedPeaks : figure.severalResolvedIntensityMaxima = true
  centralMaximumLargest : figure.largestMaximumNearCenter = true
  symmetricEnvelope : figure.approximatelySymmetricEnvelope = true
  outerPeaksSmaller : figure.peakAmplitudeFallsAwayFromCenter = true

/-!
Standard reference data used by the calculation.  Physlib supplies the
reduced Planck constant `Constants.ℏ` in joule-seconds, so the ordinary Planck
action is `2πℏ`.  The neutron mass uses its standard SI value.  Neither datum
contains the requested speed.
-/
structure UsesStandardNeutronReferenceData
    (setup : NeutronDoubleSlitSetup) : Prop where
  neutronMassKilograms :
    massInKilograms setup.particleMass = 1.67492749804e-27
  planckActionJouleSeconds :
    actionInJouleSeconds setup.planckAction =
      2 * Real.pi * (Constants.ℏ : ℝ)

/-- Positivity conditions selecting a physically meaningful experiment. -/
structure HasPhysicalNeutronInterferenceParameters
    (setup : NeutronDoubleSlitSetup) : Prop where
  positiveSlitSeparation : 0 < lengthInMeters setup.slitSeparation
  positiveDetectorDistance :
    0 < lengthInMeters setup.slitToDetectorDistance
  positiveFringeSpacing :
    0 < lengthInMeters setup.adjacentBrightFringeSpacing
  positiveWavelength : 0 < lengthInMeters setup.matterWavelength
  positiveParticleMass : 0 < massInKilograms setup.particleMass
  positivePlanckAction : 0 < actionInJouleSeconds setup.planckAction
  positiveNeutronSpeed : 0 < speedInMetersPerSecond setup.neutronSpeed

/-!
The three governing relations used in the calculation:

* a linear image calibration converts the central peak spacing from pixels
  into a detector length using the `100 μm` bar;
* adjacent paraxial double-slit maxima obey `Δy d = L λ`;
* nonrelativistic neutrons obey de Broglie's relation `λ m v = h`.

The first two relations are stated in arbitrary length units.  These laws do
not specialize the speed, wavelength, fringe spacing, or answer label to the
current problem's result.
-/
structure SatisfiesNeutronInterferenceLaws
    (setup : NeutronDoubleSlitSetup) : Prop where
  linearFigureCalibration : ∀ unit : LengthUnit,
    lengthReadout unit setup.adjacentBrightFringeSpacing *
        (setup.figure.horizontalPixelAt .scaleBarRightEndpoint -
          setup.figure.horizontalPixelAt .scaleBarLeftEndpoint) =
      lengthReadout unit setup.figure.scaleBarLength *
        (setup.figure.horizontalPixelAt .firstRightIntensityMaximum -
          setup.figure.horizontalPixelAt .centralIntensityMaximum)
  paraxialAdjacentFringeLaw : ∀ unit : LengthUnit,
    lengthReadout unit setup.adjacentBrightFringeSpacing *
        lengthReadout unit setup.slitSeparation =
      lengthReadout unit setup.slitToDetectorDistance *
        lengthReadout unit setup.matterWavelength
  deBroglieMatterWaveLaw :
    lengthInMeters setup.matterWavelength *
          massInKilograms setup.particleMass *
          speedInMetersPerSecond setup.neutronSpeed =
      actionInJouleSeconds setup.planckAction

/-! ## Displayed choices and current target -/

/-- Labels of the four speed choices supplied with the problem. -/
inductive AnswerChoice where
  | A
  | B
  | C
  | D
  deriving DecidableEq, Fintype, Repr

/-- Displayed speeds in metres per second. -/
def displayedSpeedInMetersPerSecond : AnswerChoice → ℝ
  | .A => 150
  | .B => 170
  | .C => 200
  | .D => 120

/-- The answer label recorded by the source dataset. -/
def recordedDatasetAnswer : AnswerChoice := .C

/-!
`reported` is `value` rounded to one significant figure when it is a single
nonzero decimal digit times a power of ten and ordinary nearest-place rounding
of `value` gives that number.
-/
def RoundsToOneSignificantFigure (value reported : ℝ) : Prop :=
  ∃ (digit : ℕ) (exponent : ℤ),
    1 ≤ digit ∧ digit ≤ 9 ∧
      let placeValue : ℝ := (10 : ℝ) ^ exponent
      reported = (digit : ℝ) * placeValue ∧
        ((round (value / placeValue) : ℤ) : ℝ) * placeValue = reported

/-- A displayed choice agrees with the modeled speed to one significant figure. -/
def MatchesDisplayedSpeed
    (setup : NeutronDoubleSlitSetup) (choice : AnswerChoice) : Prop :=
  RoundsToOneSignificantFigure
    (speedInMetersPerSecond setup.neutronSpeed)
    (displayedSpeedInMetersPerSecond choice)

/-!
The primary-image calibration first determines an adjacent central-fringe
spacing of `100 μm × 32/48 = 200/3 μm`.
-/
lemma adjacent_fringe_spacing_micrometers_eq
    (setup : NeutronDoubleSlitSetup)
    (h_figure : MatchesSuppliedDetectorFigure setup.figure)
    (h_laws : SatisfiesNeutronInterferenceLaws setup) :
    lengthInMicrometers setup.adjacentBrightFringeSpacing = 200 / 3 := by
  have h := h_laws.linearFigureCalibration LengthUnit.micrometers
  change
    lengthInMicrometers setup.adjacentBrightFringeSpacing *
        (setup.figure.horizontalPixelAt .scaleBarRightEndpoint -
          setup.figure.horizontalPixelAt .scaleBarLeftEndpoint) =
      lengthInMicrometers setup.figure.scaleBarLength *
        (setup.figure.horizontalPixelAt .firstRightIntensityMaximum -
          setup.figure.horizontalPixelAt .centralIntensityMaximum) at h
  rw [h_figure.scaleBarRightPixel, h_figure.scaleBarLeftPixel,
    h_figure.scaleBarMicrometers, h_figure.rightAdjacentPeakPixel,
    h_figure.centralPeakPixel] at h
  norm_num at h ⊢
  linarith

/-!
Combining that calibrated fringe spacing with `d = 0.10 nm`, `L = 3.5 m`,
and the paraxial double-slit law gives `λ = 40/21 fm`.
-/
lemma matter_wavelength_femtometers_eq
    (setup : NeutronDoubleSlitSetup)
    (h_readouts : MatchesProblemLengthReadouts setup)
    (h_figure : MatchesSuppliedDetectorFigure setup.figure)
    (h_laws : SatisfiesNeutronInterferenceLaws setup) :
    lengthInFemtometers setup.matterWavelength = 40 / 21 := by
  have femto_eq_nano (q : LengthQuantity) :
      lengthInFemtometers q = 1000000 * lengthInNanometers q := by
    have h := q.2
      {UnitChoices.SI with length := LengthUnit.nanometers}
      {UnitChoices.SI with length := LengthUnit.femtometers}
    have hval := congrArg
      (fun x : WithDim L𝓭 NNReal => (x.val : ℝ)) h
    change lengthInFemtometers q =
      ((UnitChoices.dimScale
        {UnitChoices.SI with length := LengthUnit.nanometers}
        {UnitChoices.SI with length := LengthUnit.femtometers} L𝓭) •
          (q {UnitChoices.SI with length := LengthUnit.nanometers})).val at hval
    norm_num [UnitChoices.dimScale, LengthUnit.nanometers,
      LengthUnit.femtometers, LengthUnit.meters, LengthUnit.scale,
      LengthUnit.div_eq_val] at hval
    rw [hval]
    norm_num [lengthInNanometers, lengthReadout, LengthUnit.nanometers,
      LengthUnit.scale, LengthUnit.meters]
    left
    rfl
  have femto_eq_micro (q : LengthQuantity) :
      lengthInFemtometers q = 1000000000 * lengthInMicrometers q := by
    have h := q.2
      {UnitChoices.SI with length := LengthUnit.micrometers}
      {UnitChoices.SI with length := LengthUnit.femtometers}
    have hval := congrArg
      (fun x : WithDim L𝓭 NNReal => (x.val : ℝ)) h
    change lengthInFemtometers q =
      ((UnitChoices.dimScale
        {UnitChoices.SI with length := LengthUnit.micrometers}
        {UnitChoices.SI with length := LengthUnit.femtometers} L𝓭) •
          (q {UnitChoices.SI with length := LengthUnit.micrometers})).val at hval
    norm_num [UnitChoices.dimScale, LengthUnit.micrometers,
      LengthUnit.femtometers, LengthUnit.meters, LengthUnit.scale,
      LengthUnit.div_eq_val] at hval
    rw [hval]
    norm_num [lengthInMicrometers, lengthReadout, LengthUnit.micrometers,
      LengthUnit.scale, LengthUnit.meters]
    left
    rfl
  have femto_eq_meter (q : LengthQuantity) :
      lengthInFemtometers q = 1000000000000000 * lengthInMeters q := by
    have h := q.2
      {UnitChoices.SI with length := LengthUnit.meters}
      {UnitChoices.SI with length := LengthUnit.femtometers}
    have hval := congrArg
      (fun x : WithDim L𝓭 NNReal => (x.val : ℝ)) h
    change lengthInFemtometers q =
      ((UnitChoices.dimScale
        {UnitChoices.SI with length := LengthUnit.meters}
        {UnitChoices.SI with length := LengthUnit.femtometers} L𝓭) •
          (q {UnitChoices.SI with length := LengthUnit.meters})).val at hval
    norm_num [UnitChoices.dimScale, LengthUnit.femtometers,
      LengthUnit.meters, LengthUnit.scale, LengthUnit.div_eq_val] at hval
    rw [hval]
    norm_num [lengthInMeters, lengthReadout, LengthUnit.meters]
    left
    rfl
  have h_spacing :=
    adjacent_fringe_spacing_micrometers_eq setup h_figure h_laws
  have h_law := h_laws.paraxialAdjacentFringeLaw LengthUnit.femtometers
  change
    lengthInFemtometers setup.adjacentBrightFringeSpacing *
        lengthInFemtometers setup.slitSeparation =
      lengthInFemtometers setup.slitToDetectorDistance *
        lengthInFemtometers setup.matterWavelength at h_law
  rw [femto_eq_micro, h_spacing, femto_eq_nano,
    h_readouts.slitSeparationNanometers, femto_eq_meter,
    h_readouts.detectorDistanceMeters] at h_law
  norm_num at h_law ⊢
  linarith

/-!
The literal `0.10 nm` slit separation, calibrated pattern, double-slit
relation, de Broglie relation, and standard constants put the neutron speed in
the nearest-`10^8 m/s` interval that rounds to `2 × 10^8 m/s`.  This is not the
nearest-hundred interval associated with the source's recorded choice C.
-/
lemma neutron_speed_in_literal_data_rounding_interval
    (setup : NeutronDoubleSlitSetup)
    (h_physical : HasPhysicalNeutronInterferenceParameters setup)
    (h_readouts : MatchesProblemLengthReadouts setup)
    (h_figure : MatchesSuppliedDetectorFigure setup.figure)
    (h_reference : UsesStandardNeutronReferenceData setup)
    (h_laws : SatisfiesNeutronInterferenceLaws setup) :
    150000000 ≤ speedInMetersPerSecond setup.neutronSpeed ∧
      speedInMetersPerSecond setup.neutronSpeed < 250000000 := by
  have femto_eq_meter (q : LengthQuantity) :
      lengthInFemtometers q = 1000000000000000 * lengthInMeters q := by
    have h := q.2
      {UnitChoices.SI with length := LengthUnit.meters}
      {UnitChoices.SI with length := LengthUnit.femtometers}
    have hval := congrArg
      (fun x : WithDim L𝓭 NNReal => (x.val : ℝ)) h
    change lengthInFemtometers q =
      ((UnitChoices.dimScale
        {UnitChoices.SI with length := LengthUnit.meters}
        {UnitChoices.SI with length := LengthUnit.femtometers} L𝓭) •
          (q {UnitChoices.SI with length := LengthUnit.meters})).val at hval
    norm_num [UnitChoices.dimScale, LengthUnit.femtometers,
      LengthUnit.meters, LengthUnit.scale, LengthUnit.div_eq_val] at hval
    rw [hval]
    norm_num [lengthInMeters, lengthReadout, LengthUnit.meters]
    left
    rfl
  have h_wave_fm :=
    matter_wavelength_femtometers_eq setup h_readouts h_figure h_laws
  have h_wave_scale := femto_eq_meter setup.matterWavelength
  rw [h_wave_fm] at h_wave_scale
  have h_wave_m :
      lengthInMeters setup.matterWavelength = (40 / 21) * 1e-15 := by
    norm_num at h_wave_scale ⊢
    linarith
  have h_deBroglie := h_laws.deBroglieMatterWaveLaw
  rw [h_wave_m, h_reference.neutronMassKilograms,
    h_reference.planckActionJouleSeconds] at h_deBroglie
  norm_num [Constants.ℏ] at h_deBroglie
  have pi_lower : (5 / 2 : ℝ) < Real.pi := by
    have hbound := Real.cos_bound (x := (5 / 8 : ℝ)) (by norm_num)
    have habs := abs_le.mp hbound
    have hcospos : 0 < Real.cos (5 / 8 : ℝ) :=
      Real.cos_pos_of_le_one (by norm_num)
    have hcosfivefour : 0 < Real.cos (5 / 4 : ℝ) := by
      rw [show (5 / 4 : ℝ) = 2 * (5 / 8) by norm_num,
        Real.cos_two_mul]
      norm_num at habs
      nlinarith
    by_contra hpi
    have hpi' : Real.pi ≤ (5 / 2 : ℝ) := le_of_not_gt hpi
    have hx1 : Real.pi / 2 ≤ (5 / 4 : ℝ) := by linarith
    have hx2 : (5 / 4 : ℝ) ≤ Real.pi + Real.pi / 2 := by
      nlinarith [Real.two_le_pi]
    have hnonpos :=
      Real.cos_nonpos_of_pi_div_two_le_of_le hx1 hx2
    linarith
  have pi_upper : Real.pi < (7 / 2 : ℝ) := by
    have hbound := Real.cos_bound (x := (7 / 8 : ℝ)) (by norm_num)
    have habs := abs_le.mp hbound
    have hcospos : 0 < Real.cos (7 / 8 : ℝ) :=
      Real.cos_pos_of_le_one (by norm_num)
    have hcossevenfour : Real.cos (7 / 4 : ℝ) < 0 := by
      rw [show (7 / 4 : ℝ) = 2 * (7 / 8) by norm_num,
        Real.cos_two_mul]
      norm_num at habs
      nlinarith
    by_contra hpi
    have hpi' : (7 / 2 : ℝ) ≤ Real.pi := le_of_not_gt hpi
    have hx2 : (7 / 4 : ℝ) ≤ Real.pi / 2 := by linarith
    have hx1 : -(Real.pi / 2) ≤ (7 / 4 : ℝ) := by
      nlinarith [Real.pi_pos]
    have hnonneg :=
      Real.cos_nonneg_of_neg_pi_div_two_le_of_le hx1 hx2
    linarith
  constructor <;> nlinarith

/-!
The figure-derived spacing is `200/3 μm`, the corresponding neutron matter
wavelength is `40/21 fm`, and the literal source data together with de
Broglie's relation give about `2.08 × 10^8 m/s`, hence `2 × 10^8 m/s` to one
significant figure.  None of the displayed values, all near `200 m/s`, matches
that result.  The recorded choice C remains represented only by
`recordedDatasetAnswer`.

This formalizes `thm:physics:phyx_mini_0500:target`.  Neither the derived
spacing, wavelength, speed interval, rounded speed, nor failure of the answer
choices occurs in a scenario, figure, reference-data, positivity, or
governing-law premise.
-/
theorem problem_phyx_mini_0500
    (setup : NeutronDoubleSlitSetup)
    (h_scenario : MatchesNeutronDoubleSlitScenario setup)
    (h_physical : HasPhysicalNeutronInterferenceParameters setup)
    (h_readouts : MatchesProblemLengthReadouts setup)
    (h_figure : MatchesSuppliedDetectorFigure setup.figure)
    (h_reference : UsesStandardNeutronReferenceData setup)
    (h_laws : SatisfiesNeutronInterferenceLaws setup) :
    lengthInMicrometers setup.adjacentBrightFringeSpacing = 200 / 3 ∧
      lengthInFemtometers setup.matterWavelength = 40 / 21 ∧
      (150000000 ≤ speedInMetersPerSecond setup.neutronSpeed ∧
        speedInMetersPerSecond setup.neutronSpeed < 250000000) ∧
      RoundsToOneSignificantFigure
        (speedInMetersPerSecond setup.neutronSpeed) 200000000 ∧
      (∀ choice : AnswerChoice, ¬ MatchesDisplayedSpeed setup choice) := by
  have h_spacing :=
    adjacent_fringe_spacing_micrometers_eq setup h_figure h_laws
  have h_wave :=
    matter_wavelength_femtometers_eq setup h_readouts h_figure h_laws
  have h_interval :=
    neutron_speed_in_literal_data_rounding_interval setup h_physical
      h_readouts h_figure h_reference h_laws
  have h_round :
      RoundsToOneSignificantFigure
        (speedInMetersPerSecond setup.neutronSpeed) 200000000 := by
    refine ⟨2, 8, by norm_num, by norm_num, ?_⟩
    dsimp
    constructor
    · norm_num
    · rw [round_eq]
      have hfloor :
          ⌊speedInMetersPerSecond setup.neutronSpeed / 100000000 +
              1 / 2⌋ = (2 : ℤ) := by
        rw [Int.floor_eq_iff]
        constructor <;> norm_num <;> linarith [h_interval.1, h_interval.2]
      norm_num at hfloor ⊢
      rw [hfloor]
      norm_num
  have no_small_report (reported : ℝ)
      (hreported_pos : 0 < reported) (hreported_le : reported ≤ 200) :
      ¬ RoundsToOneSignificantFigure
        (speedInMetersPerSecond setup.neutronSpeed) reported := by
    rintro ⟨digit, exponent, hdigit_one, _hdigit_nine,
      hreported, hround⟩
    let placeValue : ℝ := (10 : ℝ) ^ exponent
    have hplace_pos : 0 < placeValue := by
      exact zpow_pos (by norm_num) exponent
    have hdigit_real : (1 : ℝ) ≤ digit := by exact_mod_cast hdigit_one
    have hround_real :
        ((round
          (speedInMetersPerSecond setup.neutronSpeed / placeValue) : ℤ) : ℝ) =
            digit := by
      dsimp [placeValue] at hreported hround ⊢
      nlinarith
    have hround_int :
        round (speedInMetersPerSecond setup.neutronSpeed / placeValue) =
          (digit : ℤ) := by
      exact_mod_cast hround_real
    rw [round_eq] at hround_int
    have hfloor_bounds := Int.floor_eq_iff.mp hround_int
    have hquotient_upper :
        speedInMetersPerSecond setup.neutronSpeed / placeValue <
          (digit : ℝ) + 1 / 2 := by
      norm_num at hfloor_bounds ⊢
      linarith
    have hspeed_upper :
        speedInMetersPerSecond setup.neutronSpeed <
          ((digit : ℝ) + 1 / 2) * placeValue :=
      (div_lt_iff₀ hplace_pos).mp hquotient_upper
    have hplace_le_reported : placeValue ≤ reported := by
      calc
        placeValue = 1 * placeValue := by ring
        _ ≤ (digit : ℝ) * placeValue :=
          mul_le_mul_of_nonneg_right hdigit_real hplace_pos.le
        _ = reported := hreported.symm
    have hspeed_below_three_hundred :
        speedInMetersPerSecond setup.neutronSpeed < 300 := by
      calc
        speedInMetersPerSecond setup.neutronSpeed <
            ((digit : ℝ) + 1 / 2) * placeValue := hspeed_upper
        _ = reported + placeValue / 2 := by
          rw [hreported]
          ring
        _ ≤ reported + reported / 2 := by
          gcongr
        _ ≤ 300 := by linarith
    linarith [h_interval.1]
  have h_no_choice :
      ∀ choice : AnswerChoice, ¬ MatchesDisplayedSpeed setup choice := by
    intro choice
    unfold MatchesDisplayedSpeed
    cases choice <;>
      apply no_small_report <;>
      norm_num [displayedSpeedInMetersPerSecond]
  exact ⟨h_spacing, h_wave, h_interval, h_round, h_no_choice⟩

end PhyXMiniProblems.ProblemPhyXMini0500
