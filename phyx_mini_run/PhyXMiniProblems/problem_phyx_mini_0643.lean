import Mathlib.Algebra.Order.Round
import Physlib.ClassicalMechanics.Mass.MassUnit
import Physlib.QuantumMechanics.PlanckConstant
import Physlib.SpaceAndTime.Space.LengthUnit
import Physlib.Units.WithDim.Speed

noncomputable section

namespace PhyXMiniProblems.ProblemPhyXMini0643

open Dimension

/-!
# Neutron speed from a double-slit detector trace

Neutrons pass through two slits separated by `0.10 nm`, and a detector is
`3.5 m` beyond the slit plane.  The supplied `770 × 394` raster has an
unlabelled horizontal detector-position axis, a vertical axis labelled
"Neutron intensity", several resolved maxima, and a scale bar labelled
`100 μm`.

Rounded image coordinates put the adjacent central maxima at horizontal
pixels `365`, `422`, and `476`; the scale-bar endpoints are at pixels `640`
and `724`.  Averaging the two central peak spacings therefore gives a physical
fringe spacing of `100 μm * (476 - 365) / (2 * (724 - 640))`.

Lengths, mass, ordinary Planck action, and neutron speed are represented by
unit-independent Physlib quantities.  Real numbers occur only at explicit
unit-readout boundaries, as dimensionless raster coordinates, or as displayed
answer values.  The requested speed is an independent field constrained by
general interference and de Broglie laws; it is not defined from answer B.
-/

/-! ## Dimensionful physical quantities and named-unit readouts -/

/-- A nonnegative, unit-independent physical length. -/
abbrev LengthQuantity : Type :=
  Dimensionful (WithDim L𝓭 NNReal)

/-- A nonnegative, unit-independent physical mass. -/
abbrev MassQuantity : Type :=
  Dimensionful (WithDim M𝓭 NNReal)

/-- The dimension of action, `M L² T⁻¹`, carried by Planck's constant. -/
def actionDimension : Dimension :=
  M𝓭 * L𝓭 * L𝓭 * T𝓭⁻¹

/-- A nonnegative, unit-independent physical action. -/
abbrev ActionQuantity : Type :=
  Dimensionful (WithDim actionDimension NNReal)

/-- Read a physical length in a selected named length unit. -/
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

/-- Coherent-SI readout of an action, in joule-seconds. -/
def actionInJouleSeconds (action : ActionQuantity) : ℝ :=
  ((action UnitChoices.SI).val : ℝ)

/-! ## Experiment roles and primary-figure vocabulary -/

/-- Particle species sent through the slits. -/
inductive ParticleSpecies where
  | neutron
  | other
  deriving DecidableEq, Repr

/-- Aperture arrangement used by the experiment. -/
inductive SlitArrangement where
  | twoNarrowParallelSlits
  | other
  deriving DecidableEq, Repr

/-- Approximation regime used by the textbook calculation. -/
inductive PropagationRegime where
  | nonrelativisticParaxial
  | other
  deriving DecidableEq, Repr

/-- The two axes of the detector-output graph. -/
inductive PlotAxis where
  | horizontal
  | vertical
  deriving DecidableEq, Repr

/-- Physical role assigned to an axis of the detector-output graph. -/
inductive PlotAxisRole where
  | transverseDetectorPosition
  | neutronIntensity
  deriving DecidableEq, Repr

/-- Printed labels whose presence is relevant to the detector graph. -/
inductive PlotLabel where
  | neutronIntensity
  | oneHundredMicrometerScale
  | other
  deriving DecidableEq, Repr

/-- Horizontal landmarks measured from the supplied raster. -/
inductive FigureLandmark where
  | firstLeftIntensityMaximum
  | centralIntensityMaximum
  | firstRightIntensityMaximum
  | scaleBarLeftEndpoint
  | scaleBarRightEndpoint
  deriving DecidableEq, Fintype, Repr

/-!
Presentation-level information from the primary figure.  Pixel coordinates
are dimensionless raster measurements, whereas `scaleBarLength` is a genuine
physical detector length.
-/
structure NeutronDetectorFigure where
  rasterWidthPixels : ℕ
  rasterHeightPixels : ℕ
  axisRole : PlotAxis → PlotAxisRole
  axisHasPrintedLabel : PlotAxis → Bool
  verticalAxisLabel : PlotLabel
  scaleBarLabel : PlotLabel
  horizontalPixelAt : FigureLandmark → ℝ
  scaleBarLength : LengthQuantity
  severalResolvedIntensityMaxima : Bool
  largestMaximumNearCenter : Bool
  approximatelySymmetricEnvelope : Bool
  peakAmplitudeFallsAwayFromCenter : Bool

/-!
Independent physical quantities in the experiment.  The inferred adjacent
fringe spacing, matter wavelength, and neutron speed are fields rather than
definitions; the calibration and governing-law premises below relate them.
-/
structure NeutronDoubleSlitSetup where
  particleSpecies : ParticleSpecies
  slitArrangement : SlitArrangement
  regime : PropagationRegime
  slitSeparation : LengthQuantity
  slitToDetectorDistance : LengthQuantity
  adjacentBrightFringeSpacing : LengthQuantity
  matterWavelength : LengthQuantity
  neutronMass : MassQuantity
  ordinaryPlanckAction : ActionQuantity
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
The two calibrated physical lengths stated in the prose.  This premise
contains no fringe spacing, wavelength, neutron speed, or answer choice.
-/
structure MatchesProblemLengthReadouts
    (setup : NeutronDoubleSlitSetup) : Prop where
  slitSeparationNanometers :
    lengthInNanometers setup.slitSeparation = 0.10
  detectorDistanceMeters :
    lengthInMeters setup.slitToDetectorDistance = 3.5

/-!
Rounded landmark coordinates measured from image 643 and the physical label
on its scale bar.  The two central peak intervals are averaged to reduce the
one-pixel asymmetry introduced by rasterization.  These are figure/data
readouts, not wavelength or speed conclusions.
-/
structure MatchesSuppliedDetectorFigure
    (figure : NeutronDetectorFigure) : Prop where
  rasterDimensions :
    figure.rasterWidthPixels = 770 ∧ figure.rasterHeightPixels = 394
  horizontalRole :
    figure.axisRole .horizontal = .transverseDetectorPosition
  verticalRole : figure.axisRole .vertical = .neutronIntensity
  horizontalAxisUnlabelled :
    figure.axisHasPrintedLabel .horizontal = false
  verticalAxisLabelled : figure.axisHasPrintedLabel .vertical = true
  verticalLabelText : figure.verticalAxisLabel = .neutronIntensity
  scaleBarLabelText : figure.scaleBarLabel = .oneHundredMicrometerScale
  leftAdjacentPeakPixel :
    figure.horizontalPixelAt .firstLeftIntensityMaximum = 365
  centralPeakPixel :
    figure.horizontalPixelAt .centralIntensityMaximum = 422
  rightAdjacentPeakPixel :
    figure.horizontalPixelAt .firstRightIntensityMaximum = 476
  scaleBarLeftPixel :
    figure.horizontalPixelAt .scaleBarLeftEndpoint = 640
  scaleBarRightPixel :
    figure.horizontalPixelAt .scaleBarRightEndpoint = 724
  scaleBarMicrometers : lengthInMicrometers figure.scaleBarLength = 100
  resolvedPeaks : figure.severalResolvedIntensityMaxima = true
  centralMaximumLargest : figure.largestMaximumNearCenter = true
  symmetricEnvelope : figure.approximatelySymmetricEnvelope = true
  outerPeaksSmaller : figure.peakAmplitudeFallsAwayFromCenter = true

/-!
Standard reference data used by the calculation.  Physlib provides the scalar
reduced Planck constant `Constants.ℏ` in joule-seconds, so the ordinary Planck
action has SI readout `2 π ℏ`.  Neither calibration contains the requested
speed.
-/
structure UsesStandardNeutronReferenceData
    (setup : NeutronDoubleSlitSetup) : Prop where
  neutronMassKilograms :
    massInKilograms setup.neutronMass = 1.67492749804e-27
  ordinaryPlanckActionJouleSeconds :
    actionInJouleSeconds setup.ordinaryPlanckAction =
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
  positiveNeutronMass : 0 < massInKilograms setup.neutronMass
  positivePlanckAction :
    0 < actionInJouleSeconds setup.ordinaryPlanckAction
  positiveNeutronSpeed : 0 < speedInMetersPerSecond setup.neutronSpeed

/-!
The three general governing relations used in the calculation:

* linear image calibration converts the average of the two central peak
  intervals into a physical detector length using the `100 μm` bar;
* adjacent paraxial double-slit maxima obey `Δy d = L λ`;
* nonrelativistic neutrons obey de Broglie's relation `λ m v = h`.

The first two relations are stated in arbitrary length units.  They do not
specialize any unknown to the result requested by this problem.
-/
structure SatisfiesNeutronInterferenceLaws
    (setup : NeutronDoubleSlitSetup) : Prop where
  linearFigureCalibration : ∀ unit : LengthUnit,
    2 * lengthReadout unit setup.adjacentBrightFringeSpacing *
        (setup.figure.horizontalPixelAt .scaleBarRightEndpoint -
          setup.figure.horizontalPixelAt .scaleBarLeftEndpoint) =
      lengthReadout unit setup.figure.scaleBarLength *
        (setup.figure.horizontalPixelAt .firstRightIntensityMaximum -
          setup.figure.horizontalPixelAt .firstLeftIntensityMaximum)
  paraxialAdjacentFringeLaw : ∀ unit : LengthUnit,
    lengthReadout unit setup.adjacentBrightFringeSpacing *
        lengthReadout unit setup.slitSeparation =
      lengthReadout unit setup.slitToDetectorDistance *
        lengthReadout unit setup.matterWavelength
  deBroglieMatterWaveLaw :
    lengthInMeters setup.matterWavelength *
          massInKilograms setup.neutronMass *
          speedInMetersPerSecond setup.neutronSpeed =
      actionInJouleSeconds setup.ordinaryPlanckAction

/-! ## Displayed choices and current target -/

/-- Labels of the four speed choices supplied with the problem. -/
inductive AnswerChoice where
  | A
  | B
  | C
  | D
  deriving DecidableEq, Fintype, Repr

/-- Speed in metres per second printed beside each answer label. -/
def displayedSpeedInMetersPerSecond : AnswerChoice → ℝ
  | .A => 150
  | .B => 200
  | .C => 250
  | .D => 300

/-- Answer label recorded by the source dataset, retained as metadata only. -/
def recordedDatasetAnswer : AnswerChoice := .B

/-!
`reported` is `value` rounded to one significant figure when it consists of
one nonzero decimal digit times a power of ten and ordinary nearest-place
rounding of `value` gives that number.
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
The primary-image calibration gives an averaged adjacent fringe spacing
`100 μm * 111 / (2 * 84) = 925/14 μm`.
-/
lemma adjacent_fringe_spacing_micrometers_eq
    (setup : NeutronDoubleSlitSetup)
    (h_figure : MatchesSuppliedDetectorFigure setup.figure)
    (h_laws : SatisfiesNeutronInterferenceLaws setup) :
    lengthInMicrometers setup.adjacentBrightFringeSpacing = 925 / 14 := by
  have h := h_laws.linearFigureCalibration LengthUnit.micrometers
  change
    2 * lengthInMicrometers setup.adjacentBrightFringeSpacing *
        (setup.figure.horizontalPixelAt .scaleBarRightEndpoint -
          setup.figure.horizontalPixelAt .scaleBarLeftEndpoint) =
      lengthInMicrometers setup.figure.scaleBarLength *
        (setup.figure.horizontalPixelAt .firstRightIntensityMaximum -
          setup.figure.horizontalPixelAt .firstLeftIntensityMaximum) at h
  rw [h_figure.scaleBarRightPixel, h_figure.scaleBarLeftPixel,
    h_figure.scaleBarMicrometers, h_figure.rightAdjacentPeakPixel,
    h_figure.leftAdjacentPeakPixel] at h
  norm_num at h ⊢
  linarith

/-!
Combining that calibrated fringe spacing with `d = 0.10 nm`, `L = 3.5 m`,
and the paraxial double-slit law gives `λ = 185/98 fm`.
-/
lemma matter_wavelength_femtometers_eq
    (setup : NeutronDoubleSlitSetup)
    (h_readouts : MatchesProblemLengthReadouts setup)
    (h_figure : MatchesSuppliedDetectorFigure setup.figure)
    (h_laws : SatisfiesNeutronInterferenceLaws setup) :
    lengthInFemtometers setup.matterWavelength = 185 / 98 := by
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
Substituting the image-derived wavelength, the standard neutron mass, and
ordinary Planck action into the de Broglie law gives the exact SI expression
below.  In particular, the source's literal `0.10 nm` datum makes the result
about `2.1 × 10^8 m/s`, rather than any of the displayed speeds.
-/
lemma neutron_speed_meters_per_second_eq
    (setup : NeutronDoubleSlitSetup)
    (h_physical : HasPhysicalNeutronInterferenceParameters setup)
    (h_readouts : MatchesProblemLengthReadouts setup)
    (h_figure : MatchesSuppliedDetectorFigure setup.figure)
    (h_reference : UsesStandardNeutronReferenceData setup)
    (h_laws : SatisfiesNeutronInterferenceLaws setup) :
    speedInMetersPerSecond setup.neutronSpeed =
      (2 * Real.pi * (Constants.ℏ : ℝ)) /
        ((185 / 98) * 1e-15 * 1.67492749804e-27) := by
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
      lengthInMeters setup.matterWavelength = (185 / 98) * 1e-15 := by
    norm_num at h_wave_scale ⊢
    linarith
  have h_deBroglie := h_laws.deBroglieMatterWaveLaw
  rw [h_wave_m, h_reference.neutronMassKilograms,
    h_reference.ordinaryPlanckActionJouleSeconds] at h_deBroglie
  apply (eq_div_iff (by norm_num)).2
  nlinarith

/-!
The exact expression lies between `2.09 × 10^8` and `2.10 × 10^8` metres per
second.  This is the physically supported speed interval under the stated
data and the textbook nonrelativistic de Broglie model.
-/
lemma neutron_speed_in_physically_supported_interval
    (setup : NeutronDoubleSlitSetup)
    (h_physical : HasPhysicalNeutronInterferenceParameters setup)
    (h_readouts : MatchesProblemLengthReadouts setup)
    (h_figure : MatchesSuppliedDetectorFigure setup.figure)
    (h_reference : UsesStandardNeutronReferenceData setup)
    (h_laws : SatisfiesNeutronInterferenceLaws setup) :
    209000000 < speedInMetersPerSecond setup.neutronSpeed ∧
      speedInMetersPerSecond setup.neutronSpeed < 210000000 := by
  have pi_lower : (157 / 50 : ℝ) < Real.pi := by
    have hbound :=
      Real.cos_bound (x := (157 / 3200 : ℝ)) (by norm_num)
    have habs := abs_le.mp hbound
    have hc0 :
        (998796 / 1000000 : ℝ) < Real.cos (157 / 3200 : ℝ) := by
      norm_num at habs ⊢
      linarith
    have hc1 :
        (995186 / 1000000 : ℝ) < Real.cos (157 / 1600 : ℝ) := by
      rw [show (157 / 1600 : ℝ) = 2 * (157 / 3200) by norm_num,
        Real.cos_two_mul]
      have hp : 0 <
          (Real.cos (157 / 3200 : ℝ) - 998796 / 1000000) *
            (Real.cos (157 / 3200 : ℝ) + 998796 / 1000000) :=
        mul_pos (sub_pos.mpr hc0) (by nlinarith [hc0])
      nlinarith
    have hc2 :
        (980790 / 1000000 : ℝ) < Real.cos (157 / 800 : ℝ) := by
      rw [show (157 / 800 : ℝ) = 2 * (157 / 1600) by norm_num,
        Real.cos_two_mul]
      have hp : 0 <
          (Real.cos (157 / 1600 : ℝ) - 995186 / 1000000) *
            (Real.cos (157 / 1600 : ℝ) + 995186 / 1000000) :=
        mul_pos (sub_pos.mpr hc1) (by nlinarith [hc1])
      nlinarith
    have hc3 :
        (923890 / 1000000 : ℝ) < Real.cos (157 / 400 : ℝ) := by
      rw [show (157 / 400 : ℝ) = 2 * (157 / 800) by norm_num,
        Real.cos_two_mul]
      have hp : 0 <
          (Real.cos (157 / 800 : ℝ) - 980790 / 1000000) *
            (Real.cos (157 / 800 : ℝ) + 980790 / 1000000) :=
        mul_pos (sub_pos.mpr hc2) (by nlinarith [hc2])
      nlinarith
    have hc4 :
        (707120 / 1000000 : ℝ) < Real.cos (157 / 200 : ℝ) := by
      rw [show (157 / 200 : ℝ) = 2 * (157 / 400) by norm_num,
        Real.cos_two_mul]
      have hp : 0 <
          (Real.cos (157 / 400 : ℝ) - 923890 / 1000000) *
            (Real.cos (157 / 400 : ℝ) + 923890 / 1000000) :=
        mul_pos (sub_pos.mpr hc3) (by nlinarith [hc3])
      nlinarith
    have hcospos : 0 < Real.cos (157 / 100 : ℝ) := by
      rw [show (157 / 100 : ℝ) = 2 * (157 / 200) by norm_num,
        Real.cos_two_mul]
      have hp : 0 <
          (Real.cos (157 / 200 : ℝ) - 707120 / 1000000) *
            (Real.cos (157 / 200 : ℝ) + 707120 / 1000000) :=
        mul_pos (sub_pos.mpr hc4) (by nlinarith [hc4])
      nlinarith
    by_contra hpi
    have hpi' : Real.pi ≤ (157 / 50 : ℝ) := le_of_not_gt hpi
    have hx1 : Real.pi / 2 ≤ (157 / 100 : ℝ) := by linarith
    have hx2 : (157 / 100 : ℝ) ≤ Real.pi + Real.pi / 2 := by
      nlinarith [Real.two_le_pi]
    have hnonpos :=
      Real.cos_nonpos_of_pi_div_two_le_of_le hx1 hx2
    linarith
  have pi_upper : Real.pi < (629 / 200 : ℝ) := by
    have hbound :=
      Real.cos_bound (x := (629 / 12800 : ℝ)) (by norm_num)
    have habs := abs_le.mp hbound
    have hc0 :
        Real.cos (629 / 12800 : ℝ) < (998793 / 1000000 : ℝ) := by
      norm_num at habs ⊢
      linarith
    have hc1 :
        Real.cos (629 / 6400 : ℝ) < (995180 / 1000000 : ℝ) := by
      rw [show (629 / 6400 : ℝ) = 2 * (629 / 12800) by norm_num,
        Real.cos_two_mul]
      have hp : 0 <
          (998793 / 1000000 - Real.cos (629 / 12800 : ℝ)) *
            (998793 / 1000000 + Real.cos (629 / 12800 : ℝ)) :=
        mul_pos (sub_pos.mpr hc0)
          (by
            nlinarith [Real.cos_pos_of_le_one
              (x := (629 / 12800 : ℝ)) (by norm_num)])
      nlinarith
    have hc2 :
        Real.cos (629 / 3200 : ℝ) < (980770 / 1000000 : ℝ) := by
      rw [show (629 / 3200 : ℝ) = 2 * (629 / 6400) by norm_num,
        Real.cos_two_mul]
      have hp : 0 <
          (995180 / 1000000 - Real.cos (629 / 6400 : ℝ)) *
            (995180 / 1000000 + Real.cos (629 / 6400 : ℝ)) :=
        mul_pos (sub_pos.mpr hc1)
          (by
            nlinarith [Real.cos_pos_of_le_one
              (x := (629 / 6400 : ℝ)) (by norm_num)])
      nlinarith
    have hc3 :
        Real.cos (629 / 1600 : ℝ) < (923830 / 1000000 : ℝ) := by
      rw [show (629 / 1600 : ℝ) = 2 * (629 / 3200) by norm_num,
        Real.cos_two_mul]
      have hp : 0 <
          (980770 / 1000000 - Real.cos (629 / 3200 : ℝ)) *
            (980770 / 1000000 + Real.cos (629 / 3200 : ℝ)) :=
        mul_pos (sub_pos.mpr hc2)
          (by
            nlinarith [Real.cos_pos_of_le_one
              (x := (629 / 3200 : ℝ)) (by norm_num)])
      nlinarith
    have hc4 :
        Real.cos (629 / 800 : ℝ) < (707000 / 1000000 : ℝ) := by
      rw [show (629 / 800 : ℝ) = 2 * (629 / 1600) by norm_num,
        Real.cos_two_mul]
      have hp : 0 <
          (923830 / 1000000 - Real.cos (629 / 1600 : ℝ)) *
            (923830 / 1000000 + Real.cos (629 / 1600 : ℝ)) :=
        mul_pos (sub_pos.mpr hc3)
          (by
            nlinarith [Real.cos_pos_of_le_one
              (x := (629 / 1600 : ℝ)) (by norm_num)])
      nlinarith
    have hcosneg : Real.cos (629 / 400 : ℝ) < 0 := by
      rw [show (629 / 400 : ℝ) = 2 * (629 / 800) by norm_num,
        Real.cos_two_mul]
      have hp : 0 <
          (707000 / 1000000 - Real.cos (629 / 800 : ℝ)) *
            (707000 / 1000000 + Real.cos (629 / 800 : ℝ)) :=
        mul_pos (sub_pos.mpr hc4)
          (by
            nlinarith [Real.cos_pos_of_le_one
              (x := (629 / 800 : ℝ)) (by norm_num)])
      nlinarith
    by_contra hpi
    have hpi' : (629 / 200 : ℝ) ≤ Real.pi := le_of_not_gt hpi
    have hx2 : (629 / 400 : ℝ) ≤ Real.pi / 2 := by linarith
    have hx1 : -(Real.pi / 2) ≤ (629 / 400 : ℝ) := by
      nlinarith [Real.pi_pos]
    have hnonneg :=
      Real.cos_nonneg_of_neg_pi_div_two_le_of_le hx1 hx2
    linarith
  have h_speed :=
    neutron_speed_meters_per_second_eq setup h_physical h_readouts
      h_figure h_reference h_laws
  rw [h_speed]
  norm_num [Constants.ℏ]
  constructor <;> nlinarith

/-! The modeled speed rounds to `2 × 10^8 m/s` at one significant figure. -/
lemma neutron_speed_rounds_to_two_hundred_million
    (setup : NeutronDoubleSlitSetup)
    (h_physical : HasPhysicalNeutronInterferenceParameters setup)
    (h_readouts : MatchesProblemLengthReadouts setup)
    (h_figure : MatchesSuppliedDetectorFigure setup.figure)
    (h_reference : UsesStandardNeutronReferenceData setup)
    (h_laws : SatisfiesNeutronInterferenceLaws setup) :
    RoundsToOneSignificantFigure
      (speedInMetersPerSecond setup.neutronSpeed) 200000000 := by
  have h_interval :=
    neutron_speed_in_physically_supported_interval setup h_physical
      h_readouts h_figure h_reference h_laws
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

/-!
Consequently none of the four displayed values `150`, `200`, `250`, or `300`
metres per second matches the speed inferred from the literal source data.
The recorded label B remains available only through `recordedDatasetAnswer`.
-/
lemma no_displayed_speed_matches
    (setup : NeutronDoubleSlitSetup)
    (h_physical : HasPhysicalNeutronInterferenceParameters setup)
    (h_readouts : MatchesProblemLengthReadouts setup)
    (h_figure : MatchesSuppliedDetectorFigure setup.figure)
    (h_reference : UsesStandardNeutronReferenceData setup)
    (h_laws : SatisfiesNeutronInterferenceLaws setup) :
    ∀ choice : AnswerChoice, ¬ MatchesDisplayedSpeed setup choice := by
  have h_interval :=
    neutron_speed_in_physically_supported_interval setup h_physical
      h_readouts h_figure h_reference h_laws
  have no_small_report (reported : ℝ)
      (hreported_pos : 0 < reported) (hreported_le : reported ≤ 300) :
      ¬ RoundsToOneSignificantFigure
        (speedInMetersPerSecond setup.neutronSpeed) reported := by
    rintro ⟨digit, exponent, hdigit_one, _hdigit_nine,
      hreported, hround⟩
    let placeValue : ℝ := (10 : ℝ) ^ exponent
    have hplace_pos : 0 < placeValue := by
      exact zpow_pos (by norm_num) exponent
    have hdigit_real : (1 : ℝ) ≤ digit := by
      exact_mod_cast hdigit_one
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
    have hspeed_below_four_hundred_fifty :
        speedInMetersPerSecond setup.neutronSpeed < 450 := by
      calc
        speedInMetersPerSecond setup.neutronSpeed <
            ((digit : ℝ) + 1 / 2) * placeValue := hspeed_upper
        _ = reported + placeValue / 2 := by
          rw [hreported]
          ring
        _ ≤ reported + reported / 2 := by
          gcongr
        _ ≤ 450 := by linarith
    linarith [h_interval.1]
  intro choice
  unfold MatchesDisplayedSpeed
  cases choice <;>
    apply no_small_report <;>
    norm_num [displayedSpeedInMetersPerSecond]

/-!
Under the literal source data, the detector trace gives a speed between
`2.09 × 10^8` and `2.10 × 10^8 m/s`, hence `2 × 10^8 m/s` to one significant
figure.  The theorem also exposes the exact SI expression and the intermediate
image-derived fringe spacing and matter wavelength.

This formalizes `thm:physics:phyx_mini_0643:target`.  Neither the derived
spacing, wavelength, exact speed, speed interval, rounded speed, nor the
failure of all displayed choices occurs in a scenario, figure, reference-data,
positivity, or governing-law premise.

The recorded answer B would instead be consistent with a slit separation on
the order of `0.10 mm`.  That likely source typo is not silently repaired:
choice B is retained as metadata, while the theorem states the result supported
by the printed `0.10 nm` datum and the modeled laws.
-/
theorem problem_phyx_mini_0643
    (setup : NeutronDoubleSlitSetup)
    (h_scenario : MatchesNeutronDoubleSlitScenario setup)
    (h_physical : HasPhysicalNeutronInterferenceParameters setup)
    (h_readouts : MatchesProblemLengthReadouts setup)
    (h_figure : MatchesSuppliedDetectorFigure setup.figure)
    (h_reference : UsesStandardNeutronReferenceData setup)
    (h_laws : SatisfiesNeutronInterferenceLaws setup) :
    lengthInMicrometers setup.adjacentBrightFringeSpacing = 925 / 14 ∧
      lengthInFemtometers setup.matterWavelength = 185 / 98 ∧
      speedInMetersPerSecond setup.neutronSpeed =
        (2 * Real.pi * (Constants.ℏ : ℝ)) /
          ((185 / 98) * 1e-15 * 1.67492749804e-27) ∧
      (209000000 < speedInMetersPerSecond setup.neutronSpeed ∧
        speedInMetersPerSecond setup.neutronSpeed < 210000000) ∧
      RoundsToOneSignificantFigure
        (speedInMetersPerSecond setup.neutronSpeed) 200000000 ∧
      (∀ choice : AnswerChoice, ¬ MatchesDisplayedSpeed setup choice) := by
  have h_spacing :=
    adjacent_fringe_spacing_micrometers_eq setup h_figure h_laws
  have h_wave :=
    matter_wavelength_femtometers_eq setup h_readouts h_figure h_laws
  have h_speed :=
    neutron_speed_meters_per_second_eq setup h_physical h_readouts
      h_figure h_reference h_laws
  have h_interval :=
    neutron_speed_in_physically_supported_interval setup h_physical
      h_readouts h_figure h_reference h_laws
  have h_round :=
    neutron_speed_rounds_to_two_hundred_million setup h_physical
      h_readouts h_figure h_reference h_laws
  have h_no_choice :=
    no_displayed_speed_matches setup h_physical h_readouts h_figure
      h_reference h_laws
  exact ⟨h_spacing, h_wave, h_speed, h_interval, h_round, h_no_choice⟩

end PhyXMiniProblems.ProblemPhyXMini0643
