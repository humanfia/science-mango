import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Physlib.SpaceAndTime.Space.LengthUnit
import Physlib.Units.WithDim.Basic

noncomputable section

namespace PhyXMiniProblems.ProblemPhyXMini0325

open Dimension

/-!
# Amplitude ratio in a two-path acoustic interferometer

An oscillating diaphragm at `S` sends sound through the fixed path `SAD` and
the variable path `SBD`.  The two waves interfere at the detector `D`.  The
movable arm on branch `B` is shifted by `1.65 cm`, during which the detector
reading climbs continuously from `100` to `900` arbitrary intensity units.

Those two extrema determine the two amplitudes only up to interchange.  Thus
the physically supported oriented ratio `SAD/SBD` is `2` or `1/2`; the source's
recorded answer `D : 2` is retained below as metadata, not as an assumption or
as a uniquely derivable conclusion.

Path lengths, acoustic pressure amplitudes, and acoustic intensities are
unit-independent Physlib quantities.  Real numbers below are either readouts
in explicitly named units, dimensionless phases in radians, or the arbitrary
scalar intensity units displayed by the detector.
-/

/-! ## Dimensionful acoustic quantities and readouts -/

/-- A nonnegative physical acoustic-path length. -/
abbrev AcousticPathLength : Type := Dimensionful (WithDim L𝓭 NNReal)

/-- The physical dimension of acoustic pressure: mass per length per time squared. -/
def acousticPressureDimension : Dimension :=
  M𝓭 * L𝓭⁻¹ * T𝓭⁻¹ * T𝓭⁻¹

/-- A nonnegative acoustic pressure amplitude carried by one path at `D`. -/
abbrev AcousticPressureAmplitude : Type :=
  Dimensionful (WithDim acousticPressureDimension NNReal)

/-- The physical dimension of acoustic intensity: power per area. -/
def acousticIntensityDimension : Dimension :=
  M𝓭 * T𝓭⁻¹ * T𝓭⁻¹ * T𝓭⁻¹

/-- A nonnegative physical acoustic intensity at the detector. -/
abbrev AcousticIntensity : Type :=
  Dimensionful (WithDim acousticIntensityDimension NNReal)

/-- Read a physical path length in a selected length unit. -/
def lengthReadout
    (unit : LengthUnit) (length : AcousticPathLength) : ℝ :=
  ((length {UnitChoices.SI with length := unit}).val : ℝ)

/-- Read an acoustic pressure amplitude in coherent SI pressure units. -/
def pressureAmplitudeInPascals
    (amplitude : AcousticPressureAmplitude) : ℝ :=
  ((amplitude UnitChoices.SI).val : ℝ)

/-- Read an acoustic intensity in coherent SI watt-per-square-metre units. -/
def acousticIntensityInWattsPerSquareMeter
    (intensity : AcousticIntensity) : ℝ :=
  ((intensity UnitChoices.SI).val : ℝ)

/-! ## Figure labels and physical setup -/

/-- The two source-to-detector routes named in the problem. -/
inductive AcousticPath where
  | SAD
  | SBD
  deriving DecidableEq, Repr

/-- The two endpoint positions of the movable arm in the demonstration. -/
inductive ArmPosition where
  | atMinimum
  | afterShiftAtMaximum
  deriving DecidableEq, Repr

/-- All letter labels visible in the supplied figure. -/
inductive FigureLabel where
  | S
  | A
  | B
  | D
  deriving DecidableEq, Repr

/-- Physical roles of the labels in the acoustic interferometer. -/
inductive FigureRole where
  | soundSource
  | fixedPathBranch
  | movablePathBranch
  | soundDetector
  deriving DecidableEq, Repr

/-- Qualitative shape of the two-branch tube in the supplied image. -/
inductive TubeGeometry where
  | twoBranchRacetrack
  | other
  deriving DecidableEq, Repr

/-- The sound-producing object at `S`. -/
inductive SoundSourceKind where
  | oscillatingDiaphragm
  | other
  deriving DecidableEq, Repr

/-- The physical detector pictured at `D`. -/
inductive SoundDetectorKind where
  | ear
  | microphone
  | other
  deriving DecidableEq, Repr

/-- The propagation medium filling the interferometer. -/
inductive AcousticMedium where
  | air
  | other
  deriving DecidableEq, Repr

/-- Typed qualitative contents of the supplied diagram. -/
structure AcousticInterferometerFigure where
  role : FigureLabel → FigureRole
  tubeGeometry : TubeGeometry

/-!
Physical parameters and observable readouts for the demonstration.

`detectorIntensityReading` is expressed in the arbitrary units used for the
reported values `100` and `900`.  `detectorTrace` takes a displacement in
centimetres from the initial arm position.  The two positive scale factors
are left as physical calibration parameters; neither fixes the requested
amplitude ratio.
-/
structure AcousticInterferometerSetup where
  sourceKind : SoundSourceKind
  detectorKind : SoundDetectorKind
  medium : AcousticMedium
  pathLength : AcousticPath → ArmPosition → AcousticPathLength
  movableArmShift : AcousticPathLength
  wavelength : AcousticPathLength
  pressureAmplitudeAtD : AcousticPath → AcousticPressureAmplitude
  acousticIntensityAtD : ArmPosition → AcousticIntensity
  phaseDifferenceRadians : ArmPosition → ℝ
  detectorIntensityReading : ArmPosition → ℝ
  detectorTrace : ℝ → ℝ
  detectorUnitsPerSIIntensity : ℝ
  siIntensityPerPressureSquared : ℝ
  figure : AcousticInterferometerFigure

/-!
The squared resultant pressure factor for two coherent waves with phase
difference `phaseDifferenceRadians position`.  This is the general
superposition expression, not a problem-specific answer formula.
-/
def coherentPressureSquare
    (setup : AcousticInterferometerSetup) (position : ArmPosition) : ℝ :=
  let a := pressureAmplitudeInPascals (setup.pressureAmplitudeAtD .SAD)
  let b := pressureAmplitudeInPascals (setup.pressureAmplitudeAtD .SBD)
  a ^ 2 + b ^ 2 +
    2 * a * b * Real.cos (setup.phaseDifferenceRadians position)

/-!
Problem statement and primary-image evidence.  Branch `A` is fixed, branch
`B` is movable, and moving the pictured U-shaped arm changes both straight
segments of `SBD`, hence twice the arm displacement.  The last four fields
formalize that the detector reading continuously and monotonically climbs
from the stated minimum to the stated maximum.
-/
structure MatchesProblemAndFigureReadouts
    (setup : AcousticInterferometerSetup) : Prop where
  sourceIsOscillatingDiaphragm :
    setup.sourceKind = .oscillatingDiaphragm
  detectorIsPicturedEar : setup.detectorKind = .ear
  mediumIsAir : setup.medium = .air
  sourceLabel : setup.figure.role .S = .soundSource
  fixedBranchLabel : setup.figure.role .A = .fixedPathBranch
  movableBranchLabel : setup.figure.role .B = .movablePathBranch
  detectorLabel : setup.figure.role .D = .soundDetector
  racetrackGeometry : setup.figure.tubeGeometry = .twoBranchRacetrack
  sadPathIsFixed : ∀ unit : LengthUnit,
    lengthReadout unit (setup.pathLength .SAD .atMinimum) =
      lengthReadout unit
        (setup.pathLength .SAD .afterShiftAtMaximum)
  sbdPathChangeIsTwiceArmShift : ∀ unit : LengthUnit,
    |lengthReadout unit
          (setup.pathLength .SBD .afterShiftAtMaximum) -
        lengthReadout unit (setup.pathLength .SBD .atMinimum)| =
      2 * lengthReadout unit setup.movableArmShift
  armShiftCentimeters :
    lengthReadout LengthUnit.centimeters setup.movableArmShift = 1.65
  minimumReading : setup.detectorIntensityReading .atMinimum = 100
  maximumReading :
    setup.detectorIntensityReading .afterShiftAtMaximum = 900
  traceStartsAtMinimum :
    setup.detectorTrace 0 =
      setup.detectorIntensityReading .atMinimum
  traceEndsAtMaximum :
    setup.detectorTrace
        (lengthReadout LengthUnit.centimeters setup.movableArmShift) =
      setup.detectorIntensityReading .afterShiftAtMaximum
  traceIsContinuous :
    ContinuousOn setup.detectorTrace
      (Set.Icc 0
        (lengthReadout LengthUnit.centimeters setup.movableArmShift))
  traceClimbs :
    MonotoneOn setup.detectorTrace
      (Set.Icc 0
        (lengthReadout LengthUnit.centimeters setup.movableArmShift))

/-!
Positivity and nondegeneracy assumptions.  In particular, no ordering is
imposed on the two amplitudes: neither the text nor the image states which
arriving wave is stronger.
-/
structure HasPhysicalAcousticParameters
    (setup : AcousticInterferometerSetup) : Prop where
  pathLengthsPositive : ∀ path position,
    0 < lengthReadout LengthUnit.meters (setup.pathLength path position)
  armShiftPositive :
    0 < lengthReadout LengthUnit.centimeters setup.movableArmShift
  wavelengthPositive :
    0 < lengthReadout LengthUnit.meters setup.wavelength
  pressureAmplitudesPositive : ∀ path,
    0 < pressureAmplitudeInPascals (setup.pressureAmplitudeAtD path)
  intensitiesPositive : ∀ position,
    0 < acousticIntensityInWattsPerSquareMeter
      (setup.acousticIntensityAtD position)
  detectorCalibrationPositive : 0 < setup.detectorUnitsPerSIIntensity
  pressureIntensityScalePositive :
    0 < setup.siIntensityPerPressureSquared

/-!
The governing laws of the ideal coherent acoustic interferometer.

The phase is generated by the path-length difference modulo the cosine.  The
physical intensity is proportional to the squared coherent pressure sum, and
the detector applies a positive linear calibration to that intensity.  The
observed minimum and maximum are respectively destructive and constructive
interference endpoints.  No field states an amplitude ratio.
-/
structure SatisfiesCoherentAcousticInterference
    (setup : AcousticInterferometerSetup) : Prop where
  phaseFromPathDifference : ∀ position,
    Real.cos (setup.phaseDifferenceRadians position) =
      Real.cos
        (2 * Real.pi *
          ((lengthReadout LengthUnit.meters
                (setup.pathLength .SBD position) -
              lengthReadout LengthUnit.meters
                (setup.pathLength .SAD position)) /
            lengthReadout LengthUnit.meters setup.wavelength))
  intensityFromCoherentPressure : ∀ position,
    acousticIntensityInWattsPerSquareMeter
        (setup.acousticIntensityAtD position) =
      setup.siIntensityPerPressureSquared *
        coherentPressureSquare setup position
  detectorCalibration : ∀ position,
    setup.detectorIntensityReading position =
      setup.detectorUnitsPerSIIntensity *
        acousticIntensityInWattsPerSquareMeter
          (setup.acousticIntensityAtD position)
  destructiveAtMinimum :
    Real.cos (setup.phaseDifferenceRadians .atMinimum) = -1
  constructiveAtMaximum :
    Real.cos
      (setup.phaseDifferenceRadians .afterShiftAtMaximum) = 1

/-! ## Requested ratio and answer choices -/

/-- The requested amplitude at `D` of the `SAD` wave divided by that of `SBD`. -/
def amplitudeRatioAtD (setup : AcousticInterferometerSetup) : ℝ :=
  pressureAmplitudeInPascals (setup.pressureAmplitudeAtD .SAD) /
    pressureAmplitudeInPascals (setup.pressureAmplitudeAtD .SBD)

/-- Labels of the four amplitude-ratio choices printed in the problem. -/
inductive AnswerChoice where
  | A
  | B
  | C
  | D
  deriving DecidableEq, Repr

/-- The numerical ratio printed beside each answer label. -/
def displayedAmplitudeRatio : AnswerChoice → ℝ
  | .A => 5
  | .B => 4
  | .C => 3
  | .D => 2

/-- A choice is correct when its displayed value equals the physical ratio. -/
def IsCorrectAnswer
    (setup : AcousticInterferometerSetup) (choice : AnswerChoice) : Prop :=
  amplitudeRatioAtD setup = displayedAmplitudeRatio choice

/-- The answer label recorded by the dataset; this is metadata, not a law. -/
def recordedAnswerChoice : AnswerChoice := .D

/-- The value printed beside the dataset's recorded answer label. -/
def recordedAnswerValue : ℝ :=
  displayedAmplitudeRatio recordedAnswerChoice

/-!
At destructive and constructive interference, the detector readings are a
common positive scale times `(a - b)^2` and `(a + b)^2`, respectively.  This
is a derived intermediate relation, not a model premise.
-/
lemma endpointDetectorReadingRelations
    (setup : AcousticInterferometerSetup)
    (h_interference : SatisfiesCoherentAcousticInterference setup) :
    let a := pressureAmplitudeInPascals
      (setup.pressureAmplitudeAtD .SAD)
    let b := pressureAmplitudeInPascals
      (setup.pressureAmplitudeAtD .SBD)
    setup.detectorIntensityReading .atMinimum =
        setup.detectorUnitsPerSIIntensity *
          setup.siIntensityPerPressureSquared * (a - b) ^ 2 ∧
      setup.detectorIntensityReading .afterShiftAtMaximum =
        setup.detectorUnitsPerSIIntensity *
          setup.siIntensityPerPressureSquared * (a + b) ^ 2 := by
  sorry

/-!
The readings `100` and `900` give an amplitude-sum to absolute
amplitude-difference ratio of three.  Since the source does not order the two
amplitudes, the oriented ratio requested in the question has the two reciprocal
possibilities `2` and `1/2`.
-/
lemma amplitudeRatioAtD_possibilities
    (setup : AcousticInterferometerSetup)
    (h_readouts : MatchesProblemAndFigureReadouts setup)
    (h_physical : HasPhysicalAcousticParameters setup)
    (h_interference : SatisfiesCoherentAcousticInterference setup) :
    amplitudeRatioAtD setup = 2 ∨
      amplitudeRatioAtD setup = (1 : ℝ) / 2 := by
  sorry

/-!
The stated observations determine the `SAD/SBD` amplitude ratio only up to
reciprocal.  The primary image labels the two routes but supplies no amplitude
ordering, so it does not resolve this ambiguity.  Consequently the recorded
choice D is represented above only as dataset metadata.

This is the Lean declaration corresponding to
`thm:physics:phyx_mini_0325:target`.  Neither possible ratio occurs in any
setup field or governing-law premise.
-/
theorem problem_phyx_mini_0325
    (setup : AcousticInterferometerSetup)
    (h_readouts : MatchesProblemAndFigureReadouts setup)
    (h_physical : HasPhysicalAcousticParameters setup)
    (h_interference : SatisfiesCoherentAcousticInterference setup) :
    amplitudeRatioAtD setup = 2 ∨
      amplitudeRatioAtD setup = (1 : ℝ) / 2 := by
  sorry

end PhyXMiniProblems.ProblemPhyXMini0325
