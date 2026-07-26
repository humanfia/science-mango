import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Physlib.SpaceAndTime.Space.Basic
import Physlib.Units.WithDim.Basic

/-!
# Phase difference from two isotropic point sources

This file formalizes problem `phyx_mini_0087`.  The primary figure fixes a
nanometre coordinate chart in a two-dimensional `Space 2`: the two sources
lie on the `y` axis, `P₁` lies on the positive `x` axis, and `P₂` lies on the
positive `y` axis.  The common wavelength remains a unit-aware physical
length.  Coordinates, distances, phases in radians, and phase-cycle counts
are real scalar readouts in their explicitly stated units.

The phases below are *unwrapped* real phases.  This is essential because the
question asks for a path-equivalent phase difference of `2.90` wavelengths,
not merely for its residue modulo one wavelength.
-/

noncomputable section

namespace PhyXMiniProblems.ProblemPhyXMini0087

/-- A unit-aware physical length. -/
abbrev DimLength : Type := Dimensionful (WithDim Dimension.L𝓭 ℝ)

/-- Read a physical length as a real scalar in the specified length unit. -/
def lengthValueIn (unit : LengthUnit) (length : DimLength) : ℝ :=
  (length ({ UnitChoices.SI with length := unit } : UnitChoices)).val

/-- The nanometre readout used for all coordinates and path lengths. -/
def nanometersValue (length : DimLength) : ℝ :=
  lengthValueIn LengthUnit.nanometers length

/-- Labels of the two isotropic point sources in the figure. -/
inductive SourceLabel where
  | S1
  | S2
  deriving DecidableEq, Repr

/-- Labels of the two observation points in the figure. -/
inductive ObservationLabel where
  | P1
  | P2
  deriving DecidableEq, Repr

/--
One monochromatic isotropic point source.  Its emission phase is an unwrapped
radian phase at a common reference time; isotropic propagation is imposed
separately by `SatisfiesIsotropicPhasePropagation`.
-/
structure IsotropicPointSource where
  /-- Spatial location of the point source in the nanometre coordinate chart. -/
  position : Space 2
  /-- Unwrapped source phase at the common reference time, in radians. -/
  emissionPhaseRadians : ℝ

/--
The two-source optical setup, including the unwrapped phase of each wave at
each named observation point at one common observation time.
-/
structure TwoPointSourceSetup where
  /-- The two labeled sources `S₁` and `S₂`. -/
  source : SourceLabel → IsotropicPointSource
  /-- Spatial locations of the labeled observation points `P₁` and `P₂`. -/
  observationPosition : ObservationLabel → Space 2
  /-- Common wavelength `λ` emitted by both sources. -/
  wavelength : DimLength
  /-- Unwrapped arrival phase in radians at the common observation time. -/
  arrivalPhaseRadians : SourceLabel → ObservationLabel → ℝ

/-- The `x` coordinate readout of a point in the chosen chart. -/
def xCoordinate (point : Space 2) : ℝ := point 0

/-- The `y` coordinate readout of a point in the chosen chart. -/
def yCoordinate (point : Space 2) : ℝ := point 1

/--
Signed phase by which `leading` is ahead of `trailing` at an observation
point, measured in unwrapped radians.
-/
def phaseLeadRadians
    (setup : TwoPointSourceSetup) (leading trailing : SourceLabel)
    (point : ObservationLabel) : ℝ :=
  setup.arrivalPhaseRadians leading point -
    setup.arrivalPhaseRadians trailing point

/--
The signed phase lead expressed as a number of wavelength cycles.  This is a
dimensionless multiple of `λ`: one wavelength of phase is `2π` radians.
-/
def phaseLeadInWavelengths
    (setup : TwoPointSourceSetup) (leading trailing : SourceLabel)
    (point : ObservationLabel) : ℝ :=
  phaseLeadRadians setup leading trailing point / (2 * Real.pi)

/--
The problem and primary-figure readouts, in the nanometre coordinate chart:

* `λ = 400 nm`,
* `S₁ = (0, 640) nm` and `S₂ = (0, -640) nm`,
* `P₁ = (720, 0) nm` and `P₂ = (0, 720) nm`.

This predicate contains no arrival-phase conclusion at `P₂`.
-/
def HasStatedFigureReadouts (setup : TwoPointSourceSetup) : Prop :=
  nanometersValue setup.wavelength = 400 ∧
    xCoordinate (setup.source .S1).position = 0 ∧
    yCoordinate (setup.source .S1).position = 640 ∧
    xCoordinate (setup.source .S2).position = 0 ∧
    yCoordinate (setup.source .S2).position = -640 ∧
    xCoordinate (setup.observationPosition .P1) = 720 ∧
    yCoordinate (setup.observationPosition .P1) = 0 ∧
    xCoordinate (setup.observationPosition .P2) = 0 ∧
    yCoordinate (setup.observationPosition .P2) = 720

/--
The measured calibration at `P₁`: the wave from `S₂` is ahead of the wave
from `S₁` by `0.600π = 3π/5` radians.  This is source data, not the requested
phase relation at `P₂`.
-/
def HasStatedPhaseCalibrationAtP1 (setup : TwoPointSourceSetup) : Prop :=
  phaseLeadRadians setup .S2 .S1 .P1 = (3 / 5 : ℝ) * Real.pi

/--
Radial phase propagation for monochromatic isotropic point sources.  At a
fixed common time, propagation over path length `r` subtracts
`2π r / λ` from the source phase.  Physlib's `Space` metric and the wavelength
readout both use the figure's nanometre unit here.

This law is uniform over both sources and both observation points; it does not
assert the requested numerical phase difference at `P₂`.
-/
def SatisfiesIsotropicPhasePropagation (setup : TwoPointSourceSetup) : Prop :=
  0 < nanometersValue setup.wavelength ∧
    ∀ source point,
      setup.arrivalPhaseRadians source point =
        (setup.source source).emissionPhaseRadians -
          2 * Real.pi *
            (dist (setup.source source).position
                (setup.observationPosition point) /
              nanometersValue setup.wavelength)

/-- Labels of the four answer choices printed in the problem. -/
inductive AnswerChoice where
  | A
  | B
  | C
  | D
  deriving DecidableEq, Repr

/-- Each answer as an exact dimensionless multiple of the wavelength `λ`. -/
def answerPhaseDifferenceInWavelengths : AnswerChoice → ℝ
  | .A => 13 / 5
  | .B => 27 / 10
  | .C => 29 / 10
  | .D => 16 / 5

/--
The primary-figure coordinates make the two source-to-`P₁` path lengths
equal.  Thus the stated arrival-phase lead at `P₁` calibrates the relative
emission phase without a propagation-path correction.
-/
lemma source_paths_to_P1_are_equal
    (setup : TwoPointSourceSetup)
    (h_figure : HasStatedFigureReadouts setup) :
    dist (setup.source .S1).position (setup.observationPosition .P1) =
      dist (setup.source .S2).position (setup.observationPosition .P1) := by
  rcases h_figure with
    ⟨_, hS1x, hS1y, hS2x, hS2y, hP1x, hP1y, _, _⟩
  simp only [xCoordinate, yCoordinate] at hS1x hS1y hS2x hS2y hP1x hP1y
  simp only [Space.dist_eq, Fin.sum_univ_two]
  rw [hS1x, hS1y, hS2x, hS2y, hP1x, hP1y]
  norm_num

/--
At `P₂`, the path from `S₂` is longer than the path from `S₁` by `3.20λ`.
This is a geometric intermediate conclusion, not an assumed answer to the
phase-difference question.
-/
lemma path_difference_to_P2_in_wavelengths
    (setup : TwoPointSourceSetup)
    (h_figure : HasStatedFigureReadouts setup) :
    (dist (setup.source .S2).position (setup.observationPosition .P2) -
        dist (setup.source .S1).position (setup.observationPosition .P2)) /
      nanometersValue setup.wavelength = 16 / 5 := by
  rcases h_figure with
    ⟨hLambda, hS1x, hS1y, hS2x, hS2y, _, _, hP2x, hP2y⟩
  simp only [xCoordinate, yCoordinate] at hS1x hS1y hS2x hS2y hP2x hP2y
  simp only [Space.dist_eq, Fin.sum_univ_two]
  rw [hLambda, hS1x, hS1y, hS2x, hS2y, hP2x, hP2y]
  norm_num
  have h1360 : Real.sqrt (1849600 : ℝ) = 1360 := by
    rw [show (1849600 : ℝ) = 1360 ^ 2 by norm_num, Real.sqrt_sq_eq_abs]
    norm_num
  have h80 : Real.sqrt (6400 : ℝ) = 80 := by
    rw [show (6400 : ℝ) = 80 ^ 2 by norm_num, Real.sqrt_sq_eq_abs]
    norm_num
  rw [h1360, h80]
  norm_num

/--
The source-to-`P₂` path difference of `3.20λ` reverses the calibrated
`0.30λ` lead of `S₂`.  Consequently `S₁` is ahead of `S₂` at `P₂` by
`2.90λ` of unwrapped phase, the dataset's recorded answer C.

This formalizes `thm:physics:phyx_mini_0087:target`.
-/
theorem phaseDifferenceAtP2_eq_recordedAnswerC
    (setup : TwoPointSourceSetup)
    (h_figure : HasStatedFigureReadouts setup)
    (h_calibration : HasStatedPhaseCalibrationAtP1 setup)
    (h_propagation : SatisfiesIsotropicPhasePropagation setup) :
    phaseLeadInWavelengths setup .S1 .S2 .P2 =
      answerPhaseDifferenceInWavelengths .C := by
  have hP1 := source_paths_to_P1_are_equal setup h_figure
  have hP2 := path_difference_to_P2_in_wavelengths setup h_figure
  rcases h_propagation with ⟨_, hPropagation⟩
  have hEmission :
      (setup.source .S2).emissionPhaseRadians -
          (setup.source .S1).emissionPhaseRadians =
        (3 / 5 : ℝ) * Real.pi := by
    change
      setup.arrivalPhaseRadians .S2 .P1 -
          setup.arrivalPhaseRadians .S1 .P1 =
        (3 / 5 : ℝ) * Real.pi at h_calibration
    rw [hPropagation .S2 .P1, hPropagation .S1 .P1, hP1] at h_calibration
    convert h_calibration using 1
    all_goals ring
  have hπ : Real.pi ≠ 0 := ne_of_gt Real.pi_pos
  change
    (setup.arrivalPhaseRadians .S1 .P2 -
          setup.arrivalPhaseRadians .S2 .P2) /
        (2 * Real.pi) =
      (29 / 10 : ℝ)
  rw [hPropagation .S1 .P2, hPropagation .S2 .P2]
  calc
    ((setup.source .S1).emissionPhaseRadians -
            2 * Real.pi *
              (dist (setup.source .S1).position
                  (setup.observationPosition .P2) /
                nanometersValue setup.wavelength) -
          ((setup.source .S2).emissionPhaseRadians -
            2 * Real.pi *
              (dist (setup.source .S2).position
                  (setup.observationPosition .P2) /
                nanometersValue setup.wavelength))) /
        (2 * Real.pi) =
        (-( (setup.source .S2).emissionPhaseRadians -
              (setup.source .S1).emissionPhaseRadians) +
            2 * Real.pi *
              ((dist (setup.source .S2).position
                    (setup.observationPosition .P2) -
                  dist (setup.source .S1).position
                    (setup.observationPosition .P2)) /
                nanometersValue setup.wavelength)) /
          (2 * Real.pi) := by
            ring
    _ = 29 / 10 := by
      rw [hEmission, hP2]
      field_simp [hπ]
      ring

end PhyXMiniProblems.ProblemPhyXMini0087
