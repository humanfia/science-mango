import Mathlib.Analysis.SpecialFunctions.Trigonometric.Angle
import Physlib.SpaceAndTime.Space.Basic
import Physlib.SpaceAndTime.Space.LengthUnit
import Physlib.Units.WithDim.Basic

noncomputable section

namespace PhyXMiniProblems.ProblemPhyXMini0090

open Dimension

/-!
# Phase difference from two in-phase point sources

The figure places two isotropic point sources `S₁` and `S₂` on the horizontal
axis, separated by `d`.  The screen is vertical and lies a horizontal distance
`D` to the right of `S₂`; the observation point `P` has height `yₚ`.

Physical lengths are represented by Physlib dimensionful quantities.  The
points of the planar diagram live in Physlib's `Space 2`; their real
coordinates are read in the explicitly stored `coordinateUnit`.  Optical
phase is represented by `Real.Angle`, so equality of phases is naturally
understood modulo `2π`.  The type of source amplitudes remains abstract because
only equality of the two amplitudes is relevant to this problem.

The question calls the requested quantity a phase difference, while every
answer is printed as a multiple of the wavelength.  Accordingly, the model
keeps both quantities: the phase difference at `P`, and the corresponding
geometric path difference measured in wavelengths.
-/

/-- A physical quantity carrying the dimension of length. -/
abbrev LengthQuantity : Type := Dimensionful (WithDim L𝓭 ℝ)

/-- The scalar readout of a dimensionful length in a selected length unit. -/
def lengthReadout (unit : LengthUnit) (length : LengthQuantity) : ℝ :=
  (length { UnitChoices.SI with length := unit }).val

/-- The two point-source labels shown in the figure. -/
inductive SourceLabel where
  | S1
  | S2
  deriving DecidableEq, Repr

/-- The angular radiation pattern of a source. -/
inductive RadiationPattern where
  | isotropic
  | anisotropic
  deriving DecidableEq, Repr

/-- The qualitative orientation of the viewing screen in the diagram. -/
inductive ScreenOrientation where
  | parallelToYAxis
  | other
  deriving DecidableEq, Repr

/-!
A monochromatic point source.  `Amplitude` is intentionally an abstract type:
the problem specifies equal amplitudes but supplies no amplitude calibration
or unit in which a scalar readout should be taken.
-/
structure PointLightSource (Amplitude : Type) where
  wavelength : LengthQuantity
  amplitude : Amplitude
  initialPhase : Real.Angle
  radiationPattern : RadiationPattern

/-!
The physical objects and figure-derived quantities for the two-source setup.
`screenXCoordinate` is a scalar coordinate readout in `coordinateUnit`, while
`sourceSeparation`, `screenDistanceFromS2`, `observationHeight`, wavelengths,
and ray lengths are genuine dimensionful quantities.
-/
structure TwoSourceInterferenceSetup (Amplitude : Type) where
  coordinateUnit : LengthUnit
  source : SourceLabel → PointLightSource Amplitude
  sourcePosition : SourceLabel → Space 2
  screenOrientation : ScreenOrientation
  screenXCoordinate : ℝ
  pointP : Space 2
  sourceSeparation : LengthQuantity
  screenDistanceFromS2 : LengthQuantity
  observationHeight : LengthQuantity
  rayPathLength : SourceLabel → LengthQuantity
  propagationPhaseAtP : SourceLabel → Real.Angle

/-- The common wavelength, named using the `S₁` source. -/
def commonWavelength {Amplitude : Type}
    (setup : TwoSourceInterferenceSetup Amplitude) : LengthQuantity :=
  (setup.source .S1).wavelength

/-!
The source conditions stated in the problem: both sources are isotropic, have
the same amplitude and wavelength, and emit in phase.  This says nothing about
their phase difference after propagation to `P`.
-/
def EmitsInPhaseAtSameAmplitudeIsotropically {Amplitude : Type}
    (setup : TwoSourceInterferenceSetup Amplitude) : Prop :=
  (setup.source .S1).radiationPattern = .isotropic ∧
    (setup.source .S2).radiationPattern = .isotropic ∧
    (setup.source .S1).amplitude = (setup.source .S2).amplitude ∧
    (setup.source .S1).wavelength = (setup.source .S2).wavelength ∧
    (setup.source .S1).initialPhase = (setup.source .S2).initialPhase

/-!
The categorical and coordinate layout read from the primary image.  `S₁` is
the origin, `S₂` lies `d` to its right, the screen is the vertical line at
`x = d + D`, and `P` lies on that screen at height `yₚ`.
-/
def HasDepictedLayout {Amplitude : Type}
    (setup : TwoSourceInterferenceSetup Amplitude) : Prop :=
  setup.screenOrientation = .parallelToYAxis ∧
    setup.sourcePosition .S1 0 = 0 ∧
    setup.sourcePosition .S1 1 = 0 ∧
    setup.sourcePosition .S2 0 =
      lengthReadout setup.coordinateUnit setup.sourceSeparation ∧
    setup.sourcePosition .S2 1 = 0 ∧
    setup.screenXCoordinate =
      lengthReadout setup.coordinateUnit setup.sourceSeparation +
        lengthReadout setup.coordinateUnit setup.screenDistanceFromS2 ∧
    setup.pointP 0 = setup.screenXCoordinate ∧
    setup.pointP 1 =
      lengthReadout setup.coordinateUnit setup.observationHeight

/-!
The numerical problem data, expressed covariantly in every length unit:
`d = 6λ`, `D = 20λ`, and the requested observation height is `yₚ = d`.
No ray-path or phase-difference answer occurs here.
-/
def MatchesProblemReadouts {Amplitude : Type}
    (setup : TwoSourceInterferenceSetup Amplitude) : Prop :=
  (∀ unit : LengthUnit,
      lengthReadout unit setup.sourceSeparation =
        6 * lengthReadout unit (commonWavelength setup)) ∧
    (∀ unit : LengthUnit,
      lengthReadout unit setup.screenDistanceFromS2 =
        20 * lengthReadout unit (commonWavelength setup)) ∧
    ∀ unit : LengthUnit,
      lengthReadout unit setup.observationHeight =
        lengthReadout unit setup.sourceSeparation

/-- Positivity conditions for the physical lengths in the setup. -/
def HasPositivePhysicalLengths {Amplitude : Type}
    (setup : TwoSourceInterferenceSetup Amplitude) : Prop :=
  0 < lengthReadout setup.coordinateUnit (commonWavelength setup) ∧
    0 < lengthReadout setup.coordinateUnit setup.sourceSeparation ∧
    0 < lengthReadout setup.coordinateUnit setup.screenDistanceFromS2 ∧
    0 ≤ lengthReadout setup.coordinateUnit setup.observationHeight ∧
    ∀ source : SourceLabel,
      0 < lengthReadout setup.coordinateUnit (setup.rayPathLength source)

/-!
The geometric-optics law that each ray-path length is the Euclidean distance
from its point source to `P`.  This is a generic governing relation and does
not contain the requested numerical path or phase difference.
-/
def SatisfiesEuclideanRayGeometry {Amplitude : Type}
    (setup : TwoSourceInterferenceSetup Amplitude) : Prop :=
  ∀ source : SourceLabel,
    lengthReadout setup.coordinateUnit (setup.rayPathLength source) =
      dist (setup.sourcePosition source) setup.pointP

/-!
For monochromatic propagation, a path of length `r` accumulates phase
`2π r / λ`, regarded as an element of `Real.Angle`.  The law is stated for
each source separately and does not assert the requested phase difference.
-/
def SatisfiesMonochromaticPropagationLaw {Amplitude : Type}
    (setup : TwoSourceInterferenceSetup Amplitude) : Prop :=
  ∀ source : SourceLabel,
    setup.propagationPhaseAtP source =
      (((2 * Real.pi) *
          (lengthReadout setup.coordinateUnit (setup.rayPathLength source) /
            lengthReadout setup.coordinateUnit
              (setup.source source).wavelength) : ℝ) : Real.Angle)

/-- The total phase of the wave from one source when it reaches `P`. -/
def phaseAtP {Amplitude : Type}
    (setup : TwoSourceInterferenceSetup Amplitude)
    (source : SourceLabel) : Real.Angle :=
  (setup.source source).initialPhase + setup.propagationPhaseAtP source

/-!
The directed phase difference `phase(S₁ at P) - phase(S₂ at P)`, modulo `2π`.
The figure makes the `S₁` ray longer, so this orientation agrees with the
positive path difference used by the displayed choices.
-/
def phaseDifferenceAtP {Amplitude : Type}
    (setup : TwoSourceInterferenceSetup Amplitude) : Real.Angle :=
  phaseAtP setup .S1 - phaseAtP setup .S2

/-- The geometric path difference `(r₁-r₂)/λ`, in wavelength units. -/
def pathDifferenceInWavelengths {Amplitude : Type}
    (setup : TwoSourceInterferenceSetup Amplitude) : ℝ :=
  (lengthReadout setup.coordinateUnit (setup.rayPathLength .S1) -
      lengthReadout setup.coordinateUnit (setup.rayPathLength .S2)) /
    lengthReadout setup.coordinateUnit (commonWavelength setup)

/-- Labels of the four multiple-choice answers. -/
inductive AnswerChoice where
  | A
  | B
  | C
  | D
  deriving DecidableEq, Repr

/-!
The path difference printed beside each answer, measured in wavelengths.
These are the answer-table readouts, not assumptions about the physical rays.
-/
def answerPathDifferenceInWavelengths : AnswerChoice → ℝ
  | .A => 4.80
  | .B => 6.00
  | .C => 5.80
  | .D => 5.00

/-!
A displayed choice is selected when its wavelength count is at least as close
to the exact geometric path difference as every other displayed value.  This
models the rounding implicit in the recorded answer `5.80λ`.
-/
def IsNearestDisplayedPathDifference {Amplitude : Type}
    (setup : TwoSourceInterferenceSetup Amplitude)
    (choice : AnswerChoice) : Prop :=
  ∀ other : AnswerChoice,
    |pathDifferenceInWavelengths setup -
        answerPathDifferenceInWavelengths choice| ≤
      |pathDifferenceInWavelengths setup -
        answerPathDifferenceInWavelengths other|

/-!
At `d = yₚ = 6λ` and `D = 20λ`, the two ray lengths are respectively
`√712 λ` and `√436 λ`.  This is derived from the depicted coordinates and
the Euclidean ray-length law.
-/
lemma normalizedRayPathLengths
    {Amplitude : Type}
    (setup : TwoSourceInterferenceSetup Amplitude)
    (h_layout : HasDepictedLayout setup)
    (h_readouts : MatchesProblemReadouts setup)
    (h_physical : HasPositivePhysicalLengths setup)
    (h_geometry : SatisfiesEuclideanRayGeometry setup) :
    lengthReadout setup.coordinateUnit (setup.rayPathLength .S1) /
          lengthReadout setup.coordinateUnit (commonWavelength setup) =
        Real.sqrt (712 : ℝ) ∧
      lengthReadout setup.coordinateUnit (setup.rayPathLength .S2) /
          lengthReadout setup.coordinateUnit (commonWavelength setup) =
        Real.sqrt (436 : ℝ) := by
  rcases h_layout with
    ⟨_, hs1x, hs1y, hs2x, hs2y, hscreen, hpx, hpy⟩
  rcases h_readouts with ⟨hd, hD, hy⟩
  rcases h_physical with ⟨h_wave, _, _, _, _⟩
  have hd' := hd setup.coordinateUnit
  have hD' := hD setup.coordinateUnit
  have hy' := hy setup.coordinateUnit
  have hr1 := h_geometry .S1
  have hr2 := h_geometry .S2
  constructor
  · rw [hr1, Space.dist_eq, Fin.sum_univ_two]
    rw [hs1x, hs1y, hpx, hpy, hscreen, hd', hD', hy', hd']
    rw [show
      (0 - (6 * lengthReadout setup.coordinateUnit (commonWavelength setup) +
          20 * lengthReadout setup.coordinateUnit (commonWavelength setup))) ^ 2 +
        (0 - 6 * lengthReadout setup.coordinateUnit (commonWavelength setup)) ^ 2 =
          712 * lengthReadout setup.coordinateUnit (commonWavelength setup) ^ 2 by ring]
    rw [Real.sqrt_mul (by norm_num : 0 ≤ (712 : ℝ)),
      Real.sqrt_sq_eq_abs, abs_of_pos h_wave]
    field_simp
  · rw [hr2, Space.dist_eq, Fin.sum_univ_two]
    rw [hs2x, hs2y, hpx, hpy, hscreen, hd', hD', hy', hd']
    rw [show
      (6 * lengthReadout setup.coordinateUnit (commonWavelength setup) -
          (6 * lengthReadout setup.coordinateUnit (commonWavelength setup) +
            20 * lengthReadout setup.coordinateUnit (commonWavelength setup))) ^ 2 +
        (0 - 6 * lengthReadout setup.coordinateUnit (commonWavelength setup)) ^ 2 =
          436 * lengthReadout setup.coordinateUnit (commonWavelength setup) ^ 2 by ring]
    rw [Real.sqrt_mul (by norm_num : 0 ≤ (436 : ℝ)),
      Real.sqrt_sq_eq_abs, abs_of_pos h_wave]
    field_simp

/-- The exact geometric path difference in wavelength units. -/
lemma pathDifferenceInWavelengths_eq
    {Amplitude : Type}
    (setup : TwoSourceInterferenceSetup Amplitude)
    (h_layout : HasDepictedLayout setup)
    (h_readouts : MatchesProblemReadouts setup)
    (h_physical : HasPositivePhysicalLengths setup)
    (h_geometry : SatisfiesEuclideanRayGeometry setup) :
    pathDifferenceInWavelengths setup =
      Real.sqrt (712 : ℝ) - Real.sqrt (436 : ℝ) := by
  rcases normalizedRayPathLengths setup h_layout h_readouts h_physical h_geometry with
    ⟨hr1, hr2⟩
  have h_wave :
      lengthReadout setup.coordinateUnit (commonWavelength setup) ≠ 0 :=
    ne_of_gt h_physical.1
  rw [pathDifferenceInWavelengths]
  calc
    (lengthReadout setup.coordinateUnit (setup.rayPathLength .S1) -
          lengthReadout setup.coordinateUnit (setup.rayPathLength .S2)) /
        lengthReadout setup.coordinateUnit (commonWavelength setup) =
        lengthReadout setup.coordinateUnit (setup.rayPathLength .S1) /
            lengthReadout setup.coordinateUnit (commonWavelength setup) -
          lengthReadout setup.coordinateUnit (setup.rayPathLength .S2) /
            lengthReadout setup.coordinateUnit (commonWavelength setup) := by
              field_simp
    _ = Real.sqrt (712 : ℝ) - Real.sqrt (436 : ℝ) := by rw [hr1, hr2]

/-!
Equal source phases and the monochromatic propagation law turn the geometric
path difference into the corresponding phase difference modulo `2π`.
-/
lemma phaseDifferenceAtP_eq
    {Amplitude : Type}
    (setup : TwoSourceInterferenceSetup Amplitude)
    (h_emission : EmitsInPhaseAtSameAmplitudeIsotropically setup)
    (h_layout : HasDepictedLayout setup)
    (h_readouts : MatchesProblemReadouts setup)
    (h_physical : HasPositivePhysicalLengths setup)
    (h_geometry : SatisfiesEuclideanRayGeometry setup)
    (h_propagation : SatisfiesMonochromaticPropagationLaw setup) :
    phaseDifferenceAtP setup =
      (((2 * Real.pi) *
          (Real.sqrt (712 : ℝ) - Real.sqrt (436 : ℝ)) : ℝ) :
        Real.Angle) := by
  rcases h_emission with ⟨_, _, _, h_wavelength, h_initial⟩
  rcases normalizedRayPathLengths setup h_layout h_readouts h_physical h_geometry with
    ⟨hr1, hr2⟩
  simp only [commonWavelength] at hr1 hr2
  have hp1 := h_propagation .S1
  have hp2 := h_propagation .S2
  unfold phaseDifferenceAtP phaseAtP
  rw [h_initial, hp1, hp2, ← h_wavelength]
  simp only [add_sub_add_left_eq_sub]
  rw [← Real.Angle.coe_sub]
  congr 1
  rw [mul_sub, hr1, hr2]

/-!
The phase difference at `P` is the phase associated with the exact path
difference `√712 - √436` wavelengths.  That path difference is approximately
`5.8027λ`, so the nearest displayed readout is `5.80λ`, answer choice C.

This formalizes blueprint label `thm:physics:phyx_mini_0090:target`.
-/
theorem problem_phyx_mini_0090
    {Amplitude : Type}
    (setup : TwoSourceInterferenceSetup Amplitude)
    (h_emission : EmitsInPhaseAtSameAmplitudeIsotropically setup)
    (h_layout : HasDepictedLayout setup)
    (h_readouts : MatchesProblemReadouts setup)
    (h_physical : HasPositivePhysicalLengths setup)
    (h_geometry : SatisfiesEuclideanRayGeometry setup)
    (h_propagation : SatisfiesMonochromaticPropagationLaw setup) :
    phaseDifferenceAtP setup =
        (((2 * Real.pi) *
            (Real.sqrt (712 : ℝ) - Real.sqrt (436 : ℝ)) : ℝ) :
          Real.Angle) ∧
      IsNearestDisplayedPathDifference setup .C := by
  constructor
  · exact phaseDifferenceAtP_eq setup h_emission h_layout h_readouts
      h_physical h_geometry h_propagation
  · unfold IsNearestDisplayedPathDifference
    intro other
    rw [pathDifferenceInWavelengths_eq setup h_layout h_readouts h_physical h_geometry]
    have h712_nonneg : 0 ≤ Real.sqrt (712 : ℝ) := Real.sqrt_nonneg _
    have h436_nonneg : 0 ≤ Real.sqrt (436 : ℝ) := Real.sqrt_nonneg _
    have h712_sq : (Real.sqrt (712 : ℝ)) ^ 2 = 712 :=
      Real.sq_sqrt (by norm_num)
    have h436_sq : (Real.sqrt (436 : ℝ)) ^ 2 = 436 :=
      Real.sq_sqrt (by norm_num)
    have h712_lower : (26681 / 1000 : ℝ) ≤ Real.sqrt 712 := by
      nlinarith
    have h436_upper : Real.sqrt 436 ≤ (20881 / 1000 : ℝ) := by
      nlinarith
    have h712_upper : Real.sqrt 712 ≤ (267 / 10 : ℝ) := by
      nlinarith
    have h436_lower : (208 / 10 : ℝ) ≤ Real.sqrt 436 := by
      nlinarith
    have hlower : (29 / 5 : ℝ) ≤ Real.sqrt 712 - Real.sqrt 436 := by
      linarith
    have hupper : Real.sqrt 712 - Real.sqrt 436 ≤ (59 / 10 : ℝ) := by
      linarith
    cases other with
    | A =>
        norm_num [answerPathDifferenceInWavelengths]
        rw [abs_of_nonneg (by linarith), abs_of_nonneg (by linarith)]
        linarith
    | B =>
        norm_num [answerPathDifferenceInWavelengths]
        rw [abs_of_nonneg (by linarith), abs_of_nonpos (by linarith)]
        linarith
    | C => simp
    | D =>
        norm_num [answerPathDifferenceInWavelengths]
        rw [abs_of_nonneg (by linarith), abs_of_nonneg (by linarith)]
        linarith

end PhyXMiniProblems.ProblemPhyXMini0090
