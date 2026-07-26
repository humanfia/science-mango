import Mathlib.Analysis.Real.Sqrt
import Physlib.SpaceAndTime.Space.LengthUnit
import Physlib.Units.WithDim.Basic

/-!
# Phase difference from two vertically separated sound sources

The primary figure places the isotropic point source `S₁` at the Cartesian
origin, the source `S₂` a distance `d` directly below it, and the observation
point `P` on the positive horizontal axis. The sources emit coherently and in
phase with wavelength `2.00 m`, while `d = 16.0 m`. The question asks for the
horizontal distance at which the propagation-path difference is `1.50`
wavelengths.

Wavelength, source separation, propagation-path lengths, and their difference
are unit-independent Physlib length quantities. Real numbers are used only for
signed coordinate readouts in meters, phase difference measured in wavelength
cycles, and displayed meter-valued answers.
-/

noncomputable section

namespace PhyXMiniProblems.ProblemPhyXMini0316

open Dimension

/-! ## Dimensionful quantities and figure labels -/

/-- A nonnegative physical length, independent of the unit used to read it. -/
abbrev LengthQuantity : Type := Dimensionful (WithDim L𝓭 NNReal)

/-- A signed physical length used for Cartesian coordinates in the figure. -/
abbrev SignedLengthQuantity : Type := Dimensionful (WithDim L𝓭 ℝ)

/-- Read a nonnegative physical length in a selected length unit. -/
def lengthReadout (unit : LengthUnit) (length : LengthQuantity) : ℝ :=
  ((length {UnitChoices.SI with length := unit}).val : ℝ)

/-- Read a signed Cartesian coordinate in a selected length unit. -/
def signedLengthReadout
    (unit : LengthUnit) (coordinate : SignedLengthQuantity) : ℝ :=
  (coordinate {UnitChoices.SI with length := unit}).val

/-- Meter readout of a nonnegative physical length. -/
def lengthInMeters (length : LengthQuantity) : ℝ :=
  lengthReadout LengthUnit.meters length

/-- Meter readout of a signed figure coordinate. -/
def signedLengthInMeters (coordinate : SignedLengthQuantity) : ℝ :=
  signedLengthReadout LengthUnit.meters coordinate

/-- Labels of the two sound sources printed in the primary figure. -/
inductive SourceLabel where
  | S₁
  | S₂
  deriving DecidableEq, Repr

/-- Point labels printed in the primary figure. -/
inductive FigurePointLabel where
  | S₁
  | S₂
  | P
  deriving DecidableEq, Repr

/-- Cartesian axis labels printed in the primary figure. -/
inductive CoordinateAxis where
  | x
  | y
  deriving DecidableEq, Repr

/-- The source type stated in the problem. -/
inductive AcousticSourceKind where
  | isotropicPointSource
  deriving DecidableEq, Repr

/-- The common homogeneous propagation medium implicit in the sound diagram. -/
inductive AcousticMedium where
  | ambientAir
  deriving DecidableEq, Repr

/-- A Cartesian point whose coordinates are dimensionful signed lengths. -/
structure PlanePoint where
  horizontal : SignedLengthQuantity
  vertical : SignedLengthQuantity

/-- Meter readout of one coordinate of a physical figure point. -/
def coordinateInMeters (point : PlanePoint) : CoordinateAxis → ℝ
  | .x => signedLengthInMeters point.horizontal
  | .y => signedLengthInMeters point.vertical

/-!
The physical quantities, figure-labelled objects, paths, and phase observable.

`observationPointPAtMeters x` is the point labelled `P` whose nonnegative
horizontal coordinate is read as `x` meters. The path lengths and their
geometric difference remain dimensionful. No field assigns a numerical value
to the requested coordinate `x` or selects an answer choice.
-/
structure TwoPointSourceInterferenceSetup where
  propagationMedium : AcousticMedium
  sourceKind : SourceLabel → AcousticSourceKind
  sourceFigurePoint : SourceLabel → FigurePointLabel
  sourcePosition : SourceLabel → PlanePoint
  observationPointLabel : FigurePointLabel
  observationPointPAtMeters : ℝ → PlanePoint
  sourceSeparationD : LengthQuantity
  soundWavelengthLambda : LengthQuantity
  sourcesMutuallyCoherent : Prop
  emittedPhaseCycles : SourceLabel → ℝ
  bothWavesOverlapAtP : ℝ → Prop
  pathLengthToP : SourceLabel → ℝ → LengthQuantity
  geometricPathDifference : ℝ → LengthQuantity
  phaseDifferenceInWavelengthsAt : ℝ → ℝ
  requestedPhaseDifferenceInWavelengths : ℝ

/-! ## Scenario, readouts, and primary-figure geometry -/

/-!
The qualitative acoustic description: the sources are isotropic, mutually
coherent, and initially in phase in one common medium. Isotropic propagation
also makes both waves available to overlap at every pictured point on the
nonnegative `x` axis. This contains no distinguished distance.
-/
def MatchesCoherentInPhaseSourceDescription
    (setup : TwoPointSourceInterferenceSetup) : Prop :=
  setup.propagationMedium = .ambientAir ∧
    (∀ source : SourceLabel,
      setup.sourceKind source = .isotropicPointSource) ∧
    setup.sourcesMutuallyCoherent ∧
    setup.emittedPhaseCycles .S₁ = setup.emittedPhaseCycles .S₂ ∧
    ∀ x : ℝ, 0 ≤ x → setup.bothWavesOverlapAtP x

/-!
Numerical data stated in the problem and question: `lambda = 2.00 m`,
`d = 16.0 m`, and the requested phase difference is `1.50` wavelengths.
No observation distance or answer-choice value occurs in these readouts.
-/
def MatchesProblemAndQuestionReadouts
    (setup : TwoPointSourceInterferenceSetup) : Prop :=
  lengthInMeters setup.soundWavelengthLambda = 2 ∧
    lengthInMeters setup.sourceSeparationD = 16 ∧
    setup.requestedPhaseDifferenceInWavelengths = 3 / 2

/-!
Coordinate and label information read from the primary image. `S₁` is at the
axes' intersection, `S₂` is directly below it by `d`, and the point `P` runs
along the nonnegative `x` axis. These are figure readouts only; they contain no
phase condition.
-/
def MatchesSuppliedFigure
    (setup : TwoPointSourceInterferenceSetup) : Prop :=
  setup.sourceFigurePoint .S₁ = .S₁ ∧
    setup.sourceFigurePoint .S₂ = .S₂ ∧
    setup.observationPointLabel = .P ∧
    coordinateInMeters (setup.sourcePosition .S₁) .x = 0 ∧
    coordinateInMeters (setup.sourcePosition .S₁) .y = 0 ∧
    coordinateInMeters (setup.sourcePosition .S₂) .x = 0 ∧
    coordinateInMeters (setup.sourcePosition .S₁) .y -
        coordinateInMeters (setup.sourcePosition .S₂) .y =
      lengthInMeters setup.sourceSeparationD ∧
    ∀ x : ℝ, 0 ≤ x →
      coordinateInMeters (setup.observationPointPAtMeters x) .x = x ∧
        coordinateInMeters (setup.observationPointPAtMeters x) .y = 0

/-- Positivity and nondegeneracy of the physical wave and path quantities. -/
def HasPhysicalAcousticParameters
    (setup : TwoPointSourceInterferenceSetup) : Prop :=
  0 < lengthInMeters setup.soundWavelengthLambda ∧
    0 < lengthInMeters setup.sourceSeparationD ∧
    0 < setup.requestedPhaseDifferenceInWavelengths ∧
    ∀ (source : SourceLabel) (x : ℝ), 0 ≤ x →
      0 ≤ lengthInMeters (setup.pathLengthToP source x)

/-! ## Governing geometric and acoustic laws -/

/-!
Straight-line Euclidean propagation geometry on the horizontal observation
ray. A point `x` meters from `S₁` is `x` meters from `S₁` and
`sqrt (x^2 + d^2)` meters from `S₂`. This law is quantified over arbitrary
nonnegative `x` and does not single out the requested phase condition.
-/
structure SatisfiesPerpendicularPathGeometry
    (setup : TwoPointSourceInterferenceSetup) : Prop where
  pathLengths : ∀ x : ℝ, 0 ≤ x →
    lengthInMeters (setup.pathLengthToP .S₁ x) = x ∧
      lengthInMeters (setup.pathLengthToP .S₂ x) =
        Real.sqrt (x ^ 2 + lengthInMeters setup.sourceSeparationD ^ 2)

/-!
In one homogeneous medium, the geometric propagation-path difference is the
magnitude of the difference of the two source-to-observer path lengths. The
relation is required in every length unit and contains no requested value.
-/
structure SatisfiesGeometricPathDifferenceLaw
    (setup : TwoPointSourceInterferenceSetup) : Prop where
  pathDifferenceMagnitude : ∀ (x : ℝ) (unit : LengthUnit), 0 ≤ x →
    lengthReadout unit (setup.geometricPathDifference x) =
      |lengthReadout unit (setup.pathLengthToP .S₂ x) -
        lengthReadout unit (setup.pathLengthToP .S₁ x)|

/-!
For coherent in-phase sources, phase difference measured in wavelength cycles
is geometric path difference divided by wavelength. Stating the ratio in every
length unit records its dimensionless physical meaning. This is a general wave
law and does not assert where a particular phase occurs.
-/
structure SatisfiesInPhaseAcousticPhaseLaw
    (setup : TwoPointSourceInterferenceSetup) : Prop where
  phaseDifferenceFromPathDifference :
    ∀ (x : ℝ) (unit : LengthUnit), 0 ≤ x →
      setup.phaseDifferenceInWavelengthsAt x =
        lengthReadout unit (setup.geometricPathDifference x) /
          lengthReadout unit setup.soundWavelengthLambda

/-! ## Requested distance and displayed answers -/

/-- A nonnegative meter coordinate at which the question's phase occurs. -/
def HasRequestedPhaseDifferenceAtMeters
    (setup : TwoPointSourceInterferenceSetup) (x : ℝ) : Prop :=
  0 ≤ x ∧
    setup.phaseDifferenceInWavelengthsAt x =
      setup.requestedPhaseDifferenceInWavelengths

/-- The set of all nonnegative meter coordinates satisfying the question. -/
def requestedPhaseDistanceSetMeters
    (setup : TwoPointSourceInterferenceSetup) : Set ℝ :=
  {x | HasRequestedPhaseDifferenceAtMeters setup x}

/-- Labels of the four displayed multiple-choice answers. -/
inductive AnswerChoice where
  | A
  | B
  | C
  | D
  deriving DecidableEq, Repr

/-- Distance in meters printed beside each answer label. -/
def displayedDistanceInMeters : AnswerChoice → ℝ
  | .A => 193 / 5
  | .B => 199 / 5
  | .C => 203 / 5
  | .D => 206 / 5

/-!
An exact distance rounds to a displayed tenth-meter choice when it differs
from that printed value by less than half of `0.1 m`.
-/
def RoundsToDisplayedDistance (x : ℝ) (choice : AnswerChoice) : Prop :=
  |x - displayedDistanceInMeters choice| < 1 / 20

/-- Exactly one displayed value agrees with the exact derived distance. -/
def IsUniqueMatchingAnswer (x : ℝ) (choice : AnswerChoice) : Prop :=
  RoundsToDisplayedDistance x choice ∧
    ∀ other : AnswerChoice,
      RoundsToDisplayedDistance x other → other = choice

/-!
The perpendicular-path and in-phase wave laws determine the unique exact
coordinate `x = 247/6 m` for a `3/2`-wavelength phase difference. The exact
value occurs only in this conclusion, not in setup data or governing laws.
-/
lemma requestedPhaseDistanceSet_eq_singleton
    (setup : TwoPointSourceInterferenceSetup)
    (h_readouts : MatchesProblemAndQuestionReadouts setup)
    (h_physical : HasPhysicalAcousticParameters setup)
    (h_geometry : SatisfiesPerpendicularPathGeometry setup)
    (h_pathDifference : SatisfiesGeometricPathDifferenceLaw setup)
    (h_phase : SatisfiesInPhaseAcousticPhaseLaw setup) :
    requestedPhaseDistanceSetMeters setup = {(247 / 6 : ℝ)} := by
  rcases h_readouts with ⟨h_wavelength, h_separation, h_requested_value⟩
  ext x
  simp only [requestedPhaseDistanceSetMeters, Set.mem_setOf_eq,
    HasRequestedPhaseDifferenceAtMeters, Set.mem_singleton_iff]
  constructor
  · rintro ⟨hx, h_requested⟩
    have h_paths := h_geometry.pathLengths x hx
    have h_path_difference :=
      h_pathDifference.pathDifferenceMagnitude x LengthUnit.meters hx
    have h_phase_difference :=
      h_phase.phaseDifferenceFromPathDifference x LengthUnit.meters hx
    change
      lengthInMeters (setup.geometricPathDifference x) =
        |lengthInMeters (setup.pathLengthToP .S₂ x) -
          lengthInMeters (setup.pathLengthToP .S₁ x)|
      at h_path_difference
    change
      setup.phaseDifferenceInWavelengthsAt x =
        lengthInMeters (setup.geometricPathDifference x) /
          lengthInMeters setup.soundWavelengthLambda
      at h_phase_difference
    rw [h_path_difference, h_paths.1, h_paths.2, h_separation,
      h_wavelength] at h_phase_difference
    have h_phase_value :
        setup.phaseDifferenceInWavelengthsAt x = 3 / 2 :=
      h_requested.trans h_requested_value
    have h_abs :
        |Real.sqrt (x ^ 2 + 256) - x| = 3 := by
      norm_num at h_phase_difference h_phase_value
      linarith
    have h_radicand_nonnegative :
        0 ≤ x ^ 2 + (256 : ℝ) := by positivity
    have h_sqrt_sq :=
      Real.sq_sqrt h_radicand_nonnegative
    have h_sqrt_nonnegative :=
      Real.sqrt_nonneg (x ^ 2 + (256 : ℝ))
    have h_difference_nonnegative :
        0 ≤ Real.sqrt (x ^ 2 + 256) - x := by
      nlinarith
    rw [abs_of_nonneg h_difference_nonnegative] at h_abs
    nlinarith
  · intro hx
    subst x
    constructor
    · norm_num
    · have hx_nonnegative : (0 : ℝ) ≤ 247 / 6 := by norm_num
      have h_paths := h_geometry.pathLengths (247 / 6) hx_nonnegative
      have h_path_difference :=
        h_pathDifference.pathDifferenceMagnitude
          (247 / 6) LengthUnit.meters hx_nonnegative
      have h_phase_difference :=
        h_phase.phaseDifferenceFromPathDifference
          (247 / 6) LengthUnit.meters hx_nonnegative
      change
        lengthInMeters (setup.geometricPathDifference (247 / 6)) =
          |lengthInMeters (setup.pathLengthToP .S₂ (247 / 6)) -
            lengthInMeters (setup.pathLengthToP .S₁ (247 / 6))|
        at h_path_difference
      change
        setup.phaseDifferenceInWavelengthsAt (247 / 6) =
          lengthInMeters (setup.geometricPathDifference (247 / 6)) /
            lengthInMeters setup.soundWavelengthLambda
        at h_phase_difference
      rw [h_path_difference, h_paths.1, h_paths.2, h_separation,
        h_wavelength] at h_phase_difference
      have h_sqrt :
          Real.sqrt (((247 / 6 : ℝ) ^ 2) + (16 : ℝ) ^ 2) =
            265 / 6 := by
        rw [show ((247 / 6 : ℝ) ^ 2) + (16 : ℝ) ^ 2 =
          (265 / 6 : ℝ) ^ 2 by norm_num]
        rw [Real.sqrt_sq_eq_abs]
        norm_num
      rw [h_sqrt] at h_phase_difference
      norm_num at h_phase_difference
      rw [h_requested_value]
      exact h_phase_difference

/-!
For the pictured coherent sources with `lambda = 2.00 m` and `d = 16.0 m`,
the unique exact distance is `247/6 m`, approximately `41.1667 m`. It rounds
to `41.2 m`, uniquely selecting answer choice D.

This formalizes `thm:physics:phyx_mini_0316:target`.
-/
theorem problem_phyx_mini_0316
    (setup : TwoPointSourceInterferenceSetup)
    (h_sources : MatchesCoherentInPhaseSourceDescription setup)
    (h_readouts : MatchesProblemAndQuestionReadouts setup)
    (h_figure : MatchesSuppliedFigure setup)
    (h_physical : HasPhysicalAcousticParameters setup)
    (h_geometry : SatisfiesPerpendicularPathGeometry setup)
    (h_pathDifference : SatisfiesGeometricPathDifferenceLaw setup)
    (h_phase : SatisfiesInPhaseAcousticPhaseLaw setup) :
    requestedPhaseDistanceSetMeters setup = {(247 / 6 : ℝ)} ∧
      IsUniqueMatchingAnswer (247 / 6 : ℝ) .D := by
  constructor
  · exact requestedPhaseDistanceSet_eq_singleton setup h_readouts h_physical
      h_geometry h_pathDifference h_phase
  · constructor
    · norm_num [RoundsToDisplayedDistance, displayedDistanceInMeters]
    · intro other h_other
      cases other with
      | A => norm_num [RoundsToDisplayedDistance, displayedDistanceInMeters] at h_other
      | B => norm_num [RoundsToDisplayedDistance, displayedDistanceInMeters] at h_other
      | C => norm_num [RoundsToDisplayedDistance, displayedDistanceInMeters] at h_other
      | D => rfl

end PhyXMiniProblems.ProblemPhyXMini0316
