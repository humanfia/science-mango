import Mathlib.Analysis.SpecialFunctions.Trigonometric.Complex
import Physlib.Units.WithDim.Pressure

noncomputable section

namespace PhyXMiniProblems.ProblemPhyXMini0192

open Dimension

/-!
# Quiet locations in front of a reflecting wall

A directional loudspeaker sends a longitudinal sound wave toward a rigid wall.
The reflected wave forms the one-dimensional standing-wave pattern shown in
the supplied image.  The labels `N` and `A` in that image are displacement
nodes and antinodes: the wall is a displacement node, while the points marked
`A` at distances `lambda/4`, `3 lambda/4`, and `5 lambda/4` from the wall are
displacement antinodes.  For a longitudinal sound wave, those displacement
antinodes are pressure nodes and hence quiet listening locations.

Lengths and acoustic pressure amplitudes below are genuine dimensionful
Physlib quantities.  Real numbers occur only as readouts in explicitly named
units and as dimensionless phase or answer-choice ratios.  In particular, the
setup, figure data, and standing-wave law do not assert that any location is
silent or that answer A is correct.
-/

/-! ## Dimensionful quantities and readouts -/

/-- A nonnegative physical length, independent of the unit used to read it. -/
abbrev LengthQuantity : Type := Dimensionful (WithDim L𝓭 NNReal)

/-- A signed acoustic excess-pressure amplitude. -/
abbrev AcousticPressureAmplitude : Type := DimPressure

/-- Read a physical length as a scalar in a selected length unit. -/
def lengthReadout (unit : LengthUnit) (length : LengthQuantity) : ℝ :=
  ((length {UnitChoices.SI with length := unit}).val : ℝ)

/-- Meter readout of a physical distance or wavelength. -/
def lengthInMeters (length : LengthQuantity) : ℝ :=
  lengthReadout LengthUnit.meters length

/-- Pascal readout of a signed acoustic excess-pressure amplitude. -/
def pressureAmplitudeInPascals
    (pressureAmplitude : AcousticPressureAmplitude) : ℝ :=
  (pressureAmplitude UnitChoices.SI).val

/-! ## Physical objects and labels from the primary image -/

/-- Kind of acoustic source on the left of the primary image. -/
inductive AcousticSourceKind where
  | directionalLoudspeaker
  deriving DecidableEq, Repr

/-- Boundary behavior of the vertical wall on the right of the image. -/
inductive AcousticBoundaryCondition where
  | rigidReflectingWall
  deriving DecidableEq, Repr

/-- Kind of wave established between the source and reflecting wall. -/
inductive AcousticWaveKind where
  | longitudinalStandingSoundWave
  deriving DecidableEq, Repr

/-- Displacement-amplitude labels denoted by `N` and `A` in the figure. -/
inductive DisplacementRole where
  | node
  | antinode
  deriving DecidableEq, Repr

/-!
Named axial locations in increasing distance from the wall.  The last point is
the additional `N` visible just to the right of the loudspeaker beam.
-/
inductive FigurePoint where
  | wall
  | firstAntinode
  | firstInteriorNode
  | secondAntinode
  | secondInteriorNode
  | thirdAntinode
  | outerNode
  deriving DecidableEq, Repr

/-- Positions and `N/A` annotations read from the supplied standing-wave image. -/
structure StandingWaveFigure where
  positionFromWall : FigurePoint → LengthQuantity
  displacementRole : FigurePoint → DisplacementRole

/-!
The physical standing-wave experiment.  `pressureAmplitudeAt` is the unknown
spatial pressure-amplitude field of the resulting wave, and
`wallPressureAmplitude` is its nonzero scale at the reflecting wall.  Neither
field is initialized with the requested quiet-location relation.
-/
structure LoudspeakerWallSetup where
  sourceKind : AcousticSourceKind
  wallBoundary : AcousticBoundaryCondition
  waveKind : AcousticWaveKind
  wavelength : LengthQuantity
  speakerDistanceFromWall : LengthQuantity
  wallPressureAmplitude : AcousticPressureAmplitude
  pressureAmplitudeAt : LengthQuantity → AcousticPressureAmplitude
  figure : StandingWaveFigure

/-- A distance lies on the modeled waveguide segment between wall and speaker. -/
def IsOnWavePath
    (setup : LoudspeakerWallSetup) (distanceFromWall : LengthQuantity) : Prop :=
  lengthInMeters distanceFromWall ≤
    lengthInMeters setup.speakerDistanceFromWall

/-!
The prose setup and all discrete or measured information taken from the
primary image.  The figure displays a displacement node at the wall and then
alternating antinodes and nodes at quarter-wavelength intervals.  Its three
dimension arrows terminate at the antinodes `lambda/4`, `3 lambda/4`, and
`5 lambda/4` from the wall.

These are geometric and displacement-role readouts only.  No field asserts
zero pressure, silence, or correctness of an answer choice.
-/
structure MatchesProblemAndFigure (setup : LoudspeakerWallSetup) : Prop where
  sourceIsDirectionalLoudspeaker :
    setup.sourceKind = .directionalLoudspeaker
  boundaryIsRigidReflectingWall :
    setup.wallBoundary = .rigidReflectingWall
  waveIsLongitudinalStandingSound :
    setup.waveKind = .longitudinalStandingSoundWave
  allFigurePointsOnWavePath :
    ∀ point, IsOnWavePath setup (setup.figure.positionFromWall point)
  wallPosition :
    lengthInMeters (setup.figure.positionFromWall .wall) = 0
  firstAntinodePosition :
    4 * lengthInMeters (setup.figure.positionFromWall .firstAntinode) =
      lengthInMeters setup.wavelength
  firstInteriorNodePosition :
    2 * lengthInMeters (setup.figure.positionFromWall .firstInteriorNode) =
      lengthInMeters setup.wavelength
  secondAntinodePosition :
    4 * lengthInMeters (setup.figure.positionFromWall .secondAntinode) =
      3 * lengthInMeters setup.wavelength
  secondInteriorNodePosition :
    lengthInMeters (setup.figure.positionFromWall .secondInteriorNode) =
      lengthInMeters setup.wavelength
  thirdAntinodePosition :
    4 * lengthInMeters (setup.figure.positionFromWall .thirdAntinode) =
      5 * lengthInMeters setup.wavelength
  outerNodePosition :
    2 * lengthInMeters (setup.figure.positionFromWall .outerNode) =
      3 * lengthInMeters setup.wavelength
  wallRole : setup.figure.displacementRole .wall = .node
  firstAntinodeRole :
    setup.figure.displacementRole .firstAntinode = .antinode
  firstInteriorNodeRole :
    setup.figure.displacementRole .firstInteriorNode = .node
  secondAntinodeRole :
    setup.figure.displacementRole .secondAntinode = .antinode
  secondInteriorNodeRole :
    setup.figure.displacementRole .secondInteriorNode = .node
  thirdAntinodeRole :
    setup.figure.displacementRole .thirdAntinode = .antinode
  outerNodeRole : setup.figure.displacementRole .outerNode = .node

/-- Positivity and nondegeneracy conditions for an audible incident wave. -/
structure HasPhysicalAcousticParameters (setup : LoudspeakerWallSetup) : Prop where
  wavelengthPositive : 0 < lengthInMeters setup.wavelength
  speakerDistancePositive :
    0 < lengthInMeters setup.speakerDistanceFromWall
  wallPressureAmplitudeNonzero :
    pressureAmplitudeInPascals setup.wallPressureAmplitude ≠ 0

/-!
The governing pressure profile for a one-dimensional wave reflected from a
rigid wall.  Taking distance `x` outward from the wall, the excess-pressure
amplitude is `P_wall cos(2 pi x / lambda)`.  Thus the wall itself is a pressure
antinode even though it is a displacement node.

This is a general standing-wave law.  It does not list the zeros of the cosine
and does not state any requested distance or answer choice.
-/
structure SatisfiesRigidWallStandingWavePressureLaw
    (setup : LoudspeakerWallSetup) : Prop where
  pressureProfile :
    ∀ distanceFromWall,
      IsOnWavePath setup distanceFromWall →
        pressureAmplitudeInPascals
            (setup.pressureAmplitudeAt distanceFromWall) =
          pressureAmplitudeInPascals setup.wallPressureAmplitude *
            Real.cos
              (2 * Real.pi * lengthInMeters distanceFromWall /
                lengthInMeters setup.wavelength)

/-! ## Silence and displayed answers -/

/--
A listener hears no sound from the modeled mode at a location on the wave
path exactly when the acoustic pressure amplitude there vanishes.
-/
def IsSilentStandingLocation
    (setup : LoudspeakerWallSetup) (distanceFromWall : LengthQuantity) : Prop :=
  IsOnWavePath setup distanceFromWall ∧
    pressureAmplitudeInPascals
      (setup.pressureAmplitudeAt distanceFromWall) = 0

/-- Labels of the four distance choices printed with the problem. -/
inductive AnswerChoice where
  | A
  | B
  | C
  | D
  deriving DecidableEq, Repr

/-- Dimensionless coefficient of `lambda` displayed beside an answer label. -/
def displayedWavelengthRatio : AnswerChoice → ℝ
  | .A => 1 / 4
  | .B => 1 / 2
  | .C => 1 / 8
  | .D => 1 / 3

/-- A physical distance has the wavelength ratio printed beside a choice. -/
def MatchesDisplayedDistance
    (setup : LoudspeakerWallSetup) (distanceFromWall : LengthQuantity)
    (choice : AnswerChoice) : Prop :=
  lengthInMeters distanceFromWall =
    displayedWavelengthRatio choice * lengthInMeters setup.wavelength

/-- A choice is physically possible when a silent point has its displayed ratio. -/
def IsPhysicallyCorrectChoice
    (setup : LoudspeakerWallSetup) (choice : AnswerChoice) : Prop :=
  ∃ distanceFromWall,
    IsSilentStandingLocation setup distanceFromWall ∧
      MatchesDisplayedDistance setup distanceFromWall choice

/-- Answer label recorded in the supplied dataset metadata. -/
def recordedDatasetAnswer : AnswerChoice := .A

/-!
Under the rigid-wall pressure law, silence is equivalent to the vanishing of
the cosine phase factor.  This intermediate result uses nonzero incident
amplitude but does not solve the cosine-zero equation.
-/
lemma silent_iff_cosine_phase_zero
    (setup : LoudspeakerWallSetup)
    (h_physical : HasPhysicalAcousticParameters setup)
    (h_wave : SatisfiesRigidWallStandingWavePressureLaw setup)
    (distanceFromWall : LengthQuantity) :
    IsSilentStandingLocation setup distanceFromWall ↔
      IsOnWavePath setup distanceFromWall ∧
        Real.cos
          (2 * Real.pi * lengthInMeters distanceFromWall /
            lengthInMeters setup.wavelength) = 0 := by
  constructor
  · rintro ⟨h_on_path, h_silent⟩
    refine ⟨h_on_path, ?_⟩
    have h_profile := h_wave.pressureProfile distanceFromWall h_on_path
    rw [h_silent] at h_profile
    exact
      (mul_eq_zero.mp h_profile.symm).resolve_left
        h_physical.wallPressureAmplitudeNonzero
  · rintro ⟨h_on_path, h_cosine⟩
    refine ⟨h_on_path, ?_⟩
    rw [h_wave.pressureProfile distanceFromWall h_on_path, h_cosine, mul_zero]

/-!
The complete family of quiet listening locations is the set of nonnegative
odd quarter-wavelengths which still lie between the wall and loudspeaker.
This conclusion is derived from the pressure law; it is not a premise.
-/
lemma silent_locations_are_odd_quarter_wavelengths
    (setup : LoudspeakerWallSetup)
    (h_physical : HasPhysicalAcousticParameters setup)
    (h_wave : SatisfiesRigidWallStandingWavePressureLaw setup) :
    ∀ distanceFromWall,
      IsSilentStandingLocation setup distanceFromWall ↔
        ∃ n : ℕ,
          lengthInMeters distanceFromWall =
              ((2 * n + 1 : ℕ) : ℝ) *
                lengthInMeters setup.wavelength / 4 ∧
            IsOnWavePath setup distanceFromWall := by
  intro distanceFromWall
  rw [silent_iff_cosine_phase_zero setup h_physical h_wave]
  constructor
  · rintro ⟨h_on_path, h_cosine⟩
    obtain ⟨k, h_phase⟩ := Real.cos_eq_zero_iff.mp h_cosine
    have h_distance_nonnegative :
        0 ≤ lengthInMeters distanceFromWall := by
      unfold lengthInMeters lengthReadout
      positivity
    have h_k_nonnegative : 0 ≤ k := by
      have h_phase_nonnegative :
          0 ≤
            2 * Real.pi * lengthInMeters distanceFromWall /
              lengthInMeters setup.wavelength := by
        exact
          div_nonneg
            (mul_nonneg
              (mul_nonneg (by norm_num) Real.pi_pos.le)
              h_distance_nonnegative)
            h_physical.wavelengthPositive.le
      rw [h_phase] at h_phase_nonnegative
      by_contra h_k_negative
      have h_k_le_neg_one : k ≤ -1 := by omega
      have h_k_le_neg_one_real : (k : ℝ) ≤ -1 := by
        exact_mod_cast h_k_le_neg_one
      nlinarith [Real.pi_pos]
    refine ⟨k.toNat, ?_, h_on_path⟩
    have h_k_cast : ((k.toNat : ℕ) : ℝ) = (k : ℝ) := by
      exact_mod_cast Int.toNat_of_nonneg h_k_nonnegative
    push_cast
    rw [h_k_cast]
    field_simp [ne_of_gt h_physical.wavelengthPositive] at h_phase
    nlinarith [Real.pi_pos]
  · rintro ⟨n, h_distance, h_on_path⟩
    refine ⟨h_on_path, ?_⟩
    rw [h_distance]
    apply Real.cos_eq_zero_iff.mpr
    refine ⟨(n : ℤ), ?_⟩
    push_cast
    field_simp [ne_of_gt h_physical.wavelengthPositive]
    ring

/-!
The first `A` in the image, marked at `lambda/4` from the wall, is a quiet
pressure node.  This connects the general pressure law to the particular
figure readout without treating the displayed `A` displacement label itself
as an assumption of silence.
-/
lemma first_pictured_antinode_is_silent
    (setup : LoudspeakerWallSetup)
    (h_figure : MatchesProblemAndFigure setup)
    (h_physical : HasPhysicalAcousticParameters setup)
    (h_wave : SatisfiesRigidWallStandingWavePressureLaw setup) :
    IsSilentStandingLocation setup
      (setup.figure.positionFromWall .firstAntinode) := by
  apply
    (silent_locations_are_odd_quarter_wavelengths
      setup h_physical h_wave
      (setup.figure.positionFromWall .firstAntinode)).mpr
  refine
    ⟨0, ?_,
      h_figure.allFigurePointsOnWavePath .firstAntinode⟩
  norm_num
  linarith [h_figure.firstAntinodePosition]

/-!
All silent points are at `lambda/4`, `3 lambda/4`, `5 lambda/4`, and so on,
within the available wave path.  Consequently choice A (`d = lambda/4`) is
possible, whereas the other displayed ratios are not.

This formalizes `thm:physics:phyx_mini_0192:target`.
-/
theorem problem_phyx_mini_0192
    (setup : LoudspeakerWallSetup)
    (h_figure : MatchesProblemAndFigure setup)
    (h_physical : HasPhysicalAcousticParameters setup)
    (h_wave : SatisfiesRigidWallStandingWavePressureLaw setup) :
    (∀ distanceFromWall,
      IsSilentStandingLocation setup distanceFromWall ↔
        ∃ n : ℕ,
          lengthInMeters distanceFromWall =
              ((2 * n + 1 : ℕ) : ℝ) *
                lengthInMeters setup.wavelength / 4 ∧
            IsOnWavePath setup distanceFromWall) ∧
      IsSilentStandingLocation setup
        (setup.figure.positionFromWall .firstAntinode) ∧
      IsPhysicallyCorrectChoice setup .A ∧
      ¬ IsPhysicallyCorrectChoice setup .B ∧
      ¬ IsPhysicallyCorrectChoice setup .C ∧
      ¬ IsPhysicallyCorrectChoice setup .D ∧
      recordedDatasetAnswer = .A := by
  have h_silent_locations :=
    silent_locations_are_odd_quarter_wavelengths
      setup h_physical h_wave
  have h_first_silent :=
    first_pictured_antinode_is_silent
      setup h_figure h_physical h_wave
  have h_ratio_of_correct_choice :
      ∀ choice,
        IsPhysicallyCorrectChoice setup choice →
          ∃ n : ℕ,
            ((2 * n + 1 : ℕ) : ℝ) / 4 =
              displayedWavelengthRatio choice := by
    intro choice h_correct
    obtain ⟨distanceFromWall, h_silent, h_matches⟩ := h_correct
    obtain ⟨n, h_odd_quarter, _⟩ :=
      (h_silent_locations distanceFromWall).mp h_silent
    refine ⟨n, ?_⟩
    apply
      mul_right_cancel₀
        (ne_of_gt h_physical.wavelengthPositive)
    calc
      (((2 * n + 1 : ℕ) : ℝ) / 4) *
            lengthInMeters setup.wavelength =
          ((2 * n + 1 : ℕ) : ℝ) *
            lengthInMeters setup.wavelength / 4 := by ring
      _ = lengthInMeters distanceFromWall := h_odd_quarter.symm
      _ =
          displayedWavelengthRatio choice *
            lengthInMeters setup.wavelength := h_matches
  refine
    ⟨h_silent_locations, h_first_silent, ?_, ?_, ?_, ?_, rfl⟩
  · refine
      ⟨setup.figure.positionFromWall .firstAntinode,
        h_first_silent, ?_⟩
    unfold MatchesDisplayedDistance
    norm_num [displayedWavelengthRatio]
    linarith [h_figure.firstAntinodePosition]
  · intro h_correct
    obtain ⟨n, h_ratio⟩ :=
      h_ratio_of_correct_choice .B h_correct
    rcases n with _ | n
    · norm_num [displayedWavelengthRatio] at h_ratio
    · push_cast at h_ratio
      norm_num [displayedWavelengthRatio] at h_ratio
      have h_n_nonnegative : (0 : ℝ) ≤ n := by positivity
      nlinarith
  · intro h_correct
    obtain ⟨n, h_ratio⟩ :=
      h_ratio_of_correct_choice .C h_correct
    push_cast at h_ratio
    norm_num [displayedWavelengthRatio] at h_ratio
    have h_n_nonnegative : (0 : ℝ) ≤ n := by positivity
    nlinarith
  · intro h_correct
    obtain ⟨n, h_ratio⟩ :=
      h_ratio_of_correct_choice .D h_correct
    rcases n with _ | n
    · norm_num [displayedWavelengthRatio] at h_ratio
    · push_cast at h_ratio
      norm_num [displayedWavelengthRatio] at h_ratio
      have h_n_nonnegative : (0 : ℝ) ≤ n := by positivity
      nlinarith

end PhyXMiniProblems.ProblemPhyXMini0192
