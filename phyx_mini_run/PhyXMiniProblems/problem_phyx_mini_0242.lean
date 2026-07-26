import Mathlib
import Physlib.Units.WithDim.Basic

/- USER: The assigned Lean file did not exist when this autoformalization task began. -/

/-!
# A mass supported at the center of a taut string

This file models problem `phyx_mini_0242`.  A light string of total length
`L` is tied between two walls whose tie points are separated by `3L/4`.  The
suspended object is attached at the center of the string, so each straight
segment has length `L/2`.  The requested transverse-wave speed determines the
string tension, and vertical static equilibrium then determines the mass.

All physical magnitudes are unit-independent Physlib `Dimensionful`
quantities.  Real numbers are used only for coherent unit readouts, planar
coordinates measured in meters, dimensionless ratios, and displayed answer
values.
-/

noncomputable section

namespace PhyXMiniProblems.ProblemPhyXMini0242

open Dimension

/-! ## Dimensionful physical quantities and coherent SI readouts -/

/-- A physical length. -/
abbrev LengthQuantity : Type := Dimensionful (WithDim L𝓭 NNReal)

/-- A physical mass. -/
abbrev MassQuantity : Type := Dimensionful (WithDim M𝓭 NNReal)

/-- A physical mass per unit length, with dimension `M L⁻¹`. -/
abbrev LinearMassDensityQuantity : Type :=
  Dimensionful (WithDim (M𝓭 * L𝓭⁻¹) NNReal)

/-- A physical propagation speed, with dimension `L T⁻¹`. -/
abbrev SpeedQuantity : Type :=
  Dimensionful (WithDim (L𝓭 * T𝓭⁻¹) NNReal)

/-- A physical acceleration magnitude, with dimension `L T⁻²`. -/
abbrev AccelerationQuantity : Type :=
  Dimensionful (WithDim (L𝓭 * T𝓭⁻¹ * T𝓭⁻¹) NNReal)

/-- A physical force magnitude, used for tension and weight. -/
abbrev ForceQuantity : Type :=
  Dimensionful (WithDim (M𝓭 * L𝓭 * T𝓭⁻¹ * T𝓭⁻¹) NNReal)

/-- Read a nonnegative dimensionful quantity in a chosen coherent unit system. -/
def quantityReadout {d : Dimension}
    (units : UnitChoices) (quantity : Dimensionful (WithDim d NNReal)) : ℝ :=
  ((quantity units).val : ℝ)

/-- Meter readout of a physical length. -/
def lengthInMeters (length : LengthQuantity) : ℝ :=
  quantityReadout UnitChoices.SI length

/-- Kilogram readout of a physical mass. -/
def massInKilograms (mass : MassQuantity) : ℝ :=
  quantityReadout UnitChoices.SI mass

/-- Kilograms-per-meter readout of a physical linear mass density. -/
def linearMassDensityInKilogramsPerMeter
    (density : LinearMassDensityQuantity) : ℝ :=
  quantityReadout UnitChoices.SI density

/-- Meters-per-second readout of a physical speed. -/
def speedInMetersPerSecond (speed : SpeedQuantity) : ℝ :=
  quantityReadout UnitChoices.SI speed

/-- Meters-per-second-squared readout of an acceleration magnitude. -/
def accelerationInMetersPerSecondSquared
    (acceleration : AccelerationQuantity) : ℝ :=
  quantityReadout UnitChoices.SI acceleration

/-- Newton readout of a force magnitude in coherent SI base units. -/
def forceInNewtons (force : ForceQuantity) : ℝ :=
  quantityReadout UnitChoices.SI force

/-! ## Primary-figure labels and physical setup -/

/-- The two straight halves of the string shown in the figure. -/
inductive StringSide where
  | left
  | right
  deriving DecidableEq, Repr

/-- The three labeled geometric points visible in the primary figure. -/
inductive FigurePoint where
  | leftWallTie
  | suspendedObject
  | rightWallTie
  deriving DecidableEq, Repr

/-- The wall tie point belonging to a given half of the string. -/
def StringSide.wallTiePoint : StringSide → FigurePoint
  | .left => .leftWallTie
  | .right => .rightWallTie

/--
The complete state of the string and suspended object.  The planar coordinates
are scalar readouts in meters; all lengths and mechanical quantities remain
dimensionful objects.  No field assigns the suspended mass its requested
value.
-/
structure SuspendedStringSetup where
  /-- Position `(x,y)` in meters of each labeled point in the diagram. -/
  figurePositionInMeters : FigurePoint → ℝ × ℝ
  /-- Total string length, denoted by `L` in the figure. -/
  totalStringLength : LengthQuantity
  /-- Horizontal separation of the two wall tie points. -/
  wallSeparation : LengthQuantity
  /-- Length of each of the two straight string segments. -/
  segmentLength : StringSide → LengthQuantity
  /-- Horizontal projection of each straight string segment. -/
  horizontalProjection : StringSide → LengthQuantity
  /-- Vertical distance from the wall tie-point level to the object. -/
  verticalDrop : LengthQuantity
  /-- Uniform mass per unit length of the string. -/
  stringLinearMassDensity : LinearMassDensityQuantity
  /-- The mass `m` suspended at the string's midpoint. -/
  suspendedMass : MassQuantity
  /-- Requested transverse-wave propagation speed on the taut string. -/
  transverseWaveSpeed : SpeedQuantity
  /-- Tension magnitude in each side of the string. -/
  tension : StringSide → ForceQuantity
  /-- Local gravitational acceleration magnitude. -/
  gravitationalAcceleration : AccelerationQuantity
  /-- Downward weight magnitude of the suspended object. -/
  suspendedObjectWeight : ForceQuantity
  /-- The source's light-string idealization. -/
  stringIsLight : Bool
  /-- The source's statement that the object is attached at string center. -/
  objectAttachedAtStringCenter : Bool
  /-- Whether each displayed string endpoint is tied to its wall. -/
  endpointTiedToWall : StringSide → Bool

/-- Horizontal coordinate, in meters, of a labeled figure point. -/
def xCoordinateInMeters
    (setup : SuspendedStringSetup) (point : FigurePoint) : ℝ :=
  (setup.figurePositionInMeters point).1

/-- Vertical coordinate, in meters, of a labeled figure point. -/
def yCoordinateInMeters
    (setup : SuspendedStringSetup) (point : FigurePoint) : ℝ :=
  (setup.figurePositionInMeters point).2

/--
Data read directly from the prose and primary figure.  It records the
`8.00 g/m = 1/125 kg/m` density, the `60.0 m/s` wave speed, the two labels
`L/2`, the wall separation `3L/4`, the centered object, and the displayed
inverted-V geometry.  It contains no mass value.
-/
def MatchesProblemAndPrimaryFigure (setup : SuspendedStringSetup) : Prop :=
  setup.stringIsLight = true ∧
    setup.objectAttachedAtStringCenter = true ∧
    (∀ side : StringSide, setup.endpointTiedToWall side = true) ∧
    linearMassDensityInKilogramsPerMeter setup.stringLinearMassDensity =
      1 / 125 ∧
    speedInMetersPerSecond setup.transverseWaveSpeed = 60 ∧
    (∀ side : StringSide,
      lengthInMeters (setup.segmentLength side) =
        lengthInMeters setup.totalStringLength / 2) ∧
    lengthInMeters setup.wallSeparation =
      3 * lengthInMeters setup.totalStringLength / 4 ∧
    xCoordinateInMeters setup .rightWallTie -
        xCoordinateInMeters setup .leftWallTie =
      lengthInMeters setup.wallSeparation ∧
    xCoordinateInMeters setup .suspendedObject =
      (xCoordinateInMeters setup .leftWallTie +
        xCoordinateInMeters setup .rightWallTie) / 2 ∧
    yCoordinateInMeters setup .leftWallTie =
      yCoordinateInMeters setup .rightWallTie ∧
    (∀ side : StringSide,
      lengthInMeters (setup.horizontalProjection side) =
        |xCoordinateInMeters setup side.wallTiePoint -
          xCoordinateInMeters setup .suspendedObject|) ∧
    (∀ side : StringSide,
      lengthInMeters setup.verticalDrop =
        yCoordinateInMeters setup side.wallTiePoint -
          yCoordinateInMeters setup .suspendedObject)

/--
Each string half is a straight segment, so its length, horizontal projection,
and vertical drop obey the planar Pythagorean relation.  This is a governing
geometric law; it does not assume the derived `sqrt 7 / 4` direction ratio.
-/
structure SatisfiesStraightSegmentGeometry
    (setup : SuspendedStringSetup) : Prop where
  pythagorean : ∀ side : StringSide,
    lengthInMeters (setup.segmentLength side) ^ 2 =
      lengthInMeters (setup.horizontalProjection side) ^ 2 +
        lengthInMeters setup.verticalDrop ^ 2

/-- The standard classroom calibration `g = 9.80 m/s²`. -/
def UsesStandardGravity (setup : SuspendedStringSetup) : Prop :=
  accelerationInMetersPerSecondSquared setup.gravitationalAcceleration = 49 / 5

/-- Positivity conditions for a nondegenerate taut-string configuration. -/
def HasPositivePhysicalParameters (setup : SuspendedStringSetup) : Prop :=
  0 < lengthInMeters setup.totalStringLength ∧
    0 < lengthInMeters setup.wallSeparation ∧
    (∀ side : StringSide, 0 < lengthInMeters (setup.segmentLength side)) ∧
    (∀ side : StringSide, 0 < lengthInMeters (setup.horizontalProjection side)) ∧
    0 < lengthInMeters setup.verticalDrop ∧
    0 < linearMassDensityInKilogramsPerMeter setup.stringLinearMassDensity ∧
    0 < speedInMetersPerSecond setup.transverseWaveSpeed ∧
    (∀ side : StringSide, 0 < forceInNewtons (setup.tension side)) ∧
    0 < massInKilograms setup.suspendedMass ∧
    0 < accelerationInMetersPerSecondSquared setup.gravitationalAcceleration ∧
    0 < forceInNewtons setup.suspendedObjectWeight

/-! ## Governing wave and mechanical laws -/

/--
The taut-string wave law, weight law, light-string tension equality, and
vertical force balance.  The last equation resolves each tension along its
straight string segment; no numerical mass or answer choice occurs here.
-/
structure SatisfiesWaveAndStaticEquilibriumLaws
    (setup : SuspendedStringSetup) : Prop where
  taut_string_wave_law : ∀ side : StringSide,
    forceInNewtons (setup.tension side) =
      linearMassDensityInKilogramsPerMeter setup.stringLinearMassDensity *
        speedInMetersPerSecond setup.transverseWaveSpeed ^ 2
  light_string_uniform_tension :
    forceInNewtons (setup.tension .left) =
      forceInNewtons (setup.tension .right)
  weight_law :
    forceInNewtons setup.suspendedObjectWeight =
      massInKilograms setup.suspendedMass *
        accelerationInMetersPerSecondSquared setup.gravitationalAcceleration
  vertical_static_equilibrium :
    forceInNewtons setup.suspendedObjectWeight =
      forceInNewtons (setup.tension .left) *
          (lengthInMeters setup.verticalDrop /
            lengthInMeters (setup.segmentLength .left)) +
        forceInNewtons (setup.tension .right) *
          (lengthInMeters setup.verticalDrop /
            lengthInMeters (setup.segmentLength .right))

/-! ## Derived geometry, exact mass, and displayed answer -/

/--
The figure labels and straight-segment geometry imply that the vertical
direction ratio of either string half is `sqrt 7 / 4`.  This relation is
derived rather than included among the figure readouts.
-/
lemma verticalComponentRatio_eq_sqrtSevenOverFour
    (setup : SuspendedStringSetup)
    (h_figure : MatchesProblemAndPrimaryFigure setup)
    (h_geometry : SatisfiesStraightSegmentGeometry setup)
    (h_positive : HasPositivePhysicalParameters setup) :
    ∀ side : StringSide,
      lengthInMeters setup.verticalDrop /
          lengthInMeters (setup.segmentLength side) =
        Real.sqrt 7 / 4 := by
  rcases h_figure with
    ⟨_, _, _, _, _, h_segment, h_wall_sep, h_wall_coords, h_center, _,
      h_horizontal, _⟩
  rcases h_positive with
    ⟨h_total_pos, _, _, _, h_drop_pos, _⟩
  intro side
  have h_horizontal_value :
      lengthInMeters (setup.horizontalProjection side) =
        3 * lengthInMeters setup.totalStringLength / 8 := by
    rw [h_horizontal side, h_center]
    cases side with
    | left =>
        simp only [StringSide.wallTiePoint]
        rw [abs_of_nonpos]
        · linarith [h_wall_coords, h_wall_sep]
        · linarith [h_wall_coords, h_wall_sep]
    | right =>
        simp only [StringSide.wallTiePoint]
        rw [abs_of_nonneg]
        · linarith [h_wall_coords, h_wall_sep]
        · linarith [h_wall_coords, h_wall_sep]
  have h_pythagorean := h_geometry.pythagorean side
  rw [h_segment side, h_horizontal_value] at h_pythagorean
  have hsqrt : (Real.sqrt 7) ^ 2 = 7 :=
    Real.sq_sqrt (by norm_num)
  have hsquares :
      (8 * lengthInMeters setup.verticalDrop) ^ 2 =
        (Real.sqrt 7 * lengthInMeters setup.totalStringLength) ^ 2 := by
    nlinarith
  have hroot :
      8 * lengthInMeters setup.verticalDrop =
        Real.sqrt 7 * lengthInMeters setup.totalStringLength := by
    rcases (sq_eq_sq_iff_eq_or_eq_neg).mp hsquares with h | h
    · exact h
    · have hnonneg : 0 ≤ Real.sqrt 7 := Real.sqrt_nonneg 7
      nlinarith
  rw [h_segment side]
  field_simp
  nlinarith

/--
The unrounded mass derived from `T = μv²` and vertical equilibrium is
`72 sqrt(7) / 49` kilograms.
-/
lemma suspendedMassInKilograms_eq_exact
    (setup : SuspendedStringSetup)
    (h_figure : MatchesProblemAndPrimaryFigure setup)
    (h_geometry : SatisfiesStraightSegmentGeometry setup)
    (h_gravity : UsesStandardGravity setup)
    (h_positive : HasPositivePhysicalParameters setup)
    (h_laws : SatisfiesWaveAndStaticEquilibriumLaws setup) :
    massInKilograms setup.suspendedMass = 72 * Real.sqrt 7 / 49 := by
  have h_ratio :=
    verticalComponentRatio_eq_sqrtSevenOverFour
      setup h_figure h_geometry h_positive
  have h_left_ratio := h_ratio .left
  have h_right_ratio := h_ratio .right
  rcases h_figure with ⟨_, _, _, h_density, h_speed, _⟩
  have h_left_tension := h_laws.taut_string_wave_law .left
  have h_right_tension := h_laws.taut_string_wave_law .right
  rw [h_density, h_speed] at h_left_tension h_right_tension
  norm_num at h_left_tension h_right_tension
  have h_weight := h_laws.weight_law
  have h_equilibrium := h_laws.vertical_static_equilibrium
  rw [h_weight, h_gravity, h_left_tension, h_right_tension,
    h_left_ratio, h_right_ratio] at h_equilibrium
  nlinarith

/-- Labels of the four answers printed with the problem. -/
inductive AnswerChoice where
  | A
  | B
  | C
  | D
  deriving DecidableEq, Repr

/-- Mass in kilograms printed beside each answer label. -/
def AnswerChoice.kilograms : AnswerChoice → ℝ
  | .A => 319 / 100
  | .B => 419 / 100
  | .C => 399 / 100
  | .D => 389 / 100

/-- The answer label recorded in the supplied dataset metadata. -/
def recordedAnswerChoice : AnswerChoice := .D

/--
Agreement with a kilogram value displayed to the nearest hundredth.  The
half-hundredth tolerance avoids identifying an unrounded physical value with
the printed decimal exactly.
-/
def MatchesAnswerChoice (mass : MassQuantity) (choice : AnswerChoice) : Prop :=
  |massInKilograms mass - choice.kilograms| < 1 / 200

/-!
The required mass is exactly `72 sqrt(7) / 49 kg`, which rounds to `3.89 kg`
and therefore selects answer D.

This formalizes `thm:physics:phyx_mini_0242:target`.
-/
theorem problem_phyx_mini_0242
    (setup : SuspendedStringSetup)
    (h_figure : MatchesProblemAndPrimaryFigure setup)
    (h_geometry : SatisfiesStraightSegmentGeometry setup)
    (h_gravity : UsesStandardGravity setup)
    (h_positive : HasPositivePhysicalParameters setup)
    (h_laws : SatisfiesWaveAndStaticEquilibriumLaws setup) :
    massInKilograms setup.suspendedMass = 72 * Real.sqrt 7 / 49 ∧
      MatchesAnswerChoice setup.suspendedMass recordedAnswerChoice := by
  have h_mass :=
    suspendedMassInKilograms_eq_exact
      setup h_figure h_geometry h_gravity h_positive h_laws
  refine ⟨h_mass, ?_⟩
  simp only [MatchesAnswerChoice, recordedAnswerChoice, AnswerChoice.kilograms]
  rw [h_mass]
  have hsqrt_sq : (Real.sqrt 7) ^ 2 = 7 :=
    Real.sq_sqrt (by norm_num)
  have hsqrt_nonneg : 0 ≤ Real.sqrt 7 := Real.sqrt_nonneg 7
  rw [abs_of_nonpos]
  · nlinarith
  · nlinarith

end PhyXMiniProblems.ProblemPhyXMini0242
