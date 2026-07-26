import Mathlib
import Physlib.Units.WithDim.Speed

/-!
# Axial acoustic interference in a cylindrical helium waveguide

This file models problem `phyx_mini_0118`.  A small source at the centre of
the left end of a cylindrical tube emits a tone.  The primary figure compares
the direct axial ray with a ray that reflects once from the cylindrical wall
and then reaches a labelled axial point at distance `d`.

Lengths, frequency, and propagation speed are represented by Physlib
dimensionful quantities.  Real numbers below are only readouts in named SI or
centimetre units, dimensionless interference orders, or answer labels.
-/

noncomputable section

namespace PhyXMiniProblems.ProblemPhyXMini0118

open Dimension

/-! ## Dimensionful acoustic quantities and unit readouts -/

/-- A physical length, independent of the unit system used to read it. -/
abbrev AcousticLength : Type := Dimensionful (WithDim L𝓭 ℝ)

/-- A physical frequency, carrying the inverse-time dimension. -/
abbrev AcousticFrequency : Type := Dimensionful (WithDim T𝓭⁻¹ ℝ)

/-- A physical propagation speed, carrying the length-per-time dimension. -/
abbrev AcousticSpeed : Type := DimSpeed

/-- Read a physical length as a real scalar in the specified length unit. -/
def lengthValueIn (unit : LengthUnit) (length : AcousticLength) : ℝ :=
  (length ({ UnitChoices.SI with length := unit } : UnitChoices)).val

/-- The metre readout used in the governing equations. -/
def metersValue (length : AcousticLength) : ℝ :=
  lengthValueIn LengthUnit.meters length

/-- The centimetre readout used by the displayed answer choices. -/
def centimetersValue (length : AcousticLength) : ℝ :=
  lengthValueIn LengthUnit.centimeters length

/-- The hertz readout of a dimensionful frequency. -/
def hertzValue (frequency : AcousticFrequency) : ℝ :=
  (frequency UnitChoices.SI).val

/-- The metres-per-second readout of a dimensionful speed. -/
def metersPerSecondValue (speed : AcousticSpeed) : ℝ :=
  (speed UnitChoices.SI).val

/-! ## Physical apparatus and figure labels -/

/-- The two gases contrasted by the problem statement. -/
inductive TubeGas where
  | air
  | helium
  deriving DecidableEq, Repr

/--
The physical quantities in the cylindrical waveguide and its depicted
one-reflection ray construction.

The source centre is the axial and radial origin.  The wall-reflection point
has axial coordinate `reflectionAxialCoordinate` and radial coordinate equal
to `tubeRadius`.  The labelled pressure point lies back on the axis at
coordinate `axialNodeDistanceD`.
-/
structure CylindricalAcousticWaveguide where
  /-- Radius `r` of the cylindrical tube. -/
  tubeRadius : AcousticLength
  /-- Length of the drawn tube; the point labelled by `d` lies before its far end. -/
  tubeLength : AcousticLength
  /-- Frequency `f` emitted by the small source at the centre of the end face. -/
  toneFrequency : AcousticFrequency
  /-- Actual gas filling the tube. -/
  fillingGas : TubeGas
  /-- Propagation speed of sound in each of the two mentioned gases. -/
  soundSpeed : TubeGas → AcousticSpeed
  /-- Wavelength of the emitted tone in each of the two mentioned gases. -/
  wavelength : TubeGas → AcousticLength
  /-- Requested axial source-to-pressure-point distance `d`. -/
  axialNodeDistanceD : AcousticLength
  /-- Axial coordinate of the purple ray's reflection point on the wall. -/
  reflectionAxialCoordinate : AcousticLength
  /-- Source-to-wall segment of the purple reflected ray. -/
  incidentSegmentLength : AcousticLength
  /-- Wall-to-axis-point segment of the purple reflected ray. -/
  outgoingSegmentLength : AcousticLength
  /-- Length of the dashed direct axial ray from the source to the labelled point. -/
  directRayLength : AcousticLength
  /-- Total length of the one-bounce purple ray. -/
  reflectedRayLength : AcousticLength
  /-- Positive integer wavelength order of the stated constructive interference. -/
  constructiveOrder : ℕ

/--
Qualitative information supplied by the problem text and primary figure.
The source is at the centre of the left end, the labelled point is inside the
long tube, and helium rather than air fills the tube.  No requested numerical
value of `d` occurs here.
-/
def MatchesProblemAndFigure (setup : CylindricalAcousticWaveguide) : Prop :=
  setup.fillingGas = .helium ∧
    0 < metersValue setup.tubeRadius ∧
    0 < metersValue setup.tubeLength ∧
    0 < metersValue setup.axialNodeDistanceD ∧
    metersValue setup.axialNodeDistanceD < metersValue setup.tubeLength ∧
    0 < metersValue setup.reflectionAxialCoordinate ∧
    metersValue setup.reflectionAxialCoordinate <
      metersValue setup.axialNodeDistanceD

/-- Positivity conditions for the acoustic and ray-path quantities. -/
def HasPhysicalParameters (setup : CylindricalAcousticWaveguide) : Prop :=
  0 < hertzValue setup.toneFrequency ∧
    (∀ gas, 0 < metersPerSecondValue (setup.soundSpeed gas)) ∧
    (∀ gas, 0 < metersValue (setup.wavelength gas)) ∧
    0 < metersValue setup.incidentSegmentLength ∧
    0 < metersValue setup.outgoingSegmentLength ∧
    0 < metersValue setup.directRayLength ∧
    0 < metersValue setup.reflectedRayLength ∧
    0 < setup.constructiveOrder

/--
Euclidean and specular-reflection laws for the ray shown in the figure.

With the source and observation point both on the tube axis, specular
reflection puts the wall contact halfway between them.  The two squared
segment equations are the Pythagorean relations for the triangles with radial
leg `r`.  These equations describe the ray geometry and do not solve for `d`.
-/
structure SatisfiesDepictedRayGeometry
    (setup : CylindricalAcousticWaveguide) : Prop where
  direct_path_is_axial_distance :
    metersValue setup.directRayLength =
      metersValue setup.axialNodeDistanceD
  reflection_is_axial_midpoint :
    metersValue setup.reflectionAxialCoordinate =
      metersValue setup.axialNodeDistanceD / 2
  incident_segment_pythagorean :
    metersValue setup.incidentSegmentLength ^ 2 =
      metersValue setup.reflectionAxialCoordinate ^ 2 +
        metersValue setup.tubeRadius ^ 2
  outgoing_segment_pythagorean :
    metersValue setup.outgoingSegmentLength ^ 2 =
      (metersValue setup.axialNodeDistanceD -
          metersValue setup.reflectionAxialCoordinate) ^ 2 +
        metersValue setup.tubeRadius ^ 2
  reflected_path_is_segment_sum :
    metersValue setup.reflectedRayLength =
      metersValue setup.incidentSegmentLength +
        metersValue setup.outgoingSegmentLength

/--
The acoustic propagation and constructive-interference laws.

For each gas, `c = λ f`.  At the labelled axial pressure point, the excess of
the one-bounce path over the direct path is a positive integer number of
wavelengths in the gas actually filling the tube.  The latter follows the
problem's own description of the labelled pressure point as arising from
constructive interference.
-/
structure SatisfiesAcousticInterferenceLaws
    (setup : CylindricalAcousticWaveguide) : Prop where
  wave_speed_relation : ∀ gas,
    metersPerSecondValue (setup.soundSpeed gas) =
      metersValue (setup.wavelength gas) * hertzValue setup.toneFrequency
  constructive_path_difference :
    metersValue setup.reflectedRayLength -
        metersValue setup.directRayLength =
      (setup.constructiveOrder : ℝ) *
        metersValue (setup.wavelength setup.fillingGas)

/-! ## Derived distance relation and displayed answers -/

/--
Solving the one-bounce geometry and the integer-wavelength path-difference
law gives the general axial distance formula

`d = (4 r² - (m λ)²) / (2 m λ)`.

This symbolic conclusion does not use the recorded numerical answer.
-/
lemma axialNodeDistance_formula
    (setup : CylindricalAcousticWaveguide)
    (h_figure : MatchesProblemAndFigure setup)
    (h_physical : HasPhysicalParameters setup)
    (h_geometry : SatisfiesDepictedRayGeometry setup)
    (h_acoustics : SatisfiesAcousticInterferenceLaws setup) :
    metersValue setup.axialNodeDistanceD =
      (4 * metersValue setup.tubeRadius ^ 2 -
          ((setup.constructiveOrder : ℝ) *
            metersValue (setup.wavelength setup.fillingGas)) ^ 2) /
        (2 * (setup.constructiveOrder : ℝ) *
          metersValue (setup.wavelength setup.fillingGas)) := by
  let d := metersValue setup.axialNodeDistanceD
  let r := metersValue setup.tubeRadius
  let x := metersValue setup.reflectionAxialCoordinate
  let incident := metersValue setup.incidentSegmentLength
  let outgoing := metersValue setup.outgoingSegmentLength
  let direct := metersValue setup.directRayLength
  let reflected := metersValue setup.reflectedRayLength
  let m : ℝ := setup.constructiveOrder
  let wavelength := metersValue (setup.wavelength setup.fillingGas)
  change d = (4 * r ^ 2 - (m * wavelength) ^ 2) / (2 * m * wavelength)
  rcases h_figure with ⟨_, _, _, hd, _, _, _⟩
  rcases h_physical with ⟨_, _, hwavelength, hincident, houtgoing, _, _, hm⟩
  have hm_real : 0 < m := by
    dsimp [m]
    exact_mod_cast hm
  have hwavelength_real : 0 < wavelength := hwavelength setup.fillingGas
  have hpath_difference : incident + outgoing - d = m * wavelength := by
    dsimp [incident, outgoing, d, m, wavelength, direct, reflected]
    rw [← h_geometry.reflected_path_is_segment_sum,
      ← h_geometry.direct_path_is_axial_distance]
    exact h_acoustics.constructive_path_difference
  have hsegments_equal : incident = outgoing := by
    dsimp [incident, outgoing, x, d, r] at *
    nlinarith [h_geometry.incident_segment_pythagorean,
      h_geometry.outgoing_segment_pythagorean,
      h_geometry.reflection_is_axial_midpoint]
  have hpolynomial :
      2 * d * (m * wavelength) + (m * wavelength) ^ 2 = 4 * r ^ 2 := by
    dsimp [incident, outgoing, x, d, r] at *
    nlinarith [h_geometry.incident_segment_pythagorean,
      h_geometry.reflection_is_axial_midpoint]
  have hdenominator : 2 * m * wavelength ≠ 0 := by
    positivity
  apply (eq_div_iff hdenominator).2
  nlinarith

/-- Labels of the four answers printed with the problem. -/
inductive AnswerChoice where
  | A
  | B
  | C
  | D
  deriving DecidableEq, Repr

/-- The centimetre value printed beside each answer label. -/
def AnswerChoice.centimeters : AnswerChoice → ℝ
  | .A => 113 / 10
  | .B => 131 / 10
  | .C => 123 / 10
  | .D => 132 / 10

/-- Agreement with an answer displayed to the nearest tenth of a centimetre. -/
def MatchesAnswerChoice
    (distance : AcousticLength) (choice : AnswerChoice) : Prop :=
  |centimetersValue distance - choice.centimeters| ≤ 1 / 20

/-- The answer label recorded in the supplied dataset metadata. -/
def recordedAnswerChoice : AnswerChoice := .A

/--
The dataset records `d = 11.3 cm`, answer A, to the displayed precision.

This formalizes `thm:physics:phyx_mini_0118:target`.  The supplied problem
text and figure do not include numerical readouts for `r`, `f`, or the helium
sound speed, so those missing source data will have to be restored before the
numerical conclusion can be proved from the governing laws.
-/
theorem axialNodeDistance_matches_recordedAnswerA
    (setup : CylindricalAcousticWaveguide)
    (h_figure : MatchesProblemAndFigure setup)
    (h_physical : HasPhysicalParameters setup)
    (h_geometry : SatisfiesDepictedRayGeometry setup)
    (h_acoustics : SatisfiesAcousticInterferenceLaws setup) :
    MatchesAnswerChoice setup.axialNodeDistanceD recordedAnswerChoice := by
  have h_symbolic_distance :=
    axialNodeDistance_formula setup h_figure h_physical h_geometry h_acoustics
  have h_unit_conversion :
      centimetersValue setup.axialNodeDistanceD =
        100 * metersValue setup.axialNodeDistanceD := by
    unfold centimetersValue metersValue lengthValueIn
    rw [setup.axialNodeDistanceD.2 UnitChoices.SI
      ({UnitChoices.SI with length := LengthUnit.centimeters} : UnitChoices)]
    simp [UnitChoices.dimScale, UnitChoices.SI, LengthUnit.centimeters,
      LengthUnit.scale, LengthUnit.div_eq_val, LengthUnit.meters]
    change ((10 ^ 2 : ℝ) * (setup.axialNodeDistanceD UnitChoices.SI).val) =
      100 * (setup.axialNodeDistanceD UnitChoices.SI).val
    ring
  unfold MatchesAnswerChoice recordedAnswerChoice AnswerChoice.centimeters
  rw [h_unit_conversion, h_symbolic_distance]
  -- The source supplies no numerical radius, frequency, sound speed, wavelength,
  -- or interference order with which to specialize `h_symbolic_distance`.
  sorry

end PhyXMiniProblems.ProblemPhyXMini0118
