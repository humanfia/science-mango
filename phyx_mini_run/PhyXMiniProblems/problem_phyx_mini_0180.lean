import Mathlib
import Physlib.Units.WithDim.Speed
import Physlib.SpaceAndTime.Space.LengthUnit

noncomputable section

namespace PhyXMiniProblems.ProblemPhyXMini0180

open Dimension

/-!
# Spring stretch for a standing wave on a steel wire

A wall-mounted spring tensions a steel wire.  An oscillating magnetic field
drives the wire transversely at a fixed frequency, while the spring stretch is
varied to select a fixed-end standing-wave mode.  The primary figure labels
the spring, steel wire, and rightward pull, and draws three antinodes.

Lengths, frequencies, tensions, spring stiffness, linear mass density, and
wave speeds are represented by dimensionful Physlib quantities.  Real numbers
are used only for scalar readouts in a specified unit system; in particular,
the data and requested answer are read in centimeters.
-/

/-- A signed physical length represented coherently in every choice of units. -/
abbrev DimLength : Type := Dimensionful (WithDim L𝓭 ℝ)

/-- A physical frequency, with dimension inverse time. -/
abbrev DimFrequency : Type := Dimensionful (WithDim T𝓭⁻¹ ℝ)

/-- A tensile force, with dimension mass times length per time squared. -/
abbrev DimTension : Type :=
  Dimensionful (WithDim (M𝓭 * L𝓭 * T𝓭⁻¹ * T𝓭⁻¹) ℝ)

/-- Spring stiffness, with dimension force per length. -/
abbrev DimSpringStiffness : Type :=
  Dimensionful (WithDim (M𝓭 * T𝓭⁻¹ * T𝓭⁻¹) ℝ)

/-- Linear mass density, with dimension mass per length. -/
abbrev DimLinearMassDensity : Type :=
  Dimensionful (WithDim (M𝓭 * L𝓭⁻¹) ℝ)

/-- SI base units with centimeters selected as the length unit. -/
noncomputable def centimeterUnitChoices : UnitChoices :=
  { UnitChoices.SI with length := LengthUnit.centimeters }

/-- The scalar centimeter readout of a physical length. -/
def lengthInCentimeters (length : DimLength) : ℝ :=
  (length centimeterUnitChoices).val

/-- The scalar readout of a frequency in a specified coherent unit system. -/
def frequencyInUnits (frequency : DimFrequency) (units : UnitChoices) : ℝ :=
  (frequency units).val

/-- The scalar readout of a tensile force in a specified coherent unit system. -/
def tensionInUnits (tension : DimTension) (units : UnitChoices) : ℝ :=
  (tension units).val

/-- The scalar readout of spring stiffness in a specified coherent unit system. -/
def springStiffnessInUnits
    (stiffness : DimSpringStiffness) (units : UnitChoices) : ℝ :=
  (stiffness units).val

/-- The scalar readout of linear mass density in a specified coherent unit system. -/
def linearMassDensityInUnits
    (density : DimLinearMassDensity) (units : UnitChoices) : ℝ :=
  (density units).val

/-- The real-valued scalar readout of Physlib's nonnegative speed quantity. -/
def speedInUnits (speed : DimSpeed) (units : UnitChoices) : ℝ :=
  (speed units).val

/-- Material classification of the vibrating wire. -/
inductive WireMaterial where
  | steel
  | other
  deriving DecidableEq, Repr

/-- How the spring is supported in the apparatus. -/
inductive SpringMount where
  | wall
  | free
  deriving DecidableEq, Repr

/-- Physical mechanism used to drive the wire. -/
inductive DriveMechanism where
  | oscillatingMagneticField
  | other
  deriving DecidableEq, Repr

/-- Qualitative motion produced by the drive. -/
inductive DrivenMotion where
  | backAndForth
  | static
  deriving DecidableEq, Repr

/-- The two endpoints of the horizontal wire in the source figure. -/
inductive WireEnd where
  | springSide
  | pulledSide
  deriving DecidableEq, Repr

/-- Horizontal directions used by the pull arrow. -/
inductive HorizontalDirection where
  | left
  | right
  deriving DecidableEq, Repr

/-- Boundary-node information for a standing wave on the wire segment. -/
inductive StandingWaveBoundary where
  | nodesAtBothEnds
  | other
  deriving DecidableEq, Repr

/-- Physical elements explicitly shown in the primary figure. -/
inductive FigureElement where
  | spring
  | steelWire
  | pullArrow
  deriving DecidableEq, Repr

/-- Text labels printed in the primary figure. -/
inductive FigureLabel where
  | spring
  | steelWire
  | pull
  deriving DecidableEq, Repr

/-!
Physical quantities and figure-derived roles for the spring--wire apparatus.

The functions indexed by antinode count describe each resonant configuration
obtained by stretching the same spring and wire while retaining the same wire
length, linear density, spring stiffness, and magnetic drive frequency.
-/
structure SteelWireSpringSetup where
  wireMaterial : WireMaterial
  springMount : SpringMount
  driveMechanism : DriveMechanism
  drivenMotion : DrivenMotion
  springConnectedWireEnd : WireEnd
  pullAppliedWireEnd : WireEnd
  pullDirection : HorizontalDirection
  boundaryCondition : StandingWaveBoundary
  figureLabelTarget : FigureLabel → FigureElement
  figureAntinodeCount : ℕ
  requestedAntinodeCount : ℕ
  wireLength : DimLength
  linearMassDensity : DimLinearMassDensity
  springStiffness : DimSpringStiffness
  driveFrequency : DimFrequency
  springExtensionAtAntinodeCount : ℕ → DimLength
  wireTensionAtAntinodeCount : ℕ → DimTension
  waveSpeedAtAntinodeCount : ℕ → DimSpeed

/-!
Readouts and qualitative geometry taken from the primary image.  The exact
spring stretch is not read from the image: the `8.0 cm` datum comes from the
problem text and is recorded separately below.
-/
structure MatchesPrimaryFigure (setup : SteelWireSpringSetup) : Prop where
  spring_is_wall_mounted : setup.springMount = .wall
  spring_attaches_to_left_wire_end :
    setup.springConnectedWireEnd = .springSide
  pull_is_at_right_wire_end : setup.pullAppliedWireEnd = .pulledSide
  pull_points_right : setup.pullDirection = .right
  three_antinodes_are_drawn : setup.figureAntinodeCount = 3
  spring_label_target : setup.figureLabelTarget .spring = .spring
  steel_wire_label_target : setup.figureLabelTarget .steelWire = .steelWire
  pull_label_target : setup.figureLabelTarget .pull = .pullArrow

/-!
Problem-statement data: the wire is steel, an oscillating magnetic field drives
it back and forth, the three-antinode resonance occurs at `8.0 cm`, and the
question asks for the two-antinode resonance.  No stretch for two antinodes is
specified here.
-/
structure MatchesProblemDescription (setup : SteelWireSpringSetup) : Prop where
  wire_is_steel : setup.wireMaterial = .steel
  magnetic_field_drive : setup.driveMechanism = .oscillatingMagneticField
  drive_is_back_and_forth : setup.drivenMotion = .backAndForth
  reference_extension_cm :
    lengthInCentimeters
        (setup.springExtensionAtAntinodeCount setup.figureAntinodeCount) = 8
  asks_for_two_antinodes : setup.requestedAntinodeCount = 2

/-- Positivity conditions for the physical branch of every nonzero mode. -/
def HasPhysicalParameters (setup : SteelWireSpringSetup) : Prop :=
  0 < lengthInCentimeters setup.wireLength ∧
    0 < linearMassDensityInUnits setup.linearMassDensity UnitChoices.SI ∧
    0 < springStiffnessInUnits setup.springStiffness UnitChoices.SI ∧
    0 < frequencyInUnits setup.driveFrequency UnitChoices.SI ∧
    ∀ n : ℕ, 0 < n →
      0 < lengthInCentimeters (setup.springExtensionAtAntinodeCount n) ∧
        0 < tensionInUnits
          (setup.wireTensionAtAntinodeCount n) UnitChoices.SI ∧
        0 < speedInUnits (setup.waveSpeedAtAntinodeCount n) UnitChoices.SI

/-!
Hooke's law for the magnitude of the wire tension: `T = k x`.  It is stated in
every coherent unit system, so it relates physical quantities rather than only
their centimeter/SI readouts.
-/
def ObeysHookeTensionLaw (setup : SteelWireSpringSetup) : Prop :=
  ∀ (n : ℕ) (_hn : 0 < n) (units : UnitChoices),
    tensionInUnits (setup.wireTensionAtAntinodeCount n) units =
      springStiffnessInUnits setup.springStiffness units *
        (setup.springExtensionAtAntinodeCount n units).val

/-!
Transverse-wave speed on a stretched string, in the homogeneous squared form
`μ v² = T`.
-/
def ObeysStretchedStringWaveSpeedLaw (setup : SteelWireSpringSetup) : Prop :=
  ∀ (n : ℕ) (_hn : 0 < n) (units : UnitChoices),
    linearMassDensityInUnits setup.linearMassDensity units *
        speedInUnits (setup.waveSpeedAtAntinodeCount n) units ^ 2 =
      tensionInUnits (setup.wireTensionAtAntinodeCount n) units

/-!
Fixed-end standing-wave resonance with `n` antinodes, written as
`2 L f = n v`.  The single `driveFrequency` field records that the oscillating
magnetic drive has the same frequency in every stretched configuration.
-/
def ObeysFixedEndStandingWaveLaw (setup : SteelWireSpringSetup) : Prop :=
  setup.boundaryCondition = .nodesAtBothEnds ∧
    ∀ (n : ℕ) (_hn : 0 < n) (units : UnitChoices),
      2 * (setup.wireLength units).val *
          frequencyInUnits setup.driveFrequency units =
        (n : ℝ) * speedInUnits (setup.waveSpeedAtAntinodeCount n) units

/-- Labels of the four answer choices in the problem statement. -/
inductive AnswerChoice where
  | A
  | B
  | C
  | D
  deriving DecidableEq, Repr

/-- The spring stretch in centimeters printed beside each answer choice. -/
def AnswerChoice.stretchInCentimeters : AnswerChoice → ℝ
  | .A => 8
  | .B => 24
  | .C => 12
  | .D => 18

/-- A choice reports the requested resonant spring stretch exactly. -/
def IsCorrectStretchAnswer
    (setup : SteelWireSpringSetup) (choice : AnswerChoice) : Prop :=
  lengthInCentimeters
      (setup.springExtensionAtAntinodeCount setup.requestedAntinodeCount) =
    choice.stretchInCentimeters

/-!
For a fixed wire, spring, and drive, the string and Hooke laws imply that
`n² x_n` is independent of the positive antinode count `n`.
-/
lemma antinodeCount_sq_mul_extension_is_invariant
    (setup : SteelWireSpringSetup)
    (_physical : HasPhysicalParameters setup)
    (_hooke : ObeysHookeTensionLaw setup)
    (_waveSpeed : ObeysStretchedStringWaveSpeedLaw setup)
    (_standingWave : ObeysFixedEndStandingWaveLaw setup)
    {m n : ℕ} (_hm : 0 < m) (_hn : 0 < n) :
    (m : ℝ) ^ 2 *
        lengthInCentimeters (setup.springExtensionAtAntinodeCount m) =
      (n : ℝ) ^ 2 *
        lengthInCentimeters (setup.springExtensionAtAntinodeCount n) := by
  have hkSI :
      0 < springStiffnessInUnits setup.springStiffness UnitChoices.SI :=
    _physical.2.2.1
  have hk :
      springStiffnessInUnits setup.springStiffness centimeterUnitChoices ≠ 0 := by
    intro hk0
    have hkSI0 :
        springStiffnessInUnits setup.springStiffness UnitChoices.SI = 0 := by
      change (setup.springStiffness UnitChoices.SI).val = 0
      rw [setup.springStiffness.2 centimeterUnitChoices UnitChoices.SI]
      simp only [WithDim.smul_val]
      change
        (↑(UnitChoices.dimScale centimeterUnitChoices UnitChoices.SI
            (M𝓭 * T𝓭⁻¹ * T𝓭⁻¹)) : ℝ) *
            (setup.springStiffness centimeterUnitChoices).val =
          0
      change (setup.springStiffness centimeterUnitChoices).val = 0 at hk0
      rw [hk0, mul_zero]
    exact (ne_of_gt hkSI) hkSI0
  have hHookM := _hooke m _hm centimeterUnitChoices
  have hHookN := _hooke n _hn centimeterUnitChoices
  change
    tensionInUnits (setup.wireTensionAtAntinodeCount m)
          centimeterUnitChoices =
      springStiffnessInUnits setup.springStiffness centimeterUnitChoices *
        lengthInCentimeters (setup.springExtensionAtAntinodeCount m) at hHookM
  change
    tensionInUnits (setup.wireTensionAtAntinodeCount n)
          centimeterUnitChoices =
      springStiffnessInUnits setup.springStiffness centimeterUnitChoices *
        lengthInCentimeters (setup.springExtensionAtAntinodeCount n) at hHookN
  have hWaveM := _waveSpeed m _hm centimeterUnitChoices
  have hWaveN := _waveSpeed n _hn centimeterUnitChoices
  have hStandingM := _standingWave.2 m _hm centimeterUnitChoices
  have hStandingN := _standingWave.2 n _hn centimeterUnitChoices
  have hMode :
      (m : ℝ) *
          speedInUnits (setup.waveSpeedAtAntinodeCount m)
            centimeterUnitChoices =
        (n : ℝ) *
          speedInUnits (setup.waveSpeedAtAntinodeCount n)
            centimeterUnitChoices :=
    hStandingM.symm.trans hStandingN
  have hModeSq :
      (m : ℝ) ^ 2 *
          speedInUnits (setup.waveSpeedAtAntinodeCount m)
              centimeterUnitChoices ^ 2 =
        (n : ℝ) ^ 2 *
          speedInUnits (setup.waveSpeedAtAntinodeCount n)
              centimeterUnitChoices ^ 2 := by
    calc
      (m : ℝ) ^ 2 *
            speedInUnits (setup.waveSpeedAtAntinodeCount m)
                centimeterUnitChoices ^ 2 =
          ((m : ℝ) *
              speedInUnits (setup.waveSpeedAtAntinodeCount m)
                centimeterUnitChoices) ^ 2 := by ring
      _ = ((n : ℝ) *
              speedInUnits (setup.waveSpeedAtAntinodeCount n)
                centimeterUnitChoices) ^ 2 :=
        congrArg (fun x : ℝ => x ^ 2) hMode
      _ = (n : ℝ) ^ 2 *
            speedInUnits (setup.waveSpeedAtAntinodeCount n)
                centimeterUnitChoices ^ 2 := by ring
  have hTension :
      (m : ℝ) ^ 2 *
          tensionInUnits (setup.wireTensionAtAntinodeCount m)
            centimeterUnitChoices =
        (n : ℝ) ^ 2 *
          tensionInUnits (setup.wireTensionAtAntinodeCount n)
            centimeterUnitChoices := by
    calc
      (m : ℝ) ^ 2 *
            tensionInUnits (setup.wireTensionAtAntinodeCount m)
              centimeterUnitChoices =
          linearMassDensityInUnits setup.linearMassDensity centimeterUnitChoices *
            ((m : ℝ) ^ 2 *
              speedInUnits (setup.waveSpeedAtAntinodeCount m)
                centimeterUnitChoices ^ 2) := by
                  rw [← hWaveM]
                  ring
      _ = linearMassDensityInUnits setup.linearMassDensity centimeterUnitChoices *
            ((n : ℝ) ^ 2 *
              speedInUnits (setup.waveSpeedAtAntinodeCount n)
                centimeterUnitChoices ^ 2) := by rw [hModeSq]
      _ = (n : ℝ) ^ 2 *
            tensionInUnits (setup.wireTensionAtAntinodeCount n)
              centimeterUnitChoices := by
                  rw [← hWaveN]
                  ring
  apply mul_left_cancel₀ hk
  calc
    springStiffnessInUnits setup.springStiffness centimeterUnitChoices *
          ((m : ℝ) ^ 2 *
            lengthInCentimeters (setup.springExtensionAtAntinodeCount m)) =
        (m : ℝ) ^ 2 *
          tensionInUnits (setup.wireTensionAtAntinodeCount m)
            centimeterUnitChoices := by
              rw [hHookM]
              ring
    _ = (n : ℝ) ^ 2 *
          tensionInUnits (setup.wireTensionAtAntinodeCount n)
            centimeterUnitChoices := hTension
    _ = springStiffnessInUnits setup.springStiffness centimeterUnitChoices *
          ((n : ℝ) ^ 2 *
            lengthInCentimeters (setup.springExtensionAtAntinodeCount n)) := by
              rw [hHookN]
              ring

/-!
The reference resonance has three antinodes at `8.0 cm`.  Since `n² x_n` is
constant, the requested two-antinode resonance has stretch
`(3 / 2)² · 8 cm = 18 cm`.
-/
lemma requestedExtensionInCentimeters_eq_eighteen
    (setup : SteelWireSpringSetup)
    (_description : MatchesProblemDescription setup)
    (_figure : MatchesPrimaryFigure setup)
    (_physical : HasPhysicalParameters setup)
    (_hooke : ObeysHookeTensionLaw setup)
    (_waveSpeed : ObeysStretchedStringWaveSpeedLaw setup)
    (_standingWave : ObeysFixedEndStandingWaveLaw setup) :
    lengthInCentimeters
        (setup.springExtensionAtAntinodeCount setup.requestedAntinodeCount) =
      18 := by
  have hInvariant :=
    antinodeCount_sq_mul_extension_is_invariant setup _physical _hooke
      _waveSpeed _standingWave (m := 3) (n := 2) (by norm_num) (by norm_num)
  have hReference :
      lengthInCentimeters (setup.springExtensionAtAntinodeCount 3) = 8 := by
    rw [← _figure.three_antinodes_are_drawn]
    exact _description.reference_extension_cm
  rw [_description.asks_for_two_antinodes]
  norm_num [hReference] at hInvariant
  linarith

/-!
A steel wire showing three antinodes when its spring is stretched `8.0 cm`
must be stretched `18 cm` to show two antinodes at the same drive frequency.
Thus the recorded answer is choice D.

This formalizes `thm:physics:phyx_mini_0180:target`.
-/
theorem problem_phyx_mini_0180
    (setup : SteelWireSpringSetup)
    (_description : MatchesProblemDescription setup)
    (_figure : MatchesPrimaryFigure setup)
    (_physical : HasPhysicalParameters setup)
    (_hooke : ObeysHookeTensionLaw setup)
    (_waveSpeed : ObeysStretchedStringWaveSpeedLaw setup)
    (_standingWave : ObeysFixedEndStandingWaveLaw setup) :
    lengthInCentimeters
        (setup.springExtensionAtAntinodeCount setup.requestedAntinodeCount) =
      18 ∧
      IsCorrectStretchAnswer setup .D := by
  have hExtension :=
    requestedExtensionInCentimeters_eq_eighteen setup _description _figure
      _physical _hooke _waveSpeed _standingWave
  constructor
  · exact hExtension
  · simpa [IsCorrectStretchAnswer, AnswerChoice.stretchInCentimeters] using
      hExtension

end PhyXMiniProblems.ProblemPhyXMini0180
