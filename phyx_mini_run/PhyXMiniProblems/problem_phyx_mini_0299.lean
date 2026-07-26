import Mathlib
import Physlib.Units.WithDim.Speed

/- USER: The assigned source file did not exist when this autoformalization task began. -/

noncomputable section

namespace PhyXMiniProblems.ProblemPhyXMini0299

open Dimension

/-!
# Lowest joint-node resonance of a compound wire

The primary image shows an aluminum segment of length `L₁` fixed at the left,
joined to a steel segment of length `L₂` which passes over a supporting pulley
to a block labelled `m`.  The two horizontal segments have the same
cross-sectional area.  A variable-frequency transverse source excites the
compound wire, and the pulley is a displacement node.

All basic physical quantities below use Physlib's unit-independent
`Dimensionful (WithDim _ _)` representation.  Scalar real numbers occur only
as readouts in a coherent unit system, as harmonic counts, and as the
whole-hertz values printed in the answer choices.

Because `86.6 cm` and the other measurements are printed to finite precision,
the aluminum and steel modal frequencies are not asserted to be exactly equal
as real numbers.  A displayed whole-hertz drive matches a mode when it is
within half a hertz of that mode.  This makes the precision convention explicit
instead of replacing the printed data by unreported exact values.
-/

/-! ## Dimensionful physical quantities -/

/-- A nonnegative physical length. -/
abbrev LengthQuantity : Type :=
  Dimensionful (WithDim L𝓭 NNReal)

/-- A nonnegative cross-sectional area. -/
abbrev AreaQuantity : Type :=
  Dimensionful (WithDim (L𝓭 * L𝓭) NNReal)

/-- A nonnegative mass per unit volume. -/
abbrev VolumeMassDensityQuantity : Type :=
  Dimensionful (WithDim (M𝓭 * L𝓭⁻¹ * L𝓭⁻¹ * L𝓭⁻¹) NNReal)

/-- A nonnegative mass per unit length. -/
abbrev LinearMassDensityQuantity : Type :=
  Dimensionful (WithDim (M𝓭 * L𝓭⁻¹) NNReal)

/-- A nonnegative physical mass. -/
abbrev MassQuantity : Type :=
  Dimensionful (WithDim M𝓭 NNReal)

/-- A nonnegative acceleration magnitude. -/
abbrev AccelerationQuantity : Type :=
  Dimensionful (WithDim (L𝓭 * T𝓭⁻¹ * T𝓭⁻¹) NNReal)

/-- A nonnegative tensile force. -/
abbrev TensionQuantity : Type :=
  Dimensionful (WithDim (M𝓭 * L𝓭 * T𝓭⁻¹ * T𝓭⁻¹) NNReal)

/-- An ordinary cyclic frequency, with inverse-time dimension. -/
abbrev FrequencyQuantity : Type :=
  Dimensionful (WithDim T𝓭⁻¹ NNReal)

/-- A nonnegative transverse-wave propagation speed. -/
abbrev SpeedQuantity : Type := DimSpeed

/-- Read a nonnegative dimensionful quantity in a coherent unit system. -/
def quantityReadout {d : Dimension}
    (units : UnitChoices) (quantity : Dimensionful (WithDim d NNReal)) : ℝ :=
  ((quantity units).val : ℝ)

/-- SI metre readout of a length. -/
def lengthInMeters (length : LengthQuantity) : ℝ :=
  quantityReadout UnitChoices.SI length

/-- SI square-metre readout of an area. -/
def areaInSquareMeters (area : AreaQuantity) : ℝ :=
  quantityReadout UnitChoices.SI area

/-- SI kilogram-per-cubic-metre readout of a volume mass density. -/
def volumeDensityInKilogramsPerCubicMeter
    (density : VolumeMassDensityQuantity) : ℝ :=
  quantityReadout UnitChoices.SI density

/-- SI kilogram-per-metre readout of a linear mass density. -/
def linearDensityInKilogramsPerMeter
    (density : LinearMassDensityQuantity) : ℝ :=
  quantityReadout UnitChoices.SI density

/-- Kilogram readout of a mass. -/
def massInKilograms (mass : MassQuantity) : ℝ :=
  quantityReadout UnitChoices.SI mass

/-- SI metre-per-second-squared readout of an acceleration. -/
def accelerationInMetersPerSecondSquared
    (acceleration : AccelerationQuantity) : ℝ :=
  quantityReadout UnitChoices.SI acceleration

/-- SI newton readout of a tension. -/
def tensionInNewtons (tension : TensionQuantity) : ℝ :=
  quantityReadout UnitChoices.SI tension

/-- SI hertz readout of an ordinary frequency. -/
def frequencyInHertz (frequency : FrequencyQuantity) : ℝ :=
  quantityReadout UnitChoices.SI frequency

/-- SI metre-per-second readout of a speed. -/
def speedInMetersPerSecond (speed : SpeedQuantity) : ℝ :=
  quantityReadout UnitChoices.SI speed

/-! ## Material, geometry, and primary-image labels -/

/-- The two horizontal portions of the compound wire. -/
inductive WireSegment where
  | left
  | right
  deriving DecidableEq, Repr

/-- Material names printed below the two horizontal wire segments. -/
inductive WireMaterial where
  | aluminum
  | steel
  deriving DecidableEq, Repr

/-- Length symbols printed above the two horizontal segments. -/
inductive FigureLengthLabel where
  | L1
  | L2
  deriving DecidableEq, Repr

/-- Distinguished locations or objects visible in the primary image. -/
inductive FigurePoint where
  | leftSupport
  | materialJoint
  | supportingPulley
  | hangingBlock
  deriving DecidableEq, Repr

/-- Mechanical role of each distinguished image location. -/
inductive FigureConnection where
  | fixedWall
  | aluminumSteelJoint
  | pulley
  | suspendedLoad
  deriving DecidableEq, Repr

/-- The route taken by the compound wire in the primary image. -/
inductive WireRoute where
  | fixedAtLeftAcrossJointOverPulleyToHangingBlock
  deriving DecidableEq, Repr

/-- The drive described in the problem text. -/
inductive DriveKind where
  | variableFrequencyTransverseSource
  deriving DecidableEq, Repr

/-- Transverse-displacement behavior at a supported point. -/
inductive TransverseBoundaryCondition where
  | node
  | unspecified
  deriving DecidableEq, Repr

/-- Structured transcription of labels and connections in the primary image. -/
structure SourceFigure where
  materialLabel : WireSegment → WireMaterial
  lengthLabel : WireSegment → FigureLengthLabel
  connectionAt : FigurePoint → FigureConnection
  route : WireRoute
  blockLabel : String

/-! ## Compound-wire setup -/

/--
Independent physical quantities for the compound-wire apparatus.

`nodeToNodeModeFrequency segment n` is the physical frequency of the local
`n`th node-to-node standing-wave mode of that segment.  Its generic relation
to length and wave speed is imposed below.  No common mode, lowest mode, or
answer value is selected in this structure.
-/
structure CompoundWireSetup where
  figure : SourceFigure
  driveKind : DriveKind
  pulleyBoundaryCondition : TransverseBoundaryCondition
  segmentLength : WireSegment → LengthQuantity
  commonCrossSectionalArea : AreaQuantity
  volumeMassDensity : WireMaterial → VolumeMassDensityQuantity
  linearMassDensity : WireSegment → LinearMassDensityQuantity
  hangingBlockMass : MassQuantity
  gravitationalAcceleration : AccelerationQuantity
  segmentTension : WireSegment → TensionQuantity
  transverseWaveSpeed : WireSegment → SpeedQuantity
  nodeToNodeModeFrequency : WireSegment → ℕ → FrequencyQuantity

/-! ## Stated measurements and primary-image readouts -/

/--
The numerical data printed in the problem, converted to exact SI readouts of
the printed decimals:

* `60.0 cm = 3/5 m` and `86.6 cm = 433/500 m`;
* `1.00 × 10⁻² cm² = 10⁻⁶ m²`;
* `2.60 g/cm³ = 2600 kg/m³` and `7.80 g/cm³ = 7800 kg/m³`;
* `m = 10.0 kg`.

The source is variable-frequency and transverse, and the problem explicitly
states that the pulley is a node.  No condition at the material joint occurs
in this data structure.
-/
structure MatchesProblemData (setup : CompoundWireSetup) : Prop where
  aluminumLengthMeters :
    lengthInMeters (setup.segmentLength .left) = 3 / 5
  steelLengthMeters :
    lengthInMeters (setup.segmentLength .right) = 433 / 500
  commonAreaSquareMeters :
    areaInSquareMeters setup.commonCrossSectionalArea = 1 / 1000000
  aluminumDensityKilogramsPerCubicMeter :
    volumeDensityInKilogramsPerCubicMeter
        (setup.volumeMassDensity .aluminum) = 2600
  steelDensityKilogramsPerCubicMeter :
    volumeDensityInKilogramsPerCubicMeter
        (setup.volumeMassDensity .steel) = 7800
  blockMassKilograms : massInKilograms setup.hangingBlockMass = 10
  variableFrequencyTransverseDrive :
    setup.driveKind = .variableFrequencyTransverseSource
  pulleyIsNode : setup.pulleyBoundaryCondition = .node

/--
The usual textbook value `g = 9.80 m/s²` used with the hanging `10.0 kg`
block.  This is an environmental calibration, not a frequency conclusion.
-/
def UsesStandardTerrestrialGravity (setup : CompoundWireSetup) : Prop :=
  accelerationInMetersPerSecondSquared setup.gravitationalAcceleration = 49 / 5

/--
Primary-image readout: a left fixed support, an aluminum `L₁` segment, the
material joint, a steel `L₂` segment, a pulley, and a hanging block labelled
`m`, in that route order.
-/
structure MatchesPrimaryFigure (setup : CompoundWireSetup) : Prop where
  leftSegmentMaterial : setup.figure.materialLabel .left = .aluminum
  rightSegmentMaterial : setup.figure.materialLabel .right = .steel
  leftLengthLabel : setup.figure.lengthLabel .left = .L1
  rightLengthLabel : setup.figure.lengthLabel .right = .L2
  fixedLeftSupport : setup.figure.connectionAt .leftSupport = .fixedWall
  materialJointShown :
    setup.figure.connectionAt .materialJoint = .aluminumSteelJoint
  supportingPulleyShown :
    setup.figure.connectionAt .supportingPulley = .pulley
  suspendedLoadShown :
    setup.figure.connectionAt .hangingBlock = .suspendedLoad
  routeReadout :
    setup.figure.route = .fixedAtLeftAcrossJointOverPulleyToHangingBlock
  hangingBlockLabel : setup.figure.blockLabel = "m"

/-- Positivity and nondegeneracy conditions for the taut-wire model. -/
structure HasPositivePhysicalParameters (setup : CompoundWireSetup) : Prop where
  lengthsPositive :
    ∀ segment, 0 < lengthInMeters (setup.segmentLength segment)
  areaPositive : 0 < areaInSquareMeters setup.commonCrossSectionalArea
  volumeDensitiesPositive :
    ∀ material,
      0 < volumeDensityInKilogramsPerCubicMeter
        (setup.volumeMassDensity material)
  linearDensitiesPositive :
    ∀ segment,
      0 < linearDensityInKilogramsPerMeter
        (setup.linearMassDensity segment)
  blockMassPositive : 0 < massInKilograms setup.hangingBlockMass
  gravityPositive :
    0 < accelerationInMetersPerSecondSquared setup.gravitationalAcceleration
  tensionsPositive :
    ∀ segment, 0 < tensionInNewtons (setup.segmentTension segment)
  waveSpeedsPositive :
    ∀ segment, 0 < speedInMetersPerSecond (setup.transverseWaveSpeed segment)
  positiveModeFrequencies :
    ∀ segment n, 0 < n →
      0 < frequencyInHertz (setup.nodeToNodeModeFrequency segment n)

/-! ## Governing compound-wire laws -/

/-- Material associated to each segment independently of the source figure. -/
def segmentMaterial : WireSegment → WireMaterial
  | .left => .aluminum
  | .right => .steel

/--
The standard physical laws used in the calculation, expressed in every
coherent unit system:

* linear density is volume density times common cross-sectional area;
* an ideal pulley and a static hanging block give each segment tension `mg`;
* a taut string obeys `μ v² = T`;
* the `n`th node-to-node mode obeys `2 L fₙ = n v`.

These laws describe the full modal spectra.  They do not assert that a mode of
one material coincides with a mode of the other, do not select a lowest common
mode, and contain neither `324` nor an answer label.
-/
structure SatisfiesCompoundWireLaws (setup : CompoundWireSetup) : Prop where
  linearDensityFromVolumeDensity :
    ∀ segment units,
      quantityReadout units (setup.linearMassDensity segment) =
        quantityReadout units
            (setup.volumeMassDensity (segmentMaterial segment)) *
          quantityReadout units setup.commonCrossSectionalArea
  idealPulleyAndStaticLoadTension :
    ∀ segment units,
      quantityReadout units (setup.segmentTension segment) =
        quantityReadout units setup.hangingBlockMass *
          quantityReadout units setup.gravitationalAcceleration
  stretchedStringWaveSpeed :
    ∀ segment units,
      quantityReadout units (setup.linearMassDensity segment) *
          quantityReadout units (setup.transverseWaveSpeed segment) ^ 2 =
        quantityReadout units (setup.segmentTension segment)
  nodeToNodeStandingWaveModes :
    ∀ segment n, 0 < n → ∀ units,
      2 * quantityReadout units (setup.segmentLength segment) *
          quantityReadout units (setup.nodeToNodeModeFrequency segment n) =
        (n : ℝ) * quantityReadout units (setup.transverseWaveSpeed segment)

/-! ## Whole-hertz common resonance and answer choices -/

/--
A positive aluminum/steel harmonic pair agrees with a whole-hertz drive
readout when each local node-to-node mode lies within half a hertz of it.
-/
def ModePairMatchesWholeHertz
    (setup : CompoundWireSetup)
    (aluminumHarmonic steelHarmonic displayedHertz : ℕ) : Prop :=
  0 < aluminumHarmonic ∧
    0 < steelHarmonic ∧
    |frequencyInHertz
          (setup.nodeToNodeModeFrequency .left aluminumHarmonic) -
        (displayedHertz : ℝ)| ≤ 1 / 2 ∧
    |frequencyInHertz
          (setup.nodeToNodeModeFrequency .right steelHarmonic) -
        (displayedHertz : ℝ)| ≤ 1 / 2

/--
At the precision of the integer-hertz answers, a common joint-node standing
wave is a shared drive readout matching a node-to-node mode of each segment.
The material joint is therefore an endpoint node of both local modes.
-/
def IsJointNodeStandingWaveAtWholeHertz
    (setup : CompoundWireSetup) (displayedHertz : ℕ) : Prop :=
  ∃ aluminumHarmonic steelHarmonic,
    ModePairMatchesWholeHertz
      setup aluminumHarmonic steelHarmonic displayedHertz

/-- A common joint-node displayed frequency with no lower positive one. -/
def IsLowestJointNodeFrequencyAtWholeHertz
    (setup : CompoundWireSetup) (displayedHertz : ℕ) : Prop :=
  0 < displayedHertz ∧
    IsJointNodeStandingWaveAtWholeHertz setup displayedHertz ∧
    ∀ candidateHertz,
      0 < candidateHertz →
      IsJointNodeStandingWaveAtWholeHertz setup candidateHertz →
      displayedHertz ≤ candidateHertz

/-- Labels of the four displayed answers. -/
inductive AnswerChoice where
  | A
  | B
  | C
  | D
  deriving DecidableEq, Repr

/-- Integer-hertz frequency printed beside an answer label. -/
def AnswerChoice.frequencyInHertz : AnswerChoice → ℕ
  | .A => 305
  | .B => 312
  | .C => 318
  | .D => 324

/-- The answer label recorded in the supplied dataset metadata. -/
def recordedAnswerChoice : AnswerChoice := .D

/-!
The second aluminum mode and fifth steel mode both agree with the displayed
frequency `324 Hz` at whole-hertz precision.
-/
lemma second_aluminum_and_fifth_steel_modes_match_choice_D
    (setup : CompoundWireSetup)
    (_problem : MatchesProblemData setup)
    (_gravity : UsesStandardTerrestrialGravity setup)
    (_positive : HasPositivePhysicalParameters setup)
    (_laws : SatisfiesCompoundWireLaws setup) :
    ModePairMatchesWholeHertz
      setup 2 5 AnswerChoice.D.frequencyInHertz := by
  have hμAl :
      linearDensityInKilogramsPerMeter (setup.linearMassDensity .left) =
        volumeDensityInKilogramsPerCubicMeter
            (setup.volumeMassDensity .aluminum) *
          areaInSquareMeters setup.commonCrossSectionalArea := by
    simpa [linearDensityInKilogramsPerMeter,
      volumeDensityInKilogramsPerCubicMeter, areaInSquareMeters,
      segmentMaterial] using
      _laws.linearDensityFromVolumeDensity .left UnitChoices.SI
  rw [_problem.aluminumDensityKilogramsPerCubicMeter,
    _problem.commonAreaSquareMeters] at hμAl
  norm_num at hμAl
  have hμSteel :
      linearDensityInKilogramsPerMeter (setup.linearMassDensity .right) =
        volumeDensityInKilogramsPerCubicMeter
            (setup.volumeMassDensity .steel) *
          areaInSquareMeters setup.commonCrossSectionalArea := by
    simpa [linearDensityInKilogramsPerMeter,
      volumeDensityInKilogramsPerCubicMeter, areaInSquareMeters,
      segmentMaterial] using
      _laws.linearDensityFromVolumeDensity .right UnitChoices.SI
  rw [_problem.steelDensityKilogramsPerCubicMeter,
    _problem.commonAreaSquareMeters] at hμSteel
  norm_num at hμSteel
  have hTAl :
      tensionInNewtons (setup.segmentTension .left) =
        massInKilograms setup.hangingBlockMass *
          accelerationInMetersPerSecondSquared
            setup.gravitationalAcceleration := by
    simpa [tensionInNewtons, massInKilograms,
      accelerationInMetersPerSecondSquared] using
      _laws.idealPulleyAndStaticLoadTension .left UnitChoices.SI
  rw [_problem.blockMassKilograms, _gravity] at hTAl
  norm_num at hTAl
  have hTSteel :
      tensionInNewtons (setup.segmentTension .right) =
        massInKilograms setup.hangingBlockMass *
          accelerationInMetersPerSecondSquared
            setup.gravitationalAcceleration := by
    simpa [tensionInNewtons, massInKilograms,
      accelerationInMetersPerSecondSquared] using
      _laws.idealPulleyAndStaticLoadTension .right UnitChoices.SI
  rw [_problem.blockMassKilograms, _gravity] at hTSteel
  norm_num at hTSteel
  have hWaveAl :
      linearDensityInKilogramsPerMeter (setup.linearMassDensity .left) *
          speedInMetersPerSecond (setup.transverseWaveSpeed .left) ^ 2 =
        tensionInNewtons (setup.segmentTension .left) := by
    simpa [linearDensityInKilogramsPerMeter, speedInMetersPerSecond,
      tensionInNewtons] using
      _laws.stretchedStringWaveSpeed .left UnitChoices.SI
  have hWaveSteel :
      linearDensityInKilogramsPerMeter (setup.linearMassDensity .right) *
          speedInMetersPerSecond (setup.transverseWaveSpeed .right) ^ 2 =
        tensionInNewtons (setup.segmentTension .right) := by
    simpa [linearDensityInKilogramsPerMeter, speedInMetersPerSecond,
      tensionInNewtons] using
      _laws.stretchedStringWaveSpeed .right UnitChoices.SI
  have hModeAl :
      2 * lengthInMeters (setup.segmentLength .left) *
          frequencyInHertz (setup.nodeToNodeModeFrequency .left 2) =
        (2 : ℝ) * speedInMetersPerSecond
          (setup.transverseWaveSpeed .left) := by
    simpa [lengthInMeters, frequencyInHertz, speedInMetersPerSecond] using
      _laws.nodeToNodeStandingWaveModes .left 2 (by norm_num)
        UnitChoices.SI
  rw [_problem.aluminumLengthMeters] at hModeAl
  have hModeSteel :
      2 * lengthInMeters (setup.segmentLength .right) *
          frequencyInHertz (setup.nodeToNodeModeFrequency .right 5) =
        (5 : ℝ) * speedInMetersPerSecond
          (setup.transverseWaveSpeed .right) := by
    simpa [lengthInMeters, frequencyInHertz, speedInMetersPerSecond] using
      _laws.nodeToNodeStandingWaveModes .right 5 (by norm_num)
        UnitChoices.SI
  rw [_problem.steelLengthMeters] at hModeSteel
  have hfAl :
      0 < frequencyInHertz
        (setup.nodeToNodeModeFrequency .left 2) :=
    _positive.positiveModeFrequencies .left 2 (by norm_num)
  have hfSteel :
      0 < frequencyInHertz
        (setup.nodeToNodeModeFrequency .right 5) :=
    _positive.positiveModeFrequencies .right 5 (by norm_num)
  unfold ModePairMatchesWholeHertz AnswerChoice.frequencyInHertz
  refine ⟨by norm_num, by norm_num, ?_, ?_⟩
  · rw [abs_le]
    constructor <;> nlinarith
  · rw [abs_le]
    constructor <;> nlinarith

/-!
No lower positive whole-hertz readout simultaneously matches node-to-node
modes of both materials.
-/
lemma every_joint_node_frequency_is_at_least_choice_D
    (setup : CompoundWireSetup)
    (_problem : MatchesProblemData setup)
    (_gravity : UsesStandardTerrestrialGravity setup)
    (_positive : HasPositivePhysicalParameters setup)
    (_laws : SatisfiesCompoundWireLaws setup) :
    ∀ candidateHertz,
      0 < candidateHertz →
      IsJointNodeStandingWaveAtWholeHertz setup candidateHertz →
      AnswerChoice.D.frequencyInHertz ≤ candidateHertz := by
  intro candidateHertz _candidatePositive hJointNode
  by_contra hBelow
  have hCandidateUpper : candidateHertz ≤ 323 := by
    change ¬324 ≤ candidateHertz at hBelow
    omega
  unfold IsJointNodeStandingWaveAtWholeHertz at hJointNode
  rcases hJointNode with
    ⟨aluminumHarmonic, steelHarmonic, hModePair⟩
  unfold ModePairMatchesWholeHertz at hModePair
  rcases hModePair with
    ⟨hAluminumHarmonicPositive, hSteelHarmonicPositive,
      hAluminumClose, hSteelClose⟩
  have hμAl :
      linearDensityInKilogramsPerMeter (setup.linearMassDensity .left) =
        volumeDensityInKilogramsPerCubicMeter
            (setup.volumeMassDensity .aluminum) *
          areaInSquareMeters setup.commonCrossSectionalArea := by
    simpa [linearDensityInKilogramsPerMeter,
      volumeDensityInKilogramsPerCubicMeter, areaInSquareMeters,
      segmentMaterial] using
      _laws.linearDensityFromVolumeDensity .left UnitChoices.SI
  rw [_problem.aluminumDensityKilogramsPerCubicMeter,
    _problem.commonAreaSquareMeters] at hμAl
  norm_num at hμAl
  have hμSteel :
      linearDensityInKilogramsPerMeter (setup.linearMassDensity .right) =
        volumeDensityInKilogramsPerCubicMeter
            (setup.volumeMassDensity .steel) *
          areaInSquareMeters setup.commonCrossSectionalArea := by
    simpa [linearDensityInKilogramsPerMeter,
      volumeDensityInKilogramsPerCubicMeter, areaInSquareMeters,
      segmentMaterial] using
      _laws.linearDensityFromVolumeDensity .right UnitChoices.SI
  rw [_problem.steelDensityKilogramsPerCubicMeter,
    _problem.commonAreaSquareMeters] at hμSteel
  norm_num at hμSteel
  have hTAl :
      tensionInNewtons (setup.segmentTension .left) =
        massInKilograms setup.hangingBlockMass *
          accelerationInMetersPerSecondSquared
            setup.gravitationalAcceleration := by
    simpa [tensionInNewtons, massInKilograms,
      accelerationInMetersPerSecondSquared] using
      _laws.idealPulleyAndStaticLoadTension .left UnitChoices.SI
  rw [_problem.blockMassKilograms, _gravity] at hTAl
  norm_num at hTAl
  have hTSteel :
      tensionInNewtons (setup.segmentTension .right) =
        massInKilograms setup.hangingBlockMass *
          accelerationInMetersPerSecondSquared
            setup.gravitationalAcceleration := by
    simpa [tensionInNewtons, massInKilograms,
      accelerationInMetersPerSecondSquared] using
      _laws.idealPulleyAndStaticLoadTension .right UnitChoices.SI
  rw [_problem.blockMassKilograms, _gravity] at hTSteel
  norm_num at hTSteel
  have hWaveAl :
      linearDensityInKilogramsPerMeter (setup.linearMassDensity .left) *
          speedInMetersPerSecond (setup.transverseWaveSpeed .left) ^ 2 =
        tensionInNewtons (setup.segmentTension .left) := by
    simpa [linearDensityInKilogramsPerMeter, speedInMetersPerSecond,
      tensionInNewtons] using
      _laws.stretchedStringWaveSpeed .left UnitChoices.SI
  have hWaveSteel :
      linearDensityInKilogramsPerMeter (setup.linearMassDensity .right) *
          speedInMetersPerSecond (setup.transverseWaveSpeed .right) ^ 2 =
        tensionInNewtons (setup.segmentTension .right) := by
    simpa [linearDensityInKilogramsPerMeter, speedInMetersPerSecond,
      tensionInNewtons] using
      _laws.stretchedStringWaveSpeed .right UnitChoices.SI
  have hModeAl :
      2 * lengthInMeters (setup.segmentLength .left) *
          frequencyInHertz
            (setup.nodeToNodeModeFrequency .left aluminumHarmonic) =
        (aluminumHarmonic : ℝ) *
          speedInMetersPerSecond (setup.transverseWaveSpeed .left) := by
    simpa [lengthInMeters, frequencyInHertz, speedInMetersPerSecond] using
      _laws.nodeToNodeStandingWaveModes .left aluminumHarmonic
        hAluminumHarmonicPositive UnitChoices.SI
  rw [_problem.aluminumLengthMeters] at hModeAl
  have hModeSteel :
      2 * lengthInMeters (setup.segmentLength .right) *
          frequencyInHertz
            (setup.nodeToNodeModeFrequency .right steelHarmonic) =
        (steelHarmonic : ℝ) *
          speedInMetersPerSecond (setup.transverseWaveSpeed .right) := by
    simpa [lengthInMeters, frequencyInHertz, speedInMetersPerSecond] using
      _laws.nodeToNodeStandingWaveModes .right steelHarmonic
        hSteelHarmonicPositive UnitChoices.SI
  rw [_problem.steelLengthMeters] at hModeSteel
  have hfAlPositive :
      0 < frequencyInHertz
        (setup.nodeToNodeModeFrequency .left aluminumHarmonic) :=
    _positive.positiveModeFrequencies .left aluminumHarmonic
      hAluminumHarmonicPositive
  have hfSteelPositive :
      0 < frequencyInHertz
        (setup.nodeToNodeModeFrequency .right steelHarmonic) :=
    _positive.positiveModeFrequencies .right steelHarmonic
      hSteelHarmonicPositive
  have hvAlPositive :
      0 < speedInMetersPerSecond (setup.transverseWaveSpeed .left) :=
    _positive.waveSpeedsPositive .left
  have hvSteelPositive :
      0 < speedInMetersPerSecond (setup.transverseWaveSpeed .right) :=
    _positive.waveSpeedsPositive .right
  rcases (abs_le.mp hAluminumClose) with
    ⟨hAluminumCloseBelow, hAluminumCloseAbove⟩
  rcases (abs_le.mp hSteelClose) with
    ⟨hSteelCloseBelow, hSteelCloseAbove⟩
  have hCandidateUpperReal : (candidateHertz : ℝ) ≤ 323 := by
    exact_mod_cast hCandidateUpper
  have hfAlUpper :
      frequencyInHertz
          (setup.nodeToNodeModeFrequency .left aluminumHarmonic) ≤
        647 / 2 := by
    nlinarith only [hAluminumCloseAbove, hCandidateUpperReal]
  have hfSteelUpper :
      frequencyInHertz
          (setup.nodeToNodeModeFrequency .right steelHarmonic) ≤
        647 / 2 := by
    nlinarith only [hSteelCloseAbove, hCandidateUpperReal]
  have hAluminumHarmonicLessThanTwo : aluminumHarmonic < 2 := by
    by_contra hNotLess
    have hTwoLe : 2 ≤ aluminumHarmonic := by omega
    have hTwoLeReal : (2 : ℝ) ≤ aluminumHarmonic := by
      exact_mod_cast hTwoLe
    have hScaledSpeed :
        2 * speedInMetersPerSecond (setup.transverseWaveSpeed .left) ≤
          (aluminumHarmonic : ℝ) *
            speedInMetersPerSecond (setup.transverseWaveSpeed .left) := by
      nlinarith only [hTwoLeReal, hvAlPositive]
    nlinarith only [hμAl, hTAl, hWaveAl, hModeAl, hfAlUpper,
      hvAlPositive, hScaledSpeed]
  have hAluminumHarmonicEqualsOne : aluminumHarmonic = 1 := by
    omega
  have hSteelHarmonicLessThanFive : steelHarmonic < 5 := by
    by_contra hNotLess
    have hFiveLe : 5 ≤ steelHarmonic := by omega
    have hFiveLeReal : (5 : ℝ) ≤ steelHarmonic := by
      exact_mod_cast hFiveLe
    have hScaledSpeed :
        5 * speedInMetersPerSecond (setup.transverseWaveSpeed .right) ≤
          (steelHarmonic : ℝ) *
            speedInMetersPerSecond (setup.transverseWaveSpeed .right) := by
      nlinarith only [hFiveLeReal, hvSteelPositive]
    nlinarith only [hμSteel, hTSteel, hWaveSteel, hModeSteel,
      hfSteelUpper, hvSteelPositive, hScaledSpeed]
  have hCloseAlToSteel :
      frequencyInHertz
            (setup.nodeToNodeModeFrequency .left aluminumHarmonic) -
          frequencyInHertz
            (setup.nodeToNodeModeFrequency .right steelHarmonic) ≤
        1 := by
    linarith only [hAluminumCloseAbove, hSteelCloseBelow]
  have hCloseSteelToAl :
      frequencyInHertz
            (setup.nodeToNodeModeFrequency .right steelHarmonic) -
          frequencyInHertz
            (setup.nodeToNodeModeFrequency .left aluminumHarmonic) ≤
        1 := by
    linarith only [hSteelCloseAbove, hAluminumCloseBelow]
  subst aluminumHarmonic
  have hSteelHarmonicCases :
      steelHarmonic = 1 ∨ steelHarmonic = 2 ∨
        steelHarmonic = 3 ∨ steelHarmonic = 4 := by
    omega
  rcases hSteelHarmonicCases with hOne | hTwo | hThree | hFour
  · subst steelHarmonic
    have hfAlLower :
        161 <
          frequencyInHertz
            (setup.nodeToNodeModeFrequency .left 1) := by
      nlinarith only [hμAl, hTAl, hWaveAl, hModeAl, hfAlPositive]
    have hfSteelUpper' :
        frequencyInHertz
            (setup.nodeToNodeModeFrequency .right 1) < 65 := by
      nlinarith only [hμSteel, hTSteel, hWaveSteel, hModeSteel,
        hfSteelPositive]
    linarith only [hCloseAlToSteel, hfAlLower, hfSteelUpper']
  · subst steelHarmonic
    have hfAlLower :
        161 <
          frequencyInHertz
            (setup.nodeToNodeModeFrequency .left 1) := by
      nlinarith only [hμAl, hTAl, hWaveAl, hModeAl, hfAlPositive]
    have hfSteelUpper' :
        frequencyInHertz
            (setup.nodeToNodeModeFrequency .right 2) < 130 := by
      nlinarith only [hμSteel, hTSteel, hWaveSteel, hModeSteel,
        hfSteelPositive]
    linarith only [hCloseAlToSteel, hfAlLower, hfSteelUpper']
  · subst steelHarmonic
    have hfAlUpper' :
        frequencyInHertz
            (setup.nodeToNodeModeFrequency .left 1) < 162 := by
      nlinarith only [hμAl, hTAl, hWaveAl, hModeAl, hfAlPositive]
    have hfSteelLower :
        194 <
          frequencyInHertz
            (setup.nodeToNodeModeFrequency .right 3) := by
      nlinarith only [hμSteel, hTSteel, hWaveSteel, hModeSteel,
        hfSteelPositive]
    linarith only [hCloseSteelToAl, hfAlUpper', hfSteelLower]
  · subst steelHarmonic
    have hfAlUpper' :
        frequencyInHertz
            (setup.nodeToNodeModeFrequency .left 1) < 162 := by
      nlinarith only [hμAl, hTAl, hWaveAl, hModeAl, hfAlPositive]
    have hfSteelLower :
        258 <
          frequencyInHertz
            (setup.nodeToNodeModeFrequency .right 4) := by
      nlinarith only [hμSteel, hTSteel, hWaveSteel, hModeSteel,
        hfSteelPositive]
    linarith only [hCloseSteelToAl, hfAlUpper', hfSteelLower]

/-!
The lowest displayed frequency producing a standing wave with the aluminum--
steel joint as a node is `324 Hz`, answer choice D.  Its common modal pair is
the second aluminum mode and the fifth steel mode.

This is the Lean declaration corresponding to blueprint label
`thm:physics:phyx_mini_0299:target`.
-/
theorem problem_phyx_mini_0299
    (setup : CompoundWireSetup)
    (_problem : MatchesProblemData setup)
    (_figure : MatchesPrimaryFigure setup)
    (_gravity : UsesStandardTerrestrialGravity setup)
    (_positive : HasPositivePhysicalParameters setup)
    (_laws : SatisfiesCompoundWireLaws setup) :
    IsLowestJointNodeFrequencyAtWholeHertz
        setup recordedAnswerChoice.frequencyInHertz ∧
      ModePairMatchesWholeHertz
        setup 2 5 recordedAnswerChoice.frequencyInHertz := by
  change
    IsLowestJointNodeFrequencyAtWholeHertz
        setup AnswerChoice.D.frequencyInHertz ∧
      ModePairMatchesWholeHertz
        setup 2 5 AnswerChoice.D.frequencyInHertz
  have hModePair :=
    second_aluminum_and_fifth_steel_modes_match_choice_D
      setup _problem _gravity _positive _laws
  refine ⟨?_, hModePair⟩
  unfold IsLowestJointNodeFrequencyAtWholeHertz
  refine ⟨by norm_num [AnswerChoice.frequencyInHertz], ?_, ?_⟩
  · exact ⟨2, 5, hModePair⟩
  · exact every_joint_node_frequency_is_at_least_choice_D
      setup _problem _gravity _positive _laws

end PhyXMiniProblems.ProblemPhyXMini0299
