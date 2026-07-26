import Mathlib
import Physlib.Units.WithDim.Speed

noncomputable section

namespace PhyXMiniProblems.ProblemPhyXMini0213

open Dimension

/-!
# Sound frequency of a vibrating tree branch

The primary figure depicts the portion of a horizontal tree branch between
its attachment to the trunk and its free end near a perched bird.  The trunk
attachment is labeled as a displacement node, the bird-side end is labeled as
an antinode, and the span between them is marked `1/4 λ`.

Lengths, frequencies, and wave speed are represented by unit-independent
Physlib quantities.  Real numbers occur only as readouts in a coherent choice
of units and as the displayed answer-choice values.  In particular, neither
frequency field below is assigned the requested value `500 Hz`.
-/

/-! ## Dimensionful physical quantities and scalar readouts -/

/-- A nonnegative physical length, independent of the unit used to read it. -/
abbrev LengthQuantity : Type := Dimensionful (WithDim L𝓭 NNReal)

/-- An ordinary nonnegative frequency, with inverse-time dimension. -/
abbrev FrequencyQuantity : Type :=
  Dimensionful (WithDim T𝓭⁻¹ NNReal)

/-- The propagation speed of a transverse disturbance along the branch. -/
abbrev BranchWaveSpeed : Type := DimSpeed

/-- Read a physical length as a real scalar in a coherent unit system. -/
def lengthReadout (units : UnitChoices) (length : LengthQuantity) : ℝ :=
  ((length units).val : ℝ)

/-- Read a physical frequency as a real scalar in a coherent unit system. -/
def frequencyReadout
    (units : UnitChoices) (frequency : FrequencyQuantity) : ℝ :=
  ((frequency units).val : ℝ)

/-- Read a physical speed as a real scalar in a coherent unit system. -/
def speedReadout (units : UnitChoices) (speed : BranchWaveSpeed) : ℝ :=
  ((speed units).val : ℝ)

/-- SI-meter readout of a physical length. -/
def lengthInMeters (length : LengthQuantity) : ℝ :=
  lengthReadout UnitChoices.SI length

/-- SI-hertz readout of a physical frequency. -/
def frequencyInHertz (frequency : FrequencyQuantity) : ℝ :=
  frequencyReadout UnitChoices.SI frequency

/-- SI-meter-per-second readout of the branch-wave speed. -/
def speedInMetersPerSecond (speed : BranchWaveSpeed) : ℝ :=
  speedReadout UnitChoices.SI speed

/-! ## Physical setup and figure labels -/

/-- The two labeled locations at the ends of the quarter-wave span. -/
inductive BranchFigurePoint where
  | trunkAttachment
  | birdSideEnd
  deriving DecidableEq, Repr

/-- Transverse-displacement amplitude at a labeled point of a standing wave. -/
inductive StandingWaveRole where
  | node
  | antinode
  deriving DecidableEq, Repr

/-- The qualitative type of branch motion represented by the diagram. -/
inductive BranchWaveKind where
  | transverseStandingWave
  deriving DecidableEq, Repr

/-- The mechanism described in the prose as exciting the branch. -/
inductive BranchExcitationSource where
  | wind
  deriving DecidableEq, Repr

/-- Figure annotations, including physical positions measured from the trunk. -/
structure TreeBranchFigure where
  positionFromTrunk : BranchFigurePoint → LengthQuantity
  displacementRole : BranchFigurePoint → StandingWaveRole
  birdLocation : BranchFigurePoint

/-!
Physical quantities for the wind-excited branch and the sound it radiates.
The standing wavelength, branch-wave speed, branch vibration frequency, and
radiated sound frequency are independent fields related only by the governing
laws below.
-/
structure TreeBranchResonanceSetup where
  excitationSource : BranchExcitationSource
  waveKind : BranchWaveKind
  nodeToAntinodeSpan : LengthQuantity
  standingWavelength : LengthQuantity
  branchWaveSpeed : BranchWaveSpeed
  branchVibrationFrequency : FrequencyQuantity
  radiatedSoundFrequency : FrequencyQuantity
  figure : TreeBranchFigure

/-- Prose-level scenario data: the branch vibration is excited by wind. -/
structure MatchesProblemScenario
    (setup : TreeBranchResonanceSetup) : Prop where
  windExcitesBranch : setup.excitationSource = .wind

/-!
Data read from the supplied bitmap.  The attached end is a node, the end near
the bird is an antinode, and the marked node-to-antinode span is one quarter
of the displayed wavelength.  No frequency or wave-speed value is present in
the figure.
-/
structure MatchesSuppliedTreeBranchFigure
    (setup : TreeBranchResonanceSetup) : Prop where
  waveIsTransverseStandingWave :
    setup.waveKind = .transverseStandingWave
  trunkIsNode :
    setup.figure.displacementRole .trunkAttachment = .node
  birdSideIsAntinode :
    setup.figure.displacementRole .birdSideEnd = .antinode
  birdIsAtAntinodeEnd : setup.figure.birdLocation = .birdSideEnd
  trunkPosition :
    ∀ units,
      lengthReadout units
          (setup.figure.positionFromTrunk .trunkAttachment) = 0
  birdSidePosition :
    ∀ units,
      lengthReadout units (setup.figure.positionFromTrunk .birdSideEnd) =
        lengthReadout units setup.nodeToAntinodeSpan
  quarterWavelengthMark :
    ∀ units,
      4 * lengthReadout units setup.nodeToAntinodeSpan =
        lengthReadout units setup.standingWavelength

/-- Positivity assumptions selecting a nondegenerate physical resonance. -/
structure HasPhysicalTreeBranchParameters
    (setup : TreeBranchResonanceSetup) : Prop where
  spanPositive : 0 < lengthInMeters setup.nodeToAntinodeSpan
  wavelengthPositive : 0 < lengthInMeters setup.standingWavelength
  waveSpeedPositive :
    0 < speedInMetersPerSecond setup.branchWaveSpeed
  branchFrequencyPositive :
    0 < frequencyInHertz setup.branchVibrationFrequency
  soundFrequencyPositive :
    0 < frequencyInHertz setup.radiatedSoundFrequency

/-!
Governing laws for the modeled resonance:

* the nondispersive branch disturbance obeys `v = f λ` in every coherent
  choice of units;
* the radiated tone has the same ordinary frequency as the vibrating source.

Neither law contains the requested value `500 Hz` or an answer-choice label.
-/
structure SatisfiesTreeBranchResonanceLaws
    (setup : TreeBranchResonanceSetup) : Prop where
  waveSpeedEqualsFrequencyTimesWavelength :
    ∀ units,
      speedReadout units setup.branchWaveSpeed =
        frequencyReadout units setup.branchVibrationFrequency *
          lengthReadout units setup.standingWavelength
  soundFrequencyEqualsBranchFrequency :
    setup.radiatedSoundFrequency = setup.branchVibrationFrequency

/-!
The quarter-wave figure and `v = f λ` imply the dimensionally meaningful
cross-multiplied relation `4 L f = v`.  This is the strongest numerical
frequency relation determined by the supplied physical data.
-/
lemma quarterWave_branchFrequency_relation
    (setup : TreeBranchResonanceSetup)
    (hFigure : MatchesSuppliedTreeBranchFigure setup)
    (hLaws : SatisfiesTreeBranchResonanceLaws setup)
    (units : UnitChoices) :
    4 * lengthReadout units setup.nodeToAntinodeSpan *
        frequencyReadout units setup.branchVibrationFrequency =
      speedReadout units setup.branchWaveSpeed := by
  rw [hLaws.waveSpeedEqualsFrequencyTimesWavelength,
    ← hFigure.quarterWavelengthMark]
  ring

/-- The same quarter-wave relation expressed for the radiated sound tone. -/
lemma quarterWave_soundFrequency_relation
    (setup : TreeBranchResonanceSetup)
    (hFigure : MatchesSuppliedTreeBranchFigure setup)
    (hLaws : SatisfiesTreeBranchResonanceLaws setup)
    (units : UnitChoices) :
    4 * lengthReadout units setup.nodeToAntinodeSpan *
        frequencyReadout units setup.radiatedSoundFrequency =
      speedReadout units setup.branchWaveSpeed := by
  rw [hLaws.soundFrequencyEqualsBranchFrequency]
  exact quarterWave_branchFrequency_relation setup hFigure hLaws units

/-! ## Displayed answer data and requested conclusion -/

/-- Labels of the four frequency choices printed with the problem. -/
inductive AnswerChoice where
  | A
  | B
  | C
  | D
  deriving DecidableEq, Repr

/-- Displayed frequency beside an answer label, measured in hertz. -/
def displayedAnswerFrequencyHertz : AnswerChoice → ℝ
  | .A => 440
  | .B => 460
  | .C => 480
  | .D => 500

/-- The answer label recorded by the source dataset. -/
def recordedDatasetAnswer : AnswerChoice := .D

/-- A displayed choice agrees with the modeled radiated sound frequency. -/
def AgreesWithDisplayedFrequencyChoice
    (setup : TreeBranchResonanceSetup) (choice : AnswerChoice) : Prop :=
  frequencyInHertz setup.radiatedSoundFrequency =
    displayedAnswerFrequencyHertz choice

/-!
The recorded answer says that the vibrating branch emits a `500 Hz` tone,
which is displayed choice D; the definitions above retain that answer as
dataset metadata.

The bitmap and prose supply no numerical node-to-antinode length or branch
wave speed, so they do not support a conclusion that the modeled frequency
agrees with choice D.  The theorem instead states the strongest frequency
formula supported by the supplied evidence: in SI readouts, the radiated
sound frequency is the branch-wave speed divided by four times the displayed
node-to-antinode span.

This formalizes `thm:physics:phyx_mini_0213:target`.
-/
theorem problem_phyx_mini_0213
    (setup : TreeBranchResonanceSetup)
    (hScenario : MatchesProblemScenario setup)
    (hFigure : MatchesSuppliedTreeBranchFigure setup)
    (hPhysical : HasPhysicalTreeBranchParameters setup)
    (hLaws : SatisfiesTreeBranchResonanceLaws setup) :
    frequencyInHertz setup.radiatedSoundFrequency =
      speedInMetersPerSecond setup.branchWaveSpeed /
        (4 * lengthInMeters setup.nodeToAntinodeSpan) := by
  have hDenominator :
      4 * lengthInMeters setup.nodeToAntinodeSpan ≠ 0 :=
    mul_ne_zero (by norm_num) (ne_of_gt hPhysical.spanPositive)
  apply (eq_div_iff hDenominator).2
  simpa [frequencyInHertz, speedInMetersPerSecond, lengthInMeters,
    mul_comm] using
    quarterWave_soundFrequency_relation setup hFigure hLaws UnitChoices.SI

end PhyXMiniProblems.ProblemPhyXMini0213
