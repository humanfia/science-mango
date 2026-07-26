import Mathlib.Analysis.Real.Sqrt
import Physlib.Units.WithDim.Speed

noncomputable section

namespace PhyXMiniProblems.ProblemPhyXMini0188

open Dimension

/-!
# Transverse-wave speed at the bottom of a mine-shaft rope

A uniform rope hangs vertically through an `80.0 m` mine shaft.  Its upper end
is fixed to a support and its lower end is stretched taut by a box of rock
samples.  The geologist at the lower end launches a transverse disturbance.

The tension in a vertical massive rope varies with height.  The value relevant
at the launch point is the lower-end tension: the cross-section there supports
the sample box, while the rope's distributed weight contributes to the tension
at higher cross-sections.  All physical quantities below retain their Physlib
dimensions; real numbers are used only for explicitly named SI readouts and
for the displayed multiple-choice values.
-/

/-! ## Dimensionful physical quantities and SI readouts -/

/-- A nonnegative physical mass, independent of the unit used to read it. -/
abbrev MassQuantity : Type := Dimensionful (WithDim M𝓭 NNReal)

/-- A nonnegative physical length. -/
abbrev LengthQuantity : Type := Dimensionful (WithDim L𝓭 NNReal)

/-- Mass per unit length, the linear density of a uniform rope. -/
abbrev LinearMassDensityQuantity : Type :=
  Dimensionful (WithDim (M𝓭 * L𝓭⁻¹) NNReal)

/-- A nonnegative physical acceleration. -/
abbrev AccelerationQuantity : Type :=
  Dimensionful (WithDim (L𝓭 * T𝓭⁻¹ * T𝓭⁻¹) NNReal)

/-- A nonnegative force; the rope tension has this dimension. -/
abbrev ForceQuantity : Type :=
  Dimensionful (WithDim (M𝓭 * L𝓭 * T𝓭⁻¹ * T𝓭⁻¹) NNReal)

/-- A nonnegative propagation speed. -/
abbrev SpeedQuantity : Type := DimSpeed

/-- Kilogram readout of a physical mass. -/
def massInKilograms (mass : MassQuantity) : ℝ :=
  ((mass UnitChoices.SI).val : ℝ)

/-- Meter readout of a physical length. -/
def lengthInMeters (length : LengthQuantity) : ℝ :=
  ((length UnitChoices.SI).val : ℝ)

/-- Kilogram-per-meter readout of a physical linear mass density. -/
def linearMassDensityInKilogramsPerMeter
    (density : LinearMassDensityQuantity) : ℝ :=
  ((density UnitChoices.SI).val : ℝ)

/-- Meter-per-second-squared readout of a physical acceleration. -/
def accelerationInMetersPerSecondSquared
    (acceleration : AccelerationQuantity) : ℝ :=
  ((acceleration UnitChoices.SI).val : ℝ)

/-- Newton readout of a physical force. -/
def forceInNewtons (force : ForceQuantity) : ℝ :=
  ((force UnitChoices.SI).val : ℝ)

/-- Meter-per-second readout of a physical speed. -/
def speedInMetersPerSecond (speed : SpeedQuantity) : ℝ :=
  ((speed UnitChoices.SI).val : ℝ)

/-! ## Figure labels and physical setup -/

/-- The two labeled ends of the vertical rope. -/
inductive RopeEndpoint where
  | upperEnd
  | lowerEnd
  deriving DecidableEq, Repr

/-- The objects to which the figure shows the rope ends attached. -/
inductive AttachmentObject where
  | topSupport
  | rockSamples
  deriving DecidableEq, Repr

/-- The orientation of the rope through the shaft. -/
inductive RopeOrientation where
  | vertical
  deriving DecidableEq, Repr

/-- Whether the suspended samples have stretched the rope taut. -/
inductive RopeState where
  | taut
  | slack
  deriving DecidableEq, Repr

/-- The kind of disturbance launched by the geologist. -/
inductive RopeWaveKind where
  | transverse
  | longitudinal
  deriving DecidableEq, Repr

/--
Independent quantities and qualitative labels for the mine-shaft setup.

`lowerEndTension` and `lowerEndWaveSpeed` are local quantities at the point
where the bottom geologist jerks the rope.  They are not assigned their target
numerical values in this structure.
-/
structure MineShaftRopeSetup where
  ropeMass : MassQuantity
  samplesMass : MassQuantity
  shaftDepth : LengthQuantity
  tautRopeLength : LengthQuantity
  ropeLinearMassDensity : LinearMassDensityQuantity
  gravitationalAcceleration : AccelerationQuantity
  lowerEndTension : ForceQuantity
  lowerEndWaveSpeed : SpeedQuantity
  endpointAttachment : RopeEndpoint → AttachmentObject
  orientation : RopeOrientation
  state : RopeState
  signalOrigin : RopeEndpoint
  signalWaveKind : RopeWaveKind

/--
The quantitative labels and qualitative relationships read from the problem
statement and primary figure.
-/
structure MatchesProblemAndFigureReadouts
    (setup : MineShaftRopeSetup) : Prop where
  ropeMassKilograms : massInKilograms setup.ropeMass = 2
  samplesMassKilograms : massInKilograms setup.samplesMass = 20
  shaftDepthMeters : lengthInMeters setup.shaftDepth = 80
  ropeSpansShaft : setup.tautRopeLength = setup.shaftDepth
  upperEndFixedToSupport :
    setup.endpointAttachment .upperEnd = .topSupport
  lowerEndAttachedToSamples :
    setup.endpointAttachment .lowerEnd = .rockSamples
  ropeIsVertical : setup.orientation = .vertical
  ropeIsTaut : setup.state = .taut
  geologistSignalsFromLowerEnd : setup.signalOrigin = .lowerEnd
  disturbanceIsTransverse : setup.signalWaveKind = .transverse

/-- The standard near-Earth value `g = 9.8 m/s²` used by the answer data. -/
structure UsesStandardEarthGravity (setup : MineShaftRopeSetup) : Prop where
  gravityReadout :
    accelerationInMetersPerSecondSquared setup.gravitationalAcceleration =
      49 / 5

/-- Positivity and nondegeneracy conditions for the physical rope model. -/
structure HasPhysicalRopeParameters (setup : MineShaftRopeSetup) : Prop where
  ropeMassPositive : 0 < massInKilograms setup.ropeMass
  samplesMassPositive : 0 < massInKilograms setup.samplesMass
  ropeLengthPositive : 0 < lengthInMeters setup.tautRopeLength
  linearDensityPositive :
    0 < linearMassDensityInKilogramsPerMeter setup.ropeLinearMassDensity
  gravityPositive :
    0 < accelerationInMetersPerSecondSquared setup.gravitationalAcceleration
  lowerEndTensionPositive : 0 < forceInNewtons setup.lowerEndTension

/-!
The governing laws used for the requested local wave speed.

The first field is `μ L = m` for a uniform rope.  The second is the lower-end
force balance `T = m_samples g`; it deliberately does not add the rope mass,
because rope weight is supported only by cross-sections above the lower end.
The last field is the transverse-wave law `v = sqrt (T / μ)`.  These are
general physical relations and do not state any displayed answer value.
-/
structure SatisfiesUniformRopeWaveLaws
    (setup : MineShaftRopeSetup) : Prop where
  uniformLinearMassDensity :
    linearMassDensityInKilogramsPerMeter setup.ropeLinearMassDensity *
        lengthInMeters setup.tautRopeLength =
      massInKilograms setup.ropeMass
  lowerEndTensionFromSamples :
    forceInNewtons setup.lowerEndTension =
      massInKilograms setup.samplesMass *
        accelerationInMetersPerSecondSquared
          setup.gravitationalAcceleration
  transverseWaveSpeedLaw :
    speedInMetersPerSecond setup.lowerEndWaveSpeed =
      Real.sqrt
        (forceInNewtons setup.lowerEndTension /
          linearMassDensityInKilogramsPerMeter
            setup.ropeLinearMassDensity)

/-! ## Displayed choices and current target -/

/-- Labels of the four displayed answers. -/
inductive AnswerChoice where
  | A
  | B
  | C
  | D
  deriving DecidableEq, Repr

/-- The displayed speed for each choice, in meters per second. -/
def displayedAnswerSpeedInMetersPerSecond : AnswerChoice → ℝ
  | .A => 177 / 2
  | .B => 783 / 10
  | .C => 699 / 10
  | .D => 394 / 5

/-- The dataset's recorded label; this definition is not a theorem premise. -/
def recordedDatasetAnswer : AnswerChoice := .A

/-- Agreement to the nearest tenth of a meter per second. -/
def MatchesAnswerChoice
    (setup : MineShaftRopeSetup) (choice : AnswerChoice) : Prop :=
  abs (speedInMetersPerSecond setup.lowerEndWaveSpeed -
      displayedAnswerSpeedInMetersPerSecond choice) ≤ 1 / 20

/-- The figure and uniform-rope law imply `μ = 0.025 kg/m`. -/
lemma ropeLinearMassDensity_is_one_fortieth
    (setup : MineShaftRopeSetup)
    (hfigure : MatchesProblemAndFigureReadouts setup)
    (hphysical : HasPhysicalRopeParameters setup)
    (hlaws : SatisfiesUniformRopeWaveLaws setup) :
    linearMassDensityInKilogramsPerMeter setup.ropeLinearMassDensity =
      1 / 40 := by
  have h := hlaws.uniformLinearMassDensity
  rw [hfigure.ropeSpansShaft, hfigure.shaftDepthMeters,
    hfigure.ropeMassKilograms] at h
  norm_num at h ⊢
  linarith

/-- The sample weight gives a lower-end tension of `196 N`. -/
lemma lowerEndTension_is_196_newtons
    (setup : MineShaftRopeSetup)
    (hfigure : MatchesProblemAndFigureReadouts setup)
    (hgravity : UsesStandardEarthGravity setup)
    (hlaws : SatisfiesUniformRopeWaveLaws setup) :
    forceInNewtons setup.lowerEndTension = 196 := by
  calc
    forceInNewtons setup.lowerEndTension =
        massInKilograms setup.samplesMass *
          accelerationInMetersPerSecondSquared
            setup.gravitationalAcceleration :=
      hlaws.lowerEndTensionFromSamples
    _ = 196 := by
      rw [hfigure.samplesMassKilograms, hgravity.gravityReadout]
      norm_num

/--
For the pictured `2.00 kg`, `80.0 m` rope under the lower-end tension produced
by the `20.0 kg` samples, the transverse launch speed rounds to `88.5 m/s`,
which is displayed choice A.

Blueprint: `thm:physics:phyx_mini_0188:target`.
-/
theorem problem_phyx_mini_0188
    (setup : MineShaftRopeSetup)
    (hfigure : MatchesProblemAndFigureReadouts setup)
    (hgravity : UsesStandardEarthGravity setup)
    (hphysical : HasPhysicalRopeParameters setup)
    (hlaws : SatisfiesUniformRopeWaveLaws setup) :
    MatchesAnswerChoice setup .A := by
  have hμ :=
    ropeLinearMassDensity_is_one_fortieth setup hfigure hphysical hlaws
  have hT :=
    lowerEndTension_is_196_newtons setup hfigure hgravity hlaws
  have hv := hlaws.transverseWaveSpeedLaw
  rw [hT, hμ] at hv
  norm_num at hv
  unfold MatchesAnswerChoice
  simp only [displayedAnswerSpeedInMetersPerSecond]
  rw [hv]
  have hsqrt_sq : (Real.sqrt (7840 : ℝ)) ^ 2 = 7840 := by
    norm_num
  have hsqrt_nonneg : 0 ≤ Real.sqrt (7840 : ℝ) :=
    Real.sqrt_nonneg _
  rw [abs_le]
  constructor <;> nlinarith

end PhyXMiniProblems.ProblemPhyXMini0188
