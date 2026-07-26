import Mathlib.Analysis.Real.Sqrt
import Physlib.Units.WithDim.Speed

noncomputable section

namespace PhyXMiniProblems.ProblemPhyXMini0292

open Dimension

/-!
# Wave speed on String 2 in a three-pulley system

The primary figure shows String 1 fixed at the left support, passing over the
left fixed pulley, around a lower movable pulley carrying the mass `M`, and
ending at a knot.  String 2 starts at that knot, passes over the right fixed
pulley, and ends at the right support.

The two upward String-1 segments support the movable pulley and its load.  An
ideal massless knot transfers the String-1 tension to String 2.  All basic
physical quantities below retain their Physlib dimensions; real numbers occur
only as explicitly named coherent-SI readouts and displayed answer values.
-/

/-! ## Dimensionful physical quantities and coherent-SI readouts -/

/-- A nonnegative physical mass. -/
abbrev MassQuantity : Type := Dimensionful (WithDim M𝓭 NNReal)

/-- A nonnegative physical acceleration magnitude. -/
abbrev AccelerationQuantity : Type :=
  Dimensionful (WithDim (L𝓭 * T𝓭⁻¹ * T𝓭⁻¹) NNReal)

/-- A nonnegative force magnitude, used here for a string-segment tension. -/
abbrev TensionQuantity : Type :=
  Dimensionful (WithDim (M𝓭 * L𝓭 * T𝓭⁻¹ * T𝓭⁻¹) NNReal)

/-- A nonnegative mass per unit length of string. -/
abbrev LinearMassDensityQuantity : Type :=
  Dimensionful (WithDim (M𝓭 * L𝓭⁻¹) NNReal)

/-- A nonnegative propagation speed. -/
abbrev SpeedQuantity : Type := DimSpeed

/-- Read a nonnegative dimensionful quantity in a coherent unit system. -/
def quantityReadout {d : Dimension}
    (units : UnitChoices) (quantity : Dimensionful (WithDim d NNReal)) : ℝ :=
  ((quantity units).val : ℝ)

/-- Kilogram readout of a mass. -/
def massInKilograms (mass : MassQuantity) : ℝ :=
  quantityReadout UnitChoices.SI mass

/-- Meter-per-second-squared readout of an acceleration. -/
def accelerationInMetersPerSecondSquared
    (acceleration : AccelerationQuantity) : ℝ :=
  quantityReadout UnitChoices.SI acceleration

/-- Newton readout of a tension. -/
def tensionInNewtons (tension : TensionQuantity) : ℝ :=
  quantityReadout UnitChoices.SI tension

/-- Kilogram-per-meter readout of a linear mass density. -/
def linearMassDensityInKilogramsPerMeter
    (density : LinearMassDensityQuantity) : ℝ :=
  quantityReadout UnitChoices.SI density

/-- Meter-per-second readout of a wave speed. -/
def speedInMetersPerSecond (speed : SpeedQuantity) : ℝ :=
  quantityReadout UnitChoices.SI speed

/-! ## Primary-figure labels and topology -/

/-- The two strings explicitly labelled in the primary figure. -/
inductive StringLabel where
  | string1
  | string2
  deriving DecidableEq, Repr

/-- The three separately drawn pulleys. -/
inductive PulleyLabel where
  | leftFixed
  | rightFixed
  | lowerMovable
  deriving DecidableEq, Repr

/-- Whether a pulley is anchored to the support or moves with the load. -/
inductive PulleyMounting where
  | anchored
  | movableWithLoad
  deriving DecidableEq, Repr

/-- Individually identifiable objects shown in the primary figure. -/
inductive FigureComponent where
  | leftSupport
  | rightSupport
  | leftFixedPulley
  | rightFixedPulley
  | lowerMovablePulley
  | knot
  | hangingMassM
  | string1
  | string2
  deriving DecidableEq, Repr

/-- Objects to which the support-side and knot-side string ends attach. -/
inductive EndpointAttachment where
  | leftSupport
  | rightSupport
  | knot
  deriving DecidableEq, Repr

/-- The two distinguished ends of either pictured string. -/
inductive StringEndpoint where
  | supportSide
  | knotSide
  deriving DecidableEq, Repr

/-- The full route of each string through the pictured pulley system. -/
inductive StringRoute where
  | leftSupportOverLeftPulleyAroundMovablePulleyToKnot
  | knotOverRightPulleyToRightSupport
  deriving DecidableEq, Repr

/-!
The five straight string portions separated by pulleys and by the knot.  The
two String-1 portions adjacent to the movable pulley supply its two upward
supporting tensions.
-/
inductive StringSegment where
  | string1LeftHorizontal
  | string1LeftSupporting
  | string1RightSupporting
  | string2KnotSide
  | string2RightHorizontal
  deriving DecidableEq, Repr

/-- The string to which a named straight segment belongs. -/
def StringSegment.stringLabel : StringSegment → StringLabel
  | .string1LeftHorizontal => .string1
  | .string1LeftSupporting => .string1
  | .string1RightSupporting => .string1
  | .string2KnotSide => .string2
  | .string2RightHorizontal => .string2

/-!
Independent physical quantities and qualitative figure data.  In particular,
neither the tension on String 2 nor its requested wave speed is assigned a
numerical value here.
-/
structure PulleyStringSetup where
  figureShows : FigureComponent → Prop
  stringRoute : StringLabel → StringRoute
  endpointAttachment : StringLabel → StringEndpoint → EndpointAttachment
  pulleyMounting : PulleyLabel → PulleyMounting
  hangingMassAttachedTo : PulleyLabel
  pulleyIsIdeal : PulleyLabel → Prop
  knotIsMassless : Prop
  stringIsTaut : StringLabel → Prop
  lowerAssemblyInStaticEquilibrium : Prop
  knotInStaticEquilibrium : Prop
  hangingMass : MassQuantity
  gravitationalAcceleration : AccelerationQuantity
  linearMassDensity : StringLabel → LinearMassDensityQuantity
  segmentTension : StringSegment → TensionQuantity
  transverseWaveSpeed : StringLabel → SpeedQuantity

/-!
Figure topology and numerical readouts supplied by the problem.  The image,
taken as primary evidence, places `M` below the lower movable pulley rather
than directly below the knot.
-/
structure MatchesProblemAndPrimaryFigure (setup : PulleyStringSetup) : Prop where
  showsEveryLabelledComponent : ∀ component, setup.figureShows component
  string1Route :
    setup.stringRoute .string1 =
      .leftSupportOverLeftPulleyAroundMovablePulleyToKnot
  string2Route :
    setup.stringRoute .string2 = .knotOverRightPulleyToRightSupport
  string1SupportEndAtLeft :
    setup.endpointAttachment .string1 .supportSide = .leftSupport
  string1OtherEndAtKnot :
    setup.endpointAttachment .string1 .knotSide = .knot
  string2SupportEndAtRight :
    setup.endpointAttachment .string2 .supportSide = .rightSupport
  string2OtherEndAtKnot :
    setup.endpointAttachment .string2 .knotSide = .knot
  leftPulleyAnchored : setup.pulleyMounting .leftFixed = .anchored
  rightPulleyAnchored : setup.pulleyMounting .rightFixed = .anchored
  lowerPulleyMovesWithLoad :
    setup.pulleyMounting .lowerMovable = .movableWithLoad
  massHangsFromLowerPulley :
    setup.hangingMassAttachedTo = .lowerMovable
  bothStringsTaut : ∀ string, setup.stringIsTaut string
  lowerAssemblyStatic : setup.lowerAssemblyInStaticEquilibrium
  knotStatic : setup.knotInStaticEquilibrium
  hangingMassKilograms : massInKilograms setup.hangingMass = 1 / 2
  string1DensityKilogramsPerMeter :
    linearMassDensityInKilogramsPerMeter
        (setup.linearMassDensity .string1) = 3 / 1000
  string2DensityKilogramsPerMeter :
    linearMassDensityInKilogramsPerMeter
        (setup.linearMassDensity .string2) = 5 / 1000

/-- The conventional near-Earth gravitational readout used by the choices. -/
structure UsesStandardEarthGravity (setup : PulleyStringSetup) : Prop where
  gravityMetersPerSecondSquared :
    accelerationInMetersPerSecondSquared setup.gravitationalAcceleration =
      49 / 5

/-- Positivity and nondegeneracy conditions for the taut-string model. -/
structure HasPositivePhysicalParameters (setup : PulleyStringSetup) : Prop where
  hangingMassPositive : 0 < massInKilograms setup.hangingMass
  gravityPositive :
    0 < accelerationInMetersPerSecondSquared setup.gravitationalAcceleration
  densitiesPositive :
    ∀ string,
      0 < linearMassDensityInKilogramsPerMeter
        (setup.linearMassDensity string)
  segmentTensionsPositive :
    ∀ segment, 0 < tensionInNewtons (setup.segmentTension segment)
  waveSpeedsPositive :
    ∀ string, 0 < speedInMetersPerSecond (setup.transverseWaveSpeed string)

/-! ## Governing ideal-pulley, equilibrium, and wave laws -/

/-!
The textbook idealizations needed for the calculation:

* negligible string weight in the static balance and frictionless ideal
  pulleys transmit one tension along every segment of a given string;
* the two upward String-1 segments balance the lower pulley and mass;
* the massless static knot balances the adjacent String-1 and String-2 pulls;
* every taut string obeys `v = sqrt (T / mu)`.

These laws are stated generically in terms of independent setup quantities.
They contain neither `sqrt 490` nor the displayed answer `22.1 m/s`.
-/
structure SatisfiesIdealPulleyKnotAndWaveLaws
    (setup : PulleyStringSetup) : Prop where
  everyPulleyIdeal : ∀ pulley, setup.pulleyIsIdeal pulley
  knotMassless : setup.knotIsMassless
  idealTensionTransmission :
    ∀ segment₁ segment₂,
      segment₁.stringLabel = segment₂.stringLabel →
        tensionInNewtons (setup.segmentTension segment₁) =
          tensionInNewtons (setup.segmentTension segment₂)
  movablePulleyStaticBalance :
    setup.lowerAssemblyInStaticEquilibrium →
      tensionInNewtons (setup.segmentTension .string1LeftSupporting) +
          tensionInNewtons (setup.segmentTension .string1RightSupporting) =
        massInKilograms setup.hangingMass *
          accelerationInMetersPerSecondSquared
            setup.gravitationalAcceleration
  masslessKnotStaticBalance :
    setup.knotInStaticEquilibrium →
      tensionInNewtons (setup.segmentTension .string2KnotSide) =
        tensionInNewtons (setup.segmentTension .string1RightSupporting)
  transverseWaveSpeedLaw :
    ∀ string segment,
      segment.stringLabel = string →
      setup.stringIsTaut string →
        speedInMetersPerSecond (setup.transverseWaveSpeed string) =
          Real.sqrt
            (tensionInNewtons (setup.segmentTension segment) /
              linearMassDensityInKilogramsPerMeter
                (setup.linearMassDensity string))

/-! ## Derived mechanics and requested answer -/

/-- Each String-1 segment supporting the movable pulley has tension `2.45 N`. -/
lemma stringOneSupportingTensions_are_49_over_20_newtons
    (setup : PulleyStringSetup)
    (h_figure : MatchesProblemAndPrimaryFigure setup)
    (h_gravity : UsesStandardEarthGravity setup)
    (h_laws : SatisfiesIdealPulleyKnotAndWaveLaws setup) :
    tensionInNewtons (setup.segmentTension .string1LeftSupporting) = 49 / 20 ∧
      tensionInNewtons (setup.segmentTension .string1RightSupporting) =
        49 / 20 := by
  have h_tensions_equal :
      tensionInNewtons (setup.segmentTension .string1LeftSupporting) =
        tensionInNewtons (setup.segmentTension .string1RightSupporting) :=
    h_laws.idealTensionTransmission
      .string1LeftSupporting .string1RightSupporting (by rfl)
  have h_balance :=
    h_laws.movablePulleyStaticBalance h_figure.lowerAssemblyStatic
  rw [h_figure.hangingMassKilograms,
    h_gravity.gravityMetersPerSecondSquared] at h_balance
  constructor <;> nlinarith

/-- Static balance at the massless knot gives String 2 the same `2.45 N` tension. -/
lemma stringTwoTension_is_49_over_20_newtons
    (setup : PulleyStringSetup)
    (h_figure : MatchesProblemAndPrimaryFigure setup)
    (h_gravity : UsesStandardEarthGravity setup)
    (h_laws : SatisfiesIdealPulleyKnotAndWaveLaws setup) :
    tensionInNewtons (setup.segmentTension .string2KnotSide) = 49 / 20 := by
  have h_string_one :=
    stringOneSupportingTensions_are_49_over_20_newtons
      setup h_figure h_gravity h_laws
  have h_knot := h_laws.masslessKnotStaticBalance h_figure.knotStatic
  calc
    tensionInNewtons (setup.segmentTension .string2KnotSide) =
        tensionInNewtons (setup.segmentTension .string1RightSupporting) :=
      h_knot
    _ = 49 / 20 := h_string_one.2

/-!
With `mu_2 = 0.005 kg/m`, the unrounded requested speed is
`sqrt ((2.45 N) / (0.005 kg/m)) = sqrt 490 m/s`.
-/
lemma stringTwoWaveSpeed_exact
    (setup : PulleyStringSetup)
    (h_figure : MatchesProblemAndPrimaryFigure setup)
    (h_gravity : UsesStandardEarthGravity setup)
    (h_positive : HasPositivePhysicalParameters setup)
    (h_laws : SatisfiesIdealPulleyKnotAndWaveLaws setup) :
    speedInMetersPerSecond (setup.transverseWaveSpeed .string2) =
      Real.sqrt 490 := by
  have h_wave :=
    h_laws.transverseWaveSpeedLaw
      .string2 .string2KnotSide (by rfl) (h_figure.bothStringsTaut .string2)
  have h_density_ne :
      linearMassDensityInKilogramsPerMeter
          (setup.linearMassDensity .string2) ≠ 0 :=
    ne_of_gt (h_positive.densitiesPositive .string2)
  have h_ratio :
      tensionInNewtons (setup.segmentTension .string2KnotSide) /
          linearMassDensityInKilogramsPerMeter
            (setup.linearMassDensity .string2) = 490 := by
    apply (div_eq_iff h_density_ne).2
    rw [stringTwoTension_is_49_over_20_newtons
      setup h_figure h_gravity h_laws,
      h_figure.string2DensityKilogramsPerMeter]
    norm_num
  rw [h_wave, h_ratio]

/-- Labels printed beside the four multiple-choice answers. -/
inductive AnswerChoice where
  | A
  | B
  | C
  | D
  deriving DecidableEq, Repr

/-- Displayed wave-speed readout for each choice, in meters per second. -/
def AnswerChoice.speedInMetersPerSecond : AnswerChoice → ℝ
  | .A => 99 / 5
  | .B => 203 / 10
  | .C => 107 / 5
  | .D => 221 / 10

/-- The answer label recorded in the supplied dataset metadata. -/
def recordedAnswerChoice : AnswerChoice := .D

/-!
Agreement with a speed displayed to one decimal place.  The tolerance is
`0.05 m/s`, half a unit in the last displayed digit.
-/
def MatchesAnswerChoice
    (setup : PulleyStringSetup) (choice : AnswerChoice) : Prop :=
  abs (speedInMetersPerSecond (setup.transverseWaveSpeed .string2) -
      choice.speedInMetersPerSecond) ≤ 1 / 20

/-!
The wave speed on String 2 agrees, to the displayed precision, with recorded
choice D: `22.1 m/s`.

Blueprint: `thm:physics:phyx_mini_0292:target`.
-/
theorem problem_phyx_mini_0292
    (setup : PulleyStringSetup)
    (h_figure : MatchesProblemAndPrimaryFigure setup)
    (h_gravity : UsesStandardEarthGravity setup)
    (h_positive : HasPositivePhysicalParameters setup)
    (h_laws : SatisfiesIdealPulleyKnotAndWaveLaws setup) :
    MatchesAnswerChoice setup recordedAnswerChoice := by
  rw [MatchesAnswerChoice, recordedAnswerChoice,
    AnswerChoice.speedInMetersPerSecond,
    stringTwoWaveSpeed_exact setup h_figure h_gravity h_positive h_laws,
    abs_le]
  have h_sqrt_nonnegative : 0 ≤ Real.sqrt (490 : ℝ) :=
    Real.sqrt_nonneg _
  have h_sqrt_squared : (Real.sqrt (490 : ℝ)) ^ 2 = 490 :=
    Real.sq_sqrt (by norm_num)
  constructor <;> nlinarith

end PhyXMiniProblems.ProblemPhyXMini0292
