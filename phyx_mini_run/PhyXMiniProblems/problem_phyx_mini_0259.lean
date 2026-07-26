import Mathlib
import Physlib.ClassicalMechanics.HarmonicOscillator.Basic
import Physlib.SpaceAndTime.Space.LengthUnit
import Physlib.Units.WithDim.Energy

noncomputable section

namespace PhyXMiniProblems.ProblemPhyXMini0259

open Dimension

/-!
# Spring constant from a kinetic-energy--position graph

The supplied graph plots the kinetic energy `K` of a simple harmonic
oscillator against its signed displacement `x`.  Its horizontal axis is in
centimetres, its vertical axis is in joules, and the marked vertical scale is
`K_s = 4.0 J`.  The curve has turning points at `x = -12 cm` and `x = 12 cm`.

Length, mass, spring stiffness, and energy are represented by Physlib
dimensionful quantities.  Real numbers below occur only as coherent unit
readouts, as the one-dimensional SI coordinate required by Physlib's
`ClassicalMechanics.HarmonicOscillator` API, or as displayed answer data.
-/

/-! ## Dimensionful quantities and named-unit readouts -/

/-- A signed displacement from the oscillator's equilibrium position. -/
abbrev LengthQuantity : Type := Dimensionful (WithDim L𝓭 ℝ)

/-- The physical mass of the oscillating body. -/
abbrev MassQuantity : Type := Dimensionful (WithDim M𝓭 ℝ)

/-- Spring stiffness, whose dimension is force per length, `M T⁻²`. -/
abbrev SpringStiffnessQuantity : Type :=
  Dimensionful (WithDim (M𝓭 * T𝓭⁻¹ * T𝓭⁻¹) ℝ)

/-- Mechanical energy, whose dimension is `M L² T⁻²`. -/
abbrev EnergyQuantity : Type := DimEnergy

/-- SI base units with centimetres selected as the length unit. -/
noncomputable def centimeterUnitChoices : UnitChoices :=
  { UnitChoices.SI with length := LengthUnit.centimeters }

/-- Scalar readout of a signed physical displacement in metres. -/
def lengthInMeters (length : LengthQuantity) : ℝ :=
  (length UnitChoices.SI).val

/-- Scalar readout of a signed physical displacement in centimetres. -/
def lengthInCentimeters (length : LengthQuantity) : ℝ :=
  (length centimeterUnitChoices).val

/-- Scalar readout of a physical mass in kilograms. -/
def massInKilograms (mass : MassQuantity) : ℝ :=
  (mass UnitChoices.SI).val

/-- Scalar readout of spring stiffness in newtons per metre. -/
def stiffnessInNewtonsPerMeter (stiffness : SpringStiffnessQuantity) : ℝ :=
  (stiffness UnitChoices.SI).val

/-- Scalar readout of a mechanical energy in joules. -/
def energyInJoules (energy : EnergyQuantity) : ℝ :=
  (energy UnitChoices.SI).val

/-! ## Figure labels, axes, and grid positions -/

/-- The two coordinate axes visible in the supplied graph. -/
inductive GraphAxis where
  | horizontal
  | vertical
  deriving DecidableEq, Repr

/-- The physical observable plotted on each graph axis. -/
inductive AxisObservable where
  | displacement
  | kineticEnergy
  deriving DecidableEq, Repr

/-- Text labels printed in the graph. -/
inductive FigureLabel where
  | x
  | K
  | Ks
  deriving DecidableEq, Repr

/-- Graph features to which the printed labels refer. -/
inductive FigureFeature where
  | horizontalPositionAxis
  | verticalKineticEnergyAxis
  | verticalScaleMark
  deriving DecidableEq, Repr

/-- The seven numbered horizontal-axis ticks in the primary image. -/
inductive HorizontalTick where
  | negTwelve
  | negEight
  | negFour
  | zero
  | four
  | eight
  | twelve
  deriving DecidableEq, Repr

/-- Centimetre number printed at a horizontal-axis tick. -/
def HorizontalTick.centimeterReadout : HorizontalTick → ℝ
  | .negTwelve => -12
  | .negEight => -8
  | .negFour => -4
  | .zero => 0
  | .four => 4
  | .eight => 8
  | .twelve => 12

/-!
The physical oscillator and the independently stored graph observables.

`kineticEnergyAtDisplacement` is the measured curve rather than a definition
from the requested stiffness.  `oscillatorSIReadout` and
`positionVectorInMeters` are the scalar data needed to use Physlib's
one-dimensional harmonic-oscillator potential energy.  No numerical value for
the requested stiffness is assigned here.
-/
structure KineticEnergyGraphSetup where
  oscillatorMass : MassQuantity
  springStiffness : SpringStiffnessQuantity
  kineticEnergyAtDisplacement : LengthQuantity → EnergyQuantity
  verticalScaleKs : EnergyQuantity
  equilibriumDisplacement : LengthQuantity
  leftTurningDisplacement : LengthQuantity
  rightTurningDisplacement : LengthQuantity
  horizontalTickDisplacement : HorizontalTick → LengthQuantity
  axisObservable : GraphAxis → AxisObservable
  figureLabelTarget : FigureLabel → FigureFeature
  verticalGridStepsToKs : ℕ
  verticalGridStepsToPeak : ℕ
  oscillatorSIReadout : ClassicalMechanics.HarmonicOscillator
  positionVectorInMeters : LengthQuantity → EuclideanSpace ℝ (Fin 1)

/-- A displacement lies in the physical interval displayed between the two
turning points of the graph. -/
def IsInDisplayedDomain
    (setup : KineticEnergyGraphSetup) (displacement : LengthQuantity) : Prop :=
  lengthInMeters setup.leftTurningDisplacement ≤ lengthInMeters displacement ∧
    lengthInMeters displacement ≤ lengthInMeters setup.rightTurningDisplacement

/-!
Qualitative geometry and quantitative readouts taken from the primary bitmap.

The `K_s` mark is four vertical grid steps above zero, while the peak at
`x = 0` is six steps above zero.  The ratio field records this graphical scale
comparison without assuming any value for the spring stiffness.
-/
structure MatchesPrimaryFigure (setup : KineticEnergyGraphSetup) : Prop where
  horizontalAxisPlotsDisplacement :
    setup.axisObservable .horizontal = .displacement
  verticalAxisPlotsKineticEnergy :
    setup.axisObservable .vertical = .kineticEnergy
  xLabelTargetsHorizontalAxis :
    setup.figureLabelTarget .x = .horizontalPositionAxis
  KLabelTargetsVerticalAxis :
    setup.figureLabelTarget .K = .verticalKineticEnergyAxis
  KsLabelTargetsScaleMark :
    setup.figureLabelTarget .Ks = .verticalScaleMark
  horizontalTicksMatchImage :
    ∀ tick,
      lengthInCentimeters (setup.horizontalTickDisplacement tick) =
        tick.centimeterReadout
  equilibriumIsZeroTick :
    setup.equilibriumDisplacement = setup.horizontalTickDisplacement .zero
  leftTurningPointIsNegativeTwelveTick :
    setup.leftTurningDisplacement =
      setup.horizontalTickDisplacement .negTwelve
  rightTurningPointIsTwelveTick :
    setup.rightTurningDisplacement = setup.horizontalTickDisplacement .twelve
  curveVanishesAtLeftTurningPoint :
    energyInJoules
        (setup.kineticEnergyAtDisplacement setup.leftTurningDisplacement) = 0
  curveVanishesAtRightTurningPoint :
    energyInJoules
        (setup.kineticEnergyAtDisplacement setup.rightTurningDisplacement) = 0
  curvePeaksAtEquilibrium :
    ∀ displacement,
      IsInDisplayedDomain setup displacement →
        energyInJoules (setup.kineticEnergyAtDisplacement displacement) ≤
          energyInJoules
            (setup.kineticEnergyAtDisplacement setup.equilibriumDisplacement)
  fourGridStepsToKs : setup.verticalGridStepsToKs = 4
  sixGridStepsToPeak : setup.verticalGridStepsToPeak = 6
  peakToScaleRatio :
    energyInJoules
        (setup.kineticEnergyAtDisplacement setup.equilibriumDisplacement) =
      (3 / 2 : ℝ) * energyInJoules setup.verticalScaleKs

/-!
The numerical vertical scale stated with the problem.  The peak kinetic energy
and the spring stiffness remain unconstrained here.
-/
structure MatchesProblemData (setup : KineticEnergyGraphSetup) : Prop where
  verticalScaleKsInJoules : energyInJoules setup.verticalScaleKs = 4

/-- Positivity and nondegeneracy conditions for the physical oscillator and
the displayed kinetic-energy curve. -/
structure HasPhysicalParameters (setup : KineticEnergyGraphSetup) : Prop where
  massPositive : 0 < massInKilograms setup.oscillatorMass
  stiffnessPositive : 0 < stiffnessInNewtonsPerMeter setup.springStiffness
  scaleEnergyPositive : 0 < energyInJoules setup.verticalScaleKs
  turningPointsOrdered :
    lengthInMeters setup.leftTurningDisplacement <
      lengthInMeters setup.rightTurningDisplacement
  kineticEnergyNonnegativeOnDisplayedDomain :
    ∀ displacement,
      IsInDisplayedDomain setup displacement →
        0 ≤ energyInJoules (setup.kineticEnergyAtDisplacement displacement)

/-!
The governing simple-harmonic-oscillator energy model in coherent SI readouts.

Physlib's scalar oscillator is linked to the dimensionful physical mass and
stiffness.  Its `potentialEnergy` supplies `U(x) = (1/2) k x²`, and conservation
of mechanical energy gives `K(x) + U(x) = K(0) + U(0)` throughout the
accessible interval.  These are general model laws: no target stiffness or
answer choice appears in this interface.
-/
structure SatisfiesSimpleHarmonicEnergyLaw
    (setup : KineticEnergyGraphSetup) : Prop where
  oscillatorMassIsPhysicalMass :
    setup.oscillatorSIReadout.m = massInKilograms setup.oscillatorMass
  oscillatorStiffnessIsPhysicalStiffness :
    setup.oscillatorSIReadout.k =
      stiffnessInNewtonsPerMeter setup.springStiffness
  positionVectorIsDisplacementReadout :
    ∀ displacement,
      setup.positionVectorInMeters displacement 0 = lengthInMeters displacement
  kineticPlusPotentialIsConserved :
    ∀ displacement,
      IsInDisplayedDomain setup displacement →
        energyInJoules (setup.kineticEnergyAtDisplacement displacement) +
            ClassicalMechanics.HarmonicOscillator.potentialEnergy
              setup.oscillatorSIReadout
              (setup.positionVectorInMeters displacement) =
          energyInJoules
              (setup.kineticEnergyAtDisplacement setup.equilibriumDisplacement) +
            ClassicalMechanics.HarmonicOscillator.potentialEnergy
              setup.oscillatorSIReadout
              (setup.positionVectorInMeters setup.equilibriumDisplacement)

/-! ## Derived stiffness and displayed answer -/

/-- Labels printed beside the four candidate spring constants. -/
inductive AnswerChoice where
  | A
  | B
  | C
  | D
  deriving DecidableEq, Repr

/-- Spring stiffness printed beside an answer, in newtons per metre. -/
def AnswerChoice.newtonsPerMeter : AnswerChoice → ℝ
  | .A => 790
  | .B => 800
  | .C => 830
  | .D => 860

/-- The answer label recorded in the supplied dataset metadata. -/
def recordedAnswerChoice : AnswerChoice := .C

/-- Agreement with a value displayed to the nearest ten newtons per metre. -/
def MatchesAnswerChoice
    (setup : KineticEnergyGraphSetup) (choice : AnswerChoice) : Prop :=
  |stiffnessInNewtonsPerMeter setup.springStiffness -
      choice.newtonsPerMeter| ≤ 5

/-- The selected displayed value is strictly closer than every other option. -/
def IsUniqueClosestAnswerChoice
    (setup : KineticEnergyGraphSetup) (choice : AnswerChoice) : Prop :=
  ∀ other : AnswerChoice, other ≠ choice →
    |stiffnessInNewtonsPerMeter setup.springStiffness -
        choice.newtonsPerMeter| <
      |stiffnessInNewtonsPerMeter setup.springStiffness -
        other.newtonsPerMeter|

/-!
The graph peak is `(6 / 4) K_s = 6 J` and the turning-point magnitude is
`0.12 m`.  Conservation with `U(A) = (1/2) k A²` therefore gives the exact SI
readout `k = 2500/3 N/m`.
-/
lemma springStiffness_exact
    (setup : KineticEnergyGraphSetup)
    (_problem : MatchesProblemData setup)
    (_figure : MatchesPrimaryFigure setup)
    (_physical : HasPhysicalParameters setup)
    (_laws : SatisfiesSimpleHarmonicEnergyLaw setup) :
    stiffnessInNewtonsPerMeter setup.springStiffness = (2500 : ℝ) / 3 := by
  have h_peak :
      energyInJoules
          (setup.kineticEnergyAtDisplacement setup.equilibriumDisplacement) = 6 := by
    rw [_figure.peakToScaleRatio, _problem.verticalScaleKsInJoules]
    norm_num
  have h_right_domain :
      IsInDisplayedDomain setup setup.rightTurningDisplacement := by
    exact ⟨le_of_lt _physical.turningPointsOrdered, le_rfl⟩
  have h_right_cm :
      lengthInCentimeters setup.rightTurningDisplacement = 12 := by
    rw [_figure.rightTurningPointIsTwelveTick]
    exact _figure.horizontalTicksMatchImage .twelve
  have h_eq_cm :
      lengthInCentimeters setup.equilibriumDisplacement = 0 := by
    rw [_figure.equilibriumIsZeroTick]
    exact _figure.horizontalTicksMatchImage .zero
  have hscale :
      (UnitChoices.SI.dimScale centimeterUnitChoices)
          (dim (WithDim L𝓭 ℝ)) = (100 : NNReal) := by
    apply NNReal.eq
    norm_num [centimeterUnitChoices, UnitChoices.dimScale,
      LengthUnit.centimeters, LengthUnit.scale, LengthUnit.div_eq_val,
      LengthUnit.meters]
    rfl
  have h_right_conversion :=
    setup.rightTurningDisplacement.2 UnitChoices.SI centimeterUnitChoices
  rw [hscale] at h_right_conversion
  have h_right_conversion_val := congrArg WithDim.val h_right_conversion
  change lengthInCentimeters setup.rightTurningDisplacement =
    (100 : NNReal) • lengthInMeters setup.rightTurningDisplacement at h_right_conversion_val
  norm_num [NNReal.smul_def] at h_right_conversion_val
  have h_right_m :
      lengthInMeters setup.rightTurningDisplacement = (3 : ℝ) / 25 := by
    linarith
  have h_eq_conversion :=
    setup.equilibriumDisplacement.2 UnitChoices.SI centimeterUnitChoices
  rw [hscale] at h_eq_conversion
  have h_eq_conversion_val := congrArg WithDim.val h_eq_conversion
  change lengthInCentimeters setup.equilibriumDisplacement =
    (100 : NNReal) • lengthInMeters setup.equilibriumDisplacement at h_eq_conversion_val
  norm_num [NNReal.smul_def] at h_eq_conversion_val
  have h_eq_m : lengthInMeters setup.equilibriumDisplacement = 0 := by
    linarith
  have hcon := _laws.kineticPlusPotentialIsConserved
    setup.rightTurningDisplacement h_right_domain
  rw [_figure.curveVanishesAtRightTurningPoint, h_peak] at hcon
  simp [ClassicalMechanics.HarmonicOscillator.potentialEnergy,
    _laws.oscillatorStiffnessIsPhysicalStiffness,
    EuclideanSpace.norm_sq_eq,
    _laws.positionVectorIsDisplacementReadout, h_right_m, h_eq_m] at hcon
  norm_num at hcon ⊢
  linarith

/-!
Thus the requested spring constant is approximately
`8.3 × 10² N/m`: recorded answer C.  The exact value is included alongside
the display-precision and unique-choice conclusions.

This formalizes blueprint label `thm:physics:phyx_mini_0259:target`.
-/
theorem problem_phyx_mini_0259
    (setup : KineticEnergyGraphSetup)
    (_problem : MatchesProblemData setup)
    (_figure : MatchesPrimaryFigure setup)
    (_physical : HasPhysicalParameters setup)
    (_laws : SatisfiesSimpleHarmonicEnergyLaw setup) :
    stiffnessInNewtonsPerMeter setup.springStiffness = (2500 : ℝ) / 3 ∧
      MatchesAnswerChoice setup recordedAnswerChoice ∧
      IsUniqueClosestAnswerChoice setup recordedAnswerChoice := by
  have h_exact :=
    springStiffness_exact setup _problem _figure _physical _laws
  refine ⟨h_exact, ?_, ?_⟩
  · norm_num [MatchesAnswerChoice, recordedAnswerChoice,
      AnswerChoice.newtonsPerMeter, h_exact, abs_of_nonneg, abs_of_nonpos]
  · intro other hother
    rw [h_exact]
    cases other <;>
      norm_num [recordedAnswerChoice, AnswerChoice.newtonsPerMeter,
        abs_of_nonneg, abs_of_nonpos] at *

end PhyXMiniProblems.ProblemPhyXMini0259
