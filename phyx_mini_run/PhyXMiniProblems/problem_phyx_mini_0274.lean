import Mathlib
import Physlib.Units.WithDim.Energy

noncomputable section

namespace PhyXMiniProblems.ProblemPhyXMini0274

open Dimension

/-!
# Length of a simple pendulum from its kinetic-energy graph

The primary image plots the bob's kinetic energy `K` against its angular
displacement `θ` from the vertical.  Its horizontal axis is in milliradians,
its vertical axis is in millijoules, the curve vanishes at `±100 mrad`, and
the marked scale `K_s = 10.0 mJ` lies on the second of three equal vertical
grid steps.  Hence the central apex is at `(3 / 2) K_s`.

Mass, length, acceleration, and energy are represented by Physlib
dimensionful quantities.  Real numbers below are only coherent SI readouts,
dimensionless angular coordinates in radians, and displayed numerical data.
-/

/-! ## Dimensionful quantities and coherent SI readouts -/

/-- A nonnegative physical mass. -/
abbrev MassQuantity : Type := Dimensionful (WithDim M𝓭 NNReal)

/-- A nonnegative physical length. -/
abbrev LengthQuantity : Type := Dimensionful (WithDim L𝓭 NNReal)

/-- A nonnegative physical acceleration, with dimension `L T⁻²`. -/
abbrev AccelerationQuantity : Type :=
  Dimensionful (WithDim (L𝓭 * T𝓭⁻¹ * T𝓭⁻¹) NNReal)

/-- Physical energy, with dimension `M L² T⁻²`. -/
abbrev EnergyQuantity : Type := DimEnergy

/-- Kilogram readout of a physical mass. -/
def massInKilograms (mass : MassQuantity) : ℝ :=
  ((mass UnitChoices.SI).val : ℝ)

/-- Metre readout of a physical length. -/
def lengthInMeters (length : LengthQuantity) : ℝ :=
  ((length UnitChoices.SI).val : ℝ)

/-- Metre-per-second-squared readout of a physical acceleration. -/
def accelerationInMetersPerSecondSquared
    (acceleration : AccelerationQuantity) : ℝ :=
  ((acceleration UnitChoices.SI).val : ℝ)

/-- Joule readout of a physical energy. -/
def energyInJoules (energy : EnergyQuantity) : ℝ :=
  (energy UnitChoices.SI).val /
    (DimEnergy.joule UnitChoices.SI).val

/-- Millijoule readout used on the graph's vertical axis. -/
def energyInMilliJoules (energy : EnergyQuantity) : ℝ :=
  1000 * energyInJoules energy

/-- Convert a scalar graph coordinate in milliradians to radians. -/
def milliRadiansToRadians (angleMilliRadians : ℝ) : ℝ :=
  angleMilliRadians / 1000

/-! ## Primary-figure roles and readouts -/

/-- Physical quantity assigned to the graph's horizontal axis. -/
inductive HorizontalAxisRole where
  | angleFromVertical
  | other
  deriving DecidableEq, Repr

/-- Physical quantity assigned to the graph's vertical axis. -/
inductive VerticalAxisRole where
  | kineticEnergy
  | other
  deriving DecidableEq, Repr

/-- Unit printed on the horizontal axis. -/
inductive AngleDisplayUnit where
  | milliradian
  | other
  deriving DecidableEq, Repr

/-- Unit printed on the vertical axis. -/
inductive EnergyDisplayUnit where
  | millijoule
  | other
  deriving DecidableEq, Repr

/-- Qualitative shape of the heavy curve drawn in the supplied graph. -/
inductive GraphCurveShape where
  | symmetricParabolaLikeArc
  | other
  deriving DecidableEq, Repr

/--
The labeled graph and the energy curve it displays.  The angular argument of
`kineticEnergyAtRadians` is an SI radian readout; the endpoint fields retain
the milliradian coordinates printed in the image.
-/
structure PendulumKineticEnergyFigure where
  horizontalAxisRole : HorizontalAxisRole
  verticalAxisRole : VerticalAxisRole
  horizontalDisplayUnit : AngleDisplayUnit
  verticalDisplayUnit : EnergyDisplayUnit
  curveShape : GraphCurveShape
  leftEndpointMilliRadians : ℝ
  centerMilliRadians : ℝ
  rightEndpointMilliRadians : ℝ
  scaleEnergy : EnergyQuantity
  kineticEnergyAtRadians : ℝ → EnergyQuantity

/-! ## Physical setup, given data, and governing law -/

/-- The simple pendulum and the graph supplied with the exercise. -/
structure SimplePendulumSetup where
  figure : PendulumKineticEnergyFigure
  bobMass : MassQuantity
  pendulumLength : LengthQuantity
  gravitationalAcceleration : AccelerationQuantity

/--
Numerical and qualitative evidence stated in the problem or read from the
primary image.  The image, rather than its auxiliary caption, places `K_s` on
the second horizontal grid line and the apex on the third, giving the
`3 / 2` relation below.  No pendulum-length value occurs here.
-/
structure MatchesProblemAndPrimaryFigure
    (setup : SimplePendulumSetup) : Prop where
  horizontalAxisIsAngle :
    setup.figure.horizontalAxisRole = .angleFromVertical
  verticalAxisIsKineticEnergy :
    setup.figure.verticalAxisRole = .kineticEnergy
  horizontalAxisUsesMilliRadians :
    setup.figure.horizontalDisplayUnit = .milliradian
  verticalAxisUsesMilliJoules :
    setup.figure.verticalDisplayUnit = .millijoule
  curveIsSymmetricParabolaLikeArc :
    setup.figure.curveShape = .symmetricParabolaLikeArc
  bobMassReadout : massInKilograms setup.bobMass = (200 : ℝ) / 1000
  scaleEnergyReadout : energyInMilliJoules setup.figure.scaleEnergy = 10
  leftEndpointReadout : setup.figure.leftEndpointMilliRadians = -100
  centerReadout : setup.figure.centerMilliRadians = 0
  rightEndpointReadout : setup.figure.rightEndpointMilliRadians = 100
  kineticEnergyVanishesAtLeftEndpoint :
    energyInJoules
        (setup.figure.kineticEnergyAtRadians
          (milliRadiansToRadians setup.figure.leftEndpointMilliRadians)) = 0
  kineticEnergyVanishesAtRightEndpoint :
    energyInJoules
        (setup.figure.kineticEnergyAtRadians
          (milliRadiansToRadians setup.figure.rightEndpointMilliRadians)) = 0
  apexHeightFromUniformGrid :
    energyInJoules
        (setup.figure.kineticEnergyAtRadians
          (milliRadiansToRadians setup.figure.centerMilliRadians)) =
      (3 / 2 : ℝ) * energyInJoules setup.figure.scaleEnergy

/-- The standard near-Earth gravitational acceleration used by the answer. -/
def UsesStandardEarthGravity (setup : SimplePendulumSetup) : Prop :=
  accelerationInMetersPerSecondSquared setup.gravitationalAcceleration =
    (98 : ℝ) / 10

/-- Positivity and nondegeneracy conditions for the physical experiment. -/
structure HasPhysicalPendulumParameters
    (setup : SimplePendulumSetup) : Prop where
  bobMassPositive : 0 < massInKilograms setup.bobMass
  pendulumLengthPositive : 0 < lengthInMeters setup.pendulumLength
  gravitationalAccelerationPositive :
    0 < accelerationInMetersPerSecondSquared setup.gravitationalAcceleration
  scaleEnergyPositive : 0 < energyInJoules setup.figure.scaleEnergy
  kineticEnergyNonnegativeOnShownDomain :
    ∀ θ : ℝ,
      milliRadiansToRadians setup.figure.leftEndpointMilliRadians ≤ θ →
      θ ≤ milliRadiansToRadians setup.figure.rightEndpointMilliRadians →
      0 ≤ energyInJoules (setup.figure.kineticEnergyAtRadians θ)

/--
The exact ideal-simple-pendulum energy law on the interval shown in the
figure.  Conservation of mechanical energy and
`U(θ) - U(0) = m g L (1 - cos θ)` give the decrease of kinetic energy away
from the vertical.  The plotted arc is visually parabola-like over its small
angular range, but no small-angle approximation is promoted to an equality.
This is a governing law, not the requested numerical length.
-/
structure SatisfiesIdealPendulumEnergyLaw
    (setup : SimplePendulumSetup) : Prop where
  kineticEnergyDrop :
    ∀ θ : ℝ,
      milliRadiansToRadians setup.figure.leftEndpointMilliRadians ≤ θ →
      θ ≤ milliRadiansToRadians setup.figure.rightEndpointMilliRadians →
      energyInJoules (setup.figure.kineticEnergyAtRadians θ) =
        energyInJoules (setup.figure.kineticEnergyAtRadians 0) -
          massInKilograms setup.bobMass *
            accelerationInMetersPerSecondSquared
              setup.gravitationalAcceleration *
            lengthInMeters setup.pendulumLength * (1 - Real.cos θ)

/-! ## Displayed choices and formalization target -/

/-- Labels printed beside the four candidate lengths. -/
inductive AnswerChoice where
  | A
  | B
  | C
  | D
  deriving DecidableEq, Repr

/-- Length in metres printed beside each answer label. -/
def AnswerChoice.lengthInMeters : AnswerChoice → ℝ
  | .A => 147 / 100
  | .B => 150 / 100
  | .C => 153 / 100
  | .D => 156 / 100

/-- The answer label recorded in the supplied dataset metadata. -/
def recordedAnswerChoice : AnswerChoice := .C

/-- Agreement with a displayed two-decimal length to the nearest centimetre. -/
def MatchesDisplayedLength
    (setup : SimplePendulumSetup) (choice : AnswerChoice) : Prop :=
  |lengthInMeters setup.pendulumLength - choice.lengthInMeters| ≤
    (1 / 200 : ℝ)

/-- The selected length is strictly closer than every other displayed choice. -/
def IsUniqueClosestDisplayedChoice
    (setup : SimplePendulumSetup) (choice : AnswerChoice) : Prop :=
  ∀ other : AnswerChoice, other ≠ choice →
    |lengthInMeters setup.pendulumLength - choice.lengthInMeters| <
      |lengthInMeters setup.pendulumLength - other.lengthInMeters|

/--
The graph gives `K(0) = 15 mJ` and `K(0.100 rad) = 0`.  Substitution into
the exact ideal-pendulum energy law with `m = 0.200 kg` and `g = 9.8 m/s²`
gives `L = 3 / (392 * (1 - cos (1 / 10))) m`, which displays as `1.53 m`
to the nearest centimetre and uniquely selects answer C.

This formalizes blueprint label `thm:physics:phyx_mini_0274:target`.
-/
theorem problem_phyx_mini_0274
    (setup : SimplePendulumSetup)
    (hData : MatchesProblemAndPrimaryFigure setup)
    (hGravity : UsesStandardEarthGravity setup)
    (hPhysical : HasPhysicalPendulumParameters setup)
    (hLaw : SatisfiesIdealPendulumEnergyLaw setup) :
    lengthInMeters setup.pendulumLength =
        (3 : ℝ) / (392 * (1 - Real.cos (1 / 10))) ∧
      MatchesDisplayedLength setup recordedAnswerChoice ∧
      IsUniqueClosestDisplayedChoice setup recordedAnswerChoice := by
  have hScale :
      energyInJoules setup.figure.scaleEnergy = (1 : ℝ) / 100 := by
    have h := hData.scaleEnergyReadout
    simp only [energyInMilliJoules] at h
    linarith
  have hApex :
      energyInJoules (setup.figure.kineticEnergyAtRadians 0) =
        (3 : ℝ) / 200 := by
    calc
      energyInJoules (setup.figure.kineticEnergyAtRadians 0) =
          (3 / 2 : ℝ) * energyInJoules setup.figure.scaleEnergy := by
            simpa [hData.centerReadout, milliRadiansToRadians] using
              hData.apexHeightFromUniformGrid
      _ = (3 : ℝ) / 200 := by rw [hScale]; norm_num
  have hRight :
      energyInJoules
          (setup.figure.kineticEnergyAtRadians (1 / 10 : ℝ)) = 0 := by
    convert hData.kineticEnergyVanishesAtRightEndpoint using 1
    norm_num [hData.rightEndpointReadout, milliRadiansToRadians]
  have hDrop := hLaw.kineticEnergyDrop (1 / 10 : ℝ)
    (by
      rw [hData.leftEndpointReadout]
      norm_num [milliRadiansToRadians])
    (by
      rw [hData.rightEndpointReadout]
      norm_num [milliRadiansToRadians])
  unfold UsesStandardEarthGravity at hGravity
  rw [hRight, hApex, hData.bobMassReadout, hGravity] at hDrop
  norm_num at hDrop
  have hProduct :
      lengthInMeters setup.pendulumLength *
          (1 - Real.cos (1 / 10 : ℝ)) = (3 : ℝ) / 392 := by
    nlinarith only [hDrop]
  have hCosError :
      |Real.cos (1 / 10 : ℝ) - (199 : ℝ) / 200| ≤
        (1 : ℝ) / 192000 := by
    convert Real.cos_bound (x := (1 / 10 : ℝ)) (by norm_num) using 1 <;>
      norm_num
  have hCosBounds := abs_le.mp hCosError
  have hDropLower :
      (959 : ℝ) / 192000 ≤ 1 - Real.cos (1 / 10 : ℝ) := by
    nlinarith only [hCosBounds.2]
  have hDropUpper :
      1 - Real.cos (1 / 10 : ℝ) ≤ (961 : ℝ) / 192000 := by
    nlinarith only [hCosBounds.1]
  have hDropPositive : 0 < 1 - Real.cos (1 / 10 : ℝ) := by
    nlinarith only [hDropLower]
  have hDenominatorPositive :
      0 < 392 * (1 - Real.cos (1 / 10 : ℝ)) :=
    mul_pos (by norm_num) hDropPositive
  have hLength :
      lengthInMeters setup.pendulumLength =
        (3 : ℝ) / (392 * (1 - Real.cos (1 / 10))) := by
    apply (eq_div_iff (ne_of_gt hDenominatorPositive)).2
    nlinarith only [hProduct]
  have hLengthLower :
      (61 : ℝ) / 40 < lengthInMeters setup.pendulumLength := by
    rw [hLength]
    apply (lt_div_iff₀ hDenominatorPositive).2
    nlinarith only [hDropUpper]
  have hLengthUpper :
      lengthInMeters setup.pendulumLength < (307 : ℝ) / 200 := by
    rw [hLength]
    apply (div_lt_iff₀ hDenominatorPositive).2
    nlinarith only [hDropLower]
  refine ⟨hLength, ?_, ?_⟩
  · unfold MatchesDisplayedLength
    dsimp [recordedAnswerChoice, AnswerChoice.lengthInMeters]
    rw [abs_le]
    constructor <;> nlinarith
  · unfold IsUniqueClosestDisplayedChoice
    intro other hOther
    cases other with
    | A =>
        dsimp [recordedAnswerChoice, AnswerChoice.lengthInMeters]
        rw [abs_of_pos (by nlinarith : 0 <
          lengthInMeters setup.pendulumLength - (147 : ℝ) / 100)]
        rw [abs_lt]
        constructor <;> nlinarith
    | B =>
        dsimp [recordedAnswerChoice, AnswerChoice.lengthInMeters]
        rw [abs_of_pos (by nlinarith : 0 <
          lengthInMeters setup.pendulumLength - (150 : ℝ) / 100)]
        rw [abs_lt]
        constructor <;> nlinarith
    | C =>
        exact (hOther rfl).elim
    | D =>
        dsimp [recordedAnswerChoice, AnswerChoice.lengthInMeters]
        rw [abs_of_neg (by nlinarith :
          lengthInMeters setup.pendulumLength - (156 : ℝ) / 100 < 0)]
        rw [abs_lt]
        constructor <;> nlinarith

end PhyXMiniProblems.ProblemPhyXMini0274
