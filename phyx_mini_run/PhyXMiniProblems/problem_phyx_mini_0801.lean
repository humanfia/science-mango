import Mathlib.Data.Real.Basic
import Physlib.Units.WithDim.Basic

noncomputable section

namespace PhyXMiniProblems.ProblemPhyXMini0801

open Dimension

/-!
# Constant wind force on an iceboat

An iceboat and rider of combined mass `200 kg` start from rest on a
frictionless horizontal surface.  A constant wind force acts horizontally;
after `4.0 s` the boat's rightward velocity is `6.0 m/s`.  The supplied image
shows the sail-driven vehicle, the mark `B1` on its triangular sail, and a
rightward motion arrow, but contains no calibrated numerical scale.

Mass, duration, signed horizontal velocity, signed horizontal acceleration,
and signed horizontal force are represented by Physlib dimensionful
quantities.  Scalar real numbers below occur only as coherent unit readouts
and literal data printed in the exercise or answer choices.  Rightward is the
positive horizontal direction.

The assigned file did not exist when this formalization began, so there were
no pre-existing `USER` comments with additional file-specific instructions.
-/

/-! ## Dimensionful quantities and coherent unit readouts -/

/-- The combined physical mass of the iceboat and rider. -/
abbrev MassQuantity : Type := Dimensionful (WithDim M𝓭 ℝ)

/-- A physical elapsed duration. -/
abbrev DurationQuantity : Type := Dimensionful (WithDim T𝓭 ℝ)

/-- A signed one-dimensional horizontal velocity. -/
abbrev VelocityQuantity : Type :=
  Dimensionful (WithDim (L𝓭 * T𝓭⁻¹) ℝ)

/-- A signed one-dimensional horizontal acceleration. -/
abbrev AccelerationQuantity : Type :=
  Dimensionful (WithDim (L𝓭 * T𝓭⁻¹ * T𝓭⁻¹) ℝ)

/-- A signed one-dimensional horizontal force. -/
abbrev ForceQuantity : Type :=
  Dimensionful (WithDim (M𝓭 * L𝓭 * T𝓭⁻¹ * T𝓭⁻¹) ℝ)

/-- Read a mass in a selected mass unit. -/
def massReadout (unit : MassUnit) (mass : MassQuantity) : ℝ :=
  (mass {UnitChoices.SI with mass := unit}).val

/-- Read a duration in a selected time unit. -/
def durationReadout (unit : TimeUnit) (duration : DurationQuantity) : ℝ :=
  (duration {UnitChoices.SI with time := unit}).val

/-- Read signed velocity in coherent selected length and time units. -/
def velocityReadout
    (lengthUnit : LengthUnit) (timeUnit : TimeUnit)
    (velocity : VelocityQuantity) : ℝ :=
  (velocity {UnitChoices.SI with
    length := lengthUnit, time := timeUnit}).val

/-- Read signed acceleration in coherent selected length and time units. -/
def accelerationReadout
    (lengthUnit : LengthUnit) (timeUnit : TimeUnit)
    (acceleration : AccelerationQuantity) : ℝ :=
  (acceleration {UnitChoices.SI with
    length := lengthUnit, time := timeUnit}).val

/-- Read signed force in coherent selected mass, length, and time units. -/
def forceReadout
    (massUnit : MassUnit) (lengthUnit : LengthUnit) (timeUnit : TimeUnit)
    (force : ForceQuantity) : ℝ :=
  (force {UnitChoices.SI with
    mass := massUnit, length := lengthUnit, time := timeUnit}).val

/-- SI kilogram readout of a physical mass. -/
def massInKilograms (mass : MassQuantity) : ℝ :=
  massReadout MassUnit.kilograms mass

/-- SI second readout of a physical duration. -/
def durationInSeconds (duration : DurationQuantity) : ℝ :=
  durationReadout TimeUnit.seconds duration

/-- SI metre-per-second readout of a signed horizontal velocity. -/
def velocityInMetersPerSecond (velocity : VelocityQuantity) : ℝ :=
  velocityReadout LengthUnit.meters TimeUnit.seconds velocity

/-- SI metre-per-second-squared readout of a signed horizontal acceleration. -/
def accelerationInMetersPerSecondSquared
    (acceleration : AccelerationQuantity) : ℝ :=
  accelerationReadout LengthUnit.meters TimeUnit.seconds acceleration

/-- SI newton readout of a signed horizontal force. -/
def forceInNewtons (force : ForceQuantity) : ℝ :=
  forceReadout MassUnit.kilograms LengthUnit.meters TimeUnit.seconds force

/-! ## Scenario roles and primary-image data -/

/-- The two possible senses of the horizontal axis. -/
inductive HorizontalDirection where
  | left
  | right
  deriving DecidableEq, Repr

/-- Idealization of the horizontal support surface. -/
inductive SurfaceCondition where
  | frictionlessHorizontal
  | resistiveHorizontal
  deriving DecidableEq, Repr

/-- Whether the wind's horizontal force is constant during the observation. -/
inductive WindForceProfile where
  | constant
  | timeDependent
  deriving DecidableEq, Repr

/-- Physical objects and cues visible in image `801.png`. -/
inductive FigureObject where
  | iceboat
  | seatedRider
  | triangularSail
  | mast
  | smoothHorizontalSurface
  | leftLeaflessTree
  | rightLeaflessTree
  | rightwardMotionArrow
  deriving DecidableEq, Fintype, Repr

/-- Literal text labels visible in the supplied raster. -/
inductive FigureLabel where
  | sailMarkB1
  deriving DecidableEq, Fintype, Repr

/-!
A literal transcription of the primary image.  In particular,
`hasCalibratedMetricScale` distinguishes qualitative raster evidence from the
numerical mass, time, and velocity data stated in the prose.
-/
structure IceboatFigure where
  showsObject : FigureObject → Bool
  showsLabel : FigureLabel → Bool
  labelRefersTo : FigureLabel → FigureObject
  motionArrowDirection : HorizontalDirection
  surfaceIsDrawnHorizontal : Bool
  hasCalibratedMetricScale : Bool

/-!
Independent quantities in the physical setup.  Neither `windHorizontalForce`
nor `constantHorizontalAcceleration` is defined from an answer choice or from
the requested numerical result; the governing relations are stated below.
-/
structure IceboatWindSetup where
  combinedMass : MassQuantity
  elapsedTimeAfterRelease : DurationQuantity
  initialHorizontalVelocity : VelocityQuantity
  finalHorizontalVelocity : VelocityQuantity
  constantHorizontalAcceleration : AccelerationQuantity
  windHorizontalForce : ForceQuantity
  netHorizontalForce : ForceQuantity
  positiveHorizontalDirection : HorizontalDirection
  surfaceCondition : SurfaceCondition
  windForceProfile : WindForceProfile
  figure : IceboatFigure

/-! ## Source readouts and physical assumptions -/

/-!
Numerical and qualitative information stated in the exercise prose.  The
signed values use rightward as positive.  This structure contains no force
value and does not identify a correct answer choice.
-/
structure MatchesProblemStatement (setup : IceboatWindSetup) : Prop where
  combinedMassKilograms : massInKilograms setup.combinedMass = 200
  observationDurationSeconds :
    durationInSeconds setup.elapsedTimeAfterRelease = 4
  initiallyAtRest :
    velocityInMetersPerSecond setup.initialHorizontalVelocity = 0
  finalRightwardVelocityMetersPerSecond :
    velocityInMetersPerSecond setup.finalHorizontalVelocity = 6
  rightwardIsPositive : setup.positiveHorizontalDirection = .right
  supportIsFrictionless :
    setup.surfaceCondition = .frictionlessHorizontal
  horizontalWindForceIsConstant : setup.windForceProfile = .constant

/-!
Literal and qualitative facts read from the supplied image.  The raster's
arrow fixes the displayed direction, while the numerical velocity still comes
from the prose rather than a pixel measurement.
-/
structure MatchesSuppliedFigure (setup : IceboatWindSetup) : Prop where
  everyListedObjectIsShown :
    ∀ object, setup.figure.showsObject object = true
  everyListedLabelIsShown :
    ∀ label, setup.figure.showsLabel label = true
  b1MarkIsOnTriangularSail :
    setup.figure.labelRefersTo .sailMarkB1 = .triangularSail
  displayedArrowPointsRight :
    setup.figure.motionArrowDirection = .right
  supportLooksHorizontal : setup.figure.surfaceIsDrawnHorizontal = true
  noCalibratedRasterScale : setup.figure.hasCalibratedMetricScale = false

/-- Positivity and nondegeneracy of the two scalar physical parameters. -/
structure HasPhysicalParameters (setup : IceboatWindSetup) : Prop where
  combinedMassPositive : 0 < massInKilograms setup.combinedMass
  elapsedTimePositive : 0 < durationInSeconds setup.elapsedTimeAfterRelease

/-!
The constant-acceleration velocity law, stated in every coherent choice of
length and time units.  This is the generic relation `v_f = v_i + a Δt`, not
the evaluated acceleration requested by the calculation.
-/
def SatisfiesConstantAccelerationVelocityLaw
    (initialVelocity finalVelocity : VelocityQuantity)
    (acceleration : AccelerationQuantity)
    (duration : DurationQuantity) : Prop :=
  ∀ (lengthUnit : LengthUnit) (timeUnit : TimeUnit),
    velocityReadout lengthUnit timeUnit finalVelocity =
      velocityReadout lengthUnit timeUnit initialVelocity +
        accelerationReadout lengthUnit timeUnit acceleration *
          durationReadout timeUnit duration

/-!
Newton's second law for signed one-dimensional components, stated in every
coherent choice of mass, length, and time units.  This local predicate mirrors
the dimensionally correct `F = m a` relation without fixing any numerical
force.
-/
def SatisfiesNewtonsSecondLaw
    (mass : MassQuantity) (netForce : ForceQuantity)
    (acceleration : AccelerationQuantity) : Prop :=
  ∀ (massUnit : MassUnit) (lengthUnit : LengthUnit)
      (timeUnit : TimeUnit),
    forceReadout massUnit lengthUnit timeUnit netForce =
      massReadout massUnit mass *
        accelerationReadout lengthUnit timeUnit acceleration

/-!
The governing horizontal dynamics.  Frictionlessness and the absence of any
other stated horizontal force make the wind force equal to the net horizontal
force.  Constant-force motion then obeys the constant-acceleration kinematic
law and Newton's second law.  No field states the requested `300 N` result.
-/
structure SatisfiesConstantWindDynamics
    (setup : IceboatWindSetup) : Prop where
  windIsNetHorizontalForce :
    setup.netHorizontalForce = setup.windHorizontalForce
  constantAccelerationVelocityLaw :
    SatisfiesConstantAccelerationVelocityLaw
      setup.initialHorizontalVelocity
      setup.finalHorizontalVelocity
      setup.constantHorizontalAcceleration
      setup.elapsedTimeAfterRelease
  newtonsSecondLaw :
    SatisfiesNewtonsSecondLaw
      setup.combinedMass
      setup.netHorizontalForce
      setup.constantHorizontalAcceleration

/-!
The prose readouts and the constant-acceleration velocity law imply the
rightward acceleration `a = (6 - 0) / 4 = 3/2 m/s²`.  This is an intermediate
derived result, not a source or governing-law assumption.
-/
lemma constantHorizontalAcceleration_si
    (setup : IceboatWindSetup)
    (h_data : MatchesProblemStatement setup)
    (h_physical : HasPhysicalParameters setup)
    (h_laws : SatisfiesConstantWindDynamics setup) :
    accelerationInMetersPerSecondSquared
      setup.constantHorizontalAcceleration = 3 / 2 := by
  have h_velocity :=
    h_laws.constantAccelerationVelocityLaw
      LengthUnit.meters TimeUnit.seconds
  change
    velocityInMetersPerSecond setup.finalHorizontalVelocity =
      velocityInMetersPerSecond setup.initialHorizontalVelocity +
        accelerationInMetersPerSecondSquared
          setup.constantHorizontalAcceleration *
          durationInSeconds setup.elapsedTimeAfterRelease
    at h_velocity
  rw [h_data.finalRightwardVelocityMetersPerSecond,
    h_data.initiallyAtRest, h_data.observationDurationSeconds] at h_velocity
  norm_num at h_velocity ⊢
  linarith

/-! ## Displayed choices and final formalization target -/

/-- Labels of the four force choices printed with the problem. -/
inductive AnswerChoice where
  | A
  | B
  | C
  | D
  deriving DecidableEq, Fintype, Repr

/-- Force in newtons printed beside each displayed answer label. -/
def AnswerChoice.forceInNewtons : AnswerChoice → ℝ
  | .A => 150
  | .B => 300
  | .C => 450
  | .D => 600

/-- The answer label recorded in the supplied dataset metadata. -/
def recordedAnswerChoice : AnswerChoice := .B

/-- Exact agreement of a physical signed force with a displayed choice. -/
def MatchesDisplayedForce
    (force : ForceQuantity) (choice : AnswerChoice) : Prop :=
  forceInNewtons force = choice.forceInNewtons

/-- A displayed choice is the unique exact match for a physical force. -/
def IsUniqueMatchingDisplayedChoice
    (force : ForceQuantity) (choice : AnswerChoice) : Prop :=
  MatchesDisplayedForce force choice ∧
    ∀ other : AnswerChoice,
      MatchesDisplayedForce force other → other = choice

/-!
The acceleration is `1.5 m/s²`; Newton's second law therefore gives the
constant rightward wind force

`F_W = m a = (200 kg)(1.5 m/s²) = 300 N`.

Thus the physical force is exactly the value printed as recorded answer B,
and no other displayed choice has that value.

This formalizes blueprint label `thm:physics:phyx_mini_0801:target`.
-/
theorem wind_force_exerted_on_iceboat
    (setup : IceboatWindSetup)
    (h_data : MatchesProblemStatement setup)
    (h_figure : MatchesSuppliedFigure setup)
    (h_physical : HasPhysicalParameters setup)
    (h_laws : SatisfiesConstantWindDynamics setup) :
    forceInNewtons setup.windHorizontalForce = 300 ∧
      IsUniqueMatchingDisplayedChoice
        setup.windHorizontalForce recordedAnswerChoice := by
  have h_acceleration :=
    constantHorizontalAcceleration_si setup h_data h_physical h_laws
  have h_newton :=
    h_laws.newtonsSecondLaw
      MassUnit.kilograms LengthUnit.meters TimeUnit.seconds
  change
    forceInNewtons setup.netHorizontalForce =
      massInKilograms setup.combinedMass *
        accelerationInMetersPerSecondSquared
          setup.constantHorizontalAcceleration
    at h_newton
  have h_force : forceInNewtons setup.windHorizontalForce = 300 := by
    rw [← h_laws.windIsNetHorizontalForce, h_newton,
      h_data.combinedMassKilograms, h_acceleration]
    norm_num
  refine ⟨h_force, ?_⟩
  constructor
  · simpa [MatchesDisplayedForce, recordedAnswerChoice,
      AnswerChoice.forceInNewtons] using h_force
  · intro other h_other
    cases other <;>
      simp [MatchesDisplayedForce, recordedAnswerChoice,
        AnswerChoice.forceInNewtons, h_force] at h_other ⊢

end PhyXMiniProblems.ProblemPhyXMini0801
