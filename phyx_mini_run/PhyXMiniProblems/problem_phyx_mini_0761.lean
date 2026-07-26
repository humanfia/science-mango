import Mathlib
import Physlib.Units.WithDim.Basic

noncomputable section

namespace PhyXMiniProblems.ProblemPhyXMini0761

open Dimension

/-!
# Force between the fourth and fifth links of an accelerating chain

The primary image shows five vertically arranged links, numbered from `1` at
the bottom to `5` at the top.  An external force `F` and the common
acceleration `a` point upward.  Every link has mass `0.100 kg`, and the chain
has constant upward acceleration `2.50 m/s²`.

Mass, acceleration, and force magnitude are represented by Physlib
dimensionful quantities.  Real numbers below occur only as coherent unit
readouts or as the numerical data printed in the problem.  In particular,
the requested force on link `4` from link `5` is an independent physical
response quantity constrained by Newton's second law; it is not defined to
be the answer choice.
-/

/-! ## Dimensionful quantities and coherent readouts -/

/-- A nonnegative physical mass. -/
abbrev MassQuantity : Type := Dimensionful (WithDim M𝓭 NNReal)

/-- A nonnegative physical acceleration magnitude. -/
abbrev AccelerationQuantity : Type :=
  Dimensionful (WithDim (L𝓭 * T𝓭⁻¹ * T𝓭⁻¹) NNReal)

/-- A nonnegative physical force magnitude. -/
abbrev ForceQuantity : Type :=
  Dimensionful (WithDim (M𝓭 * L𝓭 * T𝓭⁻¹ * T𝓭⁻¹) NNReal)

/-- Read a physical mass in a selected mass unit. -/
def massReadout (unit : MassUnit) (mass : MassQuantity) : ℝ :=
  ((mass {UnitChoices.SI with mass := unit}).val : ℝ)

/-- Read an acceleration magnitude in coherent length and time units. -/
def accelerationReadout
    (lengthUnit : LengthUnit) (timeUnit : TimeUnit)
    (acceleration : AccelerationQuantity) : ℝ :=
  ((acceleration {UnitChoices.SI with
    length := lengthUnit, time := timeUnit}).val : ℝ)

/-- Read a force magnitude in coherent mass, length, and time units. -/
def forceReadout
    (massUnit : MassUnit) (lengthUnit : LengthUnit) (timeUnit : TimeUnit)
    (force : ForceQuantity) : ℝ :=
  ((force {UnitChoices.SI with
    mass := massUnit, length := lengthUnit, time := timeUnit}).val : ℝ)

/-- Kilogram readout of a mass. -/
def massInKilograms (mass : MassQuantity) : ℝ :=
  massReadout MassUnit.kilograms mass

/-- Metre-per-second-squared readout of an acceleration magnitude. -/
def accelerationInMetersPerSecondSquared
    (acceleration : AccelerationQuantity) : ℝ :=
  accelerationReadout LengthUnit.meters TimeUnit.seconds acceleration

/-- Newton readout of a force magnitude. -/
def forceInNewtons (force : ForceQuantity) : ℝ :=
  forceReadout MassUnit.kilograms LengthUnit.meters TimeUnit.seconds force

/-! ## Chain objects and primary-figure vocabulary -/

/-- The five literal link numbers, ordered from the bottom of the chain. -/
inductive ChainLink where
  | one
  | two
  | three
  | four
  | five
  deriving DecidableEq, Fintype, Repr

/-- The number printed beside a link in the supplied image. -/
def linkNumber : ChainLink → Nat
  | .one => 1
  | .two => 2
  | .three => 3
  | .four => 4
  | .five => 5

/-- Vertical directions used by the force and acceleration arrows. -/
inductive VerticalDirection where
  | upward
  | downward
  deriving DecidableEq, Repr

/-- Literal symbolic labels attached to arrows in the supplied image. -/
inductive FigureLabel where
  | appliedForceF
  | accelerationA
  deriving DecidableEq, Fintype, Repr

/-- The stated acceleration regime of the chain. -/
inductive ChainMotionRegime where
  | constantVerticalAcceleration
  | other
  deriving DecidableEq, Repr

/-!
Figure-derived structure from image `761.png`.  The arrow magnitudes are
symbolic denotations: the image itself supplies no numerical force readout.
-/
structure SuppliedChainFigure where
  showsLink : ChainLink → Bool
  printedNumberBeside : ChainLink → Nat
  verticalOrderBottomToTop : List ChainLink
  showsLabel : FigureLabel → Bool
  appliedForceArrowTail : ChainLink
  appliedForceArrowDirection : VerticalDirection
  appliedForceArrowMagnitude : ForceQuantity
  accelerationArrowDirection : VerticalDirection
  accelerationArrowMagnitude : AccelerationQuantity
  containsNumericalInteractionForceReadout : Bool

/-!
Independent physical quantities of the experiment.  `forceMagnitudeOnFrom i j`
means the magnitude of the force on link `i` exerted by link `j`; its direction
is recorded separately.  Thus the requested quantity is
`forceMagnitudeOnFrom .four .five`.
-/
structure AcceleratingChainSetup where
  linkMass : ChainLink → MassQuantity
  gravitationalAcceleration : AccelerationQuantity
  chainAcceleration : AccelerationQuantity
  appliedForceOnTopLink : ForceQuantity
  forceMagnitudeOnFrom : ChainLink → ChainLink → ForceQuantity
  forceDirectionOnFrom : ChainLink → ChainLink → VerticalDirection
  motionRegime : ChainMotionRegime
  figure : SuppliedChainFigure

/-! ## Problem data, figure readouts, and governing law -/

/-- Numerical and qualitative information supplied by the problem prose. -/
structure MatchesProblemData (setup : AcceleratingChainSetup) : Prop where
  everyLinkHasStatedMass :
    ∀ link, massInKilograms (setup.linkMass link) = 0.100
  statedAcceleration :
    accelerationInMetersPerSecondSquared setup.chainAcceleration = 2.50
  accelerationIsConstantAndVertical :
    setup.motionRegime = .constantVerticalAcceleration
  forceFromFiveOnFourPointsUpward :
    setup.forceDirectionOnFrom .four .five = .upward

/-!
Objects, numbering, order, arrows, and denotations transcribed from the
primary bitmap.  No value for the requested interaction force is included.
-/
structure MatchesSuppliedChainFigure (setup : AcceleratingChainSetup) : Prop where
  everyLinkIsShown : ∀ link, setup.figure.showsLink link = true
  printedLinkNumbers :
    ∀ link, setup.figure.printedNumberBeside link = linkNumber link
  bottomToTopOrder :
    setup.figure.verticalOrderBottomToTop =
      [.one, .two, .three, .four, .five]
  everyArrowLabelIsShown : ∀ label, setup.figure.showsLabel label = true
  appliedForceActsAtLinkFive : setup.figure.appliedForceArrowTail = .five
  appliedForcePointsUpward :
    setup.figure.appliedForceArrowDirection = .upward
  appliedForceArrowDenotesAppliedForce :
    setup.figure.appliedForceArrowMagnitude = setup.appliedForceOnTopLink
  accelerationPointsUpward :
    setup.figure.accelerationArrowDirection = .upward
  accelerationArrowDenotesChainAcceleration :
    setup.figure.accelerationArrowMagnitude = setup.chainAcceleration
  noNumericalInteractionForceReadout :
    setup.figure.containsNumericalInteractionForceReadout = false

/-- The near-Earth gravitational calibration used by the recorded answer. -/
structure UsesStandardEarthGravity (setup : AcceleratingChainSetup) : Prop where
  gravitationalAccelerationSI :
    accelerationInMetersPerSecondSquared setup.gravitationalAcceleration = 9.80

/-!
The total mass readout of links `1` through `4`, the subsystem accelerated by
the upward contact force exerted by link `5` on link `4`.
-/
def lowerFourLinksMassReadout
    (massUnit : MassUnit) (setup : AcceleratingChainSetup) : ℝ :=
  massReadout massUnit (setup.linkMass .one) +
    massReadout massUnit (setup.linkMass .two) +
    massReadout massUnit (setup.linkMass .three) +
    massReadout massUnit (setup.linkMass .four)

/-!
Newton's second law for the lower four-link subsystem, with upward positive:

`F_(5→4) - M_lower g = M_lower a`.

This is a governing mechanics law stated in every coherent choice of mass,
length, and time units.  It does not prescribe the solved value of
`F_(5→4)`.
-/
structure SatisfiesLowerFourLinkNewtonLaw
    (setup : AcceleratingChainSetup) : Prop where
  lowerSubsystemNewtonSecondLaw :
    ∀ (massUnit : MassUnit) (lengthUnit : LengthUnit)
        (timeUnit : TimeUnit),
      forceReadout massUnit lengthUnit timeUnit
            (setup.forceMagnitudeOnFrom .four .five) -
          lowerFourLinksMassReadout massUnit setup *
            accelerationReadout lengthUnit timeUnit
              setup.gravitationalAcceleration =
        lowerFourLinksMassReadout massUnit setup *
          accelerationReadout lengthUnit timeUnit setup.chainAcceleration

/-!
With four supported links of mass `0.100 kg`, upward acceleration `2.50 m/s²`,
and `g = 9.80 m/s²`, Newton's second law gives
`F_(5→4) = 4 · 0.100 · (9.80 + 2.50) = 4.92 N`.
-/
theorem force_on_link_four_from_link_five
    (setup : AcceleratingChainSetup)
    (problemData : MatchesProblemData setup)
    (figureData : MatchesSuppliedChainFigure setup)
    (standardGravity : UsesStandardEarthGravity setup)
    (newtonLaw : SatisfiesLowerFourLinkNewtonLaw setup) :
    forceInNewtons (setup.forceMagnitudeOnFrom .four .five) = 4.92 := by
  have massOne := problemData.everyLinkHasStatedMass ChainLink.one
  have massTwo := problemData.everyLinkHasStatedMass ChainLink.two
  have massThree := problemData.everyLinkHasStatedMass ChainLink.three
  have massFour := problemData.everyLinkHasStatedMass ChainLink.four
  have acceleration := problemData.statedAcceleration
  have gravity := standardGravity.gravitationalAccelerationSI
  have newton := newtonLaw.lowerSubsystemNewtonSecondLaw
    MassUnit.kilograms LengthUnit.meters TimeUnit.seconds
  change massReadout MassUnit.kilograms (setup.linkMass .one) = 0.100 at massOne
  change massReadout MassUnit.kilograms (setup.linkMass .two) = 0.100 at massTwo
  change massReadout MassUnit.kilograms (setup.linkMass .three) = 0.100 at massThree
  change massReadout MassUnit.kilograms (setup.linkMass .four) = 0.100 at massFour
  change accelerationReadout LengthUnit.meters TimeUnit.seconds
    setup.chainAcceleration = 2.50 at acceleration
  change accelerationReadout LengthUnit.meters TimeUnit.seconds
    setup.gravitationalAcceleration = 9.80 at gravity
  change forceReadout MassUnit.kilograms LengthUnit.meters TimeUnit.seconds
    (setup.forceMagnitudeOnFrom .four .five) = 4.92
  rw [lowerFourLinksMassReadout, massOne, massTwo, massThree, massFour,
    acceleration, gravity] at newton
  norm_num at newton ⊢
  linarith

end PhyXMiniProblems.ProblemPhyXMini0761
