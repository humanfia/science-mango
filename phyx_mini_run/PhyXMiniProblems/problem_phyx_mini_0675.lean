import Mathlib.Analysis.Real.Sqrt
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Physlib.Units.WithDim.Basic

/-!
# A frictionless bead sliding along an inclined rod

This file formalizes problem `phyx_mini_0675`.  A circular ring and two thin
rods lie in a vertical plane.  The vertical rod `AC` has figure length `D`,
while the inclined rod `CB` has figure length `L` and makes angle `θ` above
the horizontal.  The blue bead is released from rest at `B` and slides without
friction to `C`.

Lengths, times, speeds, and accelerations are dimensionful Physlib quantities.
Real numbers are used only for SI readouts and for the dimensionless angle in
radians.  The requested square-root expression is a theorem conclusion; it is
not a field or a governing-law assumption.

Assumption/target split:

* governing laws and initial condition: release from rest, the constant
  downhill tangential acceleration `g * sin θ`, and the one-dimensional
  constant-acceleration displacement law;
* previous-part results: none;
* problem and figure readouts: the vertical ring plane, labeled points and
  beads, rods `AC` and `CB` with labels `D` and `L`, the dashed segment `AB`,
  the angle `θ` above the horizontal, and the rods fastened inside the ring;
* current target conclusions: first the squared travel-time relation and then
  the nonnegative travel time `sqrt (2 * L / (g * sin θ))`.
-/

noncomputable section

namespace PhyXMiniProblems.ProblemPhyXMini0675

open Dimension

/-! ## Dimensionful quantities and SI readouts -/

/-- A nonnegative physical length, independent of the unit used to read it. -/
abbrev LengthQuantity : Type := Dimensionful (WithDim L𝓭 NNReal)

/-- A nonnegative physical duration, independent of the unit used to read it. -/
abbrev TimeQuantity : Type := Dimensionful (WithDim T𝓭 NNReal)

/-- A signed tangential speed, with dimension length per time. -/
abbrev SpeedQuantity : Type :=
  Dimensionful (WithDim (L𝓭 * T𝓭⁻¹) ℝ)

/-- A signed acceleration, with dimension length per time squared. -/
abbrev AccelerationQuantity : Type :=
  Dimensionful (WithDim (L𝓭 * T𝓭⁻¹ * T𝓭⁻¹) ℝ)

/-- Metre readout of a physical length. -/
def lengthInMeters (length : LengthQuantity) : ℝ :=
  ((length UnitChoices.SI).val : ℝ)

/-- Second readout of a physical duration. -/
def timeInSeconds (time : TimeQuantity) : ℝ :=
  ((time UnitChoices.SI).val : ℝ)

/-- Metre-per-second readout of a signed speed. -/
def speedInMetersPerSecond (speed : SpeedQuantity) : ℝ :=
  (speed UnitChoices.SI).val

/-- Metre-per-second-squared readout of a signed acceleration. -/
def accelerationInMetersPerSecondSquared
    (acceleration : AccelerationQuantity) : ℝ :=
  (acceleration UnitChoices.SI).val

/-! ## Apparatus and primary-figure vocabulary -/

/-- The three labeled points shown on the circular ring. -/
inductive FigurePoint where
  | A
  | B
  | C
  deriving DecidableEq, Repr

/-- The two rods distinguished by their figure labels. -/
inductive Rod where
  | verticalD
  | inclinedL
  deriving DecidableEq, Repr

/-- The two beads distinguished by their colors in the figure. -/
inductive Bead where
  | red
  | blue
  deriving DecidableEq, Repr

/-- Direction category of a rod in the vertical plane. -/
inductive RodDirection where
  | vertical
  | inclinedAboveHorizontal
  deriving DecidableEq, Repr

/-- Orientation of the plane containing a physical component. -/
inductive PlaneOrientation where
  | vertical
  | horizontal
  deriving DecidableEq, Repr

/-- A physical circular ring with an otherwise unspecified positive radius. -/
structure CircularRing where
  radius : LengthQuantity

/--
All physical quantities and figure-indexed data for the bead-and-rods setup.

`constantTangentialAcceleration` is the signed acceleration in the direction
from each bead's initial point toward its destination.  It is data to which
the frictionless force law is applied below; its value is not defined to be
the requested travel-time expression.
-/
structure InclinedRodBeadSetup where
  ring : CircularRing
  verticalRodLengthD : LengthQuantity
  inclinedRodLengthL : LengthQuantity
  gravitationalAcceleration : AccelerationQuantity
  inclinationAngleRad : ℝ
  blueBeadTravelTime : TimeQuantity
  rodEndpoints : Rod → FigurePoint × FigurePoint
  rodLength : Rod → LengthQuantity
  rodDirection : Rod → RodDirection
  rodPlane : Rod → PlaneOrientation
  ringPlane : PlaneOrientation
  pointOnRing : FigurePoint → Prop
  rodFastenedInsideRing : Rod → Prop
  beadInitialPoint : Bead → FigurePoint
  beadDestination : Bead → FigurePoint
  beadConstrainedToRod : Bead → Rod
  dashedSegmentShown : FigurePoint → FigurePoint → Prop
  initialTangentialSpeed : Bead → SpeedQuantity
  constantTangentialAcceleration : Bead → AccelerationQuantity

/-! ## Figure readouts, physical conditions, and governing laws -/

/--
Problem-statement and primary-bitmap information.

The vertical diameter-like rod joins `A` to `C` and carries label `D`; the
inclined rod joins `C` to `B` and carries label `L`.  All three endpoints lie
on the ring, both rods are fastened within it, and the dashed `AB` segment is
shown.  The red and blue beads begin at `A` and `B`, respectively, and both
are constrained to travel toward `C` on their pictured rods.
-/
def MatchesProblemAndPrimaryFigure (setup : InclinedRodBeadSetup) : Prop :=
  setup.ringPlane = .vertical ∧
    (∀ rod, setup.rodPlane rod = .vertical) ∧
    setup.rodEndpoints .verticalD = (.A, .C) ∧
    setup.rodEndpoints .inclinedL = (.C, .B) ∧
    setup.rodLength .verticalD = setup.verticalRodLengthD ∧
    setup.rodLength .inclinedL = setup.inclinedRodLengthL ∧
    setup.rodDirection .verticalD = .vertical ∧
    setup.rodDirection .inclinedL = .inclinedAboveHorizontal ∧
    (∀ point, setup.pointOnRing point) ∧
    (∀ rod, setup.rodFastenedInsideRing rod) ∧
    setup.dashedSegmentShown .A .B ∧
    setup.beadInitialPoint .red = .A ∧
    setup.beadInitialPoint .blue = .B ∧
    setup.beadDestination .red = .C ∧
    setup.beadDestination .blue = .C ∧
    setup.beadConstrainedToRod .red = .verticalD ∧
    setup.beadConstrainedToRod .blue = .inclinedL ∧
    lengthInMeters setup.verticalRodLengthD =
      2 * lengthInMeters setup.ring.radius

/--
Nondegeneracy and the acute physical branch pictured for `θ`.  Gravity and
all figure lengths are strictly positive.
-/
def HasPhysicalParameters (setup : InclinedRodBeadSetup) : Prop :=
  0 < lengthInMeters setup.ring.radius ∧
    0 < lengthInMeters setup.verticalRodLengthD ∧
    0 < lengthInMeters setup.inclinedRodLengthL ∧
    0 < accelerationInMetersPerSecondSquared
      setup.gravitationalAcceleration ∧
    setup.inclinationAngleRad ∈ Set.Ioo 0 (Real.pi / 2)

/--
Frictionless constrained dynamics for the blue bead.  It is released from
rest, and the component of gravity along rod `BC` is `g sin θ`, constant
toward `C` because the rod is straight.
-/
def ObeysFrictionlessInclinedRodDynamics
    (setup : InclinedRodBeadSetup) : Prop :=
  speedInMetersPerSecond (setup.initialTangentialSpeed .blue) = 0 ∧
    accelerationInMetersPerSecondSquared
        (setup.constantTangentialAcceleration .blue) =
      accelerationInMetersPerSecondSquared setup.gravitationalAcceleration *
        Real.sin setup.inclinationAngleRad

/--
The constant-acceleration displacement law `L = u t + (1/2) a t²` for the
blue bead's complete trip from `B` to `C`.
-/
def ObeysConstantAccelerationKinematics
    (setup : InclinedRodBeadSetup) : Prop :=
  lengthInMeters setup.inclinedRodLengthL =
    speedInMetersPerSecond (setup.initialTangentialSpeed .blue) *
        timeInSeconds setup.blueBeadTravelTime +
      (1 / 2 : ℝ) *
        accelerationInMetersPerSecondSquared
          (setup.constantTangentialAcceleration .blue) *
        (timeInSeconds setup.blueBeadTravelTime) ^ 2

/-! ## Derived travel-time relations -/

/--
The governing laws first determine the square of the blue bead's travel time.
This is a derived intermediate result, not an assumption field.
-/
lemma blueBeadTravelTime_squared
    (setup : InclinedRodBeadSetup)
    (h_parameters : HasPhysicalParameters setup)
    (h_dynamics : ObeysFrictionlessInclinedRodDynamics setup)
    (h_kinematics : ObeysConstantAccelerationKinematics setup) :
    (timeInSeconds setup.blueBeadTravelTime) ^ 2 =
      2 * lengthInMeters setup.inclinedRodLengthL /
        (accelerationInMetersPerSecondSquared
            setup.gravitationalAcceleration *
          Real.sin setup.inclinationAngleRad) := by
  unfold HasPhysicalParameters at h_parameters
  rcases h_parameters with ⟨_, _, _, hg, hθ⟩
  unfold ObeysFrictionlessInclinedRodDynamics at h_dynamics
  rcases h_dynamics with ⟨hu, ha⟩
  unfold ObeysConstantAccelerationKinematics at h_kinematics
  have hsin : 0 < Real.sin setup.inclinationAngleRad :=
    Real.sin_pos_of_pos_of_lt_pi hθ.1 (by linarith [hθ.2, Real.pi_pos])
  have hden : 0 <
      accelerationInMetersPerSecondSquared setup.gravitationalAcceleration *
        Real.sin setup.inclinationAngleRad := mul_pos hg hsin
  apply (eq_div_iff hden.ne').2
  rw [hu, ha] at h_kinematics
  nlinarith [h_kinematics]

/--
For the blue bead sliding without friction from `B` to `C`, the travel time is

`sqrt (2 L / (g sin θ))`.

This is answer choice C and formalizes
`thm:physics:phyx_mini_0675:target`.
-/
theorem problem_phyx_mini_0675
    (setup : InclinedRodBeadSetup)
    (h_figure : MatchesProblemAndPrimaryFigure setup)
    (h_parameters : HasPhysicalParameters setup)
    (h_dynamics : ObeysFrictionlessInclinedRodDynamics setup)
    (h_kinematics : ObeysConstantAccelerationKinematics setup) :
    timeInSeconds setup.blueBeadTravelTime =
      Real.sqrt
        (2 * lengthInMeters setup.inclinedRodLengthL /
          (accelerationInMetersPerSecondSquared
              setup.gravitationalAcceleration *
            Real.sin setup.inclinationAngleRad)) := by
  have h_time_nonnegative :
      0 ≤ timeInSeconds setup.blueBeadTravelTime := by
    unfold timeInSeconds
    positivity
  rw [← blueBeadTravelTime_squared setup h_parameters h_dynamics h_kinematics]
  exact (Real.sqrt_sq h_time_nonnegative).symm

end PhyXMiniProblems.ProblemPhyXMini0675
