import Mathlib
import Physlib.Units.WithDim.Basic

noncomputable section

namespace PhyXMiniProblems.ProblemPhyXMini0762

open Dimension

/-!
# Normal force on a box in two connected elevator cabs

Cab `A` is above cab `B`.  A short cable connects the two cabs, an upper
cable is attached to cab `A`, and a box of catnip rests on the floor of cab
`A`.  Signed vertical accelerations use the upward-positive convention.

Masses, acceleration magnitudes, signed accelerations, and force magnitudes
remain unit-independent dimensionful quantities.  Real numbers occur only in
coherent-SI readouts and in the displayed multiple-choice data.
-/

/-! ## Dimensionful quantities and coherent-SI readouts -/

/-- The physical dimension of acceleration, `L T⁻²`. -/
def accelerationDimension : Dimension := L𝓭 * T𝓭⁻¹ * T𝓭⁻¹

/-- The physical dimension of force, `M L T⁻²`. -/
def forceDimension : Dimension := M𝓭 * accelerationDimension

/-- A nonnegative, unit-independent physical mass. -/
abbrev MassQuantity : Type := Dimensionful (WithDim M𝓭 NNReal)

/-- A nonnegative, unit-independent acceleration magnitude. -/
abbrev AccelerationMagnitude : Type :=
  Dimensionful (WithDim accelerationDimension NNReal)

/-- A unit-independent signed acceleration along the vertical axis. -/
abbrev SignedAcceleration : Type :=
  Dimensionful (WithDim accelerationDimension ℝ)

/-- A nonnegative, unit-independent force magnitude. -/
abbrev ForceMagnitude : Type :=
  Dimensionful (WithDim forceDimension NNReal)

/-- Coherent-SI kilogram readout of a physical mass. -/
def massInKilograms (mass : MassQuantity) : ℝ :=
  ((mass UnitChoices.SI).val : ℝ)

/-- Coherent-SI metre-per-second-squared readout of an acceleration magnitude. -/
def accelerationMagnitudeInMetersPerSecondSquared
    (acceleration : AccelerationMagnitude) : ℝ :=
  ((acceleration UnitChoices.SI).val : ℝ)

/-- Coherent-SI signed metre-per-second-squared acceleration component. -/
def signedAccelerationInMetersPerSecondSquared
    (acceleration : SignedAcceleration) : ℝ :=
  (acceleration UnitChoices.SI).val

/-- Coherent-SI newton readout of a force magnitude. -/
def forceInNewtons (force : ForceMagnitude) : ℝ :=
  ((force UnitChoices.SI).val : ℝ)

/-- The gravitational weight magnitude `m g`, read in newtons. -/
def weightInNewtons
    (mass : MassQuantity) (gravity : AccelerationMagnitude) : ℝ :=
  massInKilograms mass *
    accelerationMagnitudeInMetersPerSecondSquared gravity

/-! ## Apparatus and primary-figure vocabulary -/

/-- The two cab labels printed beside the primary image. -/
inductive CabLabel where
  | A
  | B
  deriving DecidableEq, Fintype, Repr

/-- Sign convention for the scalar vertical acceleration components. -/
inductive VerticalPositiveDirection where
  | upward
  | downward
  deriving DecidableEq, Repr

/--
Qualitative information visible in the source image and stated in the
scenario.  This record contains no mass, force, or acceleration readout.
-/
structure ElevatorFigure where
  upperCableAttachment : CabLabel
  interCabCableUpperEnd : CabLabel
  interCabCableLowerEnd : CabLabel
  catnipBoxLocation : CabLabel
  cabLabelVisible : CabLabel → Bool
  boxShownOnCabFloor : Bool
  cabsShownInVerticalStack : Bool
  interCabCableShownShort : Bool
  upperCableAllowsRaisingOrLowering : Bool

/-!
The independent physical quantities of the elevator system.  In particular,
the floor normal force is an observable field; it is not defined from an
answer choice or from the requested numerical result.
-/
structure ConnectedElevatorSetup where
  cabMass : CabLabel → MassQuantity
  catnipBoxMass : MassQuantity
  gravitationalAccelerationMagnitude : AccelerationMagnitude
  cabVerticalAcceleration : CabLabel → SignedAcceleration
  catnipBoxVerticalAcceleration : SignedAcceleration
  upperCableTension : ForceMagnitude
  interCabCableTension : ForceMagnitude
  floorNormalForceOnBox : ForceMagnitude
  positiveVerticalDirection : VerticalPositiveDirection
  figure : ElevatorFigure

/-! ## Figure evidence, numerical readouts, and governing laws -/

/--
Transcription of the primary image: cab `A` is the upper cab, cab `B` is the
lower cab, the box is on `A`'s floor, and the cables are vertical.
-/
structure MatchesConnectedElevatorFigure
    (setup : ConnectedElevatorSetup) : Prop where
  upperCableAttachedToA : setup.figure.upperCableAttachment = .A
  interCabCableStartsAtA : setup.figure.interCabCableUpperEnd = .A
  interCabCableEndsAtB : setup.figure.interCabCableLowerEnd = .B
  boxLocatedInA : setup.figure.catnipBoxLocation = .A
  labelAVisible : setup.figure.cabLabelVisible .A = true
  labelBVisible : setup.figure.cabLabelVisible .B = true
  boxOnFloorShown : setup.figure.boxShownOnCabFloor = true
  verticalStackShown : setup.figure.cabsShownInVerticalStack = true
  shortConnectingCableShown : setup.figure.interCabCableShownShort = true
  upperCableCanMoveSystemEitherWay :
    setup.figure.upperCableAllowsRaisingOrLowering = true
  upwardPositive : setup.positiveVerticalDirection = .upward

/--
The masses and inter-cab cable tension stated in the problem.  No normal-force
value or answer label occurs in these independent data.
-/
structure HasConnectedElevatorProblemData
    (setup : ConnectedElevatorSetup) : Prop where
  cabAMassKilograms : massInKilograms (setup.cabMass .A) = 1700
  cabBMassKilograms : massInKilograms (setup.cabMass .B) = 1300
  boxMassKilograms : massInKilograms setup.catnipBoxMass = 12
  interCabTensionNewtons :
    forceInNewtons setup.interCabCableTension = 1.91 * (10 : ℝ) ^ 4

/--
The kinematic constraints and the two vertical Newton-second-law equations
used in the calculation.

The taut short cable makes the two cabs share a vertical acceleration, and a
box maintaining contact with `A`'s floor shares cab `A`'s acceleration.  On
cab `B`, the inter-cab tension acts upward and weight acts downward.  On the
box, the floor normal force acts upward and weight acts downward.  These are
general governing relations and contain no requested numerical normal force.
-/
structure SatisfiesConnectedElevatorDynamics
    (setup : ConnectedElevatorSetup) : Prop where
  cabsShareAcceleration :
    signedAccelerationInMetersPerSecondSquared
        (setup.cabVerticalAcceleration .A) =
      signedAccelerationInMetersPerSecondSquared
        (setup.cabVerticalAcceleration .B)
  boxSharesCabAAcceleration :
    signedAccelerationInMetersPerSecondSquared
        setup.catnipBoxVerticalAcceleration =
      signedAccelerationInMetersPerSecondSquared
        (setup.cabVerticalAcceleration .A)
  cabBVerticalNewtonSecondLaw :
    forceInNewtons setup.interCabCableTension -
        weightInNewtons (setup.cabMass .B)
          setup.gravitationalAccelerationMagnitude =
      massInKilograms (setup.cabMass .B) *
        signedAccelerationInMetersPerSecondSquared
          (setup.cabVerticalAcceleration .B)
  boxVerticalNewtonSecondLaw :
    forceInNewtons setup.floorNormalForceOnBox -
        weightInNewtons setup.catnipBoxMass
          setup.gravitationalAccelerationMagnitude =
      massInKilograms setup.catnipBoxMass *
        signedAccelerationInMetersPerSecondSquared
          setup.catnipBoxVerticalAcceleration

/-! ## Displayed choices and current target -/

/-- Labels of the four normal-force answer choices. -/
inductive NormalForceAnswerChoice where
  | A
  | B
  | C
  | D
  deriving DecidableEq, Fintype, Repr

/-- Whole-newton value printed beside each answer label. -/
def displayedNormalForceInNewtons : NormalForceAnswerChoice → ℝ
  | .A => 168
  | .B => 172
  | .C => 176
  | .D => 180

/-- A physical force magnitude rounds to a displayed whole number of newtons. -/
def RoundsToNearestNewton
    (force : ForceMagnitude) (displayedValue : ℝ) : Prop :=
  |forceInNewtons force - displayedValue| < 1 / 2

/-!
Eliminating the common acceleration and gravity from the cab-`B` and box
equations gives

`N = m_box T / m_B = 12 · 19100 / 1300 = 2292/13 N`.

Thus the physical normal force is approximately `176.31 N`: it rounds to the
displayed `176 N`, answer choice `C`, and is closer to `C` than to every other
listed whole-newton choice.

Blueprint: `thm:physics:phyx_mini_0762:target`.
-/
theorem problem_phyx_mini_0762
    (setup : ConnectedElevatorSetup)
    (h_figure : MatchesConnectedElevatorFigure setup)
    (h_data : HasConnectedElevatorProblemData setup)
    (h_dynamics : SatisfiesConnectedElevatorDynamics setup) :
    forceInNewtons setup.floorNormalForceOnBox =
        massInKilograms setup.catnipBoxMass *
          forceInNewtons setup.interCabCableTension /
          massInKilograms (setup.cabMass .B) ∧
      forceInNewtons setup.floorNormalForceOnBox = 2292 / 13 ∧
      RoundsToNearestNewton setup.floorNormalForceOnBox
        (displayedNormalForceInNewtons .C) ∧
      ∀ choice : NormalForceAnswerChoice,
        |forceInNewtons setup.floorNormalForceOnBox -
            displayedNormalForceInNewtons .C| ≤
          |forceInNewtons setup.floorNormalForceOnBox -
            displayedNormalForceInNewtons choice| := by
  have h_box_cabB :
      signedAccelerationInMetersPerSecondSquared
          setup.catnipBoxVerticalAcceleration =
        signedAccelerationInMetersPerSecondSquared
          (setup.cabVerticalAcceleration .B) := by
    calc
      signedAccelerationInMetersPerSecondSquared
          setup.catnipBoxVerticalAcceleration =
          signedAccelerationInMetersPerSecondSquared
            (setup.cabVerticalAcceleration .A) :=
        h_dynamics.boxSharesCabAAcceleration
      _ = signedAccelerationInMetersPerSecondSquared
            (setup.cabVerticalAcceleration .B) :=
        h_dynamics.cabsShareAcceleration
  have h_normal_value :
      forceInNewtons setup.floorNormalForceOnBox = 2292 / 13 := by
    have h_cabB := h_dynamics.cabBVerticalNewtonSecondLaw
    have h_box := h_dynamics.boxVerticalNewtonSecondLaw
    simp only [weightInNewtons] at h_cabB h_box
    rw [h_data.interCabTensionNewtons, h_data.cabBMassKilograms] at h_cabB
    rw [h_data.boxMassKilograms, h_box_cabB] at h_box
    norm_num at h_cabB h_box ⊢
    linarith
  have h_normal_formula :
      forceInNewtons setup.floorNormalForceOnBox =
        massInKilograms setup.catnipBoxMass *
          forceInNewtons setup.interCabCableTension /
          massInKilograms (setup.cabMass .B) := by
    rw [h_normal_value, h_data.boxMassKilograms,
      h_data.interCabTensionNewtons, h_data.cabBMassKilograms]
    norm_num
  refine ⟨h_normal_formula, h_normal_value, ?_, ?_⟩
  · simp only [RoundsToNearestNewton, h_normal_value,
      displayedNormalForceInNewtons]
    norm_num [abs_of_nonneg, abs_of_neg]
  · intro choice
    rw [h_normal_value]
    cases choice <;>
      norm_num [displayedNormalForceInNewtons, abs_of_nonneg, abs_of_neg]

end PhyXMiniProblems.ProblemPhyXMini0762
