import Mathlib.Analysis.Asymptotics.Defs
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Physlib.Units.WithDim.Basic

/- USER: The assigned source file did not exist when this autoformalization task began. -/

/-!
# Period of a T-shaped two-stick physical pendulum

Two equal uniform slender sticks, each `1 m` long, form the T shown in the
supplied figure.  The horizontal stick is blue, the vertical stick is red,
and the top endpoint of the vertical stick meets the midpoint of the
horizontal stick at the pin labeled `A`.  The assembly oscillates as a
physical pendulum about that pin.

The displayed `1.83 s` value is the zero-amplitude (linearized) period, not
the exact period at every finite amplitude.  The model therefore records the
exact sinusoidal restoring torque, its derivative and little-o remainder at
the stable equilibrium, and convergence of nonlinear periods to the
linearized period as the peak angle tends to zero from above.

All dimensional physical magnitudes are represented by Physlib
`Dimensionful` quantities.  Real numbers occur only as coherent SI readouts,
dimensionless angles and ratios, and displayed answer values.  The
linearized period is an independent field of the setup; neither its closed
form nor `1.83 s` occurs in the problem-data or governing-law hypotheses.
-/

noncomputable section

namespace PhyXMiniProblems.ProblemPhyXMini0263

open Dimension

/-! ## Dimensionful physical quantities and coherent SI readouts -/

/-- A nonnegative physical mass. -/
abbrev MassQuantity : Type := Dimensionful (WithDim M𝓭 NNReal)

/-- A nonnegative physical length. -/
abbrev LengthQuantity : Type := Dimensionful (WithDim L𝓭 NNReal)

/-- A nonnegative physical duration. -/
abbrev TimeQuantity : Type := Dimensionful (WithDim T𝓭 NNReal)

/-- A nonnegative angular-frequency magnitude, with dimension `T⁻¹`. -/
abbrev AngularFrequencyMagnitudeQuantity : Type :=
  Dimensionful (WithDim T𝓭⁻¹ NNReal)

/-- A nonnegative acceleration magnitude, with dimension `L T⁻²`. -/
abbrev AccelerationMagnitudeQuantity : Type :=
  Dimensionful (WithDim (L𝓭 * T𝓭⁻¹ * T𝓭⁻¹) NNReal)

/-- A scalar moment of inertia about an axis, with dimension `M L²`. -/
abbrev MomentOfInertiaQuantity : Type :=
  Dimensionful (WithDim (M𝓭 * L𝓭 * L𝓭) NNReal)

/-!
The coefficient of angular displacement in the linearized gravitational
restoring torque.  Angles in radians are dimensionless, so this has dimension
`M L² T⁻²`.
-/
abbrev RestoringTorqueCoefficientQuantity : Type :=
  Dimensionful
    (WithDim (M𝓭 * L𝓭 * L𝓭 * T𝓭⁻¹ * T𝓭⁻¹) NNReal)

/-- A signed torque, with dimension `M L² T⁻²`. -/
abbrev TorqueQuantity : Type :=
  Dimensionful
    (WithDim (M𝓭 * L𝓭 * L𝓭 * T𝓭⁻¹ * T𝓭⁻¹) ℝ)

/-- Read a physical mass in kilograms. -/
def massInKilograms (mass : MassQuantity) : ℝ :=
  ((mass UnitChoices.SI).val : ℝ)

/-- Read a physical length in metres. -/
def lengthInMeters (length : LengthQuantity) : ℝ :=
  ((length UnitChoices.SI).val : ℝ)

/-- Read a physical duration in seconds. -/
def timeInSeconds (time : TimeQuantity) : ℝ :=
  ((time UnitChoices.SI).val : ℝ)

/-- Read an angular-frequency magnitude in radians per second. -/
def angularFrequencyInRadiansPerSecond
    (frequency : AngularFrequencyMagnitudeQuantity) : ℝ :=
  ((frequency UnitChoices.SI).val : ℝ)

/-- Read an acceleration magnitude in metres per second squared. -/
def accelerationInMetersPerSecondSquared
    (acceleration : AccelerationMagnitudeQuantity) : ℝ :=
  ((acceleration UnitChoices.SI).val : ℝ)

/-- Read a moment of inertia in kilogram metre squared. -/
def momentOfInertiaInKilogramMetersSquared
    (inertia : MomentOfInertiaQuantity) : ℝ :=
  ((inertia UnitChoices.SI).val : ℝ)

/-- Read a restoring-torque coefficient in newton metres per radian. -/
def restoringCoefficientInNewtonMeters
    (coefficient : RestoringTorqueCoefficientQuantity) : ℝ :=
  ((coefficient UnitChoices.SI).val : ℝ)

/-- Read a signed torque in newton metres. -/
def torqueInNewtonMeters (torque : TorqueQuantity) : ℝ :=
  (torque UnitChoices.SI).val

/-! ## Apparatus roles and primary-figure labels -/

/-- The two massive sticks in the T-shaped assembly. -/
inductive StickComponent where
  | horizontal
  | vertical
  deriving DecidableEq, Repr

/-- The mass-distribution idealization used for each stick. -/
inductive StickMassDistribution where
  | uniformSlender
  | unspecified
  deriving DecidableEq, Repr

/-- Colors visible in the supplied raster figure. -/
inductive FigureColor where
  | blue
  | red
  | other
  deriving DecidableEq, Repr

/-- Distinguished geometric locations in the supplied figure. -/
inductive FigureLocation where
  | pointA
  | horizontalLeftEnd
  | horizontalRightEnd
  | verticalBottomEnd
  deriving DecidableEq, Repr

/-- Relative geometry of the two sticks at their joint. -/
inductive JointGeometry where
  | perpendicularTShape
  | other
  deriving DecidableEq, Repr

/-- Direction in which the vertical stick extends away from point `A`. -/
inductive VerticalOrientation where
  | downwardFromA
  | other
  deriving DecidableEq, Repr

/-!
Qualitative geometry and labels read from the primary image.  Location-valued
fields make the coincidence of the pin, the horizontal midpoint, and the
vertical top endpoint explicit without assigning a numerical period.
-/
structure TStickFigure where
  stickVisible : StickComponent → Bool
  stickColor : StickComponent → FigureColor
  pivotLocation : FigureLocation
  horizontalMidpointLocation : FigureLocation
  verticalTopEndpointLocation : FigureLocation
  horizontalLeftEndpointLocation : FigureLocation
  horizontalRightEndpointLocation : FigureLocation
  verticalBottomEndpointLocation : FigureLocation
  jointGeometry : JointGeometry
  verticalOrientation : VerticalOrientation
  pointALabelVisible : Bool

/-!
Physical quantities for the compound pendulum.  Component centers of mass and
moments of inertia are kept separate so that the uniform-rod and parallel-axis
laws can be stated independently.  The finite-amplitude period function is
related to the independent linearized frequency and period only by the local
governing laws below; none is defined to be the requested answer.
-/
structure TStickPendulumSetup where
  componentLength : StickComponent → LengthQuantity
  componentMass : StickComponent → MassQuantity
  massDistribution : StickComponent → StickMassDistribution
  componentCenterOfMassDistanceBelowPivot :
    StickComponent → LengthQuantity
  assemblyCenterOfMassDistanceBelowPivot : LengthQuantity
  componentMomentOfInertiaAboutCenter :
    StickComponent → MomentOfInertiaQuantity
  componentMomentOfInertiaAboutPivot :
    StickComponent → MomentOfInertiaQuantity
  totalMass : MassQuantity
  totalMomentOfInertiaAboutPivot : MomentOfInertiaQuantity
  gravitationalAccelerationMagnitude : AccelerationMagnitudeQuantity
  gravitationalRestoringCoefficient : RestoringTorqueCoefficientQuantity
  gravitationalRestoringTorque : ℝ → TorqueQuantity
  nonlinearOscillationPeriodAtPeakAngleRadians : ℝ → TimeQuantity
  linearizedAngularFrequency : AngularFrequencyMagnitudeQuantity
  linearizedSmallOscillationPeriod : TimeQuantity
  figure : TStickFigure

/-!
Primary-image readout: a blue horizontal stick and red vertical stick form a
perpendicular T.  The pin labeled `A`, the horizontal midpoint, and the top of
the downward vertical stick coincide.
-/
structure MatchesPrimaryTStickFigure
    (setup : TStickPendulumSetup) : Prop where
  horizontalStickVisible : setup.figure.stickVisible .horizontal = true
  verticalStickVisible : setup.figure.stickVisible .vertical = true
  horizontalStickBlue : setup.figure.stickColor .horizontal = .blue
  verticalStickRed : setup.figure.stickColor .vertical = .red
  pivotIsPointA : setup.figure.pivotLocation = .pointA
  horizontalMidpointIsPointA :
    setup.figure.horizontalMidpointLocation = .pointA
  verticalTopIsPointA : setup.figure.verticalTopEndpointLocation = .pointA
  horizontalLeftEndLocated :
    setup.figure.horizontalLeftEndpointLocation = .horizontalLeftEnd
  horizontalRightEndLocated :
    setup.figure.horizontalRightEndpointLocation = .horizontalRightEnd
  verticalBottomEndLocated :
    setup.figure.verticalBottomEndpointLocation = .verticalBottomEnd
  sticksFormPerpendicularT :
    setup.figure.jointGeometry = .perpendicularTShape
  verticalStickExtendsDownward :
    setup.figure.verticalOrientation = .downwardFromA
  pointALabelVisible : setup.figure.pointALabelVisible = true

/-!
Numerical data printed in the problem: both sticks have length `1 m`.
-/
structure MatchesTStickProblemData
    (setup : TStickPendulumSetup) : Prop where
  horizontalLengthMeters :
    lengthInMeters (setup.componentLength .horizontal) = 1
  verticalLengthMeters :
    lengthInMeters (setup.componentLength .vertical) = 1

/-!
Textbook mass-distribution idealization needed to obtain a unique numerical
answer: the two sticks have equal masses and are uniform and slender.  This is
kept separate from the literal source data.  No categorical "small-angle
regime" tag is used; the approximation is expressed by the local analytic
contracts in the governing laws.
-/
structure UsesEqualUniformSlenderStickIdealization
    (setup : TStickPendulumSetup) : Prop where
  equalStickMasses :
    massInKilograms (setup.componentMass .horizontal) =
      massInKilograms (setup.componentMass .vertical)
  horizontalStickUniformSlender :
    setup.massDistribution .horizontal = .uniformSlender
  verticalStickUniformSlender :
    setup.massDistribution .vertical = .uniformSlender

/-!
The conventional terrestrial value `g = 9.8 m/s²`, used to distinguish the
four numerical answer choices.  It is kept separate from the quantities
printed explicitly in the problem.
-/
def UsesStandardGravity (setup : TStickPendulumSetup) : Prop :=
  accelerationInMetersPerSecondSquared
      setup.gravitationalAccelerationMagnitude = 49 / 5

/-- Positivity and nondegeneracy assumptions for the physical assembly. -/
structure HasPhysicalTStickParameters
    (setup : TStickPendulumSetup) : Prop where
  horizontalLengthPositive :
    0 < lengthInMeters (setup.componentLength .horizontal)
  verticalLengthPositive :
    0 < lengthInMeters (setup.componentLength .vertical)
  horizontalMassPositive :
    0 < massInKilograms (setup.componentMass .horizontal)
  verticalMassPositive :
    0 < massInKilograms (setup.componentMass .vertical)
  totalMassPositive : 0 < massInKilograms setup.totalMass
  gravityPositive :
    0 < accelerationInMetersPerSecondSquared
      setup.gravitationalAccelerationMagnitude
  totalMomentOfInertiaPositive :
    0 < momentOfInertiaInKilogramMetersSquared
      setup.totalMomentOfInertiaAboutPivot
  restoringCoefficientPositive :
    0 < restoringCoefficientInNewtonMeters
      setup.gravitationalRestoringCoefficient
  linearizedAngularFrequencyPositive :
    0 < angularFrequencyInRadiansPerSecond
      setup.linearizedAngularFrequency
  linearizedPeriodPositive :
    0 < timeInSeconds setup.linearizedSmallOscillationPeriod

/-! ## Exact nonlinear and local linearized governing laws -/

/-!
Center-of-mass, inertia, restoring-torque, and local small-oscillation laws for
the T-shaped compound pendulum.

The horizontal center lies at the pivot, while the vertical center lies half
a stick length below it.  Each uniform slender stick has center inertia
`m L² / 12`; the parallel-axis theorem gives each pivot inertia.  Total mass
and pivot inertia are additive, and the gravitational restoring coefficient
is `M g d`.

The exact signed torque is `-κ sin θ`.  Its derivative and little-o remainder
are stated at `θ = 0`, making the replacement of `sin θ` by `θ` genuinely
local.  The frequency and period relations concern the resulting linearized
oscillator.  The last field connects the nonlinear periods to that oscillator
by a one-sided zero-amplitude limit.  None of these fields contains the
simplified T-stick target formula or a displayed answer value.
-/
structure SatisfiesTStickCompoundPendulumLaws
    (setup : TStickPendulumSetup) : Prop where
  horizontalCenterAtPivot :
    lengthInMeters
        (setup.componentCenterOfMassDistanceBelowPivot .horizontal) = 0
  verticalCenterLeverArm :
    lengthInMeters
        (setup.componentCenterOfMassDistanceBelowPivot .vertical) =
      lengthInMeters (setup.componentLength .vertical) / 2
  totalMassIsComponentSum :
    massInKilograms setup.totalMass =
      massInKilograms (setup.componentMass .horizontal) +
        massInKilograms (setup.componentMass .vertical)
  assemblyCenterOfMassBalance :
    massInKilograms setup.totalMass *
        lengthInMeters setup.assemblyCenterOfMassDistanceBelowPivot =
      massInKilograms (setup.componentMass .horizontal) *
          lengthInMeters
            (setup.componentCenterOfMassDistanceBelowPivot .horizontal) +
        massInKilograms (setup.componentMass .vertical) *
          lengthInMeters
            (setup.componentCenterOfMassDistanceBelowPivot .vertical)
  uniformStickCenterInertia :
    ∀ component : StickComponent,
      momentOfInertiaInKilogramMetersSquared
          (setup.componentMomentOfInertiaAboutCenter component) =
        massInKilograms (setup.componentMass component) *
          lengthInMeters (setup.componentLength component) ^ 2 / 12
  parallelAxisLaw :
    ∀ component : StickComponent,
      momentOfInertiaInKilogramMetersSquared
          (setup.componentMomentOfInertiaAboutPivot component) =
        momentOfInertiaInKilogramMetersSquared
            (setup.componentMomentOfInertiaAboutCenter component) +
          massInKilograms (setup.componentMass component) *
            lengthInMeters
                (setup.componentCenterOfMassDistanceBelowPivot component) ^ 2
  totalInertiaIsComponentSum :
    momentOfInertiaInKilogramMetersSquared
        setup.totalMomentOfInertiaAboutPivot =
      momentOfInertiaInKilogramMetersSquared
          (setup.componentMomentOfInertiaAboutPivot .horizontal) +
        momentOfInertiaInKilogramMetersSquared
          (setup.componentMomentOfInertiaAboutPivot .vertical)
  gravitationalRestoringCoefficientLaw :
    restoringCoefficientInNewtonMeters
        setup.gravitationalRestoringCoefficient =
      massInKilograms setup.totalMass *
        accelerationInMetersPerSecondSquared
          setup.gravitationalAccelerationMagnitude *
        lengthInMeters setup.assemblyCenterOfMassDistanceBelowPivot
  exactNonlinearRestoringTorqueLaw :
    ∀ angleRadians : ℝ,
      torqueInNewtonMeters
          (setup.gravitationalRestoringTorque angleRadians) =
        -restoringCoefficientInNewtonMeters
            setup.gravitationalRestoringCoefficient *
          Real.sin angleRadians
  restoringTorqueHasDerivativeAtStableEquilibrium :
    HasDerivAt
      (fun angleRadians : ℝ =>
        torqueInNewtonMeters
          (setup.gravitationalRestoringTorque angleRadians))
      (-restoringCoefficientInNewtonMeters
        setup.gravitationalRestoringCoefficient)
      0
  restoringTorqueNonlinearRemainderIsLittleO :
    Asymptotics.IsLittleO (nhds 0)
      (fun angleRadians : ℝ =>
        torqueInNewtonMeters
            (setup.gravitationalRestoringTorque angleRadians) +
          restoringCoefficientInNewtonMeters
              setup.gravitationalRestoringCoefficient * angleRadians)
      (fun angleRadians : ℝ => angleRadians)
  linearizedAngularFrequencySquaredLaw :
    angularFrequencyInRadiansPerSecond
        setup.linearizedAngularFrequency ^ 2 =
      restoringCoefficientInNewtonMeters
          setup.gravitationalRestoringCoefficient /
        momentOfInertiaInKilogramMetersSquared
          setup.totalMomentOfInertiaAboutPivot
  linearizedPeriodFrequencyLaw :
    timeInSeconds setup.linearizedSmallOscillationPeriod =
      2 * Real.pi /
        angularFrequencyInRadiansPerSecond
          setup.linearizedAngularFrequency
  nonlinearPeriodTendsToLinearizedPeriodAtZeroAmplitude :
    Filter.Tendsto
      (fun peakAngleRadians : ℝ =>
        timeInSeconds
          (setup.nonlinearOscillationPeriodAtPeakAngleRadians
            peakAngleRadians))
      (nhdsWithin 0 (Set.Ioi 0))
      (nhds (timeInSeconds setup.linearizedSmallOscillationPeriod))

/-! ## Derived mechanical parameters -/

/-!
The governing relations imply that the assembly center of mass lies `L/4`
below `A`, its pivot inertia is `5 m L² / 12`, and its linearized restoring
coefficient is `m g L / 2`, where `m` and `L` are the mass and length of the
horizontal stick.  These are derived conclusions, not premise fields.
-/
lemma tStickDerivedMechanicalParameters
    (setup : TStickPendulumSetup)
    (_data : MatchesTStickProblemData setup)
    (_idealization : UsesEqualUniformSlenderStickIdealization setup)
    (_physical : HasPhysicalTStickParameters setup)
    (_laws : SatisfiesTStickCompoundPendulumLaws setup) :
    lengthInMeters setup.assemblyCenterOfMassDistanceBelowPivot =
        lengthInMeters (setup.componentLength .horizontal) / 4 ∧
      momentOfInertiaInKilogramMetersSquared
          setup.totalMomentOfInertiaAboutPivot =
        5 * massInKilograms (setup.componentMass .horizontal) *
            lengthInMeters (setup.componentLength .horizontal) ^ 2 / 12 ∧
      restoringCoefficientInNewtonMeters
          setup.gravitationalRestoringCoefficient =
        massInKilograms (setup.componentMass .horizontal) *
          accelerationInMetersPerSecondSquared
            setup.gravitationalAccelerationMagnitude *
          lengthInMeters (setup.componentLength .horizontal) / 2 := by
  have hbalance := _laws.assemblyCenterOfMassBalance
  rw [_laws.totalMassIsComponentSum,
      _laws.horizontalCenterAtPivot,
      _laws.verticalCenterLeverArm,
      _data.verticalLengthMeters,
      ← _idealization.equalStickMasses] at hbalance
  have hd :
      lengthInMeters setup.assemblyCenterOfMassDistanceBelowPivot =
        lengthInMeters (setup.componentLength .horizontal) / 4 := by
    rw [_data.horizontalLengthMeters]
    nlinarith [_physical.horizontalMassPositive]
  have hCenterHorizontal :=
    _laws.uniformStickCenterInertia StickComponent.horizontal
  rw [_data.horizontalLengthMeters] at hCenterHorizontal
  have hPivotHorizontal :=
    _laws.parallelAxisLaw StickComponent.horizontal
  rw [hCenterHorizontal, _laws.horizontalCenterAtPivot] at hPivotHorizontal
  have hCenterVertical :=
    _laws.uniformStickCenterInertia StickComponent.vertical
  rw [_data.verticalLengthMeters,
      ← _idealization.equalStickMasses] at hCenterVertical
  have hPivotVertical :=
    _laws.parallelAxisLaw StickComponent.vertical
  rw [hCenterVertical, _laws.verticalCenterLeverArm,
      _data.verticalLengthMeters,
      ← _idealization.equalStickMasses] at hPivotVertical
  have hInertia := _laws.totalInertiaIsComponentSum
  rw [hPivotHorizontal, hPivotVertical] at hInertia
  have hI :
      momentOfInertiaInKilogramMetersSquared
          setup.totalMomentOfInertiaAboutPivot =
        5 * massInKilograms (setup.componentMass .horizontal) *
            lengthInMeters (setup.componentLength .horizontal) ^ 2 / 12 := by
    rw [_data.horizontalLengthMeters]
    nlinarith
  have hRestoring := _laws.gravitationalRestoringCoefficientLaw
  rw [_laws.totalMassIsComponentSum,
      ← _idealization.equalStickMasses, hd] at hRestoring
  refine ⟨hd, hI, ?_⟩
  nlinarith

/-! ## Displayed answers and formalization target -/

/-- Labels of the four displayed period choices. -/
inductive AnswerChoice where
  | A
  | B
  | C
  | D
  deriving DecidableEq, Repr

/-- The period in seconds printed beside each answer label. -/
def AnswerChoice.seconds : AnswerChoice → ℝ
  | .A => 42 / 25
  | .B => 87 / 50
  | .C => 183 / 100
  | .D => 48 / 25

/-- The answer label recorded in the supplied dataset. -/
def recordedAnswerChoice : AnswerChoice := .C

/-- Agreement with a displayed period after rounding to two decimal places. -/
def MatchesDisplayedPeriod
    (period : TimeQuantity) (choice : AnswerChoice) : Prop :=
  |timeInSeconds period - choice.seconds| < 1 / 200

/-- A displayed choice is at least as close as every listed alternative. -/
def IsClosestDisplayedPeriod
    (period : TimeQuantity) (choice : AnswerChoice) : Prop :=
  ∀ alternative : AnswerChoice,
    |timeInSeconds period - choice.seconds| ≤
      |timeInSeconds period - alternative.seconds|

/-!
The zero-amplitude, linearized period of the equal-stick T pendulum is
`T₀ = 2π √(5 L / (6 g))`.  For `L = 1 m` and standard gravity this rounds to
`1.83 s`, answer C, and C is closest among the displayed choices.  The
nonlinear finite-amplitude period is not claimed to equal this expression;
the governing laws relate it to `T₀` only through the zero-amplitude limit.

This formalizes `thm:physics:phyx_mini_0263:target`.
-/
theorem tStickLinearizedPeriod_matches_recordedAnswerC
    (setup : TStickPendulumSetup)
    (_figure : MatchesPrimaryTStickFigure setup)
    (_data : MatchesTStickProblemData setup)
    (_idealization : UsesEqualUniformSlenderStickIdealization setup)
    (_standardGravity : UsesStandardGravity setup)
    (_physical : HasPhysicalTStickParameters setup)
    (_laws : SatisfiesTStickCompoundPendulumLaws setup) :
    timeInSeconds setup.linearizedSmallOscillationPeriod =
        2 * Real.pi *
          Real.sqrt
            (5 * lengthInMeters (setup.componentLength .horizontal) /
              (6 * accelerationInMetersPerSecondSquared
                setup.gravitationalAccelerationMagnitude)) ∧
      MatchesDisplayedPeriod
        setup.linearizedSmallOscillationPeriod recordedAnswerChoice ∧
      IsClosestDisplayedPeriod
        setup.linearizedSmallOscillationPeriod recordedAnswerChoice := by
  rcases
      tStickDerivedMechanicalParameters
        setup _data _idealization _physical _laws with
    ⟨_hCenter, hInertia, hRestoring⟩
  have hFrequencySquared := _laws.linearizedAngularFrequencySquaredLaw
  rw [hRestoring, hInertia, _data.horizontalLengthMeters,
    _standardGravity] at hFrequencySquared
  have hMassNonzero :
      massInKilograms (setup.componentMass .horizontal) ≠ 0 :=
    ne_of_gt _physical.horizontalMassPositive
  have hFrequencySquaredValue :
      angularFrequencyInRadiansPerSecond
          setup.linearizedAngularFrequency ^ 2 =
        (294 / 25 : ℝ) := by
    field_simp [hMassNonzero] at hFrequencySquared ⊢
    nlinarith
  let root : ℝ := Real.sqrt (25 / 294 : ℝ)
  have hRootNonnegative : 0 ≤ root := Real.sqrt_nonneg _
  have hRootPositive : 0 < root := Real.sqrt_pos.2 (by norm_num)
  have hRootSquared : root ^ 2 = (25 / 294 : ℝ) :=
    Real.sq_sqrt (by norm_num)
  have hFrequencyPositive :
      0 < angularFrequencyInRadiansPerSecond
        setup.linearizedAngularFrequency :=
    _physical.linearizedAngularFrequencyPositive
  have hFrequencyRootProductSquared :
      (angularFrequencyInRadiansPerSecond
          setup.linearizedAngularFrequency * root) ^ 2 = 1 := by
    rw [mul_pow, hFrequencySquaredValue, hRootSquared]
    norm_num
  have hFrequencyRootProductPositive :
      0 < angularFrequencyInRadiansPerSecond
        setup.linearizedAngularFrequency * root :=
    mul_pos hFrequencyPositive hRootPositive
  have hFrequencyRootProduct :
      angularFrequencyInRadiansPerSecond
          setup.linearizedAngularFrequency * root = 1 := by
    nlinarith
  have hPeriodTimesFrequency :
      timeInSeconds setup.linearizedSmallOscillationPeriod *
          angularFrequencyInRadiansPerSecond
            setup.linearizedAngularFrequency =
        2 * Real.pi :=
    (eq_div_iff (ne_of_gt hFrequencyPositive)).mp
      _laws.linearizedPeriodFrequencyLaw
  have hPeriodValue :
      timeInSeconds setup.linearizedSmallOscillationPeriod =
        2 * Real.pi * root := by
    calc
      timeInSeconds setup.linearizedSmallOscillationPeriod =
          timeInSeconds setup.linearizedSmallOscillationPeriod *
            (angularFrequencyInRadiansPerSecond
              setup.linearizedAngularFrequency * root) := by
                rw [hFrequencyRootProduct, mul_one]
      _ =
          (timeInSeconds setup.linearizedSmallOscillationPeriod *
            angularFrequencyInRadiansPerSecond
              setup.linearizedAngularFrequency) * root := by
                ring
      _ = 2 * Real.pi * root := by rw [hPeriodTimesFrequency]
  have hFormula :
      timeInSeconds setup.linearizedSmallOscillationPeriod =
        2 * Real.pi *
          Real.sqrt
            (5 * lengthInMeters (setup.componentLength .horizontal) /
              (6 * accelerationInMetersPerSecondSquared
                setup.gravitationalAccelerationMagnitude)) := by
    rw [_data.horizontalLengthMeters, _standardGravity]
    norm_num [root] at hPeriodValue ⊢
    exact hPeriodValue
  have hRootLower : (2916 / 10000 : ℝ) < root := by
    apply (sq_lt_sq₀ (by norm_num) hRootNonnegative).mp
    rw [hRootSquared]
    norm_num
  have hRootUpper : root < (29161 / 100000 : ℝ) := by
    apply (sq_lt_sq₀ hRootNonnegative (by norm_num)).mp
    rw [hRootSquared]
    norm_num
  have hpiLower : (313 / 100 : ℝ) < Real.pi := by
    have hcosBound :=
      Real.cos_bound (x := (313 / 3200 : ℝ))
        (by norm_num [abs_of_nonneg])
    have hcos0 :
        (99521 / 100000 : ℝ) < Real.cos (313 / 3200 : ℝ) := by
      rw [abs_le] at hcosBound
      norm_num [abs_of_nonneg] at hcosBound ⊢
      linarith
    have hcos0Nonnegative :
        0 ≤ Real.cos (313 / 3200 : ℝ) := by
      linarith only [hcos0]
    have hcos1 :
        (98088 / 100000 : ℝ) < Real.cos (313 / 1600 : ℝ) := by
      rw [show (313 / 1600 : ℝ) = 2 * (313 / 3200 : ℝ) by
            norm_num,
          Real.cos_two_mul]
      have hs :=
        (sq_lt_sq₀
          (by norm_num : (0 : ℝ) ≤ 99521 / 100000)
          hcos0Nonnegative).2 hcos0
      nlinarith only [hs]
    have hcos1Nonnegative :
        0 ≤ Real.cos (313 / 1600 : ℝ) := by
      linarith only [hcos1]
    have hcos2 :
        (9242 / 10000 : ℝ) < Real.cos (313 / 800 : ℝ) := by
      rw [show (313 / 800 : ℝ) = 2 * (313 / 1600 : ℝ) by
            norm_num,
          Real.cos_two_mul]
      have hs :=
        (sq_lt_sq₀
          (by norm_num : (0 : ℝ) ≤ 98088 / 100000)
          hcos1Nonnegative).2 hcos1
      nlinarith only [hs]
    have hcos2Nonnegative :
        0 ≤ Real.cos (313 / 800 : ℝ) := by
      linarith only [hcos2]
    have hcos3 :
        (708 / 1000 : ℝ) < Real.cos (313 / 400 : ℝ) := by
      rw [show (313 / 400 : ℝ) = 2 * (313 / 800 : ℝ) by
            norm_num,
          Real.cos_two_mul]
      have hs :=
        (sq_lt_sq₀
          (by norm_num : (0 : ℝ) ≤ 9242 / 10000)
          hcos2Nonnegative).2 hcos2
      nlinarith only [hs]
    have hcos3Nonnegative :
        0 ≤ Real.cos (313 / 400 : ℝ) := by
      linarith only [hcos3]
    have hcosPositive : 0 < Real.cos (313 / 200 : ℝ) := by
      rw [show (313 / 200 : ℝ) = 2 * (313 / 400 : ℝ) by
            norm_num,
          Real.cos_two_mul]
      have hs :=
        (sq_lt_sq₀
          (by norm_num : (0 : ℝ) ≤ 708 / 1000)
          hcos3Nonnegative).2 hcos3
      nlinarith only [hs]
    by_contra h
    have hpi : Real.pi ≤ (313 / 100 : ℝ) := le_of_not_gt h
    have hcosNonpositive : Real.cos (313 / 200 : ℝ) ≤ 0 :=
      Real.cos_nonpos_of_pi_div_two_le_of_le
        (by nlinarith only [hpi])
        (by nlinarith only [Real.two_le_pi])
    linarith only [hcosPositive, hcosNonpositive]
  have hpiUpper : Real.pi < (629 / 200 : ℝ) := by
    have hcosBound :=
      Real.cos_bound (x := (629 / 6400 : ℝ))
        (by norm_num [abs_of_nonneg])
    have hcos0 :
        Real.cos (629 / 6400 : ℝ) <
          (995176 / 1000000 : ℝ) := by
      rw [abs_le] at hcosBound
      norm_num [abs_of_nonneg] at hcosBound ⊢
      linarith
    have hcos0Nonnegative :
        0 ≤ Real.cos (629 / 6400 : ℝ) := by
      apply Real.cos_nonneg_of_mem_Icc
      constructor
      · nlinarith only [Real.pi_pos]
      · nlinarith only [Real.two_le_pi]
    have hcos1 :
        Real.cos (629 / 3200 : ℝ) <
          (980751 / 1000000 : ℝ) := by
      rw [show (629 / 3200 : ℝ) = 2 * (629 / 6400 : ℝ) by
            norm_num,
          Real.cos_two_mul]
      have hs :=
        (sq_lt_sq₀ hcos0Nonnegative
          (by norm_num : (0 : ℝ) ≤ 995176 / 1000000)).2 hcos0
      nlinarith only [hs]
    have hcos1Nonnegative :
        0 ≤ Real.cos (629 / 3200 : ℝ) := by
      apply Real.cos_nonneg_of_mem_Icc
      constructor
      · nlinarith only [Real.pi_pos]
      · nlinarith only [Real.two_le_pi]
    have hcos2 :
        Real.cos (629 / 1600 : ℝ) <
          (923746 / 1000000 : ℝ) := by
      rw [show (629 / 1600 : ℝ) = 2 * (629 / 3200 : ℝ) by
            norm_num,
          Real.cos_two_mul]
      have hs :=
        (sq_lt_sq₀ hcos1Nonnegative
          (by norm_num : (0 : ℝ) ≤ 980751 / 1000000)).2 hcos1
      nlinarith only [hs]
    have hcos2Nonnegative :
        0 ≤ Real.cos (629 / 1600 : ℝ) := by
      apply Real.cos_nonneg_of_mem_Icc
      constructor
      · nlinarith only [Real.pi_pos]
      · nlinarith only [Real.two_le_pi]
    have hcos3 :
        Real.cos (629 / 800 : ℝ) < (70662 / 100000 : ℝ) := by
      rw [show (629 / 800 : ℝ) = 2 * (629 / 1600 : ℝ) by
            norm_num,
          Real.cos_two_mul]
      have hs :=
        (sq_lt_sq₀ hcos2Nonnegative
          (by norm_num : (0 : ℝ) ≤ 923746 / 1000000)).2 hcos2
      nlinarith only [hs]
    have hcos3Nonnegative :
        0 ≤ Real.cos (629 / 800 : ℝ) := by
      apply Real.cos_nonneg_of_mem_Icc
      constructor
      · nlinarith only [Real.pi_pos]
      · nlinarith only [Real.two_le_pi]
    have hcosNegative : Real.cos (629 / 400 : ℝ) < 0 := by
      rw [show (629 / 400 : ℝ) = 2 * (629 / 800 : ℝ) by
            norm_num,
          Real.cos_two_mul]
      have hs :=
        (sq_lt_sq₀ hcos3Nonnegative
          (by norm_num : (0 : ℝ) ≤ 70662 / 100000)).2 hcos3
      nlinarith only [hs]
    by_contra h
    have hpi : (629 / 200 : ℝ) ≤ Real.pi := le_of_not_gt h
    have hcosNonnegative : 0 ≤ Real.cos (629 / 400 : ℝ) := by
      apply Real.cos_nonneg_of_mem_Icc
      constructor
      · nlinarith only [Real.pi_pos]
      · nlinarith only [hpi]
    linarith only [hcosNegative, hcosNonnegative]
  have hPiRootLower :
      (313 / 100 : ℝ) * (2916 / 10000 : ℝ) <
        Real.pi * root := by
    exact lt_trans
      (mul_lt_mul_of_pos_left hRootLower (by norm_num))
      (mul_lt_mul_of_pos_right hpiLower hRootPositive)
  have hPiRootUpper :
      Real.pi * root <
        (629 / 200 : ℝ) * (29161 / 100000 : ℝ) := by
    exact lt_trans
      (mul_lt_mul_of_pos_right hpiUpper hRootPositive)
      (mul_lt_mul_of_pos_left hRootUpper (by norm_num))
  have hPeriodLower :
      (365 / 200 : ℝ) <
        timeInSeconds setup.linearizedSmallOscillationPeriod := by
    rw [hPeriodValue]
    nlinarith
  have hPeriodUpper :
      timeInSeconds setup.linearizedSmallOscillationPeriod <
        (367 / 200 : ℝ) := by
    rw [hPeriodValue]
    nlinarith
  refine ⟨hFormula, ?_, ?_⟩
  · simp only
      [MatchesDisplayedPeriod, recordedAnswerChoice, AnswerChoice.seconds]
    rw [abs_lt]
    constructor <;> linarith
  · intro alternative
    cases alternative with
    | A =>
        simp only [recordedAnswerChoice, AnswerChoice.seconds]
        rw [abs_of_nonneg (by
          linarith only [hPeriodLower] :
          0 ≤ timeInSeconds setup.linearizedSmallOscillationPeriod -
            42 / 25)]
        rw [abs_le]
        constructor <;> linarith only [hPeriodLower, hPeriodUpper]
    | B =>
        simp only [recordedAnswerChoice, AnswerChoice.seconds]
        rw [abs_of_nonneg (by
          linarith only [hPeriodLower] :
          0 ≤ timeInSeconds setup.linearizedSmallOscillationPeriod -
            87 / 50)]
        rw [abs_le]
        constructor <;> linarith only [hPeriodLower, hPeriodUpper]
    | C =>
        simp only [recordedAnswerChoice, AnswerChoice.seconds, le_refl]
    | D =>
        simp only [recordedAnswerChoice, AnswerChoice.seconds]
        rw [abs_of_nonpos (by
          linarith only [hPeriodUpper] :
          timeInSeconds setup.linearizedSmallOscillationPeriod -
            48 / 25 ≤ 0)]
        rw [abs_le]
        constructor <;> linarith only [hPeriodLower, hPeriodUpper]

end PhyXMiniProblems.ProblemPhyXMini0263
