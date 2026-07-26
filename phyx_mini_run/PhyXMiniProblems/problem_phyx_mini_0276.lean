import Mathlib.Algebra.Order.Round
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Mathlib.Analysis.Real.Sqrt
import Physlib.ClassicalMechanics.HarmonicOscillator.Solution
import Physlib.Units.WithDim.Basic

/-!
# Rod length for a grandfather-clock disk pendulum

A thin uniform brass disk of radius `r = 15.00 cm` and mass `1.000 kg` is
attached to the lower end of a thin rod of negligible mass.  The assembly
swings freely through small angles about an axis through the rod's upper end
and perpendicular to the rod.

The primary image is more precise than its auxiliary caption: the bracket
labelled `L` ends at the top rim of the disk, where the rod is attached.  Thus
`L` is the rod length, while the pivot-to-disk-center distance is `L + r`.

Masses, lengths, times, acceleration, moments of inertia, and the linearized
restoring coefficient are represented by unit-independent Physlib quantities.
Real numbers occur only as coherent unit readouts and displayed answer data.
The exact gravitational torque and its derivative at equilibrium are kept
separate from the linearized harmonic-oscillator model.  Thus the
small-angle approximation is a local first-order contract rather than a
global equality selected only by an idealization flag.  None of the
governing laws contains the requested numerical rod length.
-/

noncomputable section

namespace PhyXMiniProblems.ProblemPhyXMini0276

open Dimension

/-! ## Dimensionful physical quantities and coherent readouts -/

/-- A nonnegative physical mass. -/
abbrev MassQuantity : Type := Dimensionful (WithDim M𝓭 NNReal)

/-- A nonnegative physical length. -/
abbrev LengthQuantity : Type := Dimensionful (WithDim L𝓭 NNReal)

/-- A nonnegative physical time interval. -/
abbrev TimeQuantity : Type := Dimensionful (WithDim T𝓭 NNReal)

/-- A nonnegative acceleration magnitude, with dimension `L T⁻²`. -/
abbrev AccelerationMagnitudeQuantity : Type :=
  Dimensionful (WithDim (L𝓭 * T𝓭⁻¹ * T𝓭⁻¹) NNReal)

/-- A scalar moment of inertia about an axis, with dimension `M L²`. -/
abbrev MomentOfInertiaQuantity : Type :=
  Dimensionful (WithDim (M𝓭 * L𝓭 * L𝓭) NNReal)

/--
The coefficient multiplying the angular displacement in the linearized
gravitational restoring torque.  Radians are dimensionless, so this has
dimension `M L² T⁻²`.
-/
abbrev RestoringTorqueCoefficientQuantity : Type :=
  Dimensionful
    (WithDim (M𝓭 * L𝓭 * L𝓭 * T𝓭⁻¹ * T𝓭⁻¹) NNReal)

/--
A signed torque component about the pivot axis, with dimension
`M L² T⁻²`.  Unlike the restoring-coefficient magnitude, torque must allow
both signs.
-/
abbrev TorqueQuantity : Type :=
  Dimensionful
    (WithDim (M𝓭 * L𝓭 * L𝓭 * T𝓭⁻¹ * T𝓭⁻¹) ℝ)

/-- Unit choices in which lengths are read in centimeters. -/
def centimeterUnitChoices : UnitChoices :=
  { UnitChoices.SI with length := LengthUnit.centimeters }

/-- Read a physical mass in kilograms. -/
def massInKilograms (mass : MassQuantity) : ℝ :=
  ((mass UnitChoices.SI).val : ℝ)

/-- Read a physical length in meters. -/
def lengthInMeters (length : LengthQuantity) : ℝ :=
  ((length UnitChoices.SI).val : ℝ)

/-- Read a physical length in centimeters. -/
def lengthInCentimeters (length : LengthQuantity) : ℝ :=
  ((length centimeterUnitChoices).val : ℝ)

/-- Read a physical time interval in seconds. -/
def timeInSeconds (time : TimeQuantity) : ℝ :=
  ((time UnitChoices.SI).val : ℝ)

/-- Read an acceleration magnitude in meters per second squared. -/
def accelerationInMetersPerSecondSquared
    (acceleration : AccelerationMagnitudeQuantity) : ℝ :=
  ((acceleration UnitChoices.SI).val : ℝ)

/-- Read a moment of inertia in kilogram meters squared. -/
def momentOfInertiaInKilogramMetersSquared
    (inertia : MomentOfInertiaQuantity) : ℝ :=
  ((inertia UnitChoices.SI).val : ℝ)

/-- Read a restoring coefficient in newton meters per radian. -/
def restoringCoefficientInNewtonMeters
    (coefficient : RestoringTorqueCoefficientQuantity) : ℝ :=
  ((coefficient UnitChoices.SI).val : ℝ)

/-- Read a signed pivot-axis torque component in newton meters. -/
def torqueInNewtonMeters (torque : TorqueQuantity) : ℝ :=
  (torque UnitChoices.SI).val

/-! ## Apparatus roles and primary-image labels -/

/-- Material named for the pendulum disk. -/
inductive DiskMaterial where
  | brass
  | other
  deriving DecidableEq, Repr

/-- Mass-distribution and thickness idealization of the disk. -/
inductive DiskGeometry where
  | thinUniformDisk
  | unspecified
  deriving DecidableEq, Repr

/-- Idealization of the suspension rod. -/
inductive RodIdealization where
  | thinNegligibleMass
  | massive
  deriving DecidableEq, Repr

/-- Mechanical condition at the upper support. -/
inductive PivotCondition where
  | freelyRotatingFixedAxis
  | constrained
  deriving DecidableEq, Repr

/-- Plane of the clock-pendulum motion. -/
inductive MotionPlane where
  | vertical
  | other
  deriving DecidableEq, Repr

/-- Approximation used for the requested period. -/
inductive OscillationRegime where
  | linearizedSmallAngle
  | finiteAngle
  deriving DecidableEq, Repr

/-- Distinguished points visible or geometrically determined in the image. -/
inductive FigurePoint where
  | pivot
  | diskRimAttachment
  | diskCenter
  | radiusEndpointOnRim
  deriving DecidableEq, Repr

/-- Text and mathematical labels visible in the image. -/
inductive FigureLabel where
  | rotationAxisText
  | rodLengthL
  | diskRadiusR
  deriving DecidableEq, Repr

/-- The two directions indicated by the curved swing arrow. -/
inductive RotationDirection where
  | clockwise
  | counterclockwise
  deriving DecidableEq, Repr

/-!
Physical readout of the one-panel figure.  The separate rim attachment and
disk center prevent the auxiliary caption's center-distance ambiguity from
being built into the model.
-/
structure GrandfatherClockPendulumFigure where
  distanceBetween : FigurePoint → FigurePoint → LengthQuantity
  rodUpperEndpoint : FigurePoint
  rodLowerEndpoint : FigurePoint
  radiusArrowStart : FigurePoint
  radiusArrowEnd : FigurePoint
  rotationAxisPassesThrough : FigurePoint
  rotationAxisPerpendicularToRod : Bool
  labelVisible : FigureLabel → Bool
  rotationArrowheadVisible : RotationDirection → Bool

/-!
Independent physical quantities for the apparatus.  The pivot-to-center
distance and both moments of inertia are stored independently and related to
the printed lengths only by the figure and governing-law interfaces below.
The Physlib oscillator represents the linearized angular coordinate.
-/
structure GrandfatherClockPendulumSetup where
  diskMaterial : DiskMaterial
  diskGeometry : DiskGeometry
  rodIdealization : RodIdealization
  pivotCondition : PivotCondition
  motionPlane : MotionPlane
  oscillationRegime : OscillationRegime
  diskMass : MassQuantity
  diskRadius_r : LengthQuantity
  rodMass : MassQuantity
  rodLength_L : LengthQuantity
  pivotToDiskCenterDistance : LengthQuantity
  gravitationalAccelerationMagnitude : AccelerationMagnitudeQuantity
  desiredSmallOscillationPeriod : TimeQuantity
  diskCenterMomentOfInertia : MomentOfInertiaQuantity
  pendulumPivotMomentOfInertia : MomentOfInertiaQuantity
  gravitationalRestoringCoefficient : RestoringTorqueCoefficientQuantity
  gravitationalTorqueAtAngularDisplacement : ℝ → TorqueQuantity
  linearizedAngularOscillator : ClassicalMechanics.HarmonicOscillator
  figure : GrandfatherClockPendulumFigure

/-!
Primary-image incidences and labels.  In particular, `L` is the distance from
the pivot to the disk's top rim, not to its center.  Consequently the
center-of-mass lever arm is `L + r`.
-/
structure MatchesPrimaryGrandfatherClockFigure
    (setup : GrandfatherClockPendulumSetup) : Prop where
  rodStartsAtPivot : setup.figure.rodUpperEndpoint = .pivot
  rodEndsAtDiskRim : setup.figure.rodLowerEndpoint = .diskRimAttachment
  rodLengthBracketEndsAtRim :
    setup.figure.distanceBetween .pivot .diskRimAttachment =
      setup.rodLength_L
  attachmentToCenterIsRadius :
    setup.figure.distanceBetween .diskRimAttachment .diskCenter =
      setup.diskRadius_r
  pivotToCenterDistanceShownByGeometry :
    setup.figure.distanceBetween .pivot .diskCenter =
      setup.pivotToDiskCenterDistance
  centerDistanceIsRodLengthPlusRadius :
    lengthInMeters setup.pivotToDiskCenterDistance =
      lengthInMeters setup.rodLength_L +
        lengthInMeters setup.diskRadius_r
  radiusArrowStartsAtCenter :
    setup.figure.radiusArrowStart = .diskCenter
  radiusArrowEndsAtRim :
    setup.figure.radiusArrowEnd = .radiusEndpointOnRim
  radiusArrowHasDiskRadius :
    setup.figure.distanceBetween .diskCenter .radiusEndpointOnRim =
      setup.diskRadius_r
  axisPassesThroughPivot :
    setup.figure.rotationAxisPassesThrough = .pivot
  axisIsPerpendicularToRod :
    setup.figure.rotationAxisPerpendicularToRod = true
  rotationAxisTextVisible :
    setup.figure.labelVisible .rotationAxisText = true
  rodLengthLabelVisible : setup.figure.labelVisible .rodLengthL = true
  diskRadiusLabelVisible : setup.figure.labelVisible .diskRadiusR = true
  clockwiseArrowheadVisible :
    setup.figure.rotationArrowheadVisible .clockwise = true
  counterclockwiseArrowheadVisible :
    setup.figure.rotationArrowheadVisible .counterclockwise = true

/-! ## Problem data and governing physical laws -/

/-- Qualitative apparatus data and idealizations stated in the problem. -/
structure MatchesGrandfatherClockPendulumScenario
    (setup : GrandfatherClockPendulumSetup) : Prop where
  diskIsBrass : setup.diskMaterial = .brass
  diskIsThinAndUniform : setup.diskGeometry = .thinUniformDisk
  rodIsThinWithNegligibleMass :
    setup.rodIdealization = .thinNegligibleMass
  pivotAllowsFreeSwing :
    setup.pivotCondition = .freelyRotatingFixedAxis
  pendulumSwingsInVerticalPlane : setup.motionPlane = .vertical
  usesSmallAngleLinearization :
    setup.oscillationRegime = .linearizedSmallAngle

/-!
The stated numerical data and positivity conditions.  `rodLength_L` remains
an unknown positive physical length; no answer choice is assumed here.
-/
structure HasGrandfatherClockPendulumProblemData
    (setup : GrandfatherClockPendulumSetup) : Prop where
  diskRadiusCentimeters : lengthInCentimeters setup.diskRadius_r = 15
  diskMassKilograms : massInKilograms setup.diskMass = 1
  idealizedRodMassKilograms : massInKilograms setup.rodMass = 0
  desiredPeriodSeconds :
    timeInSeconds setup.desiredSmallOscillationPeriod = 2
  gravitationalAccelerationMetersPerSecondSquared :
    accelerationInMetersPerSecondSquared
        setup.gravitationalAccelerationMagnitude = 49 / 5
  diskRadiusPositive : 0 < lengthInMeters setup.diskRadius_r
  diskMassPositive : 0 < massInKilograms setup.diskMass
  rodLengthPositive : 0 < lengthInMeters setup.rodLength_L
  centerDistancePositive :
    0 < lengthInMeters setup.pivotToDiskCenterDistance
  gravityPositive :
    0 < accelerationInMetersPerSecondSquared
      setup.gravitationalAccelerationMagnitude

/-!
The rigid-body and small-oscillation laws used in the calculation:

* a thin uniform disk has center-axis inertia `m r² / 2`;
* the scalar parallel-axis theorem adds `m d²` at the pivot;
* the exact signed gravitational torque is `-m g d sin θ`;
* its derivative at the downward equilibrium is `-m g d`, expressed with
  Mathlib's local `HasDerivAt` contract;
* the corresponding positive linearized restoring coefficient is `m g d`;
* the generalized oscillator mass and stiffness are the pivot inertia and
  restoring coefficient; and
* the requested limiting small-oscillation duration is the generic Physlib
  harmonic-oscillator period.

No field states the long-root solution, the rounded rod length, or an answer
choice.
-/
structure SatisfiesGrandfatherClockPendulumLaws
    (setup : GrandfatherClockPendulumSetup) : Prop where
  thinUniformDiskCenterInertia :
    momentOfInertiaInKilogramMetersSquared
        setup.diskCenterMomentOfInertia =
      massInKilograms setup.diskMass *
        lengthInMeters setup.diskRadius_r ^ 2 / 2
  scalarParallelAxisLaw :
    momentOfInertiaInKilogramMetersSquared
        setup.pendulumPivotMomentOfInertia =
      momentOfInertiaInKilogramMetersSquared
          setup.diskCenterMomentOfInertia +
        massInKilograms setup.diskMass *
          lengthInMeters setup.pivotToDiskCenterDistance ^ 2
  exactGravitationalTorqueLaw :
    ∀ angularDisplacementRadians : ℝ,
      torqueInNewtonMeters
          (setup.gravitationalTorqueAtAngularDisplacement
            angularDisplacementRadians) =
        -(massInKilograms setup.diskMass *
            accelerationInMetersPerSecondSquared
              setup.gravitationalAccelerationMagnitude *
            lengthInMeters setup.pivotToDiskCenterDistance *
            Real.sin angularDisplacementRadians)
  gravitationalTorqueHasLocalLinearizationAtEquilibrium :
    HasDerivAt
      (fun angularDisplacementRadians : ℝ =>
        torqueInNewtonMeters
          (setup.gravitationalTorqueAtAngularDisplacement
            angularDisplacementRadians))
      (-restoringCoefficientInNewtonMeters
        setup.gravitationalRestoringCoefficient)
      0
  localLinearizedGravitationalRestoringCoefficient :
    restoringCoefficientInNewtonMeters
        setup.gravitationalRestoringCoefficient =
      massInKilograms setup.diskMass *
        accelerationInMetersPerSecondSquared
          setup.gravitationalAccelerationMagnitude *
        lengthInMeters setup.pivotToDiskCenterDistance
  oscillatorGeneralizedMass :
    setup.linearizedAngularOscillator.m =
      momentOfInertiaInKilogramMetersSquared
        setup.pendulumPivotMomentOfInertia
  oscillatorGeneralizedStiffness :
    setup.linearizedAngularOscillator.k =
      restoringCoefficientInNewtonMeters
        setup.gravitationalRestoringCoefficient
  linearizedModelPeriodLaw :
    timeInSeconds setup.desiredSmallOscillationPeriod =
      setup.linearizedAngularOscillator.period

/-! ## Displayed choices, rounding convention, and target -/

/-- Labels of the four displayed rod-length choices. -/
inductive AnswerChoice where
  | A
  | B
  | C
  | D
  deriving DecidableEq, Repr

/-- Rod length in meters printed beside each answer label. -/
def AnswerChoice.meters : AnswerChoice → ℝ
  | .A => 8023 / 10000
  | .B => 8197 / 10000
  | .C => 8545 / 10000
  | .D => 8315 / 10000

/-- The answer label recorded in the supplied dataset metadata. -/
def recordedAnswerChoice : AnswerChoice := .D

/-!
Agreement after rounding meters to the nearest `0.0001 m`, which is one tenth
of a millimeter.  Mathlib's `round` breaks exact half-way ties upward.
-/
def RoundsToNearestTenthMillimeter
    (length : LengthQuantity) (choice : AnswerChoice) : Prop :=
  round (10000 * lengthInMeters length) =
    round (10000 * choice.meters)

/-- A displayed choice is at least as close as every listed alternative. -/
def IsClosestDisplayedRodLength
    (length : LengthQuantity) (choice : AnswerChoice) : Prop :=
  ∀ alternative : AnswerChoice,
    |lengthInMeters length - choice.meters| ≤
      |lengthInMeters length - alternative.meters|

/-!
Writing `d = L + r`, the small-angle period equation gives

`d² - (g T² / (4 π²)) d + r² / 2 = 0`.

Within the first-order model certified by the local torque derivative, the
positivity of `L` selects the long root.  Subtracting the disk radius from
that center distance gives a rod length that rounds to `0.8315 m`, the
recorded answer D, and is closer to D than to every other displayed choice.

This formalizes blueprint label `thm:physics:phyx_mini_0276:target`.
-/
set_option maxHeartbeats 1000000 in
theorem grandfatherClockRodLength_inLinearizedModel_is_recordedAnswerD
    (setup : GrandfatherClockPendulumSetup)
    (_figure : MatchesPrimaryGrandfatherClockFigure setup)
    (_scenario : MatchesGrandfatherClockPendulumScenario setup)
    (_data : HasGrandfatherClockPendulumProblemData setup)
    (_laws : SatisfiesGrandfatherClockPendulumLaws setup) :
    lengthInMeters setup.pivotToDiskCenterDistance =
        ((accelerationInMetersPerSecondSquared
                setup.gravitationalAccelerationMagnitude *
              timeInSeconds setup.desiredSmallOscillationPeriod ^ 2 /
              (4 * Real.pi ^ 2)) +
            Real.sqrt
              ((accelerationInMetersPerSecondSquared
                      setup.gravitationalAccelerationMagnitude *
                    timeInSeconds setup.desiredSmallOscillationPeriod ^ 2 /
                    (4 * Real.pi ^ 2)) ^ 2 -
                2 * lengthInMeters setup.diskRadius_r ^ 2)) /
          2 ∧
      lengthInMeters setup.rodLength_L =
        ((accelerationInMetersPerSecondSquared
                setup.gravitationalAccelerationMagnitude *
              timeInSeconds setup.desiredSmallOscillationPeriod ^ 2 /
              (4 * Real.pi ^ 2)) +
            Real.sqrt
              ((accelerationInMetersPerSecondSquared
                      setup.gravitationalAccelerationMagnitude *
                    timeInSeconds setup.desiredSmallOscillationPeriod ^ 2 /
                    (4 * Real.pi ^ 2)) ^ 2 -
                2 * lengthInMeters setup.diskRadius_r ^ 2)) /
          2 - lengthInMeters setup.diskRadius_r ∧
      RoundsToNearestTenthMillimeter
        setup.rodLength_L recordedAnswerChoice ∧
      IsClosestDisplayedRodLength
        setup.rodLength_L recordedAnswerChoice := by
  set_option maxHeartbeats 10000000 in
    all_goals
      have hCentimeterScale :
          ((centimeterUnitChoices.dimScale UnitChoices.SI L𝓭 : NNReal) : ℝ) =
            1 / 100 := by
        norm_num [centimeterUnitChoices, UnitChoices.dimScale,
          LengthUnit.centimeters]
        rfl
      have hRadiusMeters :
          lengthInMeters setup.diskRadius_r = (3 : ℝ) / 20 := by
        have hScale := congrArg WithDim.val
          (setup.diskRadius_r.property centimeterUnitChoices UnitChoices.SI)
        have hScaleReal := congrArg (fun x : NNReal => (x : ℝ)) hScale
        change (↑(setup.diskRadius_r UnitChoices.SI).val : ℝ) =
          ↑(centimeterUnitChoices.dimScale UnitChoices.SI L𝓭) *
            ↑(setup.diskRadius_r centimeterUnitChoices).val at hScaleReal
        rw [hCentimeterScale] at hScaleReal
        have hRadiusCentimeters := _data.diskRadiusCentimeters
        change (↑(setup.diskRadius_r centimeterUnitChoices).val : ℝ) = 15 at hRadiusCentimeters
        change (↑(setup.diskRadius_r UnitChoices.SI).val : ℝ) = (3 : ℝ) / 20
        nlinarith
    
      let r : ℝ := lengthInMeters setup.diskRadius_r
      let d : ℝ := lengthInMeters setup.pivotToDiskCenterDistance
      let ell : ℝ := lengthInMeters setup.rodLength_L
      let mass : ℝ := massInKilograms setup.diskMass
      let g : ℝ :=
        accelerationInMetersPerSecondSquared
          setup.gravitationalAccelerationMagnitude
      let t : ℝ := timeInSeconds setup.desiredSmallOscillationPeriod
      let oscillator : ClassicalMechanics.HarmonicOscillator :=
        setup.linearizedAngularOscillator
      let a : ℝ := g * t ^ 2 / (4 * Real.pi ^ 2)
    
      have hr : r = (3 : ℝ) / 20 := by
        simpa [r] using hRadiusMeters
      have hm : mass = (1 : ℝ) := by
        simpa [mass] using _data.diskMassKilograms
      have hg : g = (49 : ℝ) / 5 := by
        simpa [g] using
          _data.gravitationalAccelerationMetersPerSecondSquared
      have ht : t = (2 : ℝ) := by
        simpa [t] using _data.desiredPeriodSeconds
      have hellPos : 0 < ell := by
        simpa [ell] using _data.rodLengthPositive
      have hdPos : 0 < d := by
        simpa [d] using _data.centerDistancePositive
      have hgeometry : d = ell + r := by
        simpa [d, ell, r] using _figure.centerDistanceIsRodLengthPlusRadius
      have hdGreaterRadius : r < d := by
        nlinarith
    
      have hOscillatorMass :
          oscillator.m = mass * r ^ 2 / 2 + mass * d ^ 2 := by
        calc
          oscillator.m =
              momentOfInertiaInKilogramMetersSquared
                setup.pendulumPivotMomentOfInertia := by
                  simpa [oscillator] using _laws.oscillatorGeneralizedMass
          _ =
              momentOfInertiaInKilogramMetersSquared
                  setup.diskCenterMomentOfInertia +
                mass * d ^ 2 := by
                  simpa [mass, d] using _laws.scalarParallelAxisLaw
          _ = mass * r ^ 2 / 2 + mass * d ^ 2 := by
                  rw [_laws.thinUniformDiskCenterInertia]
      have hOscillatorStiffness :
          oscillator.k = mass * g * d := by
        calc
          oscillator.k =
              restoringCoefficientInNewtonMeters
                setup.gravitationalRestoringCoefficient := by
                  simpa [oscillator] using _laws.oscillatorGeneralizedStiffness
          _ = mass * g * d := by
                  simpa [mass, g, d] using
                    _laws.localLinearizedGravitationalRestoringCoefficient
      have hPeriod : (2 : ℝ) = oscillator.period := by
        calc
          (2 : ℝ) = t := ht.symm
          _ = oscillator.period := by
            simpa [t, oscillator] using _laws.linearizedModelPeriodLaw
      have hAngularFrequency : oscillator.ω = Real.pi := by
        rw [ClassicalMechanics.HarmonicOscillator.period_eq] at hPeriod
        have hmul :
            2 * Real.pi = 2 * oscillator.ω :=
          (div_eq_iff oscillator.ω_ne_zero).mp hPeriod.symm
        nlinarith
      have hDenominatorPos : 0 < r ^ 2 / 2 + d ^ 2 := by
        nlinarith [sq_nonneg r, sq_pos_of_pos hdPos]
      have hFrequencySquare :
          Real.pi ^ 2 =
            ((49 : ℝ) / 5 * d) / (r ^ 2 / 2 + d ^ 2) := by
        calc
          Real.pi ^ 2 = oscillator.ω ^ 2 := by rw [hAngularFrequency]
          _ = oscillator.k / oscillator.m :=
            ClassicalMechanics.HarmonicOscillator.ω_sq oscillator
          _ = ((49 : ℝ) / 5 * d) / (r ^ 2 / 2 + d ^ 2) := by
            rw [hOscillatorStiffness, hOscillatorMass, hm, hg]
            ring
      have hPhysicalQuadratic :
          Real.pi ^ 2 * (r ^ 2 / 2 + d ^ 2) = (49 : ℝ) / 5 * d :=
        (eq_div_iff hDenominatorPos.ne').mp hFrequencySquare
    
      have hPiSquarePos : 0 < Real.pi ^ 2 := sq_pos_of_pos Real.pi_pos
      have ha : a = ((49 : ℝ) / 5) / Real.pi ^ 2 := by
        dsimp [a]
        rw [hg, ht]
        ring
      have haTimesPiSquare : a * Real.pi ^ 2 = (49 : ℝ) / 5 := by
        rw [ha]
        field_simp [hPiSquarePos.ne']
      have hQuadratic : d ^ 2 - a * d + r ^ 2 / 2 = 0 := by
        have hcancel :
            Real.pi ^ 2 * (d ^ 2 + r ^ 2 / 2) =
              Real.pi ^ 2 * (a * d) := by
          calc
            Real.pi ^ 2 * (d ^ 2 + r ^ 2 / 2) =
                (49 : ℝ) / 5 * d := by
                  nlinarith [hPhysicalQuadratic]
            _ = Real.pi ^ 2 * (a * d) := by
                rw [← haTimesPiSquare]
                ring
        nlinarith
      have rodBoundsFromCenterBounds
          (hLowerCenter : (19629 : ℝ) / 20000 < d)
          (hUpperCenter : d < (19631 : ℝ) / 20000) :
          (16629 : ℝ) / 20000 < ell ∧
            ell < (16631 : ℝ) / 20000 := by
        rw [hr] at hgeometry
        constructor
        · linarith only [hLowerCenter, hgeometry]
        · linarith only [hUpperCenter, hgeometry]
      have quadraticDifferenceFactor (x : ℝ) :
          (d - x) * (d + x - a) =
            (d ^ 2 - a * d + r ^ 2 / 2) -
              (x ^ 2 - a * x + r ^ 2 / 2) := by
        ring
      have rodFormulaFromCenterFormula
          (hCenter :
            d = (a + Real.sqrt (a ^ 2 - 2 * r ^ 2)) / 2) :
          ell =
            (a + Real.sqrt (a ^ 2 - 2 * r ^ 2)) / 2 - r := by
        linarith only [hgeometry, hCenter]
      have centerFormulaFromLongRootSign (hLong : 0 < 2 * d - a) :
          d = (a + Real.sqrt (a ^ 2 - 2 * r ^ 2)) / 2 := by
        have hSquareIdentity :
            (2 * d - a) ^ 2 = a ^ 2 - 2 * r ^ 2 := by
          nlinarith only [hQuadratic]
        have hRadicandNonnegative : 0 ≤ a ^ 2 - 2 * r ^ 2 := by
          nlinarith only [hSquareIdentity, sq_nonneg (2 * d - a)]
        have hSqrtSquare :
            Real.sqrt (a ^ 2 - 2 * r ^ 2) ^ 2 =
              a ^ 2 - 2 * r ^ 2 :=
          Real.sq_sqrt hRadicandNonnegative
        have hSqrtIdentity :
            Real.sqrt (a ^ 2 - 2 * r ^ 2) = 2 * d - a := by
          nlinarith only [hSqrtSquare, hSquareIdentity, hLong,
            Real.sqrt_nonneg (a ^ 2 - 2 * r ^ 2)]
        linarith only [hSqrtIdentity]
      have aBoundsFromPiSquareBounds
          (hPiSqUpper :
            Real.pi ^ 2 < ((3927 : ℝ) / 1250) ^ 2)
          (hPiSqLower :
            ((6283 : ℝ) / 2000) ^ 2 < Real.pi ^ 2) :
          r < a ∧ a < 1 := by
        constructor
        · rw [hr, ha]
          apply (lt_div_iff₀ hPiSquarePos).2
          nlinarith only [hPiSqUpper]
        · rw [ha]
          apply (div_lt_iff₀ hPiSquarePos).2
          nlinarith only [hPiSqLower]
      have piSquareBoundsFromPiBounds
          (hUpper : Real.pi < (3.1416 : ℝ))
          (hLower : (3.1415 : ℝ) < Real.pi) :
          Real.pi ^ 2 < ((3927 : ℝ) / 1250) ^ 2 ∧
            ((6283 : ℝ) / 2000) ^ 2 < Real.pi ^ 2 := by
        constructor
        · nlinarith only [hUpper, Real.pi_pos]
        · nlinarith only [hLower, Real.pi_pos]
      have piBoundsFromMachinAndArctanBounds
          (hMachin :
            Real.pi =
              16 * Real.arctan ((1 : ℝ) / 5) -
                4 * Real.arctan ((1 : ℝ) / 239))
          (hFiveLower :
            (1 : ℝ) / 5 - ((1 : ℝ) / 5) ^ 3 / 3 +
                  ((1 : ℝ) / 5) ^ 5 / 5 -
                ((1 : ℝ) / 5) ^ 7 / 7 ≤
              Real.arctan ((1 : ℝ) / 5))
          (hFiveUpper :
            Real.arctan ((1 : ℝ) / 5) ≤
              (1 : ℝ) / 5 - ((1 : ℝ) / 5) ^ 3 / 3 +
                    ((1 : ℝ) / 5) ^ 5 / 5 -
                  ((1 : ℝ) / 5) ^ 7 / 7 +
                ((1 : ℝ) / 5) ^ 9 / 9)
          (h239Lower :
            (1 : ℝ) / 239 - ((1 : ℝ) / 239) ^ 3 / 3 ≤
              Real.arctan ((1 : ℝ) / 239))
          (h239Upper :
            Real.arctan ((1 : ℝ) / 239) < (1 : ℝ) / 239) :
          (3.1415 : ℝ) < Real.pi ∧ Real.pi < (3.1416 : ℝ) := by
        constructor
        · rw [hMachin]
          norm_num at hFiveLower h239Upper ⊢
          linarith
        · rw [hMachin]
          norm_num at hFiveUpper h239Lower ⊢
          linarith
      have hMachin :
          Real.pi =
            16 * Real.arctan ((1 : ℝ) / 5) -
              4 * Real.arctan ((1 : ℝ) / 239) := by
        calc
          Real.pi = 4 * (Real.pi / 4) := by ring
          _ = 4 *
              (4 * Real.arctan (5 : ℝ)⁻¹ -
                Real.arctan (239 : ℝ)⁻¹) := by
              rw [Real.four_mul_arctan_inv_5_sub_arctan_inv_239]
          _ = 16 * Real.arctan ((1 : ℝ) / 5) -
                4 * Real.arctan ((1 : ℝ) / 239) := by
              rw [one_div]
              ring_nf
      have displayClaimsFromRodBounds
          (hLower : (16629 : ℝ) / 20000 < ell)
          (hUpper : ell < (16631 : ℝ) / 20000) :
          RoundsToNearestTenthMillimeter
              setup.rodLength_L recordedAnswerChoice ∧
            IsClosestDisplayedRodLength
              setup.rodLength_L recordedAnswerChoice := by
        have hLowerWeak : (16629 : ℝ) / 20000 ≤ ell := hLower.le
        have hRoundRod : round (10000 * ell) = (8315 : ℤ) := by
          apply (round_eq_iff).2
          constructor
          · linarith only [hLowerWeak]
          · linarith only [hUpper]
        have hRoundChoice :
            round (10000 * AnswerChoice.D.meters) = (8315 : ℤ) := by
          have hChoiceScaled :
              10000 * AnswerChoice.D.meters = (8315 : ℝ) := by
            norm_num [AnswerChoice.meters]
          rw [hChoiceScaled]
          exact round_intCast 8315
        have hDistanceToD :
            |ell - AnswerChoice.D.meters| ≤ (1 : ℝ) / 20000 := by
          change |ell - (8315 / 10000 : ℝ)| ≤ (1 : ℝ) / 20000
          apply abs_le.mpr
          constructor
          · linarith only [hLowerWeak]
          · linarith only [hUpper]
        have hClosest :
            IsClosestDisplayedRodLength
              setup.rodLength_L recordedAnswerChoice := by
          unfold IsClosestDisplayedRodLength recordedAnswerChoice
          intro alternative
          change
            |ell - AnswerChoice.D.meters| ≤
              |ell - alternative.meters|
          cases alternative
          · calc
              |ell - AnswerChoice.D.meters| ≤ (1 : ℝ) / 20000 :=
                hDistanceToD
              _ ≤ |ell - AnswerChoice.A.meters| := by
                rw [abs_of_nonneg]
                · norm_num [AnswerChoice.meters]
                  linarith only [hLower]
                · norm_num [AnswerChoice.meters]
                  linarith only [hLower]
          · calc
              |ell - AnswerChoice.D.meters| ≤ (1 : ℝ) / 20000 :=
                hDistanceToD
              _ ≤ |ell - AnswerChoice.B.meters| := by
                rw [abs_of_nonneg]
                · norm_num [AnswerChoice.meters]
                  linarith only [hLower]
                · norm_num [AnswerChoice.meters]
                  linarith only [hLower]
          · calc
              |ell - AnswerChoice.D.meters| ≤ (1 : ℝ) / 20000 :=
                hDistanceToD
              _ ≤ |ell - AnswerChoice.C.meters| := by
                rw [abs_of_nonpos]
                · norm_num [AnswerChoice.meters]
                  linarith only [hUpper]
                · norm_num [AnswerChoice.meters]
                  linarith only [hUpper]
          · exact le_rfl
        constructor
        · unfold RoundsToNearestTenthMillimeter recordedAnswerChoice
          change
            round (10000 * ell) =
              round (10000 * AnswerChoice.D.meters)
          exact hRoundRod.trans hRoundChoice.symm
        · exact hClosest

      have arctanLowerBounds :
          ((1 : ℝ) / 5 - ((1 : ℝ) / 5) ^ 3 / 3 +
                  ((1 : ℝ) / 5) ^ 5 / 5 -
                ((1 : ℝ) / 5) ^ 7 / 7 ≤
              Real.arctan ((1 : ℝ) / 5)) ∧
            ((1 : ℝ) / 239 - ((1 : ℝ) / 239) ^ 3 / 3 +
                    ((1 : ℝ) / 239) ^ 5 / 5 -
                  ((1 : ℝ) / 239) ^ 7 / 7 ≤
                Real.arctan ((1 : ℝ) / 239)) := by
        let f : ℝ → ℝ := fun z =>
          Real.arctan z - (z - z ^ 3 / 3 + z ^ 5 / 5 - z ^ 7 / 7)
        have hdiff : Differentiable ℝ f := by
          dsimp [f]
          exact Real.differentiable_arctan.sub (by fun_prop)
        have hmono : MonotoneOn f (Set.Ici 0) := by
          apply monotoneOn_of_deriv_nonneg (convex_Ici 0)
          · exact hdiff.continuous.continuousOn
          · exact hdiff.differentiableOn
          · intro y _
            have h := (Real.hasDerivAt_arctan y).sub
              ((((hasDerivAt_id y).sub
                    (((hasDerivAt_id y).pow 3).div_const 3)).add
                  (((hasDerivAt_id y).pow 5).div_const 5)).sub
                (((hasDerivAt_id y).pow 7).div_const 7))
            have hfun :
                (Real.arctan -
                    (((id - fun q : ℝ => (id ^ 3) q / 3) +
                      fun q : ℝ => (id ^ 5) q / 5) -
                      fun q : ℝ => (id ^ 7) q / 7)) = f := by
              funext q
              rfl
            rw [← hfun, h.deriv]
            simp only [id_eq]
            norm_num
            rw [← sub_nonneg]
            have hden : (1 + y ^ 2) ≠ 0 := by positivity
            rw [show
                (1 + y ^ 2)⁻¹ + y ^ 6 - (1 - y ^ 2 + y ^ 4) =
                  y ^ 8 / (1 + y ^ 2) by
              rw [inv_eq_one_div]
              field_simp [hden]
              ring]
            positivity
        constructor
        · have h := hmono (show (0 : ℝ) ∈ Set.Ici 0 by simp)
            (show (1 : ℝ) / 5 ∈ Set.Ici 0 by norm_num)
            (by norm_num : (0 : ℝ) ≤ 1 / 5)
          simpa [f] using h
        · have h := hmono (show (0 : ℝ) ∈ Set.Ici 0 by simp)
            (show (1 : ℝ) / 239 ∈ Set.Ici 0 by norm_num)
            (by norm_num : (0 : ℝ) ≤ 1 / 239)
          simpa [f] using h
      have hArctanFiveUpper :
          Real.arctan ((1 : ℝ) / 5) ≤
            (1 : ℝ) / 5 - ((1 : ℝ) / 5) ^ 3 / 3 +
                  ((1 : ℝ) / 5) ^ 5 / 5 -
                ((1 : ℝ) / 5) ^ 7 / 7 +
              ((1 : ℝ) / 5) ^ 9 / 9 := by
        let f : ℝ → ℝ := fun z =>
          (z - z ^ 3 / 3 + z ^ 5 / 5 - z ^ 7 / 7 + z ^ 9 / 9) -
            Real.arctan z
        have hdiff : Differentiable ℝ f := by
          have hp : Differentiable ℝ (fun z : ℝ =>
              z - z ^ 3 / 3 + z ^ 5 / 5 - z ^ 7 / 7 + z ^ 9 / 9) := by
            fun_prop
          exact hp.sub Real.differentiable_arctan
        have hmono : MonotoneOn f (Set.Ici 0) := by
          apply monotoneOn_of_deriv_nonneg (convex_Ici 0)
          · exact hdiff.continuous.continuousOn
          · exact hdiff.differentiableOn
          · intro y _
            have h :=
              (((((hasDerivAt_id y).sub
                    (((hasDerivAt_id y).pow 3).div_const 3)).add
                  (((hasDerivAt_id y).pow 5).div_const 5)).sub
                (((hasDerivAt_id y).pow 7).div_const 7)).add
              (((hasDerivAt_id y).pow 9).div_const 9)).sub
                (Real.hasDerivAt_arctan y)
            have hfun :
                (((((id - fun q : ℝ => (id ^ 3) q / 3) +
                      fun q : ℝ => (id ^ 5) q / 5) -
                      fun q : ℝ => (id ^ 7) q / 7) +
                      fun q : ℝ => (id ^ 9) q / 9) -
                    Real.arctan) = f := by
              funext q
              rfl
            rw [← hfun, h.deriv]
            simp only [id_eq]
            norm_num
            rw [← sub_nonneg]
            have hden : (1 + y ^ 2) ≠ 0 := by positivity
            rw [show
                (1 - y ^ 2 + y ^ 4 - y ^ 6 + y ^ 8) -
                    (1 + y ^ 2)⁻¹ =
                  y ^ 10 / (1 + y ^ 2) by
              rw [inv_eq_one_div]
              field_simp [hden]
              ring]
            positivity
        have h := hmono (show (0 : ℝ) ∈ Set.Ici 0 by simp)
          (show (1 : ℝ) / 5 ∈ Set.Ici 0 by norm_num)
          (by norm_num : (0 : ℝ) ≤ 1 / 5)
        simpa [f] using h
      have hArctanFiveLower := arctanLowerBounds.1
      have hArctan239Upper :
          Real.arctan ((1 : ℝ) / 239) < (1 : ℝ) / 239 := by
        simpa [Real.tan_arctan] using
          Real.lt_tan
            ((Real.arctan_pos).2 (by norm_num : (0 : ℝ) < 1 / 239))
            (Real.arctan_lt_pi_div_two ((1 : ℝ) / 239))
      have hArctan239LowerCore := arctanLowerBounds.2
      have hCubicBelowSeventh :
          (1 : ℝ) / 239 - ((1 : ℝ) / 239) ^ 3 / 3 ≤
            (1 : ℝ) / 239 - ((1 : ℝ) / 239) ^ 3 / 3 +
                ((1 : ℝ) / 239) ^ 5 / 5 -
              ((1 : ℝ) / 239) ^ 7 / 7 := by
        norm_num
      have hArctan239Lower :
          (1 : ℝ) / 239 - ((1 : ℝ) / 239) ^ 3 / 3 ≤
            Real.arctan ((1 : ℝ) / 239) :=
        hCubicBelowSeventh.trans hArctan239LowerCore
      have hPiBounds := piBoundsFromMachinAndArctanBounds hMachin
        hArctanFiveLower hArctanFiveUpper hArctan239Lower hArctan239Upper
      have hPiLower : (3.1415 : ℝ) < Real.pi := hPiBounds.1
      have hPiUpper : Real.pi < (3.1416 : ℝ) := hPiBounds.2
      clear arctanLowerBounds hMachin hArctanFiveLower
        hArctanFiveUpper hArctan239LowerCore hCubicBelowSeventh
        hArctan239Lower hArctan239Upper
      have hPiSquareBounds :=
        piSquareBoundsFromPiBounds hPiUpper hPiLower
      have hPiSquareUpper :
          Real.pi ^ 2 < ((3927 : ℝ) / 1250) ^ 2 := hPiSquareBounds.1
      have hPiSquareLower :
          ((6283 : ℝ) / 2000) ^ 2 < Real.pi ^ 2 := hPiSquareBounds.2
      have haBounds :=
        aBoundsFromPiSquareBounds hPiSquareUpper hPiSquareLower
      have haGreaterRadius : r < a := haBounds.1
      have haLessOne : a < 1 := haBounds.2
    
      have hLongRootSign : 0 < 2 * d - a := by
        by_contra hNotLong
        have hShortRaw : 2 * d - a ≤ 0 := le_of_not_gt hNotLong
        have hShortSide : 2 * d ≤ a := by
          linarith only [hShortRaw]
        have hGap : r / 2 < a - d := by
          linarith only [haGreaterRadius, hShortSide]
        have hGapPos : 0 < a - d := by
          nlinarith only [hGap, hr]
        have hProductOne :
            r * (a - d) < d * (a - d) :=
          mul_lt_mul_of_pos_right hdGreaterRadius hGapPos
        have hrPos : 0 < r := by rw [hr]; norm_num
        have hProductTwo :
            r * (r / 2) < r * (a - d) :=
          mul_lt_mul_of_pos_left hGap hrPos
        have hProductFromQuadratic : d * (a - d) = r ^ 2 / 2 := by
          nlinarith only [hQuadratic]
        nlinarith only [hProductOne, hProductTwo, hProductFromQuadratic]
    
      have hCenterFormula :
          d = (a + Real.sqrt (a ^ 2 - 2 * r ^ 2)) / 2 := by
        exact centerFormulaFromLongRootSign hLongRootSign
      have hRodFormula :
          ell =
            (a + Real.sqrt (a ^ 2 - 2 * r ^ 2)) / 2 - r := by
        exact rodFormulaFromCenterFormula hCenterFormula
    
      let lowerCenter : ℝ := (19629 : ℝ) / 20000
      let upperCenter : ℝ := (19631 : ℝ) / 20000
      have hScaledQuadratic (x : ℝ) :
          Real.pi ^ 2 * (x ^ 2 - a * x + r ^ 2 / 2) =
            Real.pi ^ 2 * (x ^ 2 + r ^ 2 / 2) - (49 : ℝ) / 5 * x := by
        rw [← haTimesPiSquare]
        ring
      have hLowerQuadratic :
          lowerCenter ^ 2 - a * lowerCenter + r ^ 2 / 2 < 0 := by
        have hScaled :
            Real.pi ^ 2 *
                (lowerCenter ^ 2 - a * lowerCenter + r ^ 2 / 2) < 0 := by
          rw [hScaledQuadratic, hr]
          dsimp [lowerCenter]
          nlinarith only [hPiSquareUpper]
        by_contra hNotNegative
        have hNonnegative :
            0 ≤ lowerCenter ^ 2 - a * lowerCenter + r ^ 2 / 2 :=
          le_of_not_gt hNotNegative
        exact (not_le_of_gt hScaled)
          (mul_nonneg hPiSquarePos.le hNonnegative)
      have hUpperQuadratic :
          0 < upperCenter ^ 2 - a * upperCenter + r ^ 2 / 2 := by
        have hScaled :
            0 < Real.pi ^ 2 *
                (upperCenter ^ 2 - a * upperCenter + r ^ 2 / 2) := by
          rw [hScaledQuadratic, hr]
          dsimp [upperCenter]
          nlinarith only [hPiSquareLower]
        by_contra hNotPositive
        have hNonpositive :
            upperCenter ^ 2 - a * upperCenter + r ^ 2 / 2 ≤ 0 :=
          le_of_not_gt hNotPositive
        exact (not_le_of_gt hScaled)
          (mul_nonpos_of_nonneg_of_nonpos hPiSquarePos.le hNonpositive)
      have hLowerSecondFactor : 0 < d + lowerCenter - a := by
        dsimp [lowerCenter]
        linarith only [hLongRootSign, haLessOne]
      have hUpperSecondFactor : 0 < d + upperCenter - a := by
        dsimp [upperCenter]
        linarith only [hLongRootSign, haLessOne]
      have hCenterLower : lowerCenter < d := by
        have hDifference :
            0 <
              (d ^ 2 - a * d + r ^ 2 / 2) -
                (lowerCenter ^ 2 - a * lowerCenter + r ^ 2 / 2) := by
          linarith only [hQuadratic, hLowerQuadratic]
        have hFactor :
            0 < (d - lowerCenter) * (d + lowerCenter - a) := by
          calc
            0 <
                (d ^ 2 - a * d + r ^ 2 / 2) -
                  (lowerCenter ^ 2 - a * lowerCenter + r ^ 2 / 2) :=
              hDifference
            _ = (d - lowerCenter) * (d + lowerCenter - a) :=
              (quadraticDifferenceFactor lowerCenter).symm
        rcases (mul_pos_iff.mp hFactor) with hPositive | hNegative
        · exact sub_pos.mp hPositive.1
        · exact False.elim ((not_lt_of_ge hLowerSecondFactor.le) hNegative.2)
      have hCenterUpper : d < upperCenter := by
        have hDifference :
            (d ^ 2 - a * d + r ^ 2 / 2) -
                (upperCenter ^ 2 - a * upperCenter + r ^ 2 / 2) < 0 := by
          linarith only [hQuadratic, hUpperQuadratic]
        have hFactor :
            (d - upperCenter) * (d + upperCenter - a) < 0 := by
          calc
            (d - upperCenter) * (d + upperCenter - a) =
                (d ^ 2 - a * d + r ^ 2 / 2) -
                  (upperCenter ^ 2 - a * upperCenter + r ^ 2 / 2) :=
              quadraticDifferenceFactor upperCenter
            _ < 0 := hDifference
        rcases (mul_neg_iff.mp hFactor) with hImpossible | hNegative
        · exact False.elim ((not_lt_of_ge hUpperSecondFactor.le) hImpossible.2)
        · exact sub_neg.mp hNegative.1
      dsimp [lowerCenter] at hCenterLower
      dsimp [upperCenter] at hCenterUpper
      have hRodBounds :=
        rodBoundsFromCenterBounds hCenterLower hCenterUpper
      have hRodLower : (16629 : ℝ) / 20000 < ell := hRodBounds.1
      have hRodUpper : ell < (16631 : ℝ) / 20000 := hRodBounds.2
      have hDisplay := displayClaimsFromRodBounds hRodLower hRodUpper
      refine ⟨?_, ?_, hDisplay.1, hDisplay.2⟩
      · simpa [d, a, g, t, r] using hCenterFormula
      · simpa [ell, a, g, t, r] using hRodFormula

end PhyXMiniProblems.ProblemPhyXMini0276
