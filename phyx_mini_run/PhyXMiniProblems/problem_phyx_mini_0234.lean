import Mathlib.Analysis.Real.Sqrt
import Mathlib.Analysis.Asymptotics.AsymptoticEquivalent
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Physlib.Units.WithDim.Basic

/-!
# Period of a helium balloon tethered as an inverted pendulum

A light helium balloon is attached to a light string whose other end is fixed
to the ground.  Buoyancy makes the vertical configuration stable: after a
small angular displacement, the tangential component of buoyancy minus weight
restores the balloon toward equilibrium.

The source image is inconsistent with that verbal apparatus: it shows two
spheres between two vertical walls, two inclined string segments, a horizontal
string split into two parts labelled `L`, and a vertical separation labelled
`y`.  Those primary-image labels are retained below in a separate figure
readout.  They are not silently turned into laws of the stated ground-tethered
balloon.

All dimensional physical magnitudes are represented by Physlib
`Dimensionful` quantities.  Real numbers are used only for coherent SI
readouts, the dimensionless angular coordinate, oscillation amplitude, and
displayed answer values.  The exact nonlinear restoring torque and its
first-order small-angle model are deliberately distinct: the latter is tied to
the former by an explicit residual and a little-`o` statement at zero.
-/

noncomputable section

namespace PhyXMiniProblems.ProblemPhyXMini0234

open Dimension Filter

/-! ## Dimensionful quantities and coherent SI readouts -/

/-- A nonnegative physical length. -/
abbrev LengthQuantity : Type := Dimensionful (WithDim L𝓭 NNReal)

/-- A nonnegative physical time interval. -/
abbrev TimeQuantity : Type := Dimensionful (WithDim T𝓭 NNReal)

/-- A nonnegative physical volume, with dimension `length^3`. -/
abbrev VolumeQuantity : Type :=
  Dimensionful (WithDim (L𝓭 * L𝓭 * L𝓭) NNReal)

/-- A nonnegative physical mass. -/
abbrev MassQuantity : Type := Dimensionful (WithDim M𝓭 NNReal)

/-- A nonnegative mass density, with dimension `mass / length^3`. -/
abbrev MassDensityQuantity : Type :=
  Dimensionful
    (WithDim (M𝓭 * L𝓭⁻¹ * L𝓭⁻¹ * L𝓭⁻¹) NNReal)

/-- A nonnegative acceleration magnitude. -/
abbrev AccelerationQuantity : Type :=
  Dimensionful (WithDim (L𝓭 * T𝓭⁻¹ * T𝓭⁻¹) NNReal)

/-- A nonnegative force magnitude. -/
abbrev ForceQuantity : Type :=
  Dimensionful
    (WithDim (M𝓭 * L𝓭 * T𝓭⁻¹ * T𝓭⁻¹) NNReal)

/-- An angular frequency; radians are dimensionless. -/
abbrev AngularFrequencyQuantity : Type :=
  Dimensionful (WithDim T𝓭⁻¹ NNReal)

/-- A signed angular velocity. -/
abbrev AngularVelocityQuantity : Type :=
  Dimensionful (WithDim T𝓭⁻¹ ℝ)

/-- A signed angular acceleration. -/
abbrev AngularAccelerationQuantity : Type :=
  Dimensionful (WithDim (T𝓭⁻¹ * T𝓭⁻¹) ℝ)

/-- Read a nonnegative dimensionful quantity in coherent SI units. -/
def nonnegativeSIReadout {d : Dimension}
    (quantity : Dimensionful (WithDim d NNReal)) : ℝ :=
  ((quantity UnitChoices.SI).val : ℝ)

/-- Read a signed dimensionful quantity in coherent SI units. -/
def signedSIReadout {d : Dimension}
    (quantity : Dimensionful (WithDim d ℝ)) : ℝ :=
  (quantity UnitChoices.SI).val

/-- Metre readout of a physical length. -/
def lengthInMeters (length : LengthQuantity) : ℝ :=
  nonnegativeSIReadout length

/-- Second readout of a physical time interval. -/
def timeInSeconds (time : TimeQuantity) : ℝ :=
  nonnegativeSIReadout time

/-- Cubic-metre readout of a physical volume. -/
def volumeInCubicMeters (volume : VolumeQuantity) : ℝ :=
  nonnegativeSIReadout volume

/-- Kilogram readout of a physical mass. -/
def massInKilograms (mass : MassQuantity) : ℝ :=
  nonnegativeSIReadout mass

/-- Kilogram-per-cubic-metre readout of a mass density. -/
def densityInKilogramsPerCubicMeter
    (density : MassDensityQuantity) : ℝ :=
  nonnegativeSIReadout density

/-- Metre-per-second-squared readout of an acceleration magnitude. -/
def accelerationInMetersPerSecondSquared
    (acceleration : AccelerationQuantity) : ℝ :=
  nonnegativeSIReadout acceleration

/-- Newton readout of a force magnitude. -/
def forceInNewtons (force : ForceQuantity) : ℝ :=
  nonnegativeSIReadout force

/-- Radian-per-second readout of an angular frequency. -/
def angularFrequencyInRadiansPerSecond
    (frequency : AngularFrequencyQuantity) : ℝ :=
  nonnegativeSIReadout frequency

/-- Radian-per-second readout of a signed angular velocity. -/
def angularVelocityInRadiansPerSecond
    (velocity : AngularVelocityQuantity) : ℝ :=
  signedSIReadout velocity

/-- Radian-per-second-squared readout of a signed angular acceleration. -/
def angularAccelerationInRadiansPerSecondSquared
    (acceleration : AngularAccelerationQuantity) : ℝ :=
  signedSIReadout acceleration

/-! ## Verbal apparatus and primary-image labels -/

/-- Gas filling the light balloon. -/
inductive BalloonGas where
  | helium
  | other
  deriving DecidableEq, Repr

/-- Where the end of the tether opposite the balloon is fixed. -/
inductive TetherAnchor where
  | ground
  | other
  deriving DecidableEq, Repr

/-- Equilibrium orientation of the tethered balloon. -/
inductive PendulumOrientation where
  | invertedBalloonAboveAnchor
  | other
  deriving DecidableEq, Repr

/-- Idealization of the masses of the tether and balloon envelope. -/
inductive AuxiliaryMassModel where
  | negligible
  | retained
  deriving DecidableEq, Repr

/-- Interaction of the ambient air with the moving balloon. -/
inductive AirInteractionModel where
  | buoyancyOnlyNoDrag
  | includesOtherAerodynamicForces
  deriving DecidableEq, Repr

/-- Left and right sides explicitly distinguished in the supplied image. -/
inductive FigureSide where
  | left
  | right
  deriving DecidableEq, Repr

/-- Two spheres visible in the supplied image. -/
inductive FigureSphere where
  | upper
  | lower
  deriving DecidableEq, Repr

/-- Three string segments visible in the supplied image. -/
inductive FigureStringSegment where
  | leftInclined
  | rightInclined
  | horizontal
  deriving DecidableEq, Repr

/-- Qualitative components of the supplied image. -/
inductive SuppliedFigureComponent where
  | leftWall
  | rightWall
  | sphere (which : FigureSphere)
  | stringSegment (which : FigureStringSegment)
  deriving DecidableEq, Repr

/-!
Primary-image data.  The two horizontal half-spans carry the label `L`, while
the dashed vertical separation of the spheres carries the label `y`.
-/
structure SuppliedFigureReadout where
  visible : SuppliedFigureComponent → Prop
  horizontalHalfSpanLabelL : FigureSide → LengthQuantity
  verticalSeparationLabelY : LengthQuantity

/-!
The physical state of the stated balloon experiment.  The finite-amplitude
motion and the first-order small-oscillation model have separate acceleration,
frequency, and period data.  In particular, no period field is defined to have
the requested numerical value.
-/
structure BalloonPendulumSetup where
  gas : BalloonGas
  tetherAnchor : TetherAnchor
  equilibriumOrientation : PendulumOrientation
  stringMassModel : AuxiliaryMassModel
  balloonEnvelopeMassModel : AuxiliaryMassModel
  airInteraction : AirInteractionModel
  stringLength : LengthQuantity
  heliumDensity : MassDensityQuantity
  airDensity : MassDensityQuantity
  heliumVolume : VolumeQuantity
  displacedAirVolume : VolumeQuantity
  balloonInertialMass : MassQuantity
  gravitationalAcceleration : AccelerationQuantity
  buoyantForce : ForceQuantity
  heliumWeight : ForceQuantity
  netUpwardForce : ForceQuantity
  radialDistanceFromAnchor : TimeQuantity → LengthQuantity
  angularDisplacement : TimeQuantity → ℝ
  angularVelocity : TimeQuantity → AngularVelocityQuantity
  angularAcceleration : TimeQuantity → AngularAccelerationQuantity
  linearizedAngularAcceleration : TimeQuantity → AngularAccelerationQuantity
  releaseTime : TimeQuantity
  smallOscillationAngularFrequency : AngularFrequencyQuantity
  motionPeriod : TimeQuantity
  motionPeriodAtAmplitude : ℝ → TimeQuantity
  smallAmplitudeLimitPeriod : TimeQuantity
  suppliedFigure : SuppliedFigureReadout

/-! ## Scenario, figure/data readouts, and governing laws -/

/-!
Categorical assumptions in the verbal statement: a helium balloon and light
string are tethered to the ground, the light envelope is neglected, and air
exerts buoyancy but no drag or other aerodynamic force.
-/
def MatchesVerbalBalloonScenario (setup : BalloonPendulumSetup) : Prop :=
  setup.gas = .helium ∧
    setup.tetherAnchor = .ground ∧
    setup.equilibriumOrientation = .invertedBalloonAboveAnchor ∧
    setup.stringMassModel = .negligible ∧
    setup.balloonEnvelopeMassModel = .negligible ∧
    setup.airInteraction = .buoyancyOnlyNoDrag

/-!
Readout of the supplied image.  It deliberately records the visible two-wall,
two-sphere, three-segment geometry without asserting that this inconsistent
geometry governs the ground-tethered balloon dynamics.
-/
structure MatchesSuppliedFigure (setup : BalloonPendulumSetup) : Prop where
  leftWallVisible : setup.suppliedFigure.visible .leftWall
  rightWallVisible : setup.suppliedFigure.visible .rightWall
  upperSphereVisible : setup.suppliedFigure.visible (.sphere .upper)
  lowerSphereVisible : setup.suppliedFigure.visible (.sphere .lower)
  leftInclinedStringVisible :
    setup.suppliedFigure.visible (.stringSegment .leftInclined)
  rightInclinedStringVisible :
    setup.suppliedFigure.visible (.stringSegment .rightInclined)
  horizontalStringVisible :
    setup.suppliedFigure.visible (.stringSegment .horizontal)
  horizontalHalfSpansShareLabelL :
    setup.suppliedFigure.horizontalHalfSpanLabelL .left =
      setup.suppliedFigure.horizontalHalfSpanLabelL .right
  verticalLabelYPositive :
    0 < lengthInMeters setup.suppliedFigure.verticalSeparationLabelY

/-!
Numerical quantities printed in the problem: `L = 3.00 m`, helium density
`0.179 kg/m^3`, and air density `1.20 kg/m^3`.  The release conditions encode
a nonzero displacement and release from rest.  Rather than inventing a numeric
cutoff for the source's qualitative word "slightly", smallness is represented
below by the positive-amplitude limit and the little-`o` linearization.
-/
structure MatchesProblemData (setup : BalloonPendulumSetup) : Prop where
  stringLengthMeters : lengthInMeters setup.stringLength = 3
  heliumDensitySI :
    densityInKilogramsPerCubicMeter setup.heliumDensity = 179 / 1000
  airDensitySI :
    densityInKilogramsPerCubicMeter setup.airDensity = 6 / 5
  releaseDisplacementNonzero :
    0 < |setup.angularDisplacement setup.releaseTime|
  releasedFromRest :
    angularVelocityInRadiansPerSecond
        (setup.angularVelocity setup.releaseTime) = 0

/-!
The conventional terrestrial calibration `g = 9.8 m/s^2`, needed to select a
numerical answer choice.  It is separated from the quantities printed in the
problem statement.
-/
def UsesStandardGravity (setup : BalloonPendulumSetup) : Prop :=
  accelerationInMetersPerSecondSquared setup.gravitationalAcceleration =
    49 / 5

/-- Positivity and nondegeneracy assumptions for the physical experiment. -/
structure HasPhysicalBalloonParameters (setup : BalloonPendulumSetup) : Prop where
  stringLengthPositive : 0 < lengthInMeters setup.stringLength
  heliumDensityPositive :
    0 < densityInKilogramsPerCubicMeter setup.heliumDensity
  airDensityExceedsHeliumDensity :
    densityInKilogramsPerCubicMeter setup.heliumDensity <
      densityInKilogramsPerCubicMeter setup.airDensity
  heliumVolumePositive : 0 < volumeInCubicMeters setup.heliumVolume
  displacedVolumePositive :
    0 < volumeInCubicMeters setup.displacedAirVolume
  inertialMassPositive : 0 < massInKilograms setup.balloonInertialMass
  gravityPositive :
    0 < accelerationInMetersPerSecondSquared
      setup.gravitationalAcceleration
  buoyantForcePositive : 0 < forceInNewtons setup.buoyantForce
  heliumWeightPositive : 0 < forceInNewtons setup.heliumWeight
  netUpwardForcePositive : 0 < forceInNewtons setup.netUpwardForce
  smallOscillationAngularFrequencyPositive :
    0 < angularFrequencyInRadiansPerSecond
      setup.smallOscillationAngularFrequency
  motionPeriodPositive : 0 < timeInSeconds setup.motionPeriod
  smallAmplitudeLimitPeriodPositive :
    0 < timeInSeconds setup.smallAmplitudeLimitPeriod

/-!
Exact governing laws for the nonlinear balloon pendulum.

The first four fields are the light-envelope mass relation, equality of helium
and displaced-air volumes, Archimedes' buoyant force, and weight.  The net
upward force is their difference.  Crucially, the tangential Newton law retains
`sin theta`; it does not replace the nonlinear restoring torque by an exact
linear law.  The amplitude-indexed period family records the physical meaning
of the small-amplitude limit without assigning that limit a numerical value.
-/
structure SatisfiesBalloonPendulumLaws
    (setup : BalloonPendulumSetup) : Prop where
  lightEnvelopeMassLaw :
    massInKilograms setup.balloonInertialMass =
      densityInKilogramsPerCubicMeter setup.heliumDensity *
        volumeInCubicMeters setup.heliumVolume
  displacedVolumeLaw :
    volumeInCubicMeters setup.displacedAirVolume =
      volumeInCubicMeters setup.heliumVolume
  archimedesBuoyancyLaw :
    forceInNewtons setup.buoyantForce =
      densityInKilogramsPerCubicMeter setup.airDensity *
        volumeInCubicMeters setup.displacedAirVolume *
          accelerationInMetersPerSecondSquared
            setup.gravitationalAcceleration
  heliumWeightLaw :
    forceInNewtons setup.heliumWeight =
      massInKilograms setup.balloonInertialMass *
        accelerationInMetersPerSecondSquared
          setup.gravitationalAcceleration
  netUpwardForceLaw :
    forceInNewtons setup.netUpwardForce =
      forceInNewtons setup.buoyantForce -
        forceInNewtons setup.heliumWeight
  tautStringConstraint :
    ∀ time,
      lengthInMeters (setup.radialDistanceFromAnchor time) =
        lengthInMeters setup.stringLength
  exactTangentialNewtonLaw :
    ∀ time,
      massInKilograms setup.balloonInertialMass *
          lengthInMeters setup.stringLength *
            angularAccelerationInRadiansPerSecondSquared
              (setup.angularAcceleration time) =
        -(forceInNewtons setup.netUpwardForce) *
          Real.sin (setup.angularDisplacement time)
  releasePeriodIsAmplitudeIndexedPeriod :
    setup.motionPeriod =
      setup.motionPeriodAtAmplitude
        |setup.angularDisplacement setup.releaseTime|
  smallAmplitudePeriodLimit :
    Tendsto
      (fun amplitude : ℝ =>
        timeInSeconds (setup.motionPeriodAtAmplitude amplitude))
      (nhdsWithin 0 (Set.Ioi 0))
      (nhds (timeInSeconds setup.smallAmplitudeLimitPeriod))

/-!
The mathematical first-order contract behind `sin theta ≈ theta`.  This is a
local asymptotic statement at `theta = 0`, not a global equality.  It can be
proved from `Real.hasDerivAt_sin` (or strengthened quantitatively using
`Real.sin_bound`).
-/
theorem sine_sub_id_isLittleO_at_zero :
    Asymptotics.IsLittleO (nhds 0)
      (fun angle : ℝ => Real.sin angle - angle)
      (fun angle : ℝ => angle) := by
  rw [Asymptotics.isLittleO_iff]
  intro c hc
  rw [Metric.eventually_nhds_iff]
  refine ⟨min 1 c, lt_min zero_lt_one hc, ?_⟩
  intro x hx
  have hxabs : |x| < min 1 c := by
    simpa [Real.dist_eq] using hx
  have hxone : |x| ≤ 1 :=
    le_trans hxabs.le (min_le_left _ _)
  have hxc : |x| ≤ c :=
    le_trans hxabs.le (min_le_right _ _)
  have hsin := Real.sin_bound hxone
  change |Real.sin x - x| ≤ c * |x|
  calc
    |Real.sin x - x| =
        |(Real.sin x - (x - x ^ 3 / 6)) - x ^ 3 / 6| := by
          congr 1
          all_goals ring
    _ ≤ |Real.sin x - (x - x ^ 3 / 6)| + |x ^ 3 / 6| :=
      abs_sub _ _
    _ ≤ |x| ^ 4 * (5 / 96) + |x| ^ 3 / 6 := by
      rw [abs_div, abs_pow]
      norm_num
      linarith
    _ ≤ c * |x| := by
      have hxa : 0 ≤ |x| := abs_nonneg x
      have hx_sq : |x| ^ 2 ≤ |x| := by
        nlinarith
      have hx_cube : |x| ^ 3 ≤ |x| ^ 2 := by
        nlinarith [
          mul_nonneg (sq_nonneg |x|) (sub_nonneg.mpr hxone)]
      have hx_fourth : |x| ^ 4 ≤ |x| ^ 2 := by
        nlinarith [sq_nonneg (|x| ^ 2 - |x|)]
      have hx_sq_c : |x| ^ 2 ≤ c * |x| := by
        nlinarith
      nlinarith

/-!
Laws of the separate first-order small-oscillation model.

The first two equations are exact statements about the *linearized surrogate*,
not about the nonlinear acceleration above.  The residual identity explicitly
connects the surrogate to the exact sine dynamics.  Combined with
`sine_sub_id_isLittleO_at_zero`, it says that the omitted restoring-torque term
is lower order than the retained term as the angular amplitude tends to zero.
The period-frequency relation is the generic phase relation for the surrogate.
None of these fields contains the requested density formula or answer choice.
-/
structure SatisfiesFirstOrderSmallOscillationModel
    (setup : BalloonPendulumSetup) : Prop where
  linearizedTangentialNewtonLaw :
    ∀ time,
      massInKilograms setup.balloonInertialMass *
          lengthInMeters setup.stringLength *
            angularAccelerationInRadiansPerSecondSquared
              (setup.linearizedAngularAcceleration time) =
        -(forceInNewtons setup.netUpwardForce) *
          setup.angularDisplacement time
  linearizedHarmonicAccelerationLaw :
    ∀ time,
      angularAccelerationInRadiansPerSecondSquared
          (setup.linearizedAngularAcceleration time) =
        -(angularFrequencyInRadiansPerSecond
            setup.smallOscillationAngularFrequency) ^ 2 *
          setup.angularDisplacement time
  exactLinearizationResidual :
    ∀ time,
      massInKilograms setup.balloonInertialMass *
          lengthInMeters setup.stringLength *
            (angularAccelerationInRadiansPerSecondSquared
                (setup.angularAcceleration time) -
              angularAccelerationInRadiansPerSecondSquared
                (setup.linearizedAngularAcceleration time)) =
        -(forceInNewtons setup.netUpwardForce) *
          (Real.sin (setup.angularDisplacement time) -
            setup.angularDisplacement time)
  smallOscillationPeriodFrequencyRelation :
    timeInSeconds setup.smallAmplitudeLimitPeriod *
        angularFrequencyInRadiansPerSecond
          setup.smallOscillationAngularFrequency =
      2 * Real.pi

/-! ## Derived period and displayed answer -/

/-!
The physical laws imply the effective small-oscillation angular frequency.
This relation is derived by comparing the two acceleration laws at the
nonzero release displacement and eliminating mass, volume, buoyancy, and
weight.
-/
lemma smallOscillationAngularFrequency_sq
    (setup : BalloonPendulumSetup)
    (_data : MatchesProblemData setup)
    (_physical : HasPhysicalBalloonParameters setup)
    (_laws : SatisfiesBalloonPendulumLaws setup)
    (_linearization : SatisfiesFirstOrderSmallOscillationModel setup) :
    angularFrequencyInRadiansPerSecond
        setup.smallOscillationAngularFrequency ^ 2 =
      accelerationInMetersPerSecondSquared
          setup.gravitationalAcceleration *
        (densityInKilogramsPerCubicMeter setup.airDensity -
          densityInKilogramsPerCubicMeter setup.heliumDensity) /
        (lengthInMeters setup.stringLength *
          densityInKilogramsPerCubicMeter setup.heliumDensity) := by
  have hθ : setup.angularDisplacement setup.releaseTime ≠ 0 := by
    exact abs_pos.mp _data.releaseDisplacementNonzero
  have hlin :=
    _linearization.linearizedTangentialNewtonLaw setup.releaseTime
  rw [_linearization.linearizedHarmonicAccelerationLaw
    setup.releaseTime] at hlin
  have hfact :
      (massInKilograms setup.balloonInertialMass *
            lengthInMeters setup.stringLength *
            angularFrequencyInRadiansPerSecond
              setup.smallOscillationAngularFrequency ^ 2 -
          forceInNewtons setup.netUpwardForce) *
        setup.angularDisplacement setup.releaseTime = 0 := by
    nlinarith [hlin]
  have hfrequency_force :
      massInKilograms setup.balloonInertialMass *
            lengthInMeters setup.stringLength *
            angularFrequencyInRadiansPerSecond
              setup.smallOscillationAngularFrequency ^ 2 =
        forceInNewtons setup.netUpwardForce := by
    have hz := (mul_eq_zero.mp hfact).resolve_right hθ
    linarith
  rw [_laws.netUpwardForceLaw, _laws.archimedesBuoyancyLaw,
      _laws.displacedVolumeLaw, _laws.heliumWeightLaw,
      _laws.lightEnvelopeMassLaw] at hfrequency_force
  have hV : volumeInCubicMeters setup.heliumVolume ≠ 0 :=
    ne_of_gt _physical.heliumVolumePositive
  have hcore :
      densityInKilogramsPerCubicMeter setup.heliumDensity *
            lengthInMeters setup.stringLength *
            angularFrequencyInRadiansPerSecond
              setup.smallOscillationAngularFrequency ^ 2 =
        accelerationInMetersPerSecondSquared
            setup.gravitationalAcceleration *
          (densityInKilogramsPerCubicMeter setup.airDensity -
            densityInKilogramsPerCubicMeter setup.heliumDensity) := by
    apply (mul_left_cancel₀ hV)
    nlinarith [hfrequency_force]
  have hden :
      lengthInMeters setup.stringLength *
          densityInKilogramsPerCubicMeter setup.heliumDensity ≠ 0 :=
    mul_ne_zero (ne_of_gt _physical.stringLengthPositive)
      (ne_of_gt _physical.heliumDensityPositive)
  apply (eq_div_iff hden).2
  nlinarith [hcore]

/-!
Period formula predicted by the first-order, small-amplitude model,

`T = 2 pi sqrt (L rho_He / (g (rho_air - rho_He)))`.

This is an equality for `smallAmplitudeLimitPeriod`, whose relation to the
nonlinear finite-amplitude period is the limit law above.  It is not asserted
as an exact finite-amplitude period formula.
-/
lemma balloonSmallAmplitudeLimitPeriod_formula
    (setup : BalloonPendulumSetup)
    (_scenario : MatchesVerbalBalloonScenario setup)
    (_figure : MatchesSuppliedFigure setup)
    (_data : MatchesProblemData setup)
    (_physical : HasPhysicalBalloonParameters setup)
    (_laws : SatisfiesBalloonPendulumLaws setup)
    (_linearization : SatisfiesFirstOrderSmallOscillationModel setup) :
    timeInSeconds setup.smallAmplitudeLimitPeriod =
      2 * Real.pi *
        Real.sqrt
          (lengthInMeters setup.stringLength *
              densityInKilogramsPerCubicMeter setup.heliumDensity /
            (accelerationInMetersPerSecondSquared
                setup.gravitationalAcceleration *
              (densityInKilogramsPerCubicMeter setup.airDensity -
                densityInKilogramsPerCubicMeter setup.heliumDensity))) := by
  have hωpos :
      0 < angularFrequencyInRadiansPerSecond
        setup.smallOscillationAngularFrequency :=
    _physical.smallOscillationAngularFrequencyPositive
  have hLpos : 0 < lengthInMeters setup.stringLength :=
    _physical.stringLengthPositive
  have hρpos :
      0 < densityInKilogramsPerCubicMeter setup.heliumDensity :=
    _physical.heliumDensityPositive
  have hdiffpos :
      0 < densityInKilogramsPerCubicMeter setup.airDensity -
        densityInKilogramsPerCubicMeter setup.heliumDensity :=
    sub_pos.mpr _physical.airDensityExceedsHeliumDensity
  have hgpos :
      0 < accelerationInMetersPerSecondSquared
        setup.gravitationalAcceleration :=
    _physical.gravityPositive
  have hradpos :
      0 < lengthInMeters setup.stringLength *
            densityInKilogramsPerCubicMeter setup.heliumDensity /
          (accelerationInMetersPerSecondSquared
              setup.gravitationalAcceleration *
            (densityInKilogramsPerCubicMeter setup.airDensity -
              densityInKilogramsPerCubicMeter setup.heliumDensity)) :=
    div_pos (mul_pos hLpos hρpos) (mul_pos hgpos hdiffpos)
  have hfreq :=
    smallOscillationAngularFrequency_sq setup _data _physical _laws
      _linearization
  have hrad_freq :
      (lengthInMeters setup.stringLength *
            densityInKilogramsPerCubicMeter setup.heliumDensity /
          (accelerationInMetersPerSecondSquared
              setup.gravitationalAcceleration *
            (densityInKilogramsPerCubicMeter setup.airDensity -
              densityInKilogramsPerCubicMeter setup.heliumDensity))) *
        angularFrequencyInRadiansPerSecond
            setup.smallOscillationAngularFrequency ^ 2 = 1 := by
    rw [hfreq]
    field_simp
  have hsqrt_freq_sq :
      (Real.sqrt
            (lengthInMeters setup.stringLength *
                densityInKilogramsPerCubicMeter setup.heliumDensity /
              (accelerationInMetersPerSecondSquared
                  setup.gravitationalAcceleration *
                (densityInKilogramsPerCubicMeter setup.airDensity -
                  densityInKilogramsPerCubicMeter
                    setup.heliumDensity))) *
          angularFrequencyInRadiansPerSecond
            setup.smallOscillationAngularFrequency) ^ 2 = 1 := by
    rw [mul_pow, Real.sq_sqrt hradpos.le]
    exact hrad_freq
  have hsqrt_freq :
      Real.sqrt
            (lengthInMeters setup.stringLength *
                densityInKilogramsPerCubicMeter setup.heliumDensity /
              (accelerationInMetersPerSecondSquared
                  setup.gravitationalAcceleration *
                (densityInKilogramsPerCubicMeter setup.airDensity -
                  densityInKilogramsPerCubicMeter
                    setup.heliumDensity))) *
          angularFrequencyInRadiansPerSecond
            setup.smallOscillationAngularFrequency = 1 := by
    have hsqrt_nonneg := Real.sqrt_nonneg
      (lengthInMeters setup.stringLength *
        densityInKilogramsPerCubicMeter setup.heliumDensity /
        (accelerationInMetersPerSecondSquared
            setup.gravitationalAcceleration *
          (densityInKilogramsPerCubicMeter setup.airDensity -
            densityInKilogramsPerCubicMeter setup.heliumDensity)))
    nlinarith [mul_nonneg hsqrt_nonneg hωpos.le]
  apply (mul_right_cancel₀ (ne_of_gt hωpos))
  rw [_linearization.smallOscillationPeriodFrequencyRelation]
  nlinarith [Real.pi_pos]

/-- Labels of the four period choices printed in the problem. -/
inductive AnswerChoice where
  | A
  | B
  | C
  | D
  deriving DecidableEq, Repr

/-- Displayed period, in seconds, associated with each answer label. -/
def answerChoiceInSeconds : AnswerChoice → ℝ
  | .A => 44 / 25
  | .B => 83 / 50
  | .C => 39 / 25
  | .D => 73 / 50

/-- A real value rounds to `rounded` at the nearest hundredth of a second. -/
def RoundsToNearestHundredth (value rounded : ℝ) : Prop :=
  |value - rounded| < 1 / 200

/-!
With `g = 9.8 m/s^2`, the derived small-amplitude limiting period is
approximately `1.4556 s`, hence rounds to `1.46 s`, answer choice D.  The
source's phrase "displaced slightly" is thus formalized as a first-order
answer-choice prediction rather than a global exact claim about every finite
amplitude.

This is the current target corresponding to blueprint label
`thm:physics:phyx_mini_0234:target`.
-/
theorem balloonMotionPeriod_is_answer_D
    (setup : BalloonPendulumSetup)
    (_scenario : MatchesVerbalBalloonScenario setup)
    (_figure : MatchesSuppliedFigure setup)
    (_data : MatchesProblemData setup)
    (_gravity : UsesStandardGravity setup)
    (_physical : HasPhysicalBalloonParameters setup)
    (_laws : SatisfiesBalloonPendulumLaws setup)
    (_linearization : SatisfiesFirstOrderSmallOscillationModel setup) :
    RoundsToNearestHundredth
      (timeInSeconds setup.smallAmplitudeLimitPeriod)
      (answerChoiceInSeconds .D) := by
  have doubleCosBounds (x lower upper : ℝ)
      (hlower : 0 ≤ lower)
      (hcos : lower ≤ Real.cos x ∧ Real.cos x ≤ upper) :
      2 * lower ^ 2 - 1 ≤ Real.cos (2 * x) ∧
        Real.cos (2 * x) ≤ 2 * upper ^ 2 - 1 := by
    rw [Real.cos_two_mul]
    constructor
    · nlinarith [mul_self_le_mul_self hlower hcos.1]
    · have hcos_nonneg : 0 ≤ Real.cos x :=
        le_trans hlower hcos.1
      nlinarith [mul_self_le_mul_self hcos_nonneg hcos.2]
  have hcos_pi_lower : 0 < Real.cos (3141 / 2000 : ℝ) := by
    let x0 : ℝ := 3141 / 128000
    let x1 : ℝ := 2 * x0
    let x2 : ℝ := 2 * x1
    let x3 : ℝ := 2 * x2
    let x4 : ℝ := 2 * x3
    let x5 : ℝ := 2 * x4
    let x6 : ℝ := 2 * x5
    let lower0 : ℝ := 1 - x0 ^ 2 / 2 - x0 ^ 4 * (5 / 96)
    let upper0 : ℝ := 1 - x0 ^ 2 / 2 + x0 ^ 4 * (5 / 96)
    let lower1 : ℝ := 2 * lower0 ^ 2 - 1
    let upper1 : ℝ := 2 * upper0 ^ 2 - 1
    let lower2 : ℝ := 2 * lower1 ^ 2 - 1
    let upper2 : ℝ := 2 * upper1 ^ 2 - 1
    let lower3 : ℝ := 2 * lower2 ^ 2 - 1
    let upper3 : ℝ := 2 * upper2 ^ 2 - 1
    let lower4 : ℝ := 2 * lower3 ^ 2 - 1
    let upper4 : ℝ := 2 * upper3 ^ 2 - 1
    let lower5 : ℝ := 2 * lower4 ^ 2 - 1
    let upper5 : ℝ := 2 * upper4 ^ 2 - 1
    let lower6 : ℝ := 2 * lower5 ^ 2 - 1
    let upper6 : ℝ := 2 * upper5 ^ 2 - 1
    have hbound := Real.cos_bound (x := x0)
      (by norm_num [x0] : |x0| ≤ 1)
    rw [abs_le] at hbound
    have h0 : lower0 ≤ Real.cos x0 ∧ Real.cos x0 ≤ upper0 := by
      dsimp [lower0, upper0]
      constructor <;> linarith [hbound.1, hbound.2]
    have h1 : lower1 ≤ Real.cos x1 ∧ Real.cos x1 ≤ upper1 := by
      exact doubleCosBounds x0 lower0 upper0
        (by norm_num [lower0, x0]) h0
    have h2 : lower2 ≤ Real.cos x2 ∧ Real.cos x2 ≤ upper2 := by
      exact doubleCosBounds x1 lower1 upper1
        (by norm_num [lower1, lower0, x0]) h1
    have h3 : lower3 ≤ Real.cos x3 ∧ Real.cos x3 ≤ upper3 := by
      exact doubleCosBounds x2 lower2 upper2
        (by norm_num [lower2, lower1, lower0, x0]) h2
    have h4 : lower4 ≤ Real.cos x4 ∧ Real.cos x4 ≤ upper4 := by
      exact doubleCosBounds x3 lower3 upper3
        (by norm_num [lower3, lower2, lower1, lower0, x0]) h3
    have h5 : lower5 ≤ Real.cos x5 ∧ Real.cos x5 ≤ upper5 := by
      exact doubleCosBounds x4 lower4 upper4
        (by
          norm_num [lower4, lower3, lower2, lower1, lower0, x0]) h4
    have h6 : lower6 ≤ Real.cos x6 ∧ Real.cos x6 ≤ upper6 := by
      exact doubleCosBounds x5 lower5 upper5
        (by
          norm_num [lower5, lower4, lower3, lower2, lower1, lower0,
            x0]) h5
    have hlower6 : 0 < lower6 := by
      norm_num [lower6, lower5, lower4, lower3, lower2, lower1,
        lower0, x0]
    have hx6 : x6 = 3141 / 2000 := by
      norm_num [x6, x5, x4, x3, x2, x1, x0]
    rw [← hx6]
    exact lt_of_lt_of_le hlower6 h6.1
  have hpi_lower : (3141 / 1000 : ℝ) < Real.pi := by
    by_contra hnot
    have hpile : Real.pi ≤ 3141 / 1000 := le_of_not_gt hnot
    rcases hpile.eq_or_lt with heq | hlt
    · have hhalf : (3141 / 2000 : ℝ) = Real.pi / 2 := by
        nlinarith
      rw [hhalf, Real.cos_pi_div_two] at hcos_pi_lower
      linarith
    · have hpi_mem : Real.pi / 2 ∈ Set.Icc (0 : ℝ) Real.pi := by
        constructor <;> nlinarith [Real.pi_pos]
      have hrat_mem :
          (3141 / 2000 : ℝ) ∈ Set.Icc (0 : ℝ) Real.pi := by
        constructor
        · norm_num
        · nlinarith [Real.two_le_pi]
      have hanti := Real.strictAntiOn_cos hpi_mem hrat_mem
        (by nlinarith)
      rw [Real.cos_pi_div_two] at hanti
      linarith
  have hcos_pi_upper : Real.cos (1571 / 1000 : ℝ) < 0 := by
    let x0 : ℝ := 1571 / 64000
    let x1 : ℝ := 2 * x0
    let x2 : ℝ := 2 * x1
    let x3 : ℝ := 2 * x2
    let x4 : ℝ := 2 * x3
    let x5 : ℝ := 2 * x4
    let x6 : ℝ := 2 * x5
    let lower0 : ℝ := 1 - x0 ^ 2 / 2 - x0 ^ 4 * (5 / 96)
    let upper0 : ℝ := 1 - x0 ^ 2 / 2 + x0 ^ 4 * (5 / 96)
    let lower1 : ℝ := 2 * lower0 ^ 2 - 1
    let upper1 : ℝ := 2 * upper0 ^ 2 - 1
    let lower2 : ℝ := 2 * lower1 ^ 2 - 1
    let upper2 : ℝ := 2 * upper1 ^ 2 - 1
    let lower3 : ℝ := 2 * lower2 ^ 2 - 1
    let upper3 : ℝ := 2 * upper2 ^ 2 - 1
    let lower4 : ℝ := 2 * lower3 ^ 2 - 1
    let upper4 : ℝ := 2 * upper3 ^ 2 - 1
    let lower5 : ℝ := 2 * lower4 ^ 2 - 1
    let upper5 : ℝ := 2 * upper4 ^ 2 - 1
    let lower6 : ℝ := 2 * lower5 ^ 2 - 1
    let upper6 : ℝ := 2 * upper5 ^ 2 - 1
    have hbound := Real.cos_bound (x := x0)
      (by norm_num [x0] : |x0| ≤ 1)
    rw [abs_le] at hbound
    have h0 : lower0 ≤ Real.cos x0 ∧ Real.cos x0 ≤ upper0 := by
      dsimp [lower0, upper0]
      constructor <;> linarith [hbound.1, hbound.2]
    have h1 : lower1 ≤ Real.cos x1 ∧ Real.cos x1 ≤ upper1 := by
      exact doubleCosBounds x0 lower0 upper0
        (by norm_num [lower0, x0]) h0
    have h2 : lower2 ≤ Real.cos x2 ∧ Real.cos x2 ≤ upper2 := by
      exact doubleCosBounds x1 lower1 upper1
        (by norm_num [lower1, lower0, x0]) h1
    have h3 : lower3 ≤ Real.cos x3 ∧ Real.cos x3 ≤ upper3 := by
      exact doubleCosBounds x2 lower2 upper2
        (by norm_num [lower2, lower1, lower0, x0]) h2
    have h4 : lower4 ≤ Real.cos x4 ∧ Real.cos x4 ≤ upper4 := by
      exact doubleCosBounds x3 lower3 upper3
        (by norm_num [lower3, lower2, lower1, lower0, x0]) h3
    have h5 : lower5 ≤ Real.cos x5 ∧ Real.cos x5 ≤ upper5 := by
      exact doubleCosBounds x4 lower4 upper4
        (by
          norm_num [lower4, lower3, lower2, lower1, lower0, x0]) h4
    have h6 : lower6 ≤ Real.cos x6 ∧ Real.cos x6 ≤ upper6 := by
      exact doubleCosBounds x5 lower5 upper5
        (by
          norm_num [lower5, lower4, lower3, lower2, lower1, lower0,
            x0]) h5
    have hupper6 : upper6 < 0 := by
      norm_num [upper6, upper5, upper4, upper3, upper2, upper1,
        upper0, x0]
    have hx6 : x6 = 1571 / 1000 := by
      norm_num [x6, x5, x4, x3, x2, x1, x0]
    rw [← hx6]
    exact lt_of_le_of_lt h6.2 hupper6
  have hpi_upper : Real.pi < (1571 / 500 : ℝ) := by
    by_contra hnot
    have hlepi : (1571 / 500 : ℝ) ≤ Real.pi := le_of_not_gt hnot
    rcases hlepi.eq_or_lt with heq | hlt
    · have hhalf : (1571 / 1000 : ℝ) = Real.pi / 2 := by
        nlinarith
      rw [hhalf, Real.cos_pi_div_two] at hcos_pi_upper
      linarith
    · have hrat_mem :
          (1571 / 1000 : ℝ) ∈ Set.Icc (0 : ℝ) Real.pi := by
        constructor
        · norm_num
        · nlinarith [Real.two_le_pi]
      have hpi_mem : Real.pi / 2 ∈ Set.Icc (0 : ℝ) Real.pi := by
        constructor <;> nlinarith [Real.pi_pos]
      have hanti := Real.strictAntiOn_cos hrat_mem hpi_mem
        (by nlinarith)
      rw [Real.cos_pi_div_two] at hanti
      linarith
  have hsqrt_lower :
      (4633 / 20000 : ℝ) < Real.sqrt (2685 / 50029) := by
    rw [Real.lt_sqrt (by norm_num : (0 : ℝ) ≤ 4633 / 20000)]
    norm_num
  have hsqrt_upper :
      Real.sqrt (2685 / 50029) < (233 / 1000 : ℝ) := by
    rw [Real.sqrt_lt' (by norm_num : (0 : ℝ) < 233 / 1000)]
    norm_num
  have hprod_lower :
      (3141 / 1000 : ℝ) * (4633 / 20000) <
        Real.pi * Real.sqrt (2685 / 50029) :=
    mul_lt_mul'' hpi_lower hsqrt_lower (by norm_num) (by norm_num)
  have hprod_upper :
      Real.pi * Real.sqrt (2685 / 50029) <
        (1571 / 500 : ℝ) * (233 / 1000) :=
    mul_lt_mul'' hpi_upper hsqrt_upper Real.pi_pos.le
      (Real.sqrt_nonneg _)
  simp only [RoundsToNearestHundredth, answerChoiceInSeconds]
  rw [balloonSmallAmplitudeLimitPeriod_formula setup _scenario _figure
    _data _physical _laws _linearization]
  rw [_data.stringLengthMeters, _data.heliumDensitySI,
    _data.airDensitySI, _gravity]
  have hrad :
      (3 : ℝ) * (179 / 1000) /
          (49 / 5 * (6 / 5 - 179 / 1000)) =
        2685 / 50029 := by
    norm_num
  rw [hrad, abs_lt]
  constructor <;> nlinarith

end PhyXMiniProblems.ProblemPhyXMini0234
