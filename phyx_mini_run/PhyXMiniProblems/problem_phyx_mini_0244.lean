import Mathlib
import Physlib.Units.WithDim.Speed

noncomputable section

namespace PhyXMiniProblems.ProblemPhyXMini0244

open Dimension NNReal

/-!
# Tension in a rapidly rolling circular chain loop

A uniform chain forms a circular loop in a vertical plane and rolls to the
right on horizontal ground with center-of-mass speed `v₀`.  The supplied image
also shows a small ground feature labelled “Bump” ahead of the loop.  In the
high-speed regime the individual-link weight is neglected relative to the
chain tension.

The quantities below are unit-independent Physlib quantities.  Real numbers
occur only as coherent scalar readouts.  The governing laws distinguish the
center-of-mass speed, the material circulation speed, and the transverse-wave
speed, so the requested relation `T = μ v₀²` is not placed in the assumptions.
-/

/-! ## Dimensionful quantities and coherent readouts -/

/-- The physical radius of the circular chain loop. -/
abbrev ChainRadius : Type :=
  Dimensionful (WithDim L𝓭 ℝ≥0)

/-- Uniform chain mass per unit arc length, with dimension `mass / length`. -/
abbrev LinearMassDensity : Type :=
  Dimensionful (WithDim (M𝓭 * L𝓭⁻¹) ℝ≥0)

/-- Angular speed of the rolling loop, with dimension `1 / time`. -/
abbrev AngularSpeed : Type :=
  Dimensionful (WithDim T𝓭⁻¹ ℝ≥0)

/-- A force magnitude, used for both tension and individual-link weight. -/
abbrev ForceMagnitude : Type :=
  Dimensionful (WithDim (M𝓭 * L𝓭 * T𝓭⁻¹ * T𝓭⁻¹) ℝ≥0)

/-- Scalar radius readout in a selected coherent unit system. -/
def radiusReadout (units : UnitChoices) (radius : ChainRadius) : ℝ :=
  (radius units).val

/-- Scalar linear-mass-density readout in a selected coherent unit system. -/
def linearMassDensityReadout
    (units : UnitChoices) (density : LinearMassDensity) : ℝ :=
  (density units).val

/-- Scalar speed readout in a selected coherent unit system. -/
def speedReadout (units : UnitChoices) (speed : DimSpeed) : ℝ :=
  (speed units).val

/-- Scalar angular-speed readout in a selected coherent unit system. -/
def angularSpeedReadout
    (units : UnitChoices) (angularSpeed : AngularSpeed) : ℝ :=
  (angularSpeed units).val

/-- Scalar force readout in a selected coherent unit system. -/
def forceReadout (units : UnitChoices) (force : ForceMagnitude) : ℝ :=
  (force units).val

/-! ## Physical roles and primary-figure labels -/

/-- Horizontal direction of the velocity arrow drawn in the figure. -/
inductive HorizontalDirection where
  | left
  | right
  deriving DecidableEq, Repr

/-- Shape of the chain's visible centerline in the primary image. -/
inductive LoopProfile where
  | circular
  deriving DecidableEq, Repr

/-- Orientation of the supporting surface drawn below the chain. -/
inductive SupportingSurfaceOrientation where
  | horizontal
  deriving DecidableEq, Repr

/-- Text label attached to the small protrusion on the ground. -/
inductive GroundFeatureLabel where
  | bump
  deriving DecidableEq, Repr

/-- The dynamical regime described in the problem statement. -/
inductive ChainMotionRegime where
  | highSpeedRollingWithoutCollapse
  deriving DecidableEq, Repr

/-- Whether a force term is retained in, or idealized out of, the model. -/
inductive ForceTermTreatment where
  | retained
  | neglectedRelativeToTension
  deriving DecidableEq, Repr

/-!
Qualitative information read from the supplied bitmap.  The image gives no
numerical radius, bump size, or separation, so none is invented here.
-/
structure RollingChainFigure where
  velocityArrowDirection : HorizontalDirection
  loopProfile : LoopProfile
  loopLiesInVerticalPlane : Prop
  supportingSurfaceOrientation : SupportingSurfaceOrientation
  loopTangentToSupportingSurface : Prop
  groundFeatureLabel : GroundFeatureLabel
  groundFeatureLiesAheadOfLoop : Prop

/-! ## Setup and assumptions -/

/-!
The physical quantities in the rolling-chain experiment.  The single field
`uniformLinearMassDensity` is the constant density `μ` of the uniform chain.
The three speed fields have distinct roles:

* `centerOfMassSpeed` is the magnitude `v₀` printed next to the red arrow;
* `materialCirculationSpeed` is a link's speed around the loop relative to its
  center;
* `transverseWaveSpeed` is the propagation speed of a transverse disturbance
  in the tensioned chain.

No field defines tension from any of these quantities.
-/
structure RollingChainSetup where
  loopRadius : ChainRadius
  uniformLinearMassDensity : LinearMassDensity
  centerOfMassSpeed : DimSpeed
  materialCirculationSpeed : DimSpeed
  transverseWaveSpeed : DimSpeed
  loopAngularSpeed : AngularSpeed
  chainTension : ForceMagnitude
  individualLinkWeight : ForceMagnitude
  motionRegime : ChainMotionRegime
  linkWeightTreatment : ForceTermTreatment
  figure : RollingChainFigure

/-- Prose assumptions, including the explicitly stated high-speed idealization. -/
structure MatchesProblemStatement (setup : RollingChainSetup) : Prop where
  highSpeedStableRolling :
    setup.motionRegime = .highSpeedRollingWithoutCollapse
  individualLinkWeightIsNeglected :
    setup.linkWeightTreatment = .neglectedRelativeToTension

/-- Qualitative geometry and labels visible in the primary image. -/
structure MatchesSuppliedFigure (setup : RollingChainSetup) : Prop where
  velocityArrowPointsRight :
    setup.figure.velocityArrowDirection = .right
  chainIsDrawnCircular : setup.figure.loopProfile = .circular
  chainLoopIsVertical : setup.figure.loopLiesInVerticalPlane
  surfaceIsHorizontal :
    setup.figure.supportingSurfaceOrientation = .horizontal
  chainTouchesGround : setup.figure.loopTangentToSupportingSurface
  protrusionIsLabelledBump : setup.figure.groundFeatureLabel = .bump
  bumpIsAhead : setup.figure.groundFeatureLiesAheadOfLoop

/-- Positivity and nondegeneracy conditions for the high-speed rolling regime. -/
structure HasPhysicalRollingParameters (setup : RollingChainSetup) : Prop where
  radiusPositive :
    ∀ units : UnitChoices, 0 < radiusReadout units setup.loopRadius
  densityPositive :
    ∀ units : UnitChoices,
      0 < linearMassDensityReadout units setup.uniformLinearMassDensity
  centerOfMassSpeedPositive :
    ∀ units : UnitChoices,
      0 < speedReadout units setup.centerOfMassSpeed
  circulationSpeedPositive :
    ∀ units : UnitChoices,
      0 < speedReadout units setup.materialCirculationSpeed
  transverseWaveSpeedPositive :
    ∀ units : UnitChoices,
      0 < speedReadout units setup.transverseWaveSpeed
  angularSpeedPositive :
    ∀ units : UnitChoices,
      0 < angularSpeedReadout units setup.loopAngularSpeed

/-!
The governing physics, stated in every coherent unit system:

* rolling without slipping gives `v₀ = ω R`;
* material links circulate around the center at speed `u = ω R`;
* persistence of the moving chain shape matches the transverse-wave speed to
  that material circulation speed;
* the standard transverse-wave law for a tensioned uniform chain is
  `c² = T / μ`.

The last law is deliberately written using the independent wave-speed field;
none of these premises states the requested formula involving `v₀`.
-/
structure SatisfiesRollingChainLaws (setup : RollingChainSetup) : Prop where
  rollingWithoutSlip :
    ∀ units : UnitChoices,
      speedReadout units setup.centerOfMassSpeed =
        angularSpeedReadout units setup.loopAngularSpeed *
          radiusReadout units setup.loopRadius
  materialCirculationKinematics :
    ∀ units : UnitChoices,
      speedReadout units setup.materialCirculationSpeed =
        angularSpeedReadout units setup.loopAngularSpeed *
          radiusReadout units setup.loopRadius
  stableShapeMatchesWaveAndCirculationSpeeds :
    ∀ units : UnitChoices,
      speedReadout units setup.transverseWaveSpeed =
        speedReadout units setup.materialCirculationSpeed
  transverseWaveLaw :
    ∀ units : UnitChoices,
      speedReadout units setup.transverseWaveSpeed ^ 2 =
        forceReadout units setup.chainTension /
          linearMassDensityReadout units setup.uniformLinearMassDensity

/-!
Rolling kinematics and stable-shape propagation identify the transverse-wave
speed with the center-of-mass speed.  This lemma derives a speed relation only;
it does not assert the requested tension.
-/
lemma transverseWaveSpeed_eq_centerOfMassSpeed
    (setup : RollingChainSetup)
    (_laws : SatisfiesRollingChainLaws setup)
    (units : UnitChoices) :
    speedReadout units setup.transverseWaveSpeed =
      speedReadout units setup.centerOfMassSpeed := by
  calc
    speedReadout units setup.transverseWaveSpeed =
        speedReadout units setup.materialCirculationSpeed :=
      _laws.stableShapeMatchesWaveAndCirculationSpeeds units
    _ = angularSpeedReadout units setup.loopAngularSpeed *
          radiusReadout units setup.loopRadius :=
      _laws.materialCirculationKinematics units
    _ = speedReadout units setup.centerOfMassSpeed :=
      (_laws.rollingWithoutSlip units).symm

/-! ## Multiple-choice metadata -/

/-- Labels of the four displayed answer choices. -/
inductive AnswerChoice where
  | A
  | B
  | C
  | D
  deriving DecidableEq, Repr

/-!
The speed dependence printed in each choice.  The source uses a generic
coefficient symbol `α`; its powers have different dimensions across choices,
so the alternatives are retained as symbolic scaling metadata rather than as
ill-typed force equalities.
-/
inductive DisplayedSpeedScaling where
  | squareRoot
  | cubic
  | linear
  | quadratic
  deriving DecidableEq, Repr

/-- Speed scaling associated with each displayed answer label. -/
def displayedSpeedScaling : AnswerChoice → DisplayedSpeedScaling
  | .A => .squareRoot
  | .B => .cubic
  | .C => .linear
  | .D => .quadratic

/-- Answer label recorded in the source dataset. -/
def recordedAnswerChoice : AnswerChoice := .D

/-!
The chain tension is its uniform linear mass density times the square of the
center-of-mass speed: `T = μ v₀²`.  Thus the physical result has the quadratic
speed dependence recorded as answer choice `D`.

This formalizes blueprint label `thm:physics:phyx_mini_0244:target`.
-/
theorem problem_phyx_mini_0244
    (setup : RollingChainSetup)
    (_statement : MatchesProblemStatement setup)
    (_figure : MatchesSuppliedFigure setup)
    (_physical : HasPhysicalRollingParameters setup)
    (_laws : SatisfiesRollingChainLaws setup) :
    ∀ units : UnitChoices,
      forceReadout units setup.chainTension =
        linearMassDensityReadout units setup.uniformLinearMassDensity *
          speedReadout units setup.centerOfMassSpeed ^ 2 := by
  intro units
  have density_ne_zero :
      linearMassDensityReadout units setup.uniformLinearMassDensity ≠ 0 :=
    ne_of_gt (_physical.densityPositive units)
  have wave_law_cleared :
      speedReadout units setup.transverseWaveSpeed ^ 2 *
          linearMassDensityReadout units setup.uniformLinearMassDensity =
        forceReadout units setup.chainTension :=
    (eq_div_iff density_ne_zero).mp (_laws.transverseWaveLaw units)
  calc
    forceReadout units setup.chainTension =
        speedReadout units setup.transverseWaveSpeed ^ 2 *
          linearMassDensityReadout units setup.uniformLinearMassDensity :=
      wave_law_cleared.symm
    _ = linearMassDensityReadout units setup.uniformLinearMassDensity *
          speedReadout units setup.centerOfMassSpeed ^ 2 := by
      rw [transverseWaveSpeed_eq_centerOfMassSpeed setup _laws units]
      ring

end PhyXMiniProblems.ProblemPhyXMini0244
