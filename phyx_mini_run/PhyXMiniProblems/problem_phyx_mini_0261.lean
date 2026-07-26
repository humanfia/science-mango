import Mathlib.Analysis.Real.Sqrt
import Physlib.ClassicalMechanics.HarmonicOscillator.Solution
import Physlib.Units.WithDim.Speed

/- USER: The assigned source file did not exist when this autoformalization task began. -/

/-!
# Completely inelastic collision with a spring oscillator

Block 2 is initially the mass of an undamped one-dimensional spring oscillator.
At the stated collision time, right-moving block 1 sticks to block 2.  The
collision is treated as impulsive relative to the oscillator period, so linear
momentum is conserved during impact while the spring displacement is continuous.
The stuck pair then oscillates on the same spring with their combined mass.

Physical masses, lengths, times, signed displacements, signed velocities, and
spring stiffness are represented by unit-independent Physlib quantities.  The
scalar fields in Physlib's `HarmonicOscillator`, `AmplitudePhase`, and
`InitialConditions` are connected explicitly to coherent SI readouts.

Assumption/target boundary:

* `MatchesProblemAndFigure` records the numerical givens, the completely
  inelastic outcome, the short-collision idealization, and the labeled geometry
  visible in the primary image.
* `SatisfiesPreCollisionSHM` states the supplied cosine trajectory and relates
  the first Physlib oscillator to block 2 and the spring.
* `SatisfiesImpulsiveCollision` states one-dimensional momentum conservation
  and continuity of the initial state for the stuck pair.
* `SatisfiesPostCollisionSHM` relates the second Physlib oscillator to the
  combined mass and defines its physical amplitude from its initial state.
* There are no previous-part results.  The collision state, common post-impact
  velocity, exact new amplitude, and rounded answer `0.024 m` occur only as
  conclusions below.
-/

noncomputable section

namespace PhyXMiniProblems.ProblemPhyXMini0261

open Dimension

/-! ## Dimensionful physical quantities and named-unit readouts -/

/-- A nonnegative physical mass. -/
abbrev MassQuantity : Type := Dimensionful (WithDim M𝓭 NNReal)

/-- A nonnegative physical length, used for oscillation amplitudes. -/
abbrev LengthQuantity : Type := Dimensionful (WithDim L𝓭 NNReal)

/-- A signed displacement along the horizontal spring axis. -/
abbrev SignedDisplacementQuantity : Type :=
  Dimensionful (WithDim L𝓭 ℝ)

/-- A nonnegative physical duration or elapsed time. -/
abbrev DurationQuantity : Type := Dimensionful (WithDim T𝓭 NNReal)

/-- A signed one-dimensional velocity along the spring axis. -/
abbrev SignedVelocityQuantity : Type :=
  Dimensionful (WithDim (L𝓭 * T𝓭⁻¹) ℝ)

/-- Spring stiffness, with dimension mass divided by time squared (`N/m`). -/
abbrev SpringStiffnessQuantity : Type :=
  Dimensionful (WithDim (M𝓭 * T𝓭⁻¹ * T𝓭⁻¹) NNReal)

/-- Read a physical mass in the selected mass unit. -/
def massReadout (unit : MassUnit) (mass : MassQuantity) : ℝ :=
  ((mass {UnitChoices.SI with mass := unit}).val : ℝ)

/-- Read a nonnegative physical length in the selected length unit. -/
def lengthReadout (unit : LengthUnit) (length : LengthQuantity) : ℝ :=
  ((length {UnitChoices.SI with length := unit}).val : ℝ)

/-- Read a signed displacement in the selected length unit. -/
def displacementReadout
    (unit : LengthUnit) (displacement : SignedDisplacementQuantity) : ℝ :=
  (displacement {UnitChoices.SI with length := unit}).val

/-- Read a physical duration in the selected time unit. -/
def durationReadout (unit : TimeUnit) (duration : DurationQuantity) : ℝ :=
  ((duration {UnitChoices.SI with time := unit}).val : ℝ)

/-- Read a signed velocity in coherent selected length and time units. -/
def velocityReadout
    (lengthUnit : LengthUnit) (timeUnit : TimeUnit)
    (velocity : SignedVelocityQuantity) : ℝ :=
  (velocity {UnitChoices.SI with
    length := lengthUnit, time := timeUnit}).val

/-- Read spring stiffness in coherent selected mass and time units. -/
def stiffnessReadout
    (massUnit : MassUnit) (timeUnit : TimeUnit)
    (stiffness : SpringStiffnessQuantity) : ℝ :=
  ((stiffness {UnitChoices.SI with
    mass := massUnit, time := timeUnit}).val : ℝ)

/-- Kilogram readout used in the oscillator models. -/
def massInKilograms (mass : MassQuantity) : ℝ :=
  massReadout MassUnit.kilograms mass

/-- Metre readout of a physical amplitude. -/
def lengthInMeters (length : LengthQuantity) : ℝ :=
  lengthReadout LengthUnit.meters length

/-- Centimetre readout used for the supplied initial amplitude. -/
def lengthInCentimeters (length : LengthQuantity) : ℝ :=
  lengthReadout LengthUnit.centimeters length

/-- Metre readout of a signed axial displacement. -/
def displacementInMeters (displacement : SignedDisplacementQuantity) : ℝ :=
  displacementReadout LengthUnit.meters displacement

/-- Second readout used in the harmonic-motion laws. -/
def durationInSeconds (duration : DurationQuantity) : ℝ :=
  durationReadout TimeUnit.seconds duration

/-- Millisecond readout used for the period and collision time. -/
def durationInMilliseconds (duration : DurationQuantity) : ℝ :=
  durationReadout TimeUnit.milliseconds duration

/-- Metres-per-second readout of a signed axial velocity. -/
def velocityInMetersPerSecond (velocity : SignedVelocityQuantity) : ℝ :=
  velocityReadout LengthUnit.meters TimeUnit.seconds velocity

/-- Newton-per-metre readout of the spring stiffness. -/
def stiffnessInNewtonsPerMeter (stiffness : SpringStiffnessQuantity) : ℝ :=
  stiffnessReadout MassUnit.kilograms TimeUnit.seconds stiffness

/-! ## Physical objects and primary-image evidence -/

/-- The numerical block labels printed in the primary image. -/
inductive BlockLabel where
  | block1
  | block2
  deriving DecidableEq, Repr

/-- Horizontal directions along the spring axis. -/
inductive HorizontalDirection where
  | left
  | right
  deriving DecidableEq, Repr

/-- Mathematical labels visible in the image. -/
inductive FigureLabel where
  | numeral1
  | numeral2
  | springConstant_k
  deriving DecidableEq, Repr

/-- Qualitative outcomes of the collision. -/
inductive CollisionOutcome where
  | completelyInelasticBodiesStick
  | bodiesSeparate
  deriving DecidableEq, Repr

/-- Comparison between the impact duration and the pre-impact oscillator period. -/
inductive CollisionTimeScale where
  | muchShorterThanOscillationPeriod
  | comparableToOscillationPeriod
  deriving DecidableEq, Repr

/-- Mechanical regimes relevant to the two intervals of motion. -/
inductive OscillationRegime where
  | undampedSimpleHarmonic
  | damped
  deriving DecidableEq, Repr

/-- Orientations used for the spring, velocity, and support surface. -/
inductive Orientation where
  | horizontal
  | vertical
  deriving DecidableEq, Repr

/-- Qualitative facts transcribed from the supplied primary image. -/
structure SpringCollisionFigure where
  displayedLabel : BlockLabel → FigureLabel
  block1LeftOfBlock2 : Bool
  block1VelocityArrow : HorizontalDirection
  block2OscillationArrow : HorizontalDirection → Bool
  springAttachedBlock : BlockLabel
  springExtendsTowardRightWall : Bool
  springLabel : FigureLabel
  wallOnRight : Bool
  supportSurfaceOrientation : Orientation

/-!
All physical quantities and intermediate states used by the model.

`postCollisionAmplitude` is deliberately an unconstrained physical length in
this structure.  Its connection to the post-impact initial state is supplied
only by the general harmonic-oscillator law below; no answer-choice value is
stored here.
-/
structure SpringCollisionSetup where
  blockMass : BlockLabel → MassQuantity
  springStiffness : SpringStiffnessQuantity
  preCollisionAmplitude : LengthQuantity
  preCollisionPeriod : DurationQuantity
  collisionTime : DurationQuantity
  collisionDuration : DurationQuantity
  incomingBlock1Velocity : SignedVelocityQuantity
  block2DisplacementImmediatelyBefore : SignedDisplacementQuantity
  block2VelocityImmediatelyBefore : SignedVelocityQuantity
  commonVelocityImmediatelyAfter : SignedVelocityQuantity
  postCollisionAmplitude : LengthQuantity
  preCollisionOscillator : ClassicalMechanics.HarmonicOscillator
  preCollisionAmplitudePhase :
    ClassicalMechanics.HarmonicOscillator.AmplitudePhase
  postCollisionOscillator : ClassicalMechanics.HarmonicOscillator
  postImpactInitialConditions :
    ClassicalMechanics.HarmonicOscillator.InitialConditions
  incomingDirection : HorizontalDirection
  springAxisOrientation : Orientation
  collisionOutcome : CollisionOutcome
  collisionTimeScale : CollisionTimeScale
  preCollisionRegime : OscillationRegime
  postCollisionRegime : OscillationRegime
  figure : SpringCollisionFigure

/-!
The numerical givens and qualitative facts stated by the problem and shown in
the primary image.  In Physlib's amplitude-phase convention the trajectory is
`A cos (omega t - phi)`, so the source's `+ pi/2` becomes `phi = -pi/2` in
`SatisfiesPreCollisionSHM`, rather than being treated as a requested result.

No field below constrains the post-collision amplitude.
-/
structure MatchesProblemAndFigure (setup : SpringCollisionSetup) : Prop where
  block1MassKilograms : massInKilograms (setup.blockMass .block1) = 4
  block2MassKilograms : massInKilograms (setup.blockMass .block2) = 2
  preCollisionAmplitudeCentimeters :
    lengthInCentimeters setup.preCollisionAmplitude = 1
  preCollisionPeriodMilliseconds :
    durationInMilliseconds setup.preCollisionPeriod = 20
  incomingBlock1VelocityMetersPerSecond :
    velocityInMetersPerSecond setup.incomingBlock1Velocity = 6
  collisionTimeMilliseconds : durationInMilliseconds setup.collisionTime = 5
  incomingBlockMovesRight : setup.incomingDirection = .right
  motionAlongSpring : setup.springAxisOrientation = .horizontal
  completelyInelastic :
    setup.collisionOutcome = .completelyInelasticBodiesStick
  impulsiveTimeScale :
    setup.collisionTimeScale = .muchShorterThanOscillationPeriod
  block2InitiallyInSHM :
    setup.preCollisionRegime = .undampedSimpleHarmonic
  stuckPairMovesInSHM :
    setup.postCollisionRegime = .undampedSimpleHarmonic
  figureBlock1Label : setup.figure.displayedLabel .block1 = .numeral1
  figureBlock2Label : setup.figure.displayedLabel .block2 = .numeral2
  figureBlock1LeftOfBlock2 : setup.figure.block1LeftOfBlock2 = true
  figureBlock1ArrowRight : setup.figure.block1VelocityArrow = .right
  figureBlock2ArrowLeft : setup.figure.block2OscillationArrow .left = true
  figureBlock2ArrowRight : setup.figure.block2OscillationArrow .right = true
  figureSpringAttachedToBlock2 : setup.figure.springAttachedBlock = .block2
  figureSpringExtendsRight : setup.figure.springExtendsTowardRightWall = true
  figureSpringLabel : setup.figure.springLabel = .springConstant_k
  figureWallOnRight : setup.figure.wallOnRight = true
  figureHorizontalSurface :
    setup.figure.supportSurfaceOrientation = .horizontal

/-! ## Governing laws -/

/-!
The supplied pre-collision simple harmonic motion.

Physlib gives `omega = sqrt (k/m)` and `period = 2 pi / omega`.  The final two
fields evaluate the given cosine trajectory and its derivative at the stated
collision time.  They determine only the state immediately before impact, not
the amplitude after impact.
-/
structure SatisfiesPreCollisionSHM (setup : SpringCollisionSetup) : Prop where
  oscillatorMass :
    setup.preCollisionOscillator.m =
      massInKilograms (setup.blockMass .block2)
  oscillatorSpringStiffness :
    setup.preCollisionOscillator.k =
      stiffnessInNewtonsPerMeter setup.springStiffness
  periodLaw :
    durationInSeconds setup.preCollisionPeriod =
      setup.preCollisionOscillator.period
  suppliedAmplitude :
    setup.preCollisionAmplitudePhase.A =
      lengthInMeters setup.preCollisionAmplitude
  suppliedPhase : setup.preCollisionAmplitudePhase.φ = -(Real.pi / 2)
  displacementAtCollision :
    displacementInMeters setup.block2DisplacementImmediatelyBefore =
      setup.preCollisionAmplitudePhase.A *
        Real.cos
          (setup.preCollisionOscillator.ω *
              durationInSeconds setup.collisionTime -
            setup.preCollisionAmplitudePhase.φ)
  velocityAtCollision :
    velocityInMetersPerSecond setup.block2VelocityImmediatelyBefore =
      -(setup.preCollisionAmplitudePhase.A *
        setup.preCollisionOscillator.ω *
        Real.sin
          (setup.preCollisionOscillator.ω *
              durationInSeconds setup.collisionTime -
            setup.preCollisionAmplitudePhase.φ))

/-!
The short, completely inelastic impact law.  Linear momentum is conserved in
every coherent choice of mass, length, and time units.  The stuck pair starts
its post-impact motion at the collision displacement and with the common
velocity produced by impact.

This law does not mention the amplitude of the later SHM.
-/
structure SatisfiesImpulsiveCollision (setup : SpringCollisionSetup) : Prop where
  momentumConservation :
    ∀ (massUnit : MassUnit) (lengthUnit : LengthUnit)
        (timeUnit : TimeUnit),
      massReadout massUnit (setup.blockMass .block1) *
          velocityReadout lengthUnit timeUnit setup.incomingBlock1Velocity +
        massReadout massUnit (setup.blockMass .block2) *
          velocityReadout lengthUnit timeUnit
            setup.block2VelocityImmediatelyBefore =
      (massReadout massUnit (setup.blockMass .block1) +
          massReadout massUnit (setup.blockMass .block2)) *
        velocityReadout lengthUnit timeUnit
          setup.commonVelocityImmediatelyAfter
  displacementContinuousThroughImpact :
    setup.postImpactInitialConditions.x₀ 0 =
      displacementInMeters setup.block2DisplacementImmediatelyBefore
  commonVelocityInitialCondition :
    setup.postImpactInitialConditions.v₀ 0 =
      velocityInMetersPerSecond setup.commonVelocityImmediatelyAfter

/-!
The stuck blocks undergo SHM on the same spring.  Their combined mass and the
unchanged spring stiffness form the second Physlib harmonic oscillator.  The
physical amplitude is the norm recovered by Physlib from its general initial
position and velocity; this is a governing amplitude definition, not the
numerical answer requested by the problem.
-/
structure SatisfiesPostCollisionSHM (setup : SpringCollisionSetup) : Prop where
  combinedOscillatorMass :
    setup.postCollisionOscillator.m =
      massInKilograms (setup.blockMass .block1) +
        massInKilograms (setup.blockMass .block2)
  unchangedSpringStiffness :
    setup.postCollisionOscillator.k =
      stiffnessInNewtonsPerMeter setup.springStiffness
  physicalAmplitudeFromInitialState :
    lengthInMeters setup.postCollisionAmplitude =
      (ClassicalMechanics.HarmonicOscillator.AmplitudePhase.fromInitialConditions
        setup.postCollisionOscillator setup.postImpactInitialConditions).A

/-! ## Derived collision state and exact amplitude -/

/-!
At `t = 5 ms = T/4`, the phase in the supplied trajectory is `pi`.  Thus block
2 is at the negative turning point and instantaneously at rest.  This is an
intermediate conclusion, not a premise.
-/
lemma block2_state_at_collision
    (setup : SpringCollisionSetup)
    (hData : MatchesProblemAndFigure setup)
    (hPre : SatisfiesPreCollisionSHM setup) :
    displacementInMeters setup.block2DisplacementImmediatelyBefore =
        -(1 / 100 : ℝ) ∧
      velocityInMetersPerSecond setup.block2VelocityImmediatelyBefore = 0 := by
  let ucm : UnitChoices :=
    {UnitChoices.SI with length := LengthUnit.centimeters}
  let um : UnitChoices :=
    {UnitChoices.SI with length := LengthUnit.meters}
  have hAmpScale :
      ucm.dimScale um L𝓭 = (⟨1 / 100, by norm_num⟩ : NNReal) := by
    norm_num [ucm, um, UnitChoices.dimScale, LengthUnit.centimeters,
      LengthUnit.meters]
  have hAmpUnits :=
    congrArg (fun q : WithDim L𝓭 NNReal => (q.val : ℝ))
      (setup.preCollisionAmplitude.2 ucm um)
  rw [show dim (WithDim L𝓭 NNReal) = L𝓭 by rfl, hAmpScale] at hAmpUnits
  dsimp [um, ucm] at hAmpUnits
  norm_num at hAmpUnits
  change lengthInMeters setup.preCollisionAmplitude =
    (1 / 100 : ℝ) * lengthInCentimeters setup.preCollisionAmplitude at hAmpUnits
  rw [hData.preCollisionAmplitudeCentimeters] at hAmpUnits
  norm_num at hAmpUnits
  let ums : UnitChoices :=
    {UnitChoices.SI with time := TimeUnit.milliseconds}
  let us : UnitChoices :=
    {UnitChoices.SI with time := TimeUnit.seconds}
  have hTimeScale :
      ums.dimScale us T𝓭 = (⟨1 / 1000, by norm_num⟩ : NNReal) := by
    norm_num [ums, us, UnitChoices.dimScale, TimeUnit.milliseconds,
      TimeUnit.seconds]
  have hPeriodUnits :=
    congrArg (fun q : WithDim T𝓭 NNReal => (q.val : ℝ))
      (setup.preCollisionPeriod.2 ums us)
  rw [show dim (WithDim T𝓭 NNReal) = T𝓭 by rfl, hTimeScale] at hPeriodUnits
  dsimp [us, ums] at hPeriodUnits
  norm_num at hPeriodUnits
  change durationInSeconds setup.preCollisionPeriod =
    (1 / 1000 : ℝ) * durationInMilliseconds setup.preCollisionPeriod at hPeriodUnits
  rw [hData.preCollisionPeriodMilliseconds] at hPeriodUnits
  norm_num at hPeriodUnits
  have hCollisionTimeUnits :=
    congrArg (fun q : WithDim T𝓭 NNReal => (q.val : ℝ))
      (setup.collisionTime.2 ums us)
  rw [show dim (WithDim T𝓭 NNReal) = T𝓭 by rfl, hTimeScale] at hCollisionTimeUnits
  dsimp [us, ums] at hCollisionTimeUnits
  norm_num at hCollisionTimeUnits
  change durationInSeconds setup.collisionTime =
    (1 / 1000 : ℝ) * durationInMilliseconds setup.collisionTime at hCollisionTimeUnits
  rw [hData.collisionTimeMilliseconds] at hCollisionTimeUnits
  norm_num at hCollisionTimeUnits
  have hPeriod := hPre.periodLaw
  rw [hPeriodUnits] at hPeriod
  change (1 / 50 : ℝ) =
    2 * Real.pi / setup.preCollisionOscillator.ω at hPeriod
  have hωne := setup.preCollisionOscillator.ω_ne_zero
  field_simp [hωne] at hPeriod
  have hOmega : setup.preCollisionOscillator.ω = 100 * Real.pi := by
    linarith
  constructor
  · rw [hPre.displacementAtCollision, hPre.suppliedAmplitude, hAmpUnits,
      hOmega, hCollisionTimeUnits, hPre.suppliedPhase]
    rw [show 100 * Real.pi * (1 / 200) - -(Real.pi / 2) =
      Real.pi by ring]
    rw [Real.cos_pi]
    norm_num
  · rw [hPre.velocityAtCollision, hPre.suppliedAmplitude, hAmpUnits,
      hOmega, hCollisionTimeUnits, hPre.suppliedPhase]
    rw [show 100 * Real.pi * (1 / 200) - -(Real.pi / 2) =
      Real.pi by ring]
    rw [Real.sin_pi]
    ring

/-!
Momentum conservation for the sticking collision gives the common speed
`(4 kg * 6 m/s + 2 kg * 0 m/s) / 6 kg = 4 m/s`.
-/
lemma common_velocity_immediately_after_collision
    (setup : SpringCollisionSetup)
    (hData : MatchesProblemAndFigure setup)
    (hPre : SatisfiesPreCollisionSHM setup)
    (hCollision : SatisfiesImpulsiveCollision setup) :
    velocityInMetersPerSecond setup.commonVelocityImmediatelyAfter = 4 := by
  have hBlock2Velocity := (block2_state_at_collision setup hData hPre).2
  have hMomentum :=
    hCollision.momentumConservation MassUnit.kilograms
      LengthUnit.meters TimeUnit.seconds
  change massInKilograms (setup.blockMass .block1) *
      velocityInMetersPerSecond setup.incomingBlock1Velocity +
    massInKilograms (setup.blockMass .block2) *
      velocityInMetersPerSecond setup.block2VelocityImmediatelyBefore =
    (massInKilograms (setup.blockMass .block1) +
      massInKilograms (setup.blockMass .block2)) *
      velocityInMetersPerSecond setup.commonVelocityImmediatelyAfter at hMomentum
  rw [hData.block1MassKilograms, hData.block2MassKilograms,
    hData.incomingBlock1VelocityMetersPerSecond, hBlock2Velocity] at hMomentum
  linarith

/-!
For a harmonic oscillator with collision-time initial state `(x_c, v_c)`, the
amplitude is `sqrt (x_c^2 + (v_c/omega_after)^2)`.  Substitution of the two
derived collision-state readouts gives this exact relation.
-/
lemma post_collision_amplitude_exact
    (setup : SpringCollisionSetup)
    (hData : MatchesProblemAndFigure setup)
    (hPre : SatisfiesPreCollisionSHM setup)
    (hCollision : SatisfiesImpulsiveCollision setup)
    (hPost : SatisfiesPostCollisionSHM setup) :
    lengthInMeters setup.postCollisionAmplitude =
      Real.sqrt
        ((1 / 100 : ℝ) ^ 2 +
          (4 / setup.postCollisionOscillator.ω) ^ 2) := by
  rw [hPost.physicalAmplitudeFromInitialState]
  change ‖(⟨setup.postImpactInitialConditions.x₀ 0,
      setup.postImpactInitialConditions.v₀ 0 /
        setup.postCollisionOscillator.ω⟩ : ℂ)‖ = _
  rw [Complex.norm_eq_sqrt_sq_add_sq]
  rw [hCollision.displacementContinuousThroughImpact,
    (block2_state_at_collision setup hData hPre).1,
    hCollision.commonVelocityInitialCondition,
    common_velocity_immediately_after_collision setup hData hPre hCollision]
  congr 1
  ring

/-! ## Displayed choices and formalization target -/

/-- Labels of the four amplitudes printed with the problem. -/
inductive AnswerChoice where
  | A
  | B
  | C
  | D
  deriving DecidableEq, Repr

/-- Amplitude in metres printed beside each answer label. -/
def AnswerChoice.amplitudeInMeters : AnswerChoice → ℝ
  | .A => 16 / 1000
  | .B => 20 / 1000
  | .C => 24 / 1000
  | .D => 28 / 1000

/-- The answer label recorded by the supplied dataset. -/
def recordedAnswerChoice : AnswerChoice := .C

/-- Agreement with a displayed amplitude after rounding to the nearest millimetre. -/
def RoundsToNearestMillimeter
    (amplitude : LengthQuantity) (displayedMeters : ℝ) : Prop :=
  |lengthInMeters amplitude - displayedMeters| < (1 / 2000 : ℝ)

/-- The physical post-collision amplitude agrees with the selected displayed choice. -/
def MatchesAnswerChoice
    (amplitude : LengthQuantity) (choice : AnswerChoice) : Prop :=
  RoundsToNearestMillimeter amplitude choice.amplitudeInMeters

/-!
The post-impact oscillator has combined mass `6 kg`, retains the original
spring stiffness, and starts at `x = -0.010 m` with velocity `4 m/s`.  Its
amplitude rounds to `0.024 m`, answer choice C.

This is the formal target corresponding to
`thm:physics:phyx_mini_0261:target`.
-/
theorem problem_phyx_mini_0261
    (setup : SpringCollisionSetup)
    (hData : MatchesProblemAndFigure setup)
    (hPre : SatisfiesPreCollisionSHM setup)
    (hCollision : SatisfiesImpulsiveCollision setup)
    (hPost : SatisfiesPostCollisionSHM setup) :
    MatchesAnswerChoice setup.postCollisionAmplitude recordedAnswerChoice := by
  let ums : UnitChoices :=
    {UnitChoices.SI with time := TimeUnit.milliseconds}
  let us : UnitChoices :=
    {UnitChoices.SI with time := TimeUnit.seconds}
  have hTimeScale :
      ums.dimScale us T𝓭 = (⟨1 / 1000, by norm_num⟩ : NNReal) := by
    norm_num [ums, us, UnitChoices.dimScale, TimeUnit.milliseconds,
      TimeUnit.seconds]
  have hPeriodUnits :=
    congrArg (fun q : WithDim T𝓭 NNReal => (q.val : ℝ))
      (setup.preCollisionPeriod.2 ums us)
  rw [show dim (WithDim T𝓭 NNReal) = T𝓭 by rfl, hTimeScale] at hPeriodUnits
  dsimp [us, ums] at hPeriodUnits
  norm_num at hPeriodUnits
  change durationInSeconds setup.preCollisionPeriod =
    (1 / 1000 : ℝ) * durationInMilliseconds setup.preCollisionPeriod at hPeriodUnits
  rw [hData.preCollisionPeriodMilliseconds] at hPeriodUnits
  norm_num at hPeriodUnits
  have hPeriod := hPre.periodLaw
  rw [hPeriodUnits] at hPeriod
  change (1 / 50 : ℝ) =
    2 * Real.pi / setup.preCollisionOscillator.ω at hPeriod
  have hPreOmegaNe := setup.preCollisionOscillator.ω_ne_zero
  field_simp [hPreOmegaNe] at hPeriod
  have hPreOmega : setup.preCollisionOscillator.ω = 100 * Real.pi := by
    linarith
  have hPreMass : setup.preCollisionOscillator.m = 2 := by
    rw [hPre.oscillatorMass, hData.block2MassKilograms]
  have hPostMass : setup.postCollisionOscillator.m = 6 := by
    rw [hPost.combinedOscillatorMass, hData.block1MassKilograms,
      hData.block2MassKilograms]
    norm_num
  have hSameK : setup.postCollisionOscillator.k =
      setup.preCollisionOscillator.k := by
    rw [hPost.unchangedSpringStiffness, hPre.oscillatorSpringStiffness]
  have hPreOmegaSq := setup.preCollisionOscillator.ω_sq
  have hPostOmegaSq := setup.postCollisionOscillator.ω_sq
  rw [hPreOmega, hPreMass] at hPreOmegaSq
  rw [hPostMass, hSameK] at hPostOmegaSq
  have hPostOmegaSqExact : setup.postCollisionOscillator.ω ^ 2 =
      (100 * Real.pi) ^ 2 / 3 := by
    nlinarith
  have hTerm : (4 / setup.postCollisionOscillator.ω) ^ 2 =
      3 / (625 * Real.pi ^ 2) := by
    rw [div_pow, hPostOmegaSqExact]
    field_simp [Real.pi_ne_zero]
    ring
  have hSinLt : Real.sin (Real.pi / 12) < Real.pi / 12 := by
    have hpos : 0 < Real.pi / 12 := by positivity
    have hle : Real.pi / 12 ≤ 1 := by
      linarith [Real.pi_le_four]
    have hx : |Real.pi / 12| = Real.pi / 12 := abs_of_nonneg hpos.le
    have hs :=
      le_of_abs_le
        (Real.sin_bound (show |Real.pi / 12| ≤ 1 by rwa [hx]))
    rw [sub_le_iff_le_add', hx] at hs
    apply hs.trans_lt
    rw [sub_add, sub_lt_self_iff, sub_pos,
      div_eq_mul_inv ((Real.pi / 12) ^ 3)]
    refine mul_lt_mul' ?_ (by norm_num) (by norm_num) (pow_pos hpos 3)
    apply pow_le_pow_of_le_one hpos.le hle
    simp
  have hSinExact : Real.sin (Real.pi / 12) =
      (Real.sqrt 6 - Real.sqrt 2) / 4 := by
    rw [show Real.pi / 12 = Real.pi / 3 - Real.pi / 4 by ring]
    rw [Real.sin_sub, Real.sin_pi_div_three, Real.cos_pi_div_four,
      Real.cos_pi_div_three, Real.sin_pi_div_four]
    ring_nf
    rw [← Real.sqrt_mul (show (0 : ℝ) ≤ 3 by norm_num) (2 : ℝ)]
    norm_num
    ring
  have hsqrt6Lower : (2449 / 1000 : ℝ) < Real.sqrt 6 := by
    rw [Real.lt_sqrt (by norm_num)]
    norm_num
  have hsqrt2Upper : Real.sqrt 2 < (1415 / 1000 : ℝ) := by
    rw [Real.sqrt_lt' (by norm_num)]
    norm_num
  have hPiLower : (31 / 10 : ℝ) < Real.pi := by
    rw [hSinExact] at hSinLt
    linarith
  have hsBound := @Real.sin_bound (13 / 24 : ℝ) (by norm_num)
  have hsLower := neg_le_of_abs_le hsBound
  norm_num [abs_of_nonneg] at hsLower
  have hs : (1 / 2 : ℝ) < Real.sin (13 / 24 : ℝ) := by
    linarith
  have hPiUpper : Real.pi < (13 / 4 : ℝ) := by
    by_contra h
    have hPiGe : (13 / 4 : ℝ) ≤ Real.pi := le_of_not_gt h
    have hxy : (13 / 24 : ℝ) ≤ Real.pi / 6 := by
      linarith
    have hmono :=
      Real.sin_le_sin_of_le_of_le_pi_div_two
        (x := (13 / 24 : ℝ)) (y := Real.pi / 6)
        (by linarith [Real.pi_pos]) (by linarith [Real.pi_pos]) hxy
    rw [Real.sin_pi_div_six] at hmono
    linarith
  have hPiSqPos : 0 < 625 * Real.pi ^ 2 := by positivity
  have hDivUpper : 3 / (625 * Real.pi ^ 2) <
      (49 / 2000 : ℝ) ^ 2 - (1 / 100 : ℝ) ^ 2 := by
    apply (div_lt_iff₀ hPiSqPos).2
    norm_num
    nlinarith [sq_nonneg (Real.pi - 31 / 10)]
  have hRadUpper : (1 / 100 : ℝ) ^ 2 +
      3 / (625 * Real.pi ^ 2) < (49 / 2000 : ℝ) ^ 2 := by
    linarith
  have hDivLower : (47 / 2000 : ℝ) ^ 2 - (1 / 100 : ℝ) ^ 2 <
      3 / (625 * Real.pi ^ 2) := by
    apply (lt_div_iff₀ hPiSqPos).2
    norm_num
    nlinarith [sq_nonneg (13 / 4 - Real.pi)]
  have hRadLower : (47 / 2000 : ℝ) ^ 2 <
      (1 / 100 : ℝ) ^ 2 + 3 / (625 * Real.pi ^ 2) := by
    linarith
  have hSqrtUpper :
      Real.sqrt ((1 / 100 : ℝ) ^ 2 + 3 / (625 * Real.pi ^ 2)) <
        49 / 2000 :=
    (Real.sqrt_lt' (by norm_num)).2 hRadUpper
  have hSqrtLower :
      (47 / 2000 : ℝ) <
        Real.sqrt ((1 / 100 : ℝ) ^ 2 + 3 / (625 * Real.pi ^ 2)) :=
    (Real.lt_sqrt (by norm_num)).2 hRadLower
  have hAmp :=
    post_collision_amplitude_exact setup hData hPre hCollision hPost
  rw [hTerm] at hAmp
  change |lengthInMeters setup.postCollisionAmplitude -
    (24 / 1000 : ℝ)| < (1 / 2000 : ℝ)
  rw [hAmp, abs_lt]
  constructor <;> linarith

end PhyXMiniProblems.ProblemPhyXMini0261
