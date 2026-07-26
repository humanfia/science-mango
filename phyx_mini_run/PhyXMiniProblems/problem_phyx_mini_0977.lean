import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Order.Filter.AtTopBot.Basic
import Physlib.Electromagnetism.Basic
import Physlib.Units.WithDim.Basic

/- USER: The assigned Lean file did not exist when this autoformalization task began. -/

noncomputable section

namespace PhyXMiniProblems.ProblemPhyXMini0977

open Dimension Filter

/-!
# Magnetic braking of a slidewire

The primary raster `977.png` shows a vertical conducting slidewire bridging
the two horizontal arms of a U-shaped conductor.  The rod moves right through
a uniform magnetic field directed into the page.  Its length (equivalently,
the rail separation) is labelled `L`, and the velocity arrow is labelled `v`.

The physical magnitudes below use Physlib's unit-covariant `Dimensionful`
quantities.  Real numbers occur only as coherent-SI readouts and as the
coherent-SI time parameter of the one-dimensional motion.

Assumption/target split:

* governing laws: uniform into-page magnetic field, kinematics, motional emf
  `epsilon = B L v`, Ohm's law, magnetic force `F = -I L B`, and Newton's
  second law with no friction or applied force after release;
* previous-part results: none;
* figure/data readouts: the U-shaped conductor, horizontal rails, vertical
  slidewire, rightward green `v` arrow, blue cross glyphs and `B` label, and
  the vertical rail-separation guide labelled `L`;
* current target: the asymptotic stopping distance is
  `m v0 R / (L^2 B^2)`, answer B.

The stopping distance is an independent physical observable.  A separate
predicate says that it is the long-time limit of displacement; it is never
defined to equal an answer-choice expression.
-/

/-! ## Dimensions, physical quantities, and coherent-SI readouts -/

/-- Speed has physical dimension `L T⁻¹`. -/
def speedDimension : Dimension :=
  L𝓭 * T𝓭⁻¹

/-- Acceleration has physical dimension `L T⁻²`. -/
def accelerationDimension : Dimension :=
  L𝓭 * T𝓭⁻¹ * T𝓭⁻¹

/-- Magnetic flux density has physical dimension `M T⁻¹ C⁻¹` (tesla). -/
def magneticFluxDensityDimension : Dimension :=
  M𝓭 * T𝓭⁻¹ * C𝓭⁻¹

/-- Electromotive force has dimension `M L² T⁻² C⁻¹` (volt). -/
def electromotiveForceDimension : Dimension :=
  M𝓭 * L𝓭 * L𝓭 * T𝓭⁻¹ * T𝓭⁻¹ * C𝓭⁻¹

/-- Electric current has dimension `C T⁻¹` (ampere). -/
def electricCurrentDimension : Dimension :=
  C𝓭 * T𝓭⁻¹

/-- Electrical resistance has dimension `M L² T⁻¹ C⁻²` (ohm). -/
def electricalResistanceDimension : Dimension :=
  M𝓭 * L𝓭 * L𝓭 * T𝓭⁻¹ * C𝓭⁻¹ * C𝓭⁻¹

/-- Force has physical dimension `M L T⁻²` (newton). -/
def forceDimension : Dimension :=
  M𝓭 * L𝓭 * T𝓭⁻¹ * T𝓭⁻¹

/-- A nonnegative, unit-independent physical length. -/
abbrev LengthQuantity : Type :=
  Dimensionful (WithDim L𝓭 NNReal)

/-- A signed one-dimensional position or displacement. -/
abbrev SignedLengthQuantity : Type :=
  Dimensionful (WithDim L𝓭 ℝ)

/-- A nonnegative, unit-independent mass. -/
abbrev MassQuantity : Type :=
  Dimensionful (WithDim M𝓭 NNReal)

/-- A nonnegative speed magnitude such as the given initial speed. -/
abbrev SpeedMagnitudeQuantity : Type :=
  Dimensionful (WithDim speedDimension NNReal)

/-- Signed horizontal velocity, with rightward chosen positive. -/
abbrev SignedVelocityQuantity : Type :=
  Dimensionful (WithDim speedDimension ℝ)

/-- Signed horizontal acceleration, with rightward chosen positive. -/
abbrev SignedAccelerationQuantity : Type :=
  Dimensionful (WithDim accelerationDimension ℝ)

/-- A nonnegative magnetic-flux-density magnitude. -/
abbrev MagneticFluxDensityMagnitude : Type :=
  Dimensionful (WithDim magneticFluxDensityDimension NNReal)

/-- Signed motional emf, positive for the counterclockwise loop orientation. -/
abbrev SignedEmfQuantity : Type :=
  Dimensionful (WithDim electromotiveForceDimension ℝ)

/-- Signed conventional current, positive counterclockwise. -/
abbrev SignedCurrentQuantity : Type :=
  Dimensionful (WithDim electricCurrentDimension ℝ)

/-- A nonnegative electrical resistance. -/
abbrev ElectricalResistanceQuantity : Type :=
  Dimensionful (WithDim electricalResistanceDimension NNReal)

/-- Signed horizontal force, with rightward chosen positive. -/
abbrev SignedForceQuantity : Type :=
  Dimensionful (WithDim forceDimension ℝ)

/-- Read a nonnegative dimensionful quantity in coherent SI units. -/
def nonnegativeSIReadout {d : Dimension}
    (quantity : Dimensionful (WithDim d NNReal)) : ℝ :=
  ((quantity UnitChoices.SI).val : ℝ)

/-- Read a signed dimensionful quantity in coherent SI units. -/
def signedSIReadout {d : Dimension}
    (quantity : Dimensionful (WithDim d ℝ)) : ℝ :=
  (quantity UnitChoices.SI).val

/-- Read a length in metres. -/
def lengthInMeters (length : LengthQuantity) : ℝ :=
  nonnegativeSIReadout length

/-- Read a signed position or displacement in metres. -/
def signedLengthInMeters (length : SignedLengthQuantity) : ℝ :=
  signedSIReadout length

/-- Read mass in kilograms. -/
def massInKilograms (mass : MassQuantity) : ℝ :=
  nonnegativeSIReadout mass

/-- Read a speed magnitude in metres per second. -/
def speedMagnitudeInMetersPerSecond
    (speed : SpeedMagnitudeQuantity) : ℝ :=
  nonnegativeSIReadout speed

/-- Read signed horizontal velocity in metres per second. -/
def signedVelocityInMetersPerSecond
    (velocity : SignedVelocityQuantity) : ℝ :=
  signedSIReadout velocity

/-- Read signed horizontal acceleration in metres per second squared. -/
def signedAccelerationInMetersPerSecondSquared
    (acceleration : SignedAccelerationQuantity) : ℝ :=
  signedSIReadout acceleration

/-- Read magnetic flux density in teslas. -/
def magneticFluxDensityInTeslas
    (fieldMagnitude : MagneticFluxDensityMagnitude) : ℝ :=
  nonnegativeSIReadout fieldMagnitude

/-- Read signed emf in volts. -/
def signedEmfInVolts (emf : SignedEmfQuantity) : ℝ :=
  signedSIReadout emf

/-- Read signed conventional current in amperes. -/
def signedCurrentInAmperes (current : SignedCurrentQuantity) : ℝ :=
  signedSIReadout current

/-- Read electrical resistance in ohms. -/
def resistanceInOhms (resistance : ElectricalResistanceQuantity) : ℝ :=
  nonnegativeSIReadout resistance

/-- Read signed horizontal force in newtons. -/
def signedForceInNewtons (force : SignedForceQuantity) : ℝ :=
  signedSIReadout force

/-! ## Spatial directions and literal figure vocabulary -/

/-- A dimensionless direction vector in three-dimensional physical space. -/
abbrev DirectionVector : Type := EuclideanSpace ℝ (Fin 3)

/-- Unit direction normal to the diagram and pointing into the page. -/
def intoPageUnitVector : DirectionVector :=
  -EuclideanSpace.single (2 : Fin 3) 1

/-- Qualitative directions occurring in the raster and force model. -/
inductive DiagramDirection where
  | leftward
  | rightward
  | upward
  | downward
  | intoPage
  | outOfPage
  deriving DecidableEq, Fintype, Repr

/-- The two orientations around the rectangular loop. -/
inductive LoopDirection where
  | clockwise
  | counterclockwise
  deriving DecidableEq, Fintype, Repr

/-- The two straight horizontal arms of the U-shaped conductor. -/
inductive Rail where
  | upper
  | lower
  deriving DecidableEq, Fintype, Repr

/-- Physical and graphical objects visible in the primary raster. -/
inductive FigureObject where
  | uShapedConductor
  | upperRail
  | lowerRail
  | movingSlidewire
  | velocityArrow
  | magneticFieldCrosses
  | lengthGuide
  deriving DecidableEq, Fintype, Repr

/-- Symbolic labels printed in `977.png`. -/
inductive FigureLabel where
  | velocityV
  | magneticFieldB
  | railSeparationL
  deriving DecidableEq, Fintype, Repr

/-- Page-normal magnetic-field glyph. -/
inductive NormalFieldGlyph where
  | cross
  | dot
  deriving DecidableEq, Repr

/-- Colors carrying literal visual information in the supplied image. -/
inductive FigureColor where
  | green
  | blue
  | yellow
  | black
  deriving DecidableEq, Fintype, Repr

/-- Typed transcription of the non-answer-bearing content of `977.png`. -/
structure SlidewireBrakingFigure where
  objectShown : FigureObject → Bool
  labelShown : FigureLabel → Bool
  railIsHorizontal : Rail → Bool
  uConductorOpensToRight : Bool
  slidewireIsVertical : Bool
  slidewireBridgesRails : Bool
  slidewireIsRightOfFixedConnector : Bool
  velocityArrowDirection : DiagramDirection
  velocityArrowColor : FigureColor
  magneticFieldGlyph : NormalFieldGlyph
  magneticFieldGlyphColor : FigureColor
  lengthGuideDirection : DiagramDirection
  lengthGuideSpansRailSeparation : Bool

/-! ## Independent apparatus and time-dependent observables -/

/-- Geometric idealization of the conductor and moving bar. -/
inductive SlidewireGeometryModel where
  | verticalRodOnHorizontalParallelRails
  | other
  deriving DecidableEq, Repr

/-- Material idealization used for the U-shaped fixed conductor. -/
inductive FixedConductorModel where
  | negligibleResistanceUConductor
  | other
  deriving DecidableEq, Repr

/-!
The apparatus and its independent observables.  The real argument of each
time-dependent quantity is elapsed time in coherent-SI seconds.  Position,
velocity, acceleration, emf, current, and force are not defined from one
another or from an answer choice.
-/
structure SlidewireBrakingSetup where
  geometryModel : SlidewireGeometryModel
  fixedConductorModel : FixedConductorModel
  magneticField : Electromagnetism.MagneticField 3
  magneticFluxDensityMagnitude : MagneticFluxDensityMagnitude
  railSeparation : LengthQuantity
  slidewireMass : MassQuantity
  slidewireResistance : ElectricalResistanceQuantity
  fixedLoopResistance : ElectricalResistanceQuantity
  initialSpeed : SpeedMagnitudeQuantity
  stoppingDistance : LengthQuantity
  positionAtSeconds : ℝ → SignedLengthQuantity
  velocityAtSeconds : ℝ → SignedVelocityQuantity
  accelerationAtSeconds : ℝ → SignedAccelerationQuantity
  inducedEmfAtSeconds : ℝ → SignedEmfQuantity
  inducedCurrentAtSeconds : ℝ → SignedCurrentQuantity
  inducedCurrentDirectionAtSeconds : ℝ → LoopDirection
  magneticForceAtSeconds : ℝ → SignedForceQuantity
  magneticForceDirectionAtSeconds : ℝ → DiagramDirection
  frictionForceAtSeconds : ℝ → SignedForceQuantity
  externalAppliedForceAtSeconds : ℝ → SignedForceQuantity
  figure : SlidewireBrakingFigure

/-! ## Scenario assumptions, primary-image evidence, and nondegeneracy -/

/-!
The prose-level idealization: the rod is released after receiving its initial
speed, mechanical friction vanishes, and the U-shaped fixed conductor's
resistance is negligible compared with the rod's resistance (idealized as
zero).  No stopping-distance formula occurs here.
-/
structure MatchesIdealSlidewireScenario
    (setup : SlidewireBrakingSetup) : Prop where
  depictedGeometry :
    setup.geometryModel = .verticalRodOnHorizontalParallelRails
  negligibleResistanceFixedConductor :
    setup.fixedConductorModel = .negligibleResistanceUConductor
  negligibleFixedLoopResistance :
    resistanceInOhms setup.fixedLoopResistance = 0
  noMechanicalFrictionAfterRelease : ∀ t : ℝ, 0 ≤ t →
    signedForceInNewtons (setup.frictionForceAtSeconds t) = 0
  noAppliedForceAfterRelease : ∀ t : ℝ, 0 ≤ t →
    signedForceInNewtons (setup.externalAppliedForceAtSeconds t) = 0

/-! Literal geometry, symbols, directions, and colors read from `977.png`. -/
structure MatchesPrimarySlidewireFigure
    (setup : SlidewireBrakingSetup) : Prop where
  everyDepictedObjectIsShown : ∀ object,
    setup.figure.objectShown object = true
  everyPrintedLabelIsShown : ∀ label,
    setup.figure.labelShown label = true
  bothRailsAreHorizontal : ∀ rail,
    setup.figure.railIsHorizontal rail = true
  uConductorOpensRight : setup.figure.uConductorOpensToRight = true
  rodIsVertical : setup.figure.slidewireIsVertical = true
  rodBridgesBothRails : setup.figure.slidewireBridgesRails = true
  rodLiesRightOfConnector :
    setup.figure.slidewireIsRightOfFixedConnector = true
  velocityPointsRight :
    setup.figure.velocityArrowDirection = .rightward
  velocityArrowIsGreen : setup.figure.velocityArrowColor = .green
  fieldIsDrawnWithCrosses : setup.figure.magneticFieldGlyph = .cross
  fieldCrossesAreBlue : setup.figure.magneticFieldGlyphColor = .blue
  lengthGuideIsVertical : setup.figure.lengthGuideDirection = .upward
  lengthGuideSpansRails :
    setup.figure.lengthGuideSpansRailSeparation = true

/-- Positivity and nondegeneracy of all given answer-bearing parameters. -/
structure HasPhysicalSlidewireParameters
    (setup : SlidewireBrakingSetup) : Prop where
  fieldMagnitudePositive :
    0 < magneticFluxDensityInTeslas setup.magneticFluxDensityMagnitude
  railSeparationPositive : 0 < lengthInMeters setup.railSeparation
  slidewireMassPositive : 0 < massInKilograms setup.slidewireMass
  slidewireResistancePositive :
    0 < resistanceInOhms setup.slidewireResistance
  initialSpeedPositive :
    0 < speedMagnitudeInMetersPerSecond setup.initialSpeed

/-! ## Governing field, induction, circuit, and mechanical laws -/

/-!
The full Physlib magnetic field is uniform in space and time, has magnitude
`B`, and points into the page as indicated by the blue crosses.
-/
structure ModelsUniformIntoPageMagneticField
    (setup : SlidewireBrakingSetup) : Prop where
  uniformIntoPageField : ∀ time position,
    setup.magneticField time position =
      magneticFluxDensityInTeslas setup.magneticFluxDensityMagnitude •
        intoPageUnitVector

/-!
One-dimensional kinematics with the initial conditions from the prose.  The
position derivative is velocity and the velocity derivative is acceleration.
-/
structure SatisfiesSlidewireKinematics
    (setup : SlidewireBrakingSetup) : Prop where
  initialPositionIsZero :
    signedLengthInMeters (setup.positionAtSeconds 0) = 0
  initialVelocityIsGivenSpeed :
    signedVelocityInMetersPerSecond (setup.velocityAtSeconds 0) =
      speedMagnitudeInMetersPerSecond setup.initialSpeed
  positionDerivative : ∀ t : ℝ, 0 ≤ t →
    HasDerivAt
      (fun s => signedLengthInMeters (setup.positionAtSeconds s))
      (signedVelocityInMetersPerSecond (setup.velocityAtSeconds t)) t
  velocityDerivative : ∀ t : ℝ, 0 ≤ t →
    HasDerivAt
      (fun s => signedVelocityInMetersPerSecond (setup.velocityAtSeconds s))
      (signedAccelerationInMetersPerSecondSquared
        (setup.accelerationAtSeconds t)) t
  forwardMotionAfterRelease : ∀ t : ℝ, 0 ≤ t →
    0 ≤ signedVelocityInMetersPerSecond (setup.velocityAtSeconds t)

/-!
Motional induction for a rod of length `L` moving perpendicular to a uniform
field: in the chosen sign convention `epsilon = B L v`.  This is a governing
law and does not mention the stopping distance or mass.
-/
structure SatisfiesMotionalEmfLaw
    (setup : SlidewireBrakingSetup) : Prop where
  motionalEmf : ∀ t : ℝ, 0 ≤ t →
    signedEmfInVolts (setup.inducedEmfAtSeconds t) =
      magneticFluxDensityInTeslas setup.magneticFluxDensityMagnitude *
        lengthInMeters setup.railSeparation *
        signedVelocityInMetersPerSecond (setup.velocityAtSeconds t)

/-!
Ohm's law for the complete conducting loop.  Keeping the fixed-conductor
resistance in this relation makes its later zero-resistance idealization
explicit rather than hiding it in a definition of total resistance.
-/
structure SatisfiesClosedLoopOhmsLaw
    (setup : SlidewireBrakingSetup) : Prop where
  ohmsLaw : ∀ t : ℝ, 0 ≤ t →
    signedEmfInVolts (setup.inducedEmfAtSeconds t) =
      (resistanceInOhms setup.slidewireResistance +
        resistanceInOhms setup.fixedLoopResistance) *
          signedCurrentInAmperes (setup.inducedCurrentAtSeconds t)
  positiveCurrentIsCounterclockwise : ∀ t : ℝ, 0 ≤ t →
    0 < signedCurrentInAmperes (setup.inducedCurrentAtSeconds t) →
      setup.inducedCurrentDirectionAtSeconds t = .counterclockwise

/-!
The magnetic force on the current-carrying slidewire has magnitude `I L B`
and points left, opposing rightward motion.  The minus sign refers to the
right-positive scalar convention.
-/
structure SatisfiesMagneticBrakingForceLaw
    (setup : SlidewireBrakingSetup) : Prop where
  magneticForceLaw : ∀ t : ℝ, 0 ≤ t →
    signedForceInNewtons (setup.magneticForceAtSeconds t) =
      -(signedCurrentInAmperes (setup.inducedCurrentAtSeconds t) *
        lengthInMeters setup.railSeparation *
        magneticFluxDensityInTeslas setup.magneticFluxDensityMagnitude)
  forceOpposesPositiveMotion : ∀ t : ℝ, 0 ≤ t →
    0 < signedVelocityInMetersPerSecond (setup.velocityAtSeconds t) →
      setup.magneticForceDirectionAtSeconds t = .leftward

/-!
Newton's second law for the slidewire.  Friction and any external drive remain
separate force observables; the scenario assumptions set both to zero after
release.
-/
structure SatisfiesNewtonSecondLaw
    (setup : SlidewireBrakingSetup) : Prop where
  newtonSecondLaw : ∀ t : ℝ, 0 ≤ t →
    massInKilograms setup.slidewireMass *
        signedAccelerationInMetersPerSecondSquared
          (setup.accelerationAtSeconds t) =
      signedForceInNewtons (setup.magneticForceAtSeconds t) +
        signedForceInNewtons (setup.frictionForceAtSeconds t) +
        signedForceInNewtons (setup.externalAppliedForceAtSeconds t)

/-!
The phrase "distance before coming to rest" is modeled asymptotically: ideal
linear magnetic drag makes the speed tend to zero as time tends to infinity.
The independent length `stoppingDistance` is calibrated by the corresponding
limit of displacement, with no closed-form value assumed.
-/
structure HasAsymptoticStoppingDistance
    (setup : SlidewireBrakingSetup) : Prop where
  velocityTendsToZero :
    Tendsto
      (fun t => signedVelocityInMetersPerSecond (setup.velocityAtSeconds t))
      atTop (nhds 0)
  displacementTendsToStoppingDistance :
    Tendsto
      (fun t => signedLengthInMeters (setup.positionAtSeconds t) -
        signedLengthInMeters (setup.positionAtSeconds 0))
      atTop (nhds (lengthInMeters setup.stoppingDistance))

/-! ## Displayed choices, dataset metadata, and target conclusion -/

/-- Labels of the four answer choices printed with the problem. -/
inductive AnswerChoice where
  | A
  | B
  | C
  | D
  deriving DecidableEq, Fintype, Repr

/-!
Literal transcription of the four displayed scalar expressions in coherent
SI units.  This answer metadata does not define the independent stopping-
distance observable.
-/
def AnswerChoice.displayedDistanceInMeters
    (choice : AnswerChoice) (setup : SlidewireBrakingSetup) : ℝ :=
  let mass := massInKilograms setup.slidewireMass
  let initialSpeed := speedMagnitudeInMetersPerSecond setup.initialSpeed
  let resistance := resistanceInOhms setup.slidewireResistance
  let field :=
    magneticFluxDensityInTeslas setup.magneticFluxDensityMagnitude
  let length := lengthInMeters setup.railSeparation
  match choice with
  | .A => mass * initialSpeed / (resistance * field ^ 2 * length ^ 2)
  | .B => mass * initialSpeed * resistance / (field ^ 2 * length ^ 2)
  | .C => mass * initialSpeed * resistance / (field ^ 2 * length)
  | .D => mass * initialSpeed * resistance / (field * length ^ 2)

/-- The answer label recorded in the supplied dataset metadata. -/
def recordedDatasetAnswer : AnswerChoice := .B

/-!
Combining motional emf, Ohm's law, magnetic braking, Newton's law, and the
asymptotic displacement relation gives

`x = m v₀ R / (L² B²)`.

This is answer B and the declaration corresponding to
`thm:physics:phyx_mini_0977:target`.  The combined formula appears only in
this conclusion (and in literal answer-choice metadata), never in a premise.
-/
theorem problem_phyx_mini_0977
    (setup : SlidewireBrakingSetup)
    (_scenario : MatchesIdealSlidewireScenario setup)
    (_figure : MatchesPrimarySlidewireFigure setup)
    (_physical : HasPhysicalSlidewireParameters setup)
    (_fieldLaw : ModelsUniformIntoPageMagneticField setup)
    (_kinematics : SatisfiesSlidewireKinematics setup)
    (_motionalEmf : SatisfiesMotionalEmfLaw setup)
    (_ohmsLaw : SatisfiesClosedLoopOhmsLaw setup)
    (_magneticForce : SatisfiesMagneticBrakingForceLaw setup)
    (_newtonLaw : SatisfiesNewtonSecondLaw setup)
    (_asymptoticRest : HasAsymptoticStoppingDistance setup) :
    lengthInMeters setup.stoppingDistance =
      massInKilograms setup.slidewireMass *
        speedMagnitudeInMetersPerSecond setup.initialSpeed *
        resistanceInOhms setup.slidewireResistance /
        (lengthInMeters setup.railSeparation ^ 2 *
          magneticFluxDensityInTeslas
            setup.magneticFluxDensityMagnitude ^ 2) := by
  let m := massInKilograms setup.slidewireMass
  let v₀ := speedMagnitudeInMetersPerSecond setup.initialSpeed
  let R := resistanceInOhms setup.slidewireResistance
  let L := lengthInMeters setup.railSeparation
  let B :=
    magneticFluxDensityInTeslas setup.magneticFluxDensityMagnitude
  let x := fun t : ℝ =>
    signedLengthInMeters (setup.positionAtSeconds t)
  let v := fun t : ℝ =>
    signedVelocityInMetersPerSecond (setup.velocityAtSeconds t)
  let a := fun t : ℝ =>
    signedAccelerationInMetersPerSecondSquared
      (setup.accelerationAtSeconds t)
  let emf := fun t : ℝ =>
    signedEmfInVolts (setup.inducedEmfAtSeconds t)
  let current := fun t : ℝ =>
    signedCurrentInAmperes (setup.inducedCurrentAtSeconds t)
  let force := fun t : ℝ =>
    signedForceInNewtons (setup.magneticForceAtSeconds t)
  let conserved := fun t : ℝ =>
    R * m * v t + (L ^ 2 * B ^ 2) * (x t - x 0)

  have hL : 0 < L := by
    simpa [L] using _physical.railSeparationPositive
  have hB : 0 < B := by
    simpa [B] using _physical.fieldMagnitudePositive
  have hv₀ : v 0 = v₀ := by
    simpa [v, v₀] using _kinematics.initialVelocityIsGivenSpeed

  have hODE (t : ℝ) (ht : 0 ≤ t) :
      R * m * a t + (L ^ 2 * B ^ 2) * v t = 0 := by
    have hEmf : emf t = B * L * v t := by
      simpa [emf, B, L, v] using _motionalEmf.motionalEmf t ht
    have hOhm : emf t = R * current t := by
      have h := _ohmsLaw.ohmsLaw t ht
      rw [_scenario.negligibleFixedLoopResistance] at h
      simpa [emf, R, current] using h
    have hForce : force t = -(current t * L * B) := by
      simpa [force, current, L, B] using
        _magneticForce.magneticForceLaw t ht
    have hNewton : m * a t = force t := by
      have h := _newtonLaw.newtonSecondLaw t ht
      rw [_scenario.noMechanicalFrictionAfterRelease t ht,
        _scenario.noAppliedForceAfterRelease t ht] at h
      simpa [m, a, force] using h
    linear_combination
      R * hNewton + R * hForce + L * B * hOhm - L * B * hEmf

  have hConservedDeriv (t : ℝ) (ht : 0 ≤ t) :
      HasDerivAt conserved 0 t := by
    have hv : HasDerivAt v (a t) t := by
      simpa [v, a] using _kinematics.velocityDerivative t ht
    have hx : HasDerivAt x (v t) t := by
      simpa [x, v] using _kinematics.positionDerivative t ht
    have hsum :=
      (hv.const_mul (R * m)).add
        ((hx.sub_const (x 0)).const_mul (L ^ 2 * B ^ 2))
    convert hsum.congr_deriv (hODE t ht) using 1 <;> rfl

  have hConserved (t : ℝ) (ht : 0 ≤ t) :
      conserved t = conserved 0 := by
    have hcontinuous : ContinuousOn conserved (Set.Icc 0 t) :=
      fun s hs =>
        (hConservedDeriv s hs.1).continuousAt.continuousWithinAt
    have hright : ∀ s ∈ Set.Ico (0 : ℝ) t,
        HasDerivWithinAt conserved 0 (Set.Ici s) s :=
      fun s hs => (hConservedDeriv s hs.1).hasDerivWithinAt
    exact
      constant_of_has_deriv_right_zero hcontinuous hright t
        ⟨ht, le_rfl⟩

  have hvLimit : Tendsto v atTop (nhds 0) := by
    simpa [v] using _asymptoticRest.velocityTendsToZero
  have hxLimit :
      Tendsto (fun t => x t - x 0) atTop
        (nhds (lengthInMeters setup.stoppingDistance)) := by
    simpa [x] using
      _asymptoticRest.displacementTendsToStoppingDistance
  have hConservedLimit :
      Tendsto conserved atTop
        (nhds
          ((R * m) * 0 +
            (L ^ 2 * B ^ 2) *
              lengthInMeters setup.stoppingDistance)) := by
    simpa [conserved] using
      (hvLimit.const_mul (R * m)).add
        (hxLimit.const_mul (L ^ 2 * B ^ 2))
  have hEventuallyConstant :
      conserved =ᶠ[atTop] fun _ : ℝ => R * m * v 0 := by
    filter_upwards [eventually_ge_atTop (0 : ℝ)] with t ht
    simpa [conserved] using hConserved t ht
  have hLimitEq :
      (R * m) * 0 +
          (L ^ 2 * B ^ 2) *
            lengthInMeters setup.stoppingDistance =
        R * m * v 0 :=
    tendsto_nhds_unique_of_eventuallyEq
      hConservedLimit tendsto_const_nhds hEventuallyConstant
  simp only [mul_zero, zero_add, hv₀] at hLimitEq

  change
    lengthInMeters setup.stoppingDistance =
      m * v₀ * R / (L ^ 2 * B ^ 2)
  have hdenom : L ^ 2 * B ^ 2 ≠ 0 :=
    mul_ne_zero (pow_ne_zero 2 hL.ne') (pow_ne_zero 2 hB.ne')
  apply (eq_div_iff hdenom).2
  calc
    lengthInMeters setup.stoppingDistance * (L ^ 2 * B ^ 2) =
        (L ^ 2 * B ^ 2) *
          lengthInMeters setup.stoppingDistance := by ring
    _ = R * m * v₀ := hLimitEq
    _ = m * v₀ * R := by ring

end PhyXMiniProblems.ProblemPhyXMini0977
