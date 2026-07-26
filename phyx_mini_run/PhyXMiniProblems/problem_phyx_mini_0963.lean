import Mathlib
import Physlib.Electromagnetism.Basic
import Physlib.Units.WithDim.Basic
import Physlib.Units.WithDim.Speed

noncomputable section

namespace PhyXMiniProblems.ProblemPhyXMini0963

open Dimension

/-!
# Magnetic force between two moving point charges

At the pictured instant, the positive charge `q` is at `(0, 0.300, 0) m`
and moves in the positive `x` direction.  The negative charge `q'` is at
`(0.400, 0, 0) m` and moves in the positive `y` direction.  The question
asks for the magnetic force exerted by `q'` on `q`.

Charges, speeds, and the requested force are retained as unit-independent
Physlib `Dimensionful` quantities.  Physlib's `Space 3` and
`Electromagnetism.MagneticField 3` retain the position and field roles.
Real-valued vectors below are explicitly coherent-SI readouts.

Assumption/target split:

* governing laws: the quasistatic magnetic field of a moving point charge,
  the magnetic Lorentz-force law, and the standard SI value of vacuum
  permeability;
* previous-part results: none;
* figure/data readouts: the two signed charges and speeds, both coordinate
  axes and the origin, the `0.300 m` and `0.400 m` position labels, particle
  colours/signs, and the rightward/upward velocity arrows;
* current target conclusions: the force is exactly
  `7.488 * 10^-8 N` in the positive `y` direction and consequently choice B,
  displayed as `7.49 * 10^-8 N` in that direction, is uniquely closest.

No premise or setup field assigns the requested force a value or direction.
-/

/-! ## Dimensionful quantities and coherent-SI readouts -/

/-- The physical dimension `M L T^-2` of force. -/
def forceDimension : Dimension :=
  M𝓭 * L𝓭 * T𝓭⁻¹ * T𝓭⁻¹

/-- Three-dimensional coherent-SI spatial vector readout. -/
abbrev SpatialVector : Type := EuclideanSpace ℝ (Fin 3)

/-- A signed, unit-independent electric charge. -/
abbrev SignedChargeQuantity : Type :=
  Dimensionful (WithDim C𝓭 ℝ)

/-- A nonnegative, unit-independent speed. -/
abbrev SpeedQuantity : Type := DimSpeed

/-- A unit-independent three-dimensional force vector. -/
abbrev ForceVectorQuantity : Type :=
  Dimensionful (WithDim forceDimension SpatialVector)

/-- Coherent-SI charge readout, in coulombs. -/
def chargeInCoulombs (charge : SignedChargeQuantity) : ℝ :=
  (charge UnitChoices.SI).val

/-- Microcoulomb readout used by the written charge data. -/
def chargeInMicrocoulombs (charge : SignedChargeQuantity) : ℝ :=
  (10 : ℝ) ^ 6 * chargeInCoulombs charge

/-- Coherent-SI speed readout, in metres per second. -/
def speedInMetersPerSecond (speed : SpeedQuantity) : ℝ :=
  ((speed UnitChoices.SI).val : ℝ)

/-- Coherent-SI force-vector readout, in newtons. -/
def forceVectorInNewtons (force : ForceVectorQuantity) : SpatialVector :=
  (force UnitChoices.SI).val

/-! ## Cartesian geometry and primary-figure vocabulary -/

/-- The two particles, retaining the prime on the source charge as a name. -/
inductive ParticleLabel where
  | q
  | qPrime
  deriving DecidableEq, Fintype, Repr

/-- The three Cartesian axes; the raster explicitly draws only `x` and `y`. -/
inductive CoordinateAxis where
  | x
  | y
  | z
  deriving DecidableEq, Fintype, Repr

/-- Signed directions along a Cartesian axis. -/
inductive AxisDirection where
  | positiveX
  | negativeX
  | positiveY
  | negativeY
  | positiveZ
  | negativeZ
  deriving DecidableEq, Fintype, Repr

/-- Plus/minus glyph shown inside a particle marker. -/
inductive ChargeSignGlyph where
  | plus
  | minus
  deriving DecidableEq, Repr

/-- Marker colours distinguished in the supplied raster. -/
inductive ParticleMarkerColor where
  | red
  | blue
  deriving DecidableEq, Repr

/-- Standard coherent-SI unit vector associated with an axis. -/
def axisVector : CoordinateAxis → SpatialVector
  | .x => EuclideanSpace.single (0 : Fin 3) 1
  | .y => EuclideanSpace.single (1 : Fin 3) 1
  | .z => EuclideanSpace.single (2 : Fin 3) 1

/-- Unit vector associated with an oriented Cartesian direction. -/
def axisDirectionVector : AxisDirection → SpatialVector
  | .positiveX => axisVector .x
  | .negativeX => -axisVector .x
  | .positiveY => axisVector .y
  | .negativeY => -axisVector .y
  | .positiveZ => axisVector .z
  | .negativeZ => -axisVector .z

/-- Mathlib's right-handed cross product transported to Euclidean space. -/
def spatialCross (left right : SpatialVector) : SpatialVector :=
  WithLp.toLp 2 (crossProduct left.ofLp right.ofLp)

/-- Interpret a metre-coordinate vector as a point of Physlib space. -/
def spacePointOfMeters (coordinates : SpatialVector) : Space 3 :=
  ⟨coordinates.ofLp⟩

/-- Read the coordinates of a Physlib point in the chosen coherent-SI chart. -/
def positionVectorInMeters (position : Space 3) : SpatialVector :=
  WithLp.toLp 2 position.val

/-- A nonzero vector points along an oriented axis when it is a positive
multiple of the corresponding unit vector. -/
def PointsInAxisDirection
    (vector : SpatialVector) (direction : AxisDirection) : Prop :=
  ∃ magnitude : ℝ, 0 < magnitude ∧
    vector = magnitude • axisDirectionVector direction

/-- Literal marker and arrow data visible in primary image `963.png`. -/
structure MovingPointChargesFigure where
  axisShown : CoordinateAxis → Bool
  originLabelShown : Bool
  particleMarkerShown : ParticleLabel → Bool
  printedParticleLabel : ParticleLabel → String
  markerColor : ParticleLabel → ParticleMarkerColor
  markerSignGlyph : ParticleLabel → ChargeSignGlyph
  particleLiesOnAxis : ParticleLabel → CoordinateAxis
  distanceLabelShown : ParticleLabel → Bool
  displayedAxisDistanceInMeters : ParticleLabel → ℝ
  velocityArrowShown : ParticleLabel → Bool
  printedVelocityLabel : ParticleLabel → String
  velocityArrowDirection : ParticleLabel → AxisDirection

/-- Particle labels transcribed from the raster. -/
def expectedParticleLabel : ParticleLabel → String
  | .q => "q"
  | .qPrime => "q'"

/-- Velocity labels transcribed from the raster. -/
def expectedVelocityLabel : ParticleLabel → String
  | .q => "v"
  | .qPrime => "v'"

/-- Marker colour transcribed from the raster. -/
def expectedMarkerColor : ParticleLabel → ParticleMarkerColor
  | .q => .red
  | .qPrime => .blue

/-- Charge-sign glyph transcribed from the raster. -/
def expectedSignGlyph : ParticleLabel → ChargeSignGlyph
  | .q => .plus
  | .qPrime => .minus

/-! ## Independent physical setup and instantaneous observables -/

/-!
The magnetic field and force are independent observables.  In particular,
neither is defined from the requested numerical answer or from an answer
choice.
-/
structure MovingPointChargeForceSetup where
  unitSystem : UnitChoices
  isPointCharge : ParticleLabel → Bool
  charge : ParticleLabel → SignedChargeQuantity
  speed : ParticleLabel → SpeedQuantity
  position : ParticleLabel → Space 3
  velocityUnitDirection : ParticleLabel → SpatialVector
  observationTime : Time
  electromagneticSystem : Electromagnetism.EMSystem
  magneticFieldDueToQPrime : Electromagnetism.MagneticField 3
  magneticForceOnQFromQPrime : ForceVectorQuantity
  figure : MovingPointChargesFigure

/-- Instantaneous velocity vector of a particle, in metres per second. -/
def velocityVectorInMetersPerSecond
    (setup : MovingPointChargeForceSetup)
    (particle : ParticleLabel) : SpatialVector :=
  speedInMetersPerSecond (setup.speed particle) •
    setup.velocityUnitDirection particle

/-- Displacement from `q'` to an arbitrary observation point, in metres. -/
def displacementFromQPrimeToPositionInMeters
    (setup : MovingPointChargeForceSetup)
    (observationPosition : Space 3) : SpatialVector :=
  positionVectorInMeters observationPosition -
    positionVectorInMeters (setup.position .qPrime)

/-- Displacement from `q'` to `q` at the pictured instant, in metres. -/
def displacementFromQPrimeToQInMeters
    (setup : MovingPointChargeForceSetup) : SpatialVector :=
  displacementFromQPrimeToPositionInMeters setup (setup.position .q)

/-- Magnetic field of `q'` evaluated at `q`, read in teslas. -/
def magneticFieldAtQInTeslas
    (setup : MovingPointChargeForceSetup) : SpatialVector :=
  setup.magneticFieldDueToQPrime setup.observationTime (setup.position .q)

/-! ## Written data and primary-image readouts -/

/-- The prose treats both objects as point charges. -/
structure MatchesMovingPointChargeScenario
    (setup : MovingPointChargeForceSetup) : Prop where
  bothParticlesArePointCharges : ∀ particle,
    setup.isPointCharge particle = true

/-- Signed charge and speed data stated in the problem. -/
structure MatchesWrittenChargeAndSpeedData
    (setup : MovingPointChargeForceSetup) : Prop where
  usesSIUnits : setup.unitSystem = UnitChoices.SI
  qChargeIsPlusEightMicrocoulombs :
    chargeInMicrocoulombs (setup.charge .q) = 8
  qPrimeChargeIsMinusFiveMicrocoulombs :
    chargeInMicrocoulombs (setup.charge .qPrime) = -5
  qSpeedIsNineTimesTenToTheFour :
    speedInMetersPerSecond (setup.speed .q) = 9 * 10 ^ 4
  qPrimeSpeedIsSixPointFiveTimesTenToTheFour :
    speedInMetersPerSecond (setup.speed .qPrime) = 65 * 10 ^ 3

/-!
Literal axes, labels, colours, positions, signs, and arrow directions from
the primary raster.  This predicate contains no force information.
-/
structure MatchesSuppliedMovingChargeFigure
    (setup : MovingPointChargeForceSetup) : Prop where
  xAxisShown : setup.figure.axisShown .x = true
  yAxisShown : setup.figure.axisShown .y = true
  zAxisNotShown : setup.figure.axisShown .z = false
  originOShown : setup.figure.originLabelShown = true
  bothParticleMarkersShown : ∀ particle,
    setup.figure.particleMarkerShown particle = true
  particleLabels : ∀ particle,
    setup.figure.printedParticleLabel particle =
      expectedParticleLabel particle
  particleColours : ∀ particle,
    setup.figure.markerColor particle = expectedMarkerColor particle
  particleSignGlyphs : ∀ particle,
    setup.figure.markerSignGlyph particle = expectedSignGlyph particle
  qLiesOnYAxis : setup.figure.particleLiesOnAxis .q = .y
  qPrimeLiesOnXAxis : setup.figure.particleLiesOnAxis .qPrime = .x
  bothDistanceLabelsShown : ∀ particle,
    setup.figure.distanceLabelShown particle = true
  qDistanceLabelReadsPointThree :
    setup.figure.displayedAxisDistanceInMeters .q = 3 / 10
  qPrimeDistanceLabelReadsPointFour :
    setup.figure.displayedAxisDistanceInMeters .qPrime = 2 / 5
  bothVelocityArrowsShown : ∀ particle,
    setup.figure.velocityArrowShown particle = true
  velocityLabels : ∀ particle,
    setup.figure.printedVelocityLabel particle =
      expectedVelocityLabel particle
  qVelocityArrowPointsRight :
    setup.figure.velocityArrowDirection .q = .positiveX
  qPrimeVelocityArrowPointsUp :
    setup.figure.velocityArrowDirection .qPrime = .positiveY

/-!
Metric interpretation of the two position labels and the two arrow
directions.  The unpictured `z` coordinate is zero.
-/
structure HasDepictedInstantaneousKinematics
    (setup : MovingPointChargeForceSetup) : Prop where
  qPosition : setup.position .q =
    spacePointOfMeters ((3 / 10 : ℝ) • axisVector .y)
  qPrimePosition : setup.position .qPrime =
    spacePointOfMeters ((2 / 5 : ℝ) • axisVector .x)
  qVelocityDirection :
    setup.velocityUnitDirection .q = axisDirectionVector .positiveX
  qPrimeVelocityDirection :
    setup.velocityUnitDirection .qPrime = axisDirectionVector .positiveY

/-- Positivity and nondegeneracy implicit in two distinct moving particles. -/
structure HasPhysicalMovingChargeParameters
    (setup : MovingPointChargeForceSetup) : Prop where
  bothSpeedsPositive : ∀ particle,
    0 < speedInMetersPerSecond (setup.speed particle)
  velocityDirectionsAreUnit : ∀ particle,
    ‖setup.velocityUnitDirection particle‖ = 1
  sourceAndTargetAreSeparated :
    ‖displacementFromQPrimeToQInMeters setup‖ ≠ 0
  vacuumPermeabilityPositive : 0 < setup.electromagneticSystem.μ₀

/-- Standard coherent-SI value `μ₀ = 4π * 10^-7` used by the model. -/
structure UsesStandardVacuumPermeability
    (setup : MovingPointChargeForceSetup) : Prop where
  standardSIReadout :
    setup.electromagneticSystem.μ₀ = 4 * Real.pi / 10 ^ 7

/-! ## Governing electromagnetic laws -/

/-!
Quasistatic magnetic field of the moving source point charge `q'`:

`B(x) = μ₀ q' / (4π |r|^3) (v' × r)`, where `r = x - x_{q'}`.

This is a general field law away from the source.  It does not state the
requested force or its answer-choice value.
-/
structure SatisfiesMovingPointChargeMagneticFieldLaw
    (setup : MovingPointChargeForceSetup) : Prop where
  fieldAtEveryNonSourcePosition : ∀ observationPosition : Space 3,
    ‖displacementFromQPrimeToPositionInMeters setup observationPosition‖ ≠ 0 →
      setup.magneticFieldDueToQPrime setup.observationTime
          observationPosition =
        (setup.electromagneticSystem.μ₀ *
            chargeInCoulombs (setup.charge .qPrime) /
            (4 * Real.pi *
              ‖displacementFromQPrimeToPositionInMeters
                setup observationPosition‖ ^ 3)) •
          spatialCross
            (velocityVectorInMetersPerSecond setup .qPrime)
            (displacementFromQPrimeToPositionInMeters
              setup observationPosition)

/-!
Magnetic part of the Lorentz-force law on `q`, `F = q (v × B)`.  The force
observable on the left is not otherwise constrained to the requested value.
-/
structure SatisfiesMagneticLorentzForceLaw
    (setup : MovingPointChargeForceSetup) : Prop where
  forceOnQFromQPrime :
    forceVectorInNewtons setup.magneticForceOnQFromQPrime =
      chargeInCoulombs (setup.charge .q) •
        spatialCross (velocityVectorInMetersPerSecond setup .q)
          (magneticFieldAtQInTeslas setup)

/-! ## Derived field, displayed answers, and requested force -/

/-- The depicted geometry gives the familiar `3-4-5` displacement vector
from `q'` to `q`. -/
lemma displacementFromQPrimeToQ_exact
    (setup : MovingPointChargeForceSetup)
    (hKinematics : HasDepictedInstantaneousKinematics setup) :
    displacementFromQPrimeToQInMeters setup =
      (-(2 / 5 : ℝ)) • axisVector .x +
        (3 / 10 : ℝ) • axisVector .y := by
  simp [displacementFromQPrimeToQInMeters,
    displacementFromQPrimeToPositionInMeters, positionVectorInMeters,
    hKinematics.qPosition, hKinematics.qPrimePosition,
    spacePointOfMeters]
  abel

/-- The source charge produces a `-z` magnetic field of
`1.04 * 10^-7 T` at `q`. -/
lemma magneticFieldAtQ_exact
    (setup : MovingPointChargeForceSetup)
    (hData : MatchesWrittenChargeAndSpeedData setup)
    (hKinematics : HasDepictedInstantaneousKinematics setup)
    (hPhysical : HasPhysicalMovingChargeParameters setup)
    (hVacuum : UsesStandardVacuumPermeability setup)
    (hFieldLaw : SatisfiesMovingPointChargeMagneticFieldLaw setup) :
    magneticFieldAtQInTeslas setup =
      (-(13 : ℝ) / (125 * 10 ^ 6)) • axisVector .z := by
  have hCharge :
      chargeInCoulombs (setup.charge .qPrime) =
        -(5 / 10 ^ 6 : ℝ) := by
    have h := hData.qPrimeChargeIsMinusFiveMicrocoulombs
    norm_num [chargeInMicrocoulombs] at h ⊢
    linarith
  have hNorm :
      ‖displacementFromQPrimeToQInMeters setup‖ = (1 / 2 : ℝ) := by
    rw [displacementFromQPrimeToQ_exact setup hKinematics,
      EuclideanSpace.norm_eq]
    simp [axisVector, EuclideanSpace.single, Fin.sum_univ_succ]
    norm_num
  have hCross :
      spatialCross (velocityVectorInMetersPerSecond setup .qPrime)
          (displacementFromQPrimeToQInMeters setup) =
        (26000 : ℝ) • axisVector .z := by
    rw [velocityVectorInMetersPerSecond,
      hData.qPrimeSpeedIsSixPointFiveTimesTenToTheFour,
      hKinematics.qPrimeVelocityDirection,
      displacementFromQPrimeToQ_exact setup hKinematics]
    ext i
    fin_cases i
    all_goals
      simp [spatialCross, axisDirectionVector, axisVector,
        cross_apply, EuclideanSpace.single]
    all_goals norm_num
  rw [magneticFieldAtQInTeslas,
    hFieldLaw.fieldAtEveryNonSourcePosition
      (setup.position .q) hPhysical.sourceAndTargetAreSeparated]
  change
    (setup.electromagneticSystem.μ₀ *
        chargeInCoulombs (setup.charge .qPrime) /
        (4 * Real.pi *
          ‖displacementFromQPrimeToQInMeters setup‖ ^ 3)) •
      spatialCross (velocityVectorInMetersPerSecond setup .qPrime)
        (displacementFromQPrimeToQInMeters setup) =
      (-(13 : ℝ) / (125 * 10 ^ 6)) • axisVector .z
  rw [hVacuum.standardSIReadout, hCharge, hNorm, hCross, smul_smul]
  congr 1
  field_simp [Real.pi_ne_zero]
  ring

/-- Labels attached to the four displayed multiple-choice answers. -/
inductive AnswerChoice where
  | A
  | B
  | C
  | D
  deriving DecidableEq, Fintype, Repr

/-- Force vector in newtons printed beside each answer label. -/
def displayedForceVectorInNewtons : AnswerChoice → SpatialVector
  | .A => ((749 : ℝ) / 10 ^ 10) • axisVector .x
  | .B => ((749 : ℝ) / 10 ^ 10) • axisVector .y
  | .C => ((749 : ℝ) / 10 ^ 11) • axisVector .y
  | .D => ((3 : ℝ) / (2 * 10 ^ 8)) • axisVector .y

/-- The answer label recorded in the source dataset. -/
def recordedDatasetAnswer : AnswerChoice := .B

/-- The vector agrees with a displayed vector to the `0.01 * 10^-8 N`
precision used in choice B. -/
def RoundsToDisplayedForcePrecision
    (actual displayed : SpatialVector) : Prop :=
  ‖actual - displayed‖ < 1 / (2 * 10 ^ 10)

/-- A displayed answer is uniquely closest to the actual force vector. -/
def IsUniqueClosestDisplayedForceAnswer
    (actual : SpatialVector) (selected : AnswerChoice) : Prop :=
  ∀ other, other ≠ selected →
    ‖actual - displayedForceVectorInNewtons selected‖ <
      ‖actual - displayedForceVectorInNewtons other‖

/-!
Blueprint declaration `thm:physics:phyx_mini_0963:target`.

The two cross products first make the source field point in `-z` and then
make the force on the positive target point in `+y`.  Its exact magnitude is
`7.488 * 10^-8 N`, which rounds to the `7.49 * 10^-8 N` vector displayed by
answer B.
-/
theorem problem_phyx_mini_0963
    (setup : MovingPointChargeForceSetup)
    (hScenario : MatchesMovingPointChargeScenario setup)
    (hData : MatchesWrittenChargeAndSpeedData setup)
    (hFigure : MatchesSuppliedMovingChargeFigure setup)
    (hKinematics : HasDepictedInstantaneousKinematics setup)
    (hPhysical : HasPhysicalMovingChargeParameters setup)
    (hVacuum : UsesStandardVacuumPermeability setup)
    (hFieldLaw : SatisfiesMovingPointChargeMagneticFieldLaw setup)
    (hForceLaw : SatisfiesMagneticLorentzForceLaw setup) :
    forceVectorInNewtons setup.magneticForceOnQFromQPrime =
        ((936 : ℝ) / (125 * 10 ^ 8)) • axisVector .y ∧
      ‖forceVectorInNewtons setup.magneticForceOnQFromQPrime‖ =
        (936 : ℝ) / (125 * 10 ^ 8) ∧
      PointsInAxisDirection
        (forceVectorInNewtons setup.magneticForceOnQFromQPrime)
        .positiveY ∧
      RoundsToDisplayedForcePrecision
        (forceVectorInNewtons setup.magneticForceOnQFromQPrime)
        (displayedForceVectorInNewtons .B) ∧
      IsUniqueClosestDisplayedForceAnswer
        (forceVectorInNewtons setup.magneticForceOnQFromQPrime) .B := by
  have hQCharge :
      chargeInCoulombs (setup.charge .q) = (8 / 10 ^ 6 : ℝ) := by
    have h := hData.qChargeIsPlusEightMicrocoulombs
    norm_num [chargeInMicrocoulombs] at h ⊢
    linarith
  have hField := magneticFieldAtQ_exact setup hData hKinematics
    hPhysical hVacuum hFieldLaw
  have hForce :
      forceVectorInNewtons setup.magneticForceOnQFromQPrime =
        ((936 : ℝ) / (125 * 10 ^ 8)) • axisVector .y := by
    rw [hForceLaw.forceOnQFromQPrime, hQCharge,
      velocityVectorInMetersPerSecond,
      hData.qSpeedIsNineTimesTenToTheFour,
      hKinematics.qVelocityDirection, hField]
    ext i
    fin_cases i
    all_goals
      simp [spatialCross, axisDirectionVector, axisVector,
        cross_apply, EuclideanSpace.single]
    all_goals norm_num
  refine ⟨hForce, ?_, ?_, ?_, ?_⟩
  · rw [hForce, norm_smul]
    norm_num [axisVector, EuclideanSpace.single]
  · refine ⟨(936 : ℝ) / (125 * 10 ^ 8), by positivity, ?_⟩
    simpa [axisDirectionVector] using hForce
  · rw [RoundsToDisplayedForcePrecision, hForce]
    simp only [displayedForceVectorInNewtons, ← sub_smul, norm_smul]
    norm_num [axisVector, EuclideanSpace.single, Real.norm_eq_abs]
  · rw [IsUniqueClosestDisplayedForceAnswer, hForce]
    intro other hOther
    fin_cases other
    · have hSelected :
          ‖((936 : ℝ) / (125 * 10 ^ 8)) • axisVector .y -
              displayedForceVectorInNewtons .B‖ =
            (1 / (5 * 10 ^ 10) : ℝ) := by
          simp only [displayedForceVectorInNewtons, ← sub_smul,
            norm_smul]
          norm_num [axisVector, EuclideanSpace.single,
            Real.norm_eq_abs]
      rw [hSelected, EuclideanSpace.norm_eq]
      simp [displayedForceVectorInNewtons, axisVector,
        EuclideanSpace.single, Fin.sum_univ_succ]
      have hSqrtNonnegative :
          0 ≤ Real.sqrt
            (((749 : ℝ) / 10 ^ 10) ^ 2 +
              ((936 : ℝ) / (125 * 10 ^ 8)) ^ 2) :=
        Real.sqrt_nonneg _
      have hSqrtSquared :
          (Real.sqrt
            (((749 : ℝ) / 10 ^ 10) ^ 2 +
              ((936 : ℝ) / (125 * 10 ^ 8)) ^ 2)) ^ 2 =
            ((749 : ℝ) / 10 ^ 10) ^ 2 +
              ((936 : ℝ) / (125 * 10 ^ 8)) ^ 2 := by
        rw [Real.sq_sqrt]
        positivity
      nlinarith
    · exact (hOther rfl).elim
    · simp only [displayedForceVectorInNewtons, ← sub_smul,
        norm_smul]
      norm_num [axisVector, EuclideanSpace.single,
        Real.norm_eq_abs]
    · simp only [displayedForceVectorInNewtons, ← sub_smul,
        norm_smul]
      norm_num [axisVector, EuclideanSpace.single,
        Real.norm_eq_abs]

end PhyXMiniProblems.ProblemPhyXMini0963
