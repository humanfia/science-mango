import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Physlib.ClassicalMechanics.HarmonicOscillator.Solution
import Physlib.Units.WithDim.Basic

noncomputable section

namespace PhyXMiniProblems.ProblemPhyXMini0237

open Dimension

/-!
# Period of a block attached to a spring with nonzero mass

A block of mass `M` is attached to the free end of a uniform spring of mass
`m`, equilibrium length `ℓ`, and force constant `k`.  The spring is fixed to a
wall at its other end and the system moves horizontally without friction.  A
spring point at distance `x` from the fixed end has velocity component
`vₓ = (x / ℓ) v`, where `v` is the block velocity component.  A short spring
element of length `dx` has mass `dm = (m / ℓ) dx`.

The basic physical quantities below are Physlib dimensionful quantities.
Real numbers occur only as signed scalar components, coherent-unit readouts,
integration coordinates, and displayed numerical coefficients.
-/

/-! ## Dimensionful quantities and coherent readouts -/

/-- A nonnegative physical mass, used for `M`, `m`, `dm`, and effective mass. -/
abbrev MassQuantity : Type := Dimensionful (WithDim M𝓭 NNReal)

/-- A nonnegative physical length, used for `ℓ`, `x`, and `dx`. -/
abbrev LengthQuantity : Type := Dimensionful (WithDim L𝓭 NNReal)

/-- A signed one-dimensional velocity component along the horizontal track. -/
abbrev SignedVelocityQuantity : Type :=
  Dimensionful (WithDim (L𝓭 * T𝓭⁻¹) ℝ)

/-- Spring force constant, with dimension force per length, or mass/time². -/
abbrev SpringStiffnessQuantity : Type :=
  Dimensionful (WithDim (M𝓭 * T𝓭⁻¹ * T𝓭⁻¹) NNReal)

/-- Uniform spring mass per unit equilibrium length. -/
abbrev LinearMassDensityQuantity : Type :=
  Dimensionful (WithDim (M𝓭 * L𝓭⁻¹) NNReal)

/-- Mechanical energy, with dimension mass·length²/time². -/
abbrev EnergyQuantity : Type :=
  Dimensionful
    (WithDim (M𝓭 * L𝓭 * L𝓭 * T𝓭⁻¹ * T𝓭⁻¹) NNReal)

/-- A nonnegative physical duration, used for the oscillation period. -/
abbrev TimeQuantity : Type := Dimensionful (WithDim T𝓭 NNReal)

/-- Scalar mass readout in a chosen coherent system of units. -/
def massReadout (units : UnitChoices) (mass : MassQuantity) : ℝ :=
  ((mass units).val : ℝ)

/-- Scalar length readout in a chosen coherent system of units. -/
def lengthReadout (units : UnitChoices) (length : LengthQuantity) : ℝ :=
  ((length units).val : ℝ)

/-- Signed scalar velocity component in a chosen coherent system of units. -/
def velocityReadout
    (units : UnitChoices) (velocity : SignedVelocityQuantity) : ℝ :=
  (velocity units).val

/-- Scalar spring-stiffness readout in a chosen coherent system of units. -/
def stiffnessReadout
    (units : UnitChoices) (stiffness : SpringStiffnessQuantity) : ℝ :=
  ((stiffness units).val : ℝ)

/-- Scalar linear-mass-density readout in a chosen coherent system of units. -/
def linearMassDensityReadout
    (units : UnitChoices) (density : LinearMassDensityQuantity) : ℝ :=
  ((density units).val : ℝ)

/-- Scalar energy readout in a chosen coherent system of units. -/
def energyReadout (units : UnitChoices) (energy : EnergyQuantity) : ℝ :=
  ((energy units).val : ℝ)

/-- Scalar duration readout in a chosen coherent system of units. -/
def timeReadout (units : UnitChoices) (time : TimeQuantity) : ℝ :=
  ((time units).val : ℝ)

/-- Kilogram readout of a physical mass. -/
def massInKilograms (mass : MassQuantity) : ℝ :=
  massReadout UnitChoices.SI mass

/-- Metre readout of a physical length. -/
def lengthInMeters (length : LengthQuantity) : ℝ :=
  lengthReadout UnitChoices.SI length

/-- Metres-per-second readout of a signed velocity component. -/
def velocityInMetersPerSecond (velocity : SignedVelocityQuantity) : ℝ :=
  velocityReadout UnitChoices.SI velocity

/-- Newton-per-metre readout of the spring force constant. -/
def stiffnessInNewtonsPerMeter (stiffness : SpringStiffnessQuantity) : ℝ :=
  stiffnessReadout UnitChoices.SI stiffness

/-- Kilogram-per-metre readout of the spring's linear mass density. -/
def linearMassDensityInKilogramsPerMeter
    (density : LinearMassDensityQuantity) : ℝ :=
  linearMassDensityReadout UnitChoices.SI density

/-- Joule readout of a physical energy. -/
def energyInJoules (energy : EnergyQuantity) : ℝ :=
  energyReadout UnitChoices.SI energy

/-- Second readout of a physical duration. -/
def timeInSeconds (time : TimeQuantity) : ℝ :=
  timeReadout UnitChoices.SI time

/-! ## Physical setup and labels from the primary figure -/

/-- Horizontal directions in the coordinate convention used by the figure. -/
inductive HorizontalDirection where
  | left
  | right
  deriving DecidableEq, Repr

/-- The two ends of the spring shown in the figure. -/
inductive SpringEnd where
  | wallSide
  | blockSide
  deriving DecidableEq, Repr

/-- Friction model for the horizontal support under the block. -/
inductive TrackFriction where
  | frictionless
  | dissipative
  deriving DecidableEq, Repr

/-- Spatial orientation of the track supporting the block. -/
inductive TrackOrientation where
  | horizontal
  | other
  deriving DecidableEq, Repr

/-- Dynamical regime specified by the problem. -/
inductive OscillationRegime where
  | simpleHarmonic
  | other
  deriving DecidableEq, Repr

/-- Phase relation among material points of the spring. -/
inductive SpringPhaseRelation where
  | inPhase
  | other
  deriving DecidableEq, Repr

/-- Text labels visible in the supplied spring--block diagram. -/
inductive FigureLabel where
  | massM
  | positionX
  | segmentLengthDx
  | blockVelocityV
  deriving DecidableEq, Repr

/-- Physical or graphical features to which the visible labels refer. -/
inductive FigureFeature where
  | block
  | distanceFromFixedEnd
  | springElement
  | rightwardVelocityArrow
  deriving DecidableEq, Repr

/-!
The distributed spring--block system and the auxiliary quantities needed to
state its continuum kinetic-energy model.

`illustratedPositionX`, `illustratedSegmentLengthDx`, and
`illustratedBlockVelocityV` are the quantities marked `x`, `dx`, and `v` in
the primary figure.  The functions `springVelocityAt` and `springSegmentMass`
describe arbitrary points and short segments, not only the illustrated one.
Neither `springEffectiveMass` nor `oscillationPeriod` is assigned its requested
value by this structure.
-/
structure MassiveSpringOscillatorSetup where
  blockMass : MassQuantity
  springMass : MassQuantity
  equilibriumLength : LengthQuantity
  springStiffness : SpringStiffnessQuantity
  springLinearMassDensity : LinearMassDensityQuantity
  springEffectiveMass : MassQuantity
  oscillationPeriod : TimeQuantity
  springVelocityAt :
    SignedVelocityQuantity → LengthQuantity → SignedVelocityQuantity
  springSegmentMass : LengthQuantity → LengthQuantity → MassQuantity
  springKineticEnergy : SignedVelocityQuantity → EnergyQuantity
  effectiveOscillator : ClassicalMechanics.HarmonicOscillator
  fixedEnd : SpringEnd
  movingEnd : SpringEnd
  trackFriction : TrackFriction
  trackOrientation : TrackOrientation
  oscillationRegime : OscillationRegime
  springPhaseRelation : SpringPhaseRelation
  positiveTrackDirection : HorizontalDirection
  illustratedPositionX : LengthQuantity
  illustratedSegmentLengthDx : LengthQuantity
  illustratedBlockVelocityV : SignedVelocityQuantity
  figureLabelTarget : FigureLabel → FigureFeature

/-- A point coordinate lies on the spring between the fixed and moving ends. -/
def IsSpringCoordinate
    (setup : MassiveSpringOscillatorSetup) (x : LengthQuantity) : Prop :=
  0 ≤ lengthInMeters x ∧
    lengthInMeters x ≤ lengthInMeters setup.equilibriumLength

/-- The segment beginning at `x` with length `dx` lies inside the spring. -/
def IsContainedSpringSegment
    (setup : MassiveSpringOscillatorSetup)
    (x dx : LengthQuantity) : Prop :=
  0 ≤ lengthInMeters x ∧
    0 ≤ lengthInMeters dx ∧
    lengthInMeters x + lengthInMeters dx ≤
      lengthInMeters setup.equilibriumLength

/-!
Qualitative and labeled information read from the primary bitmap.  The image
contains no numerical scale for `x`, `dx`, or `v`, so this predicate supplies
no requested period or effective-mass value.
-/
structure MatchesPrimaryFigure
    (setup : MassiveSpringOscillatorSetup) : Prop where
  springFixedAtWallOnLeft : setup.fixedEnd = .wallSide
  blockAttachedAtFreeEndOnRight : setup.movingEnd = .blockSide
  rightIsPositive : setup.positiveTrackDirection = .right
  illustratedElementIsInsideSpring :
    IsContainedSpringSegment setup setup.illustratedPositionX
      setup.illustratedSegmentLengthDx
  illustratedVelocityPointsRight :
    0 < velocityInMetersPerSecond setup.illustratedBlockVelocityV
  massLabelTargetsBlock : setup.figureLabelTarget .massM = .block
  xLabelTargetsDistanceFromFixedEnd :
    setup.figureLabelTarget .positionX = .distanceFromFixedEnd
  dxLabelTargetsSpringElement :
    setup.figureLabelTarget .segmentLengthDx = .springElement
  vLabelTargetsRightwardArrow :
    setup.figureLabelTarget .blockVelocityV = .rightwardVelocityArrow

/-!
Problem-statement data that specify the idealized regime.  Positivity is
separated below.  In particular, no value of the effective spring mass or
oscillation period appears here.
-/
structure MatchesProblemDescription
    (setup : MassiveSpringOscillatorSetup) : Prop where
  trackIsHorizontal : setup.trackOrientation = .horizontal
  trackIsFrictionless : setup.trackFriction = .frictionless
  motionIsSimpleHarmonic : setup.oscillationRegime = .simpleHarmonic
  allSpringPortionsMoveInPhase : setup.springPhaseRelation = .inPhase

/-- Positivity and nondegeneracy of the physical spring--block parameters. -/
structure HasPhysicalParameters
    (setup : MassiveSpringOscillatorSetup) : Prop where
  blockMassPositive : 0 < massInKilograms setup.blockMass
  springMassPositive : 0 < massInKilograms setup.springMass
  equilibriumLengthPositive : 0 < lengthInMeters setup.equilibriumLength
  stiffnessPositive :
    0 < stiffnessInNewtonsPerMeter setup.springStiffness
  effectiveSpringMassNonnegative :
    0 ≤ massInKilograms setup.springEffectiveMass

/-! ## Governing continuum and oscillator laws -/

/-!
The model laws for a uniform finite-mass spring.

* `uniformLinearMassDensity` and `shortSegmentMassLaw` encode
  `dm = (m / ℓ) dx`.
* `linearInPhaseVelocityProfile` encodes `vₓ = (x / ℓ) v`.
* `continuumSpringKineticEnergy` is the integral of `½ vₓ² dm`.
* `effectiveMassKineticEquivalence` defines effective mass by equality of
  kinetic energies, without assigning it the value `m / 3`.
* The last three fields connect the dimensionful system to Physlib's scalar
  harmonic-oscillator model in coherent SI units.

No field states either current target conclusion.
-/
structure SatisfiesMassiveSpringLaws
    (setup : MassiveSpringOscillatorSetup) : Prop where
  uniformLinearMassDensity :
    ∀ units : UnitChoices,
      linearMassDensityReadout units setup.springLinearMassDensity =
        massReadout units setup.springMass /
          lengthReadout units setup.equilibriumLength
  shortSegmentMassLaw :
    ∀ (x dx : LengthQuantity),
      IsContainedSpringSegment setup x dx →
      ∀ units : UnitChoices,
        massReadout units (setup.springSegmentMass x dx) =
          linearMassDensityReadout units setup.springLinearMassDensity *
            lengthReadout units dx
  linearInPhaseVelocityProfile :
    ∀ (blockVelocity : SignedVelocityQuantity) (x : LengthQuantity),
      IsSpringCoordinate setup x →
      ∀ units : UnitChoices,
        velocityReadout units (setup.springVelocityAt blockVelocity x) =
          lengthReadout units x /
              lengthReadout units setup.equilibriumLength *
            velocityReadout units blockVelocity
  continuumSpringKineticEnergy :
    ∀ (blockVelocity : SignedVelocityQuantity) (units : UnitChoices),
      energyReadout units (setup.springKineticEnergy blockVelocity) =
        ∫ x in (0 : ℝ)..lengthReadout units setup.equilibriumLength,
          (1 / 2 : ℝ) *
            linearMassDensityReadout units setup.springLinearMassDensity *
            ((x / lengthReadout units setup.equilibriumLength) *
                velocityReadout units blockVelocity) ^ 2
  effectiveMassKineticEquivalence :
    ∀ (blockVelocity : SignedVelocityQuantity) (units : UnitChoices),
      energyReadout units (setup.springKineticEnergy blockVelocity) =
        (1 / 2 : ℝ) * massReadout units setup.springEffectiveMass *
          velocityReadout units blockVelocity ^ 2
  effectiveOscillatorMass :
    setup.effectiveOscillator.m =
      massInKilograms setup.blockMass +
        massInKilograms setup.springEffectiveMass
  effectiveOscillatorStiffness :
    setup.effectiveOscillator.k =
      stiffnessInNewtonsPerMeter setup.springStiffness
  harmonicOscillatorPeriodLaw :
    timeInSeconds setup.oscillationPeriod =
      setup.effectiveOscillator.period

/-!
Integrating the continuum energy density with the linear velocity profile
gives `K_spring = ½ (m/3) v²` in SI units.  This is a derived intermediate
result, not a field of `SatisfiesMassiveSpringLaws`.
-/
lemma springKineticEnergy_eq_oneHalf_oneThirdMass_v_sq
    (setup : MassiveSpringOscillatorSetup)
    (_physical : HasPhysicalParameters setup)
    (_laws : SatisfiesMassiveSpringLaws setup)
    (blockVelocity : SignedVelocityQuantity) :
    energyInJoules (setup.springKineticEnergy blockVelocity) =
      (1 / 2 : ℝ) * (massInKilograms setup.springMass / 3) *
        velocityInMetersPerSecond blockVelocity ^ 2 := by
  rw [show
    energyInJoules (setup.springKineticEnergy blockVelocity) =
        ∫ x in (0 : ℝ)..lengthInMeters setup.equilibriumLength,
          (1 / 2 : ℝ) *
            linearMassDensityInKilogramsPerMeter
              setup.springLinearMassDensity *
            ((x / lengthInMeters setup.equilibriumLength) *
                velocityInMetersPerSecond blockVelocity) ^ 2 by
      simpa [energyInJoules, lengthInMeters,
        linearMassDensityInKilogramsPerMeter,
        velocityInMetersPerSecond] using
        _laws.continuumSpringKineticEnergy blockVelocity UnitChoices.SI]
  rw [show
    linearMassDensityInKilogramsPerMeter setup.springLinearMassDensity =
        massInKilograms setup.springMass /
          lengthInMeters setup.equilibriumLength by
      simpa [linearMassDensityInKilogramsPerMeter, massInKilograms,
        lengthInMeters] using
        _laws.uniformLinearMassDensity UnitChoices.SI]
  let ℓ := lengthInMeters setup.equilibriumLength
  let m := massInKilograms setup.springMass
  let v := velocityInMetersPerSecond blockVelocity
  have hℓ : ℓ ≠ 0 := ne_of_gt _physical.equilibriumLengthPositive
  change
    (∫ x in (0 : ℝ)..ℓ,
      (1 / 2 : ℝ) * (m / ℓ) * ((x / ℓ) * v) ^ 2) =
        (1 / 2 : ℝ) * (m / 3) * v ^ 2
  calc
    (∫ x in (0 : ℝ)..ℓ,
      (1 / 2 : ℝ) * (m / ℓ) * ((x / ℓ) * v) ^ 2) =
        (1 / 2 * (m / ℓ) * (v ^ 2 / ℓ ^ 2)) *
          (∫ x in (0 : ℝ)..ℓ, x ^ 2) := by
      rw [← intervalIntegral.integral_const_mul]
      apply intervalIntegral.integral_congr
      intro x _
      ring
    _ = (1 / 2 : ℝ) * (m / 3) * v ^ 2 := by
      rw [integral_pow]
      norm_num
      field_simp [hℓ]

/-!
The distributed spring has effective inertial mass `m/3` when its pointwise
speed grows linearly from zero at the wall to the block speed at the free end.
-/
lemma springEffectiveMass_eq_oneThirdSpringMass
    (setup : MassiveSpringOscillatorSetup)
    (_figure : MatchesPrimaryFigure setup)
    (_physical : HasPhysicalParameters setup)
    (_laws : SatisfiesMassiveSpringLaws setup) :
    massInKilograms setup.springEffectiveMass =
      massInKilograms setup.springMass / 3 := by
  let v := setup.illustratedBlockVelocityV
  have hcontinuum :=
    springKineticEnergy_eq_oneHalf_oneThirdMass_v_sq
      setup _physical _laws v
  have heffective :
      energyInJoules (setup.springKineticEnergy v) =
        (1 / 2 : ℝ) * massInKilograms setup.springEffectiveMass *
          velocityInMetersPerSecond v ^ 2 := by
    simpa [energyInJoules, massInKilograms,
      velocityInMetersPerSecond] using
      _laws.effectiveMassKineticEquivalence v UnitChoices.SI
  have hv : 0 < velocityInMetersPerSecond v :=
    _figure.illustratedVelocityPointsRight
  nlinarith [sq_pos_of_pos hv]

/-! ## Multiple-choice metadata and final target -/

/-- Labels of the four periods printed with the problem. -/
inductive AnswerChoice where
  | A
  | B
  | C
  | D
  deriving DecidableEq, Repr

/-- The period in seconds printed beside an answer label. -/
def AnswerChoice.periodInSeconds
    (choice : AnswerChoice) (setup : MassiveSpringOscillatorSetup) : ℝ :=
  let M := massInKilograms setup.blockMass
  let m := massInKilograms setup.springMass
  let k := stiffnessInNewtonsPerMeter setup.springStiffness
  match choice with
  | .A => 2 * Real.pi * Real.sqrt ((M + 3 * m) / k)
  | .B => 2 * Real.pi * Real.sqrt ((M + m / 2) / k)
  | .C => 2 * Real.pi * Real.sqrt ((M + m) / k)
  | .D => 2 * Real.pi * Real.sqrt ((M + m / 3) / k)

/-- The answer label recorded in the supplied dataset. -/
def recordedAnswerChoice : AnswerChoice := .D

/-- A displayed choice agrees with the physical period readout. -/
def MatchesAnswerChoice
    (setup : MassiveSpringOscillatorSetup) (choice : AnswerChoice) : Prop :=
  timeInSeconds setup.oscillationPeriod = choice.periodInSeconds setup

/-!
The block and one third of the spring mass supply the effective inertia.
Consequently

`T = 2π √((M + m/3) / k)`,

which is the formula printed as answer D.

This formalizes `thm:physics:phyx_mini_0237:target`.
-/
theorem problem_phyx_mini_0237
    (setup : MassiveSpringOscillatorSetup)
    (_description : MatchesProblemDescription setup)
    (_figure : MatchesPrimaryFigure setup)
    (_physical : HasPhysicalParameters setup)
    (_laws : SatisfiesMassiveSpringLaws setup) :
    timeInSeconds setup.oscillationPeriod =
      2 * Real.pi *
        Real.sqrt
          ((massInKilograms setup.blockMass +
              massInKilograms setup.springMass / 3) /
            stiffnessInNewtonsPerMeter setup.springStiffness) := by
  have heffective :=
    springEffectiveMass_eq_oneThirdSpringMass
      setup _figure _physical _laws
  rw [_laws.harmonicOscillatorPeriodLaw]
  rw [ClassicalMechanics.HarmonicOscillator.period_eq]
  change
    2 * Real.pi /
        Real.sqrt
          (setup.effectiveOscillator.k / setup.effectiveOscillator.m) =
      2 * Real.pi *
        Real.sqrt
          ((massInKilograms setup.blockMass +
              massInKilograms setup.springMass / 3) /
            stiffnessInNewtonsPerMeter setup.springStiffness)
  rw [_laws.effectiveOscillatorStiffness,
    _laws.effectiveOscillatorMass, heffective]
  calc
    2 * Real.pi /
        Real.sqrt
          (stiffnessInNewtonsPerMeter setup.springStiffness /
            (massInKilograms setup.blockMass +
              massInKilograms setup.springMass / 3)) =
      2 * Real.pi *
        (Real.sqrt
          (stiffnessInNewtonsPerMeter setup.springStiffness /
            (massInKilograms setup.blockMass +
              massInKilograms setup.springMass / 3)))⁻¹ := by
        rw [div_eq_mul_inv]
    _ = 2 * Real.pi *
        Real.sqrt
          ((massInKilograms setup.blockMass +
              massInKilograms setup.springMass / 3) /
            stiffnessInNewtonsPerMeter setup.springStiffness) := by
      rw [← Real.sqrt_inv, inv_div]

/-! The same conclusion stated against the dataset's recorded answer label. -/
theorem oscillationPeriod_matches_recordedAnswerD
    (setup : MassiveSpringOscillatorSetup)
    (_description : MatchesProblemDescription setup)
    (_figure : MatchesPrimaryFigure setup)
    (_physical : HasPhysicalParameters setup)
    (_laws : SatisfiesMassiveSpringLaws setup) :
    MatchesAnswerChoice setup recordedAnswerChoice := by
  simpa [MatchesAnswerChoice, recordedAnswerChoice,
    AnswerChoice.periodInSeconds] using
    problem_phyx_mini_0237 setup _description _figure _physical _laws

end PhyXMiniProblems.ProblemPhyXMini0237
