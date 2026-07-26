import Mathlib
import Physlib.Units.WithDim.Speed

noncomputable section

namespace PhyXMiniProblems.ProblemPhyXMini0865

open Dimension

/-!
# Proton crossing electrostatic equipotential curves

The primary figure shows a proton following the blue trajectory from point
`A` to point `B`.  Point `A` lies on the dashed `30 V` equipotential, the path
crosses a dashed `10 V` equipotential, and point `B` lies on the dashed
`-10 V` equipotential.  The red circle with a plus sign is treated as the
moving proton marker because it lies on the trajectory between the two
labelled points.

Speeds, mass, charge, and electric potential are unit-independent Physlib
quantities.  Real numbers occur below only as explicitly named coherent-SI
readouts.  The answer `1 * 10^5 m/s` is rounded: using standard proton data
and conservation of `K + q V` gives about `1.008 * 10^5 m/s`.  The final
statement therefore selects the unique nearest displayed answer instead of
asserting an unphysical exact equality with `100000 m/s`.

Assumption/target split:

* governing laws: nonrelativistic kinetic energy `m v^2 / 2`, electrostatic
  potential energy `q V`, and conservation of their sum from `A` to `B`;
* previous-part results: none;
* figure/data readouts: the initial `50000 m/s` speed, the three displayed
  equipotential values, membership of `A` and `B` in the `30 V` and `-10 V`
  curves, the directed trajectory, and the positive proton marker;
* target conclusion: answer D, whose displayed value is `100000 m/s`, is the
  unique nearest displayed speed to the speed at `B`.

No target speed or answer label occurs in a setup field or premise.
-/

/-! ## Dimensionful physical quantities and coherent-SI readouts -/

/-- The physical dimension of energy, `M L^2 T^-2`. -/
def energyDimension : Dimension :=
  M𝓭 * L𝓭 * L𝓭 * T𝓭⁻¹ * T𝓭⁻¹

/-- Electric potential has the physical dimension energy per charge. -/
def electricPotentialDimension : Dimension :=
  energyDimension * C𝓭⁻¹

/-- A nonnegative, unit-independent physical mass. -/
abbrev MassQuantity : Type :=
  Dimensionful (WithDim M𝓭 NNReal)

/-- A signed, unit-independent electric charge. -/
abbrev SignedChargeQuantity : Type :=
  Dimensionful (WithDim C𝓭 ℝ)

/-- A signed, unit-independent electrostatic potential. -/
abbrev ElectricPotentialQuantity : Type :=
  Dimensionful (WithDim electricPotentialDimension ℝ)

/-- A nonnegative, unit-independent physical speed. -/
abbrev SpeedQuantity : Type := DimSpeed

/-- Coherent-SI readout of a physical speed, in metres per second. -/
def speedInMetersPerSecond (speed : SpeedQuantity) : ℝ :=
  ((speed UnitChoices.SI).val : ℝ)

/-- Coherent-SI readout of a physical mass, in kilograms. -/
def massInKilograms (mass : MassQuantity) : ℝ :=
  ((mass UnitChoices.SI).val : ℝ)

/-- Coherent-SI readout of a signed physical charge, in coulombs. -/
def chargeInCoulombs (charge : SignedChargeQuantity) : ℝ :=
  (charge UnitChoices.SI).val

/-- Coherent-SI readout of electrostatic potential, in volts. -/
def potentialInVolts (potential : ElectricPotentialQuantity) : ℝ :=
  (potential UnitChoices.SI).val

/-! ## Named points, curves, and literal figure content -/

/-- The two black points labelled on the proton trajectory. -/
inductive TrajectoryPoint where
  | A
  | B
  deriving DecidableEq, Fintype, Repr

/-- The three green dashed equipotential curves, ordered left to right. -/
inductive EquipotentialCurve where
  | thirtyVolt
  | tenVolt
  | minusTenVolt
  deriving DecidableEq, Fintype, Repr

/-- The sign glyph drawn in the red moving-particle marker. -/
inductive ChargeGlyph where
  | plus
  | minus
  deriving DecidableEq, Repr

/-- Particle species distinguished by this problem. -/
inductive ParticleSpecies where
  | proton
  | other
  deriving DecidableEq, Repr

/-- The volt number printed under each dashed equipotential curve. -/
def displayedPotentialInVolts : EquipotentialCurve → ℝ
  | .thirtyVolt => 30
  | .tenVolt => 10
  | .minusTenVolt => -10

/-!
Literal typed content of image `865.png`.  The curve potentials are physical
dimensionful quantities; their printed volt values are imposed separately by
`MatchesProblemAndFigureReadouts`.
-/
structure EquipotentialTrajectoryFigure where
  curvePotential : EquipotentialCurve → ElectricPotentialQuantity
  dashedCurveShown : EquipotentialCurve → Bool
  pointCurve : TrajectoryPoint → EquipotentialCurve
  bluePathShown : Bool
  pathStart : TrajectoryPoint
  pathEnd : TrajectoryPoint
  movingParticleMarker : ParticleSpecies
  markerGlyph : ChargeGlyph
  markerBetweenAAndB : Bool

/-!
Independent physical quantities of the experiment.  In particular,
`speedAt .B` is an unknown observable and is not defined from an answer
choice.
-/
structure ProtonElectrostaticSetup where
  particleSpecies : ParticleSpecies
  particleMass : MassQuantity
  particleCharge : SignedChargeQuantity
  speedAt : TrajectoryPoint → SpeedQuantity
  figure : EquipotentialTrajectoryFigure

/-- Electrostatic potential at a named point, read from its equipotential. -/
def potentialAt
    (setup : ProtonElectrostaticSetup)
    (point : TrajectoryPoint) : ElectricPotentialQuantity :=
  setup.figure.curvePotential (setup.figure.pointCurve point)

/-! ## Problem data, primary-image evidence, and proton calibration -/

/--
Problem-statement and primary-image readouts.  This predicate records no speed
at `B` and no answer choice.
-/
structure MatchesProblemAndFigureReadouts
    (setup : ProtonElectrostaticSetup) : Prop where
  particleIsProton : setup.particleSpecies = .proton
  initialSpeedMetersPerSecond :
    speedInMetersPerSecond (setup.speedAt .A) = 50000
  everyDashedCurveIsShown :
    ∀ curve, setup.figure.dashedCurveShown curve = true
  printedCurvePotentials :
    ∀ curve,
      potentialInVolts (setup.figure.curvePotential curve) =
        displayedPotentialInVolts curve
  pointAOnThirtyVoltCurve :
    setup.figure.pointCurve .A = .thirtyVolt
  pointBOnMinusTenVoltCurve :
    setup.figure.pointCurve .B = .minusTenVolt
  bluePathIsShown : setup.figure.bluePathShown = true
  pathBeginsAtA : setup.figure.pathStart = .A
  pathEndsAtB : setup.figure.pathEnd = .B
  markerIsProton : setup.figure.movingParticleMarker = .proton
  markerHasPlusGlyph : setup.figure.markerGlyph = .plus
  markerLiesBetweenAAndB : setup.figure.markerBetweenAAndB = true

/-!
Standard coherent-SI calibration of a proton.  The elementary charge is exact
in SI; the proton mass is the standard measured value used by the model.
-/
structure HasStandardProtonCalibration
    (setup : ProtonElectrostaticSetup) : Prop where
  massKilograms :
    massInKilograms setup.particleMass =
      167262192369 / (10 : ℝ) ^ 38
  chargeCoulombs :
    chargeInCoulombs setup.particleCharge =
      1602176634 / (10 : ℝ) ^ 28

/-- Positivity conditions for the physical particle parameters. -/
structure HasPhysicalParticleParameters
    (setup : ProtonElectrostaticSetup) : Prop where
  massPositive : 0 < massInKilograms setup.particleMass
  chargePositive : 0 < chargeInCoulombs setup.particleCharge

/-! ## Governing electrostatic mechanics -/

/-- Nonrelativistic kinetic energy readout, in joules. -/
def kineticEnergyInJoules
    (setup : ProtonElectrostaticSetup)
    (point : TrajectoryPoint) : ℝ :=
  (1 / 2 : ℝ) * massInKilograms setup.particleMass *
    (speedInMetersPerSecond (setup.speedAt point)) ^ 2

/-- Electrostatic potential energy readout `q V`, in joules. -/
def electrostaticPotentialEnergyInJoules
    (setup : ProtonElectrostaticSetup)
    (point : TrajectoryPoint) : ℝ :=
  chargeInCoulombs setup.particleCharge *
    potentialInVolts (potentialAt setup point)

/-!
The governing law used by the question: mechanical energy `K + q V` is
conserved between the two named points.  This law does not mention a target
speed or an answer choice.
-/
structure SatisfiesElectrostaticEnergyConservation
    (setup : ProtonElectrostaticSetup) : Prop where
  energyConservedFromAToB :
    kineticEnergyInJoules setup .A +
        electrostaticPotentialEnergyInJoules setup .A =
      kineticEnergyInJoules setup .B +
        electrostaticPotentialEnergyInJoules setup .B

/-! ## Displayed choices and rounded target -/

/-- Labels of the four displayed multiple-choice answers. -/
inductive AnswerChoice where
  | A
  | B
  | C
  | D
  deriving DecidableEq, Fintype, Repr

/-- Displayed answer speeds, all read as metre-per-second numbers. -/
def displayedAnswerSpeedInMetersPerSecond : AnswerChoice → ℝ
  | .A => 59000
  | .B => 149000
  | .C => 19000
  | .D => 100000

/--
`selected` is the unique displayed answer numerically closest to an actual SI
speed readout.  This generic rounding predicate does not privilege answer D.
-/
def IsUniqueNearestDisplayedSpeedAnswer
    (actualSpeedMetersPerSecond : ℝ) (selected : AnswerChoice) : Prop :=
  ∀ other, other ≠ selected →
    |actualSpeedMetersPerSecond -
        displayedAnswerSpeedInMetersPerSecond selected| <
      |actualSpeedMetersPerSecond -
        displayedAnswerSpeedInMetersPerSecond other|

/--
Blueprint label: `thm:physics:phyx_mini_0865:target`.

For a standard proton moving through the supplied electrostatic-potential
diagram, conservation of `K + q V` makes answer D (`1 * 10^5 m/s`) the unique
nearest displayed value for the speed at point B.
-/
theorem proton_speed_at_point_B
    (setup : ProtonElectrostaticSetup)
    (hFigure : MatchesProblemAndFigureReadouts setup)
    (hProton : HasStandardProtonCalibration setup)
    (hPhysical : HasPhysicalParticleParameters setup)
    (hEnergy : SatisfiesElectrostaticEnergyConservation setup) :
    IsUniqueNearestDisplayedSpeedAnswer
      (speedInMetersPerSecond (setup.speedAt .B)) .D := by
  have hPotentialA :
      potentialInVolts (potentialAt setup .A) = 30 := by
    simpa [potentialAt, hFigure.pointAOnThirtyVoltCurve,
      displayedPotentialInVolts] using
      hFigure.printedCurvePotentials EquipotentialCurve.thirtyVolt
  have hPotentialB :
      potentialInVolts (potentialAt setup .B) = -10 := by
    simpa [potentialAt, hFigure.pointBOnMinusTenVoltCurve,
      displayedPotentialInVolts] using
      hFigure.printedCurvePotentials EquipotentialCurve.minusTenVolt
  let vB : ℝ := speedInMetersPerSecond (setup.speedAt .B)
  have hvB_nonnegative : 0 ≤ vB := by
    dsimp [vB, speedInMetersPerSecond]
    positivity
  have hConservation := hEnergy.energyConservedFromAToB
  simp only [kineticEnergyInJoules,
    electrostaticPotentialEnergyInJoules] at hConservation
  rw [hFigure.initialSpeedMetersPerSecond, hProton.massKilograms,
    hProton.chargeCoulombs, hPotentialA, hPotentialB] at hConservation
  change (1 / 2 : ℝ) * (167262192369 / 10 ^ 38) * 50000 ^ 2 +
      (1602176634 / 10 ^ 28) * 30 =
    (1 / 2 : ℝ) * (167262192369 / 10 ^ 38) * vB ^ 2 +
      (1602176634 / 10 ^ 28) * (-10) at hConservation
  norm_num at hConservation
  have hvB_lower : (79500 : ℝ) < vB := by
    nlinarith
  have hvB_upper : vB < (124500 : ℝ) := by
    nlinarith
  change IsUniqueNearestDisplayedSpeedAnswer vB .D
  unfold IsUniqueNearestDisplayedSpeedAnswer
  intro other hOther
  cases other with
  | A =>
      rw [← sq_lt_sq]
      simp only [displayedAnswerSpeedInMetersPerSecond]
      nlinarith
  | B =>
      rw [← sq_lt_sq]
      simp only [displayedAnswerSpeedInMetersPerSecond]
      nlinarith
  | C =>
      rw [← sq_lt_sq]
      simp only [displayedAnswerSpeedInMetersPerSecond]
      nlinarith
  | D =>
      exact (hOther rfl).elim

end PhyXMiniProblems.ProblemPhyXMini0865
