import Mathlib
import Physlib.SpaceAndTime.Space.LengthUnit
import Physlib.Units.WithDim.Basic

/- USER: The assigned Lean file did not exist when this autoformalization task began. -/

noncomputable section

namespace PhyXMiniProblems.ProblemPhyXMini0968

open Dimension

/-!
# Current required to separate two parallel rods joined by springs

Two long rigid conducting rods of length `0.50 m` lie parallel on a
frictionless table.  A lightweight conducting spring joins the rods at each
end.  The two rods carry equal current magnitudes in opposite directions, so
their magnetic interaction is repulsive.  At static equilibrium that force
is balanced by the restoring forces of the two identical springs.

Physical length, current, force, spring stiffness, and vacuum permeability
are represented by unit-independent Physlib `Dimensionful` quantities.  Real
numbers occur only as selected-unit readouts and displayed answer values.

Assumption/target split:

* governing laws: the separation is `l₀ + x`, each spring obeys Hooke's law,
  the two spring forces add, the long-parallel-wire force is
  `μ₀ I² L / (2 π d)`, and every recorded operating point is in static
  equilibrium;
* previous-part results: none;
* figure/data readouts: two parallel horizontal rods, one spring at each end,
  opposite current arrows, `L = 0.50 m`, the two measured `(I,x)` pairs, and
  the requested extension `x = 1.00 cm`;
* current target conclusions: the calibrated value of `l₀`, the squared
  current at the requested extension, and the unique closest displayed answer
  `16.0 A` (choice B).

The requested current is an independent dimensionful observable.  Its value,
its square, and answer B do not occur in any premise structure.
-/

/-! ## Dimensionful physical quantities and unit readouts -/

/-- Electric current has physical dimension charge per time. -/
def electricCurrentDimension : Dimension :=
  C𝓭 * T𝓭⁻¹

/-- Force has physical dimension `M L T⁻²`. -/
def forceDimension : Dimension :=
  M𝓭 * L𝓭 * T𝓭⁻¹ * T𝓭⁻¹

/-- A spring force constant has dimension force per length, namely `M T⁻²`. -/
def springStiffnessDimension : Dimension :=
  M𝓭 * T𝓭⁻¹ * T𝓭⁻¹

/-- Vacuum permeability has SI dimension `N A⁻² = M L C⁻²`. -/
def magneticPermeabilityDimension : Dimension :=
  M𝓭 * L𝓭 * C𝓭⁻¹ * C𝓭⁻¹

/-- A nonnegative, unit-independent physical length. -/
abbrev LengthMagnitude : Type :=
  Dimensionful (WithDim L𝓭 NNReal)

/-- A nonnegative, unit-independent electric-current magnitude. -/
abbrev ElectricCurrentMagnitude : Type :=
  Dimensionful (WithDim electricCurrentDimension NNReal)

/-- A nonnegative, unit-independent force magnitude. -/
abbrev ForceMagnitude : Type :=
  Dimensionful (WithDim forceDimension NNReal)

/-- A nonnegative, unit-independent spring stiffness. -/
abbrev SpringStiffnessMagnitude : Type :=
  Dimensionful (WithDim springStiffnessDimension NNReal)

/-- A nonnegative, unit-independent magnetic permeability. -/
abbrev MagneticPermeabilityMagnitude : Type :=
  Dimensionful (WithDim magneticPermeabilityDimension NNReal)

/-- Read a nonnegative dimensionful quantity in coherent SI units. -/
def coherentSIReadout {d : Dimension}
    (quantity : Dimensionful (WithDim d NNReal)) : ℝ :=
  ((quantity UnitChoices.SI).val : ℝ)

/-- Read a physical length in a selected length unit. -/
def lengthReadout
    (unit : LengthUnit) (length : LengthMagnitude) : ℝ :=
  ((length {UnitChoices.SI with length := unit}).val : ℝ)

/-- Coherent-SI length readout, in metres. -/
def lengthInMeters (length : LengthMagnitude) : ℝ :=
  coherentSIReadout length

/-- Coherent-SI current readout, in amperes. -/
def currentInAmperes (current : ElectricCurrentMagnitude) : ℝ :=
  coherentSIReadout current

/-- Coherent-SI force readout, in newtons. -/
def forceInNewtons (force : ForceMagnitude) : ℝ :=
  coherentSIReadout force

/-- Coherent-SI spring-stiffness readout, in newtons per metre. -/
def springStiffnessInNewtonsPerMeter
    (stiffness : SpringStiffnessMagnitude) : ℝ :=
  coherentSIReadout stiffness

/-- Coherent-SI vacuum-permeability readout, in newtons per ampere squared. -/
def magneticPermeabilityInNewtonsPerAmpereSquared
    (permeability : MagneticPermeabilityMagnitude) : ℝ :=
  coherentSIReadout permeability

/-! ## Apparatus labels and primary-figure evidence -/

/-- The upper and lower rods distinguished in the supplied image. -/
inductive RodLabel where
  | upper
  | lower
  deriving DecidableEq, Fintype, Repr

/-- The two identical springs, named by their position in the image. -/
inductive SpringLabel where
  | left
  | right
  deriving DecidableEq, Fintype, Repr

/-- The two ends of each horizontal rod. -/
inductive RodEnd where
  | left
  | right
  deriving DecidableEq, Fintype, Repr

/-- Horizontal directions used by the current arrows. -/
inductive HorizontalDirection where
  | left
  | right
  deriving DecidableEq, Repr

/-- The three operating points named in the problem statement. -/
inductive OperatingPoint where
  | lowerCurrentMeasurement
  | higherCurrentMeasurement
  | requestedOneCentimeterExtension
  deriving DecidableEq, Fintype, Repr

/-!
Literal qualitative content of image `968.png`.  It shows two horizontal
parallel rods, a spring joining their left ends and another joining their
right ends, and purple current arrows labeled `I` in opposite directions.
-/
structure ParallelRodSpringFigure where
  rodShown : RodLabel → Bool
  springShown : SpringLabel → Bool
  rodDrawnHorizontal : RodLabel → Bool
  rodsDrawnParallel : Bool
  upperRodDrawnAboveLowerRod : Bool
  springAtRodEnd : SpringLabel → RodEnd
  springJoinsUpperAndLowerRods : SpringLabel → Bool
  currentArrowShown : RodLabel → Bool
  currentLabelIShown : RodLabel → Bool
  currentArrowDirection : RodLabel → HorizontalDirection

/-!
Independent physical quantities and force observables for the apparatus.
In particular, the current at the requested extension is not defined from an
answer choice.  The force observables are constrained only by the governing
laws below.
-/
structure ParallelRodSpringSetup where
  figure : ParallelRodSpringFigure
  rodLength : LengthMagnitude
  unstretchedSpringLength : LengthMagnitude
  springStiffness : SpringStiffnessMagnitude
  vacuumPermeability : MagneticPermeabilityMagnitude
  springExtension : OperatingPoint → LengthMagnitude
  rodSeparation : OperatingPoint → LengthMagnitude
  currentMagnitude : OperatingPoint → ElectricCurrentMagnitude
  magneticRepulsiveForceOnEachRod : OperatingPoint → ForceMagnitude
  restoringForceFromEachSpring : OperatingPoint → ForceMagnitude
  totalSpringRestoringForceOnEachRod : OperatingPoint → ForceMagnitude
  rodsAreLong : Bool
  rodsAreRigid : Bool
  tableIsFrictionless : Bool
  springsAreIdentical : Bool
  springsAreVeryLightweight : Bool
  springsAreConducting : Bool
  rodsAndSpringsFormOneCircuit : Bool

/-! ## Scenario, measurements, and governing laws -/

/-- Qualitative properties stated in the written physical scenario. -/
structure MatchesWrittenParallelRodSpringScenario
    (setup : ParallelRodSpringSetup) : Prop where
  longRods : setup.rodsAreLong = true
  rigidRods : setup.rodsAreRigid = true
  frictionlessTable : setup.tableIsFrictionless = true
  identicalSprings : setup.springsAreIdentical = true
  lightweightSprings : setup.springsAreVeryLightweight = true
  conductingSprings : setup.springsAreConducting = true
  singleCircuit : setup.rodsAndSpringsFormOneCircuit = true

/-!
Primary-raster evidence only.  These fields record object placement and arrow
directions; they contain no numerical current or target-answer information.
-/
structure MatchesPrimaryParallelRodSpringFigure
    (setup : ParallelRodSpringSetup) : Prop where
  bothRodsShown : ∀ rod, setup.figure.rodShown rod = true
  bothSpringsShown : ∀ spring, setup.figure.springShown spring = true
  bothRodsHorizontal : ∀ rod, setup.figure.rodDrawnHorizontal rod = true
  rodsParallel : setup.figure.rodsDrawnParallel = true
  upperAboveLower : setup.figure.upperRodDrawnAboveLowerRod = true
  leftSpringAtLeftEnds : setup.figure.springAtRodEnd .left = .left
  rightSpringAtRightEnds : setup.figure.springAtRodEnd .right = .right
  eachSpringJoinsTheRods :
    ∀ spring, setup.figure.springJoinsUpperAndLowerRods spring = true
  bothCurrentArrowsShown :
    ∀ rod, setup.figure.currentArrowShown rod = true
  bothCurrentLabelsShown :
    ∀ rod, setup.figure.currentLabelIShown rod = true
  upperCurrentPointsRight :
    setup.figure.currentArrowDirection .upper = .right
  lowerCurrentPointsLeft :
    setup.figure.currentArrowDirection .lower = .left

/-!
Numerical problem data.  The two measured currents and extensions calibrate
the unknown spring and separation parameters.  The requested operating point
contains only its prescribed extension; its current is deliberately absent.
-/
structure MatchesParallelRodSpringMeasurements
    (setup : ParallelRodSpringSetup) : Prop where
  rodLengthMeters : lengthInMeters setup.rodLength = 1 / 2
  rodLengthCentimeters :
    lengthReadout LengthUnit.centimeters setup.rodLength = 50
  lowerMeasuredCurrentAmperes :
    currentInAmperes
      (setup.currentMagnitude .lowerCurrentMeasurement) = 805 / 100
  lowerMeasuredExtensionCentimeters :
    lengthReadout LengthUnit.centimeters
      (setup.springExtension .lowerCurrentMeasurement) = 40 / 100
  lowerMeasuredExtensionMeters :
    lengthInMeters (setup.springExtension .lowerCurrentMeasurement) = 1 / 250
  higherMeasuredCurrentAmperes :
    currentInAmperes
      (setup.currentMagnitude .higherCurrentMeasurement) = 131 / 10
  higherMeasuredExtensionCentimeters :
    lengthReadout LengthUnit.centimeters
      (setup.springExtension .higherCurrentMeasurement) = 80 / 100
  higherMeasuredExtensionMeters :
    lengthInMeters (setup.springExtension .higherCurrentMeasurement) = 1 / 125
  requestedExtensionCentimeters :
    lengthReadout LengthUnit.centimeters
      (setup.springExtension .requestedOneCentimeterExtension) = 1
  requestedExtensionMeters :
    lengthInMeters
      (setup.springExtension .requestedOneCentimeterExtension) = 1 / 100

/-- Positivity and nondegeneracy conditions for the physical apparatus. -/
structure HasPhysicalParallelRodSpringParameters
    (setup : ParallelRodSpringSetup) : Prop where
  rodLengthPositive : 0 < lengthInMeters setup.rodLength
  unstretchedSpringLengthPositive :
    0 < lengthInMeters setup.unstretchedSpringLength
  springStiffnessPositive :
    0 < springStiffnessInNewtonsPerMeter setup.springStiffness
  vacuumPermeabilityPositive :
    0 < magneticPermeabilityInNewtonsPerAmpereSquared
      setup.vacuumPermeability
  everyExtensionPositive :
    ∀ point, 0 < lengthInMeters (setup.springExtension point)
  everySeparationPositive :
    ∀ point, 0 < lengthInMeters (setup.rodSeparation point)

/-!
School-level geometry, Hooke, long-parallel-wire, and equilibrium laws.  The
magnetic law gives the magnitude on either rod when the equal currents are
oppositely directed; hence the force is repulsive as shown by the stretching
springs.  These are uniform laws over all operating points, not the solved
formula for the requested current.
-/
structure SatisfiesParallelRodSpringLaws
    (setup : ParallelRodSpringSetup) : Prop where
  separationIsUnstretchedLengthPlusExtension : ∀ point,
    lengthInMeters (setup.rodSeparation point) =
      lengthInMeters setup.unstretchedSpringLength +
        lengthInMeters (setup.springExtension point)
  hookeLawForEachSpring : ∀ point,
    forceInNewtons (setup.restoringForceFromEachSpring point) =
      springStiffnessInNewtonsPerMeter setup.springStiffness *
        lengthInMeters (setup.springExtension point)
  twoSpringForcesAddOnEachRod : ∀ point,
    forceInNewtons (setup.totalSpringRestoringForceOnEachRod point) =
      2 * forceInNewtons (setup.restoringForceFromEachSpring point)
  longParallelWireMagneticForce : ∀ point,
    forceInNewtons (setup.magneticRepulsiveForceOnEachRod point) =
      magneticPermeabilityInNewtonsPerAmpereSquared
          setup.vacuumPermeability *
        currentInAmperes (setup.currentMagnitude point) ^ 2 *
          lengthInMeters setup.rodLength /
            (2 * Real.pi * lengthInMeters (setup.rodSeparation point))
  staticEquilibriumAtEachOperatingPoint : ∀ point,
    forceInNewtons (setup.magneticRepulsiveForceOnEachRod point) =
      forceInNewtons (setup.totalSpringRestoringForceOnEachRod point)

/-! ## Answer choices and target conclusions -/

/-- Labels of the four current choices printed with the problem. -/
inductive AnswerChoice where
  | A
  | B
  | C
  | D
  deriving DecidableEq, Fintype, Repr

/-- Current in amperes printed beside each answer label. -/
def answerCurrentInAmperes : AnswerChoice → ℝ
  | .A => 12
  | .B => 16
  | .C => 131 / 10
  | .D => 182 / 10

/-- The answer label recorded in the source dataset. -/
def recordedDatasetAnswer : AnswerChoice := .B

/-- A choice is strictly nearer to the required current than every rival. -/
def IsUniqueClosestRequiredCurrentChoice
    (setup : ParallelRodSpringSetup) (choice : AnswerChoice) : Prop :=
  ∀ other, other ≠ choice →
    |currentInAmperes
        (setup.currentMagnitude .requestedOneCentimeterExtension) -
          answerCurrentInAmperes choice| <
      |currentInAmperes
          (setup.currentMagnitude .requestedOneCentimeterExtension) -
            answerCurrentInAmperes other|

/-!
Eliminating the common spring stiffness and magnetic coefficient from the two
calibration measurements gives `l₀ = 1752/210025 m`.  Applying the same laws
at `x = 1.00 cm` gives `I² = 15409/64 A²`.  Both are conclusions rather than
input data.
-/
lemma calibratedLengthAndRequiredCurrentSquared
    (setup : ParallelRodSpringSetup)
    (_data : MatchesParallelRodSpringMeasurements setup)
    (_physical : HasPhysicalParallelRodSpringParameters setup)
    (_laws : SatisfiesParallelRodSpringLaws setup) :
    lengthInMeters setup.unstretchedSpringLength = 1752 / 210025 ∧
      currentInAmperes
          (setup.currentMagnitude .requestedOneCentimeterExtension) ^ 2 =
        15409 / 64 := by
  let l₀ := lengthInMeters setup.unstretchedSpringLength
  let k := springStiffnessInNewtonsPerMeter setup.springStiffness
  let μ₀ :=
    magneticPermeabilityInNewtonsPerAmpereSquared
      setup.vacuumPermeability
  let I :=
    currentInAmperes
      (setup.currentMagnitude .requestedOneCentimeterExtension)
  have hl₀ : 0 < l₀ := by
    simpa [l₀] using _physical.unstretchedSpringLengthPositive
  have hk : 0 < k := by
    simpa [k] using _physical.springStiffnessPositive
  have hμ₀ : 0 < μ₀ := by
    simpa [μ₀] using _physical.vacuumPermeabilityPositive
  have hbalance (point : OperatingPoint) :
      magneticPermeabilityInNewtonsPerAmpereSquared
            setup.vacuumPermeability *
          currentInAmperes (setup.currentMagnitude point) ^ 2 *
            lengthInMeters setup.rodLength /
              (2 * Real.pi * lengthInMeters (setup.rodSeparation point)) =
        2 * springStiffnessInNewtonsPerMeter setup.springStiffness *
          lengthInMeters (setup.springExtension point) := by
    calc
      magneticPermeabilityInNewtonsPerAmpereSquared
              setup.vacuumPermeability *
            currentInAmperes (setup.currentMagnitude point) ^ 2 *
              lengthInMeters setup.rodLength /
                (2 * Real.pi * lengthInMeters (setup.rodSeparation point)) =
          forceInNewtons
            (setup.magneticRepulsiveForceOnEachRod point) :=
        (_laws.longParallelWireMagneticForce point).symm
      _ =
          forceInNewtons
            (setup.totalSpringRestoringForceOnEachRod point) :=
        _laws.staticEquilibriumAtEachOperatingPoint point
      _ =
          2 * forceInNewtons
            (setup.restoringForceFromEachSpring point) :=
        _laws.twoSpringForcesAddOnEachRod point
      _ =
          2 * springStiffnessInNewtonsPerMeter setup.springStiffness *
            lengthInMeters (setup.springExtension point) := by
        rw [_laws.hookeLawForEachSpring point]
        ring
  have hlower :
      μ₀ * (805 / 100 : ℝ) ^ 2 * (1 / 2) /
            (2 * Real.pi * (l₀ + 1 / 250)) =
        2 * k * (1 / 250) := by
    simpa [l₀, k, μ₀, _data.lowerMeasuredCurrentAmperes,
      _data.rodLengthMeters, _data.lowerMeasuredExtensionMeters,
      _laws.separationIsUnstretchedLengthPlusExtension
        .lowerCurrentMeasurement] using
      hbalance .lowerCurrentMeasurement
  have hhigher :
      μ₀ * (131 / 10 : ℝ) ^ 2 * (1 / 2) /
            (2 * Real.pi * (l₀ + 1 / 125)) =
        2 * k * (1 / 125) := by
    simpa [l₀, k, μ₀, _data.higherMeasuredCurrentAmperes,
      _data.rodLengthMeters, _data.higherMeasuredExtensionMeters,
      _laws.separationIsUnstretchedLengthPlusExtension
        .higherCurrentMeasurement] using
      hbalance .higherCurrentMeasurement
  have hrequested :
      μ₀ * I ^ 2 * (1 / 2) /
            (2 * Real.pi * (l₀ + 1 / 100)) =
        2 * k * (1 / 100) := by
    simpa [l₀, k, μ₀, I, _data.rodLengthMeters,
      _data.requestedExtensionMeters,
      _laws.separationIsUnstretchedLengthPlusExtension
        .requestedOneCentimeterExtension] using
      hbalance .requestedOneCentimeterExtension
  have hdenLower :
      2 * Real.pi * (l₀ + 1 / 250) ≠ 0 := by positivity
  have hdenHigher :
      2 * Real.pi * (l₀ + 1 / 125) ≠ 0 := by positivity
  have hdenRequested :
      2 * Real.pi * (l₀ + 1 / 100) ≠ 0 := by positivity
  rw [div_eq_iff hdenLower] at hlower
  rw [div_eq_iff hdenHigher] at hhigher
  rw [div_eq_iff hdenRequested] at hrequested
  norm_num at hlower hhigher hrequested
  have hl₀Value : l₀ = 1752 / 210025 := by
    nlinarith [Real.pi_pos, mul_pos hk Real.pi_pos]
  have hIValue : I ^ 2 = 15409 / 64 := by
    nlinarith [Real.pi_pos, mul_pos hk Real.pi_pos]
  exact ⟨by simpa [l₀] using hl₀Value, by simpa [I] using hIValue⟩

/-!
The nonnegative required current has square `15409/64 A²`, lies strictly
between `15 A` and `16 A`, and is closer to `16.0 A` than to any other printed
choice.  Thus the answer is B.

This declaration formalizes `thm:physics:phyx_mini_0968:target`.  Neither the
required current nor its squared value occurs in any hypothesis.
-/
theorem problem_phyx_mini_0968
    (setup : ParallelRodSpringSetup)
    (_scenario : MatchesWrittenParallelRodSpringScenario setup)
    (_figure : MatchesPrimaryParallelRodSpringFigure setup)
    (_data : MatchesParallelRodSpringMeasurements setup)
    (_physical : HasPhysicalParallelRodSpringParameters setup)
    (_laws : SatisfiesParallelRodSpringLaws setup) :
    currentInAmperes
          (setup.currentMagnitude .requestedOneCentimeterExtension) ^ 2 =
        15409 / 64 ∧
      15 < currentInAmperes
        (setup.currentMagnitude .requestedOneCentimeterExtension) ∧
      currentInAmperes
          (setup.currentMagnitude .requestedOneCentimeterExtension) < 16 ∧
      IsUniqueClosestRequiredCurrentChoice setup recordedDatasetAnswer := by
  let I :=
    currentInAmperes
      (setup.currentMagnitude .requestedOneCentimeterExtension)
  have hIsq : I ^ 2 = 15409 / 64 := by
    simpa [I] using
      (calibratedLengthAndRequiredCurrentSquared
        setup _data _physical _laws).2
  have hI_nonnegative : 0 ≤ I := by
    dsimp [I, currentInAmperes, coherentSIReadout]
    positivity
  have hI_lower : 15 < I := by
    nlinarith
  have hI_upper : I < 16 := by
    nlinarith
  refine ⟨by simpa [I] using hIsq, by simpa [I] using hI_lower,
    by simpa [I] using hI_upper, ?_⟩
  change ∀ other, other ≠ AnswerChoice.B →
    |I - 16| < |I - answerCurrentInAmperes other|
  intro other hother
  cases other with
  | A =>
      change |I - 16| < |I - 12|
      rw [abs_of_nonpos (by linarith), abs_of_nonneg (by linarith)]
      linarith
  | B =>
      exact (hother rfl).elim
  | C =>
      change |I - 16| < |I - 131 / 10|
      rw [abs_of_nonpos (by linarith), abs_of_nonneg (by linarith)]
      linarith
  | D =>
      change |I - 16| < |I - 182 / 10|
      rw [abs_of_nonpos (by linarith), abs_of_nonpos (by linarith)]
      linarith

end PhyXMiniProblems.ProblemPhyXMini0968
