import Mathlib
import Physlib.Electromagnetism.Basic
import Physlib.Units.WithDim.Basic

/- USER: The assigned Lean file did not exist when this autoformalization task began. -/

noncomputable section

namespace PhyXMiniProblems.ProblemPhyXMini0965

open Dimension

/-!
# Current in two repelling suspended parallel wires

Two long parallel wires are suspended symmetrically from a common axis by
`4.00 cm` cords.  Each wire has linear mass density `0.0125 kg/m`; the wires
carry equal current magnitudes in opposite directions and hence repel.  In
static equilibrium each cord is deflected by `6.00 degrees` from vertical.

Physical magnitudes are unit-independent Physlib `Dimensionful` quantities.
Real numbers occur only as coherent-SI readouts, dimensionless angles, and
displayed answer values.

Assumption/target split:

* governing laws: opposite parallel currents repel, the magnetic force per
  unit length is `mu_0 I_1 I_2 / (2 pi d)`, the symmetric suspension has
  separation `d = 2 ell sin(theta)`, and horizontal/vertical components of
  the combined cord support balance magnetic force and weight per unit length;
* previous-part results: none;
* figure/data readouts: two parallel wires, a common suspension axis, two cord
  stations, `4.00 cm`, two `6.00 degree` labels, and opposite arrows labelled
  `I`, together with the prose values for linear density and standard gravity;
* current target conclusions: the exact positive square-root current for each
  wire and its rounding to `23.2 A`, uniquely selecting answer B.

Neither the square-root expression nor `23.2 A` occurs in a setup field or in
any scenario, figure, geometry, calibration, magnetic-law, or equilibrium
premise.
-/

/-! ## Dimensionful physical quantities and coherent-SI readouts -/

/-- Electric current has dimension charge per time. -/
def electricCurrentDimension : Dimension :=
  C𝓭 * T𝓭⁻¹

/-- Linear mass density has dimension mass per length. -/
def linearMassDensityDimension : Dimension :=
  M𝓭 * L𝓭⁻¹

/-- Acceleration has dimension length per time squared. -/
def accelerationDimension : Dimension :=
  L𝓭 * T𝓭⁻¹ * T𝓭⁻¹

/-- Magnetic permeability has dimension `M L C⁻²`. -/
def magneticPermeabilityDimension : Dimension :=
  M𝓭 * L𝓭 * C𝓭⁻¹ * C𝓭⁻¹

/-- Force per unit wire length has dimension `M T⁻²`. -/
def forcePerLengthDimension : Dimension :=
  M𝓭 * T𝓭⁻¹ * T𝓭⁻¹

/-- A nonnegative, unit-independent physical length. -/
abbrev LengthMagnitude : Type :=
  Dimensionful (WithDim L𝓭 NNReal)

/-- A nonnegative, unit-independent mass per unit wire length. -/
abbrev LinearMassDensityMagnitude : Type :=
  Dimensionful (WithDim linearMassDensityDimension NNReal)

/-- A nonnegative, unit-independent electric-current magnitude. -/
abbrev ElectricCurrentMagnitude : Type :=
  Dimensionful (WithDim electricCurrentDimension NNReal)

/-- A nonnegative, unit-independent acceleration magnitude. -/
abbrev AccelerationMagnitude : Type :=
  Dimensionful (WithDim accelerationDimension NNReal)

/-- A nonnegative, unit-independent magnetic permeability. -/
abbrev MagneticPermeabilityMagnitude : Type :=
  Dimensionful (WithDim magneticPermeabilityDimension NNReal)

/-- A nonnegative force magnitude per unit length of wire. -/
abbrev ForcePerLengthMagnitude : Type :=
  Dimensionful (WithDim forcePerLengthDimension NNReal)

/-- Read a nonnegative dimensionful quantity in coherent SI units. -/
def nonnegativeSIReadout {dimension : Dimension}
    (quantity : Dimensionful (WithDim dimension NNReal)) : ℝ :=
  ((quantity UnitChoices.SI).val : ℝ)

/-- Read a physical length in metres. -/
def lengthInMeters (length : LengthMagnitude) : ℝ :=
  nonnegativeSIReadout length

/-- Read a physical length in centimetres. -/
def lengthInCentimeters (length : LengthMagnitude) : ℝ :=
  100 * lengthInMeters length

/-- Read linear mass density in kilograms per metre. -/
def linearMassDensityInKilogramsPerMeter
    (density : LinearMassDensityMagnitude) : ℝ :=
  nonnegativeSIReadout density

/-- Read an electric-current magnitude in amperes. -/
def currentInAmperes (current : ElectricCurrentMagnitude) : ℝ :=
  nonnegativeSIReadout current

/-- Read acceleration in metres per second squared. -/
def accelerationInMetersPerSecondSquared
    (acceleration : AccelerationMagnitude) : ℝ :=
  nonnegativeSIReadout acceleration

/-- Read permeability in newtons per ampere squared. -/
def permeabilityInNewtonsPerAmpereSquared
    (permeability : MagneticPermeabilityMagnitude) : ℝ :=
  nonnegativeSIReadout permeability

/-- Read force per unit length in newtons per metre. -/
def forcePerLengthInNewtonsPerMeter
    (forcePerLength : ForcePerLengthMagnitude) : ℝ :=
  nonnegativeSIReadout forcePerLength

/-! ## Apparatus roles and primary-raster labels -/

/-- The two conductors as they appear above and below one another in the raster. -/
inductive WireLabel where
  | upperInFigure
  | lowerInFigure
  deriving DecidableEq, Fintype, Repr

/-- The two suspension stations visible along the long wires. -/
inductive SupportStation where
  | left
  | right
  deriving DecidableEq, Fintype, Repr

/-- Direction of conventional current along a wire in the supplied view. -/
inductive AlongWireDirection where
  | leftward
  | rightward
  deriving DecidableEq, Repr

/-- Side of the common vertical plane to which a wire is deflected. -/
inductive DeflectionSide where
  | leftOfVertical
  | rightOfVertical
  deriving DecidableEq, Repr

/-- Long-wire idealization used by the parallel-wire force law. -/
inductive WireModel where
  | longStraightParallel
  | other
  deriving DecidableEq, Repr

/-- Medium approximation used for the magnetic interaction. -/
inductive MagneticMediumModel where
  | vacuumOrAir
  | other
  deriving DecidableEq, Repr

/-- Qualitative character of the force between the two wires. -/
inductive WireInteraction where
  | attractive
  | repulsive
  deriving DecidableEq, Repr

/-!
Literal objects, arrows, and scalar labels visible in image `965.png`.
The label values are presentation data and remain separate from the physical
quantities that they calibrate.
-/
structure SuspendedWiresFigure where
  wireShown : WireLabel → Bool
  commonSuspensionAxisShown : Bool
  supportStationShown : SupportStation → Bool
  cordShown : SupportStation → WireLabel → Bool
  currentArrowShown : WireLabel → Bool
  displayedCurrentDirection : WireLabel → AlongWireDirection
  currentSymbolShown : WireLabel → Bool
  angleMarkerShown : WireLabel → Bool
  displayedAngleInDegrees : WireLabel → ℝ
  cordLengthMarkerShown : Bool
  displayedCordLengthInCentimeters : ℝ
  displayedDeflectionSide : WireLabel → DeflectionSide

/-!
Independent physical observables for the suspended-wire state.  The support
tension is the combined cord-support resultant per unit wire length, so its
components can be compared directly with weight and magnetic force per unit
wire length.  The unknown currents are not defined from an answer choice.
-/
structure SuspendedParallelWiresSetup where
  wireModel : WireModel
  mediumModel : MagneticMediumModel
  cordLength : LengthMagnitude
  commonDeflectionAngleRadians : ℝ
  linearMassDensity : WireLabel → LinearMassDensityMagnitude
  gravitationalAcceleration : AccelerationMagnitude
  currentMagnitude : WireLabel → ElectricCurrentMagnitude
  currentDirection : WireLabel → AlongWireDirection
  deflectionSide : WireLabel → DeflectionSide
  wireSeparation : LengthMagnitude
  combinedSupportTensionPerLength : WireLabel → ForcePerLengthMagnitude
  magneticForcePerLength : WireLabel → ForcePerLengthMagnitude
  interaction : WireInteraction
  electromagneticSystem : Electromagnetism.EMSystem
  vacuumPermeability : MagneticPermeabilityMagnitude
  figure : SuspendedWiresFigure

/-! ## Stated data, figure evidence, and physical parameter conditions -/

/-- Numerical and qualitative data stated in the problem prose. -/
structure MatchesSuspendedParallelWiresProblem
    (setup : SuspendedParallelWiresSetup) : Prop where
  longParallelWireModel : setup.wireModel = .longStraightParallel
  vacuumOrAirApproximation : setup.mediumModel = .vacuumOrAir
  cordLengthIsFourCentimeters :
    lengthInCentimeters setup.cordLength = 4
  bothLinearMassDensitiesArePointZeroOneTwoFive : ∀ wire,
    linearMassDensityInKilogramsPerMeter
        (setup.linearMassDensity wire) = 1 / 80
  commonAngleIsSixDegrees :
    setup.commonDeflectionAngleRadians = Real.pi / 30
  equalCurrentMagnitudes :
    setup.currentMagnitude .upperInFigure =
      setup.currentMagnitude .lowerInFigure
  currentsHaveOppositeDirections :
    setup.currentDirection .upperInFigure ≠
      setup.currentDirection .lowerInFigure

/-!
Primary-raster evidence: the two wires, both pairs of cords, the common axis,
the two `6.00 degree` markers, the `4.00 cm` marker, and the opposed arrows
labelled `I`.  No current magnitude is printed in the figure.
-/
structure MatchesPrimarySuspendedWiresFigure
    (setup : SuspendedParallelWiresSetup) : Prop where
  bothWiresShown : ∀ wire, setup.figure.wireShown wire = true
  commonAxisShown : setup.figure.commonSuspensionAxisShown = true
  bothSupportStationsShown : ∀ station,
    setup.figure.supportStationShown station = true
  everyCordShown : ∀ station wire,
    setup.figure.cordShown station wire = true
  bothCurrentArrowsShown : ∀ wire,
    setup.figure.currentArrowShown wire = true
  bothCurrentSymbolsShown : ∀ wire,
    setup.figure.currentSymbolShown wire = true
  displayedUpperCurrentPointsRight :
    setup.figure.displayedCurrentDirection .upperInFigure = .rightward
  displayedLowerCurrentPointsLeft :
    setup.figure.displayedCurrentDirection .lowerInFigure = .leftward
  displayedDirectionsCalibrateCurrents : ∀ wire,
    setup.figure.displayedCurrentDirection wire = setup.currentDirection wire
  bothAngleMarkersShown : ∀ wire,
    setup.figure.angleMarkerShown wire = true
  bothAngleLabelsReadSixDegrees : ∀ wire,
    setup.figure.displayedAngleInDegrees wire = 6
  angleLabelsCalibrateCommonAngle : ∀ wire,
    setup.commonDeflectionAngleRadians =
      setup.figure.displayedAngleInDegrees wire * Real.pi / 180
  cordLengthMarkerShown : setup.figure.cordLengthMarkerShown = true
  cordLengthLabelReadsFourCentimeters :
    setup.figure.displayedCordLengthInCentimeters = 4
  cordLengthLabelCalibratesPhysicalLength :
    setup.figure.displayedCordLengthInCentimeters =
      lengthInCentimeters setup.cordLength
  upperWireDeflectsRight :
    setup.figure.displayedDeflectionSide .upperInFigure = .rightOfVertical
  lowerWireDeflectsLeft :
    setup.figure.displayedDeflectionSide .lowerInFigure = .leftOfVertical
  displayedSidesCalibrateDeflections : ∀ wire,
    setup.figure.displayedDeflectionSide wire = setup.deflectionSide wire

/-- Positivity and nondegeneracy conditions selecting the physical branch. -/
structure HasPhysicalSuspendedWireParameters
    (setup : SuspendedParallelWiresSetup) : Prop where
  cordLengthPositive : 0 < lengthInMeters setup.cordLength
  linearMassDensityPositive : ∀ wire,
    0 < linearMassDensityInKilogramsPerMeter
      (setup.linearMassDensity wire)
  gravitationalAccelerationPositive :
    0 < accelerationInMetersPerSecondSquared
      setup.gravitationalAcceleration
  currentMagnitudePositive : ∀ wire,
    0 < currentInAmperes (setup.currentMagnitude wire)
  separationPositive : 0 < lengthInMeters setup.wireSeparation
  permeabilityPositive :
    0 < permeabilityInNewtonsPerAmpereSquared setup.vacuumPermeability
  angleIsAcute :
    0 < setup.commonDeflectionAngleRadians ∧
      setup.commonDeflectionAngleRadians < Real.pi / 2

/-!
The two equal cords leave the common axis on opposite sides, so the transverse
wire separation is twice the horizontal projection of one cord.
-/
structure SatisfiesSymmetricSuspensionGeometry
    (setup : SuspendedParallelWiresSetup) : Prop where
  wiresDeflectToOppositeSides :
    setup.deflectionSide .upperInFigure ≠
      setup.deflectionSide .lowerInFigure
  separationLaw :
    lengthInMeters setup.wireSeparation =
      2 * lengthInMeters setup.cordLength *
        Real.sin setup.commonDeflectionAngleRadians

/-! Standard terrestrial gravity used for the numerical answer. -/
structure UsesStandardGravitationalAcceleration
    (setup : SuspendedParallelWiresSetup) : Prop where
  standardGravityReadout :
    accelerationInMetersPerSecondSquared
      setup.gravitationalAcceleration = 49 / 5

/-!
The dimensionful permeability agrees with Physlib's electromagnetic-system
parameter and has the standard coherent-SI vacuum value `4 pi * 10⁻⁷`.
-/
structure UsesStandardVacuumPermeability
    (setup : SuspendedParallelWiresSetup) : Prop where
  agreesWithElectromagneticSystem :
    permeabilityInNewtonsPerAmpereSquared setup.vacuumPermeability =
      setup.electromagneticSystem.μ₀
  standardSIReadout :
    permeabilityInNewtonsPerAmpereSquared setup.vacuumPermeability =
      4 * Real.pi / 10 ^ 7

/-! ## Governing magnetic and static-equilibrium laws -/

/-!
For two long parallel wires separated by `d`, the repulsive magnetic-force
magnitude per unit length is `mu_0 I_1 I_2 / (2 pi d)`.  The direction clause
records the right-hand-rule consequence of opposite conventional currents.
-/
structure SatisfiesParallelWireMagneticForceLaw
    (setup : SuspendedParallelWiresSetup) : Prop where
  oppositeCurrentsRepel :
    setup.currentDirection .upperInFigure ≠
        setup.currentDirection .lowerInFigure →
      setup.interaction = .repulsive
  forceMagnitudeLaw : ∀ wire,
    forcePerLengthInNewtonsPerMeter
        (setup.magneticForcePerLength wire) =
      permeabilityInNewtonsPerAmpereSquared setup.vacuumPermeability *
          currentInAmperes (setup.currentMagnitude .upperInFigure) *
          currentInAmperes (setup.currentMagnitude .lowerInFigure) /
        (2 * Real.pi * lengthInMeters setup.wireSeparation)

/-!
Static equilibrium for each wire.  The vertical component of the combined
cord support balances weight per unit wire length, and its horizontal
component balances the repulsive magnetic force per unit length.  Retaining
both component equations avoids assuming the derived tangent relation.
-/
structure SatisfiesStaticCordEquilibrium
    (setup : SuspendedParallelWiresSetup) : Prop where
  verticalForceBalance : ∀ wire,
    forcePerLengthInNewtonsPerMeter
          (setup.combinedSupportTensionPerLength wire) *
        Real.cos setup.commonDeflectionAngleRadians =
      linearMassDensityInKilogramsPerMeter
          (setup.linearMassDensity wire) *
        accelerationInMetersPerSecondSquared
          setup.gravitationalAcceleration
  horizontalForceBalance : ∀ wire,
    forcePerLengthInNewtonsPerMeter
          (setup.combinedSupportTensionPerLength wire) *
        Real.sin setup.commonDeflectionAngleRadians =
      forcePerLengthInNewtonsPerMeter
        (setup.magneticForcePerLength wire)

/-! ## Derived current and displayed-answer target -/

/-!
Eliminating support tension and wire separation gives the squared current for
each wire.  After substituting `ell = 0.04 m`, `lambda = 0.0125 kg/m`,
`g = 9.8 m/s²`, `theta = pi/30`, and `mu_0 = 4 pi * 10⁻⁷`, the radicand
is `49000 sin(pi/30) tan(pi/30)`.
-/
lemma currentInAmperes_sq
    (setup : SuspendedParallelWiresSetup)
    (hProblem : MatchesSuspendedParallelWiresProblem setup)
    (hPhysical : HasPhysicalSuspendedWireParameters setup)
    (hGeometry : SatisfiesSymmetricSuspensionGeometry setup)
    (hGravity : UsesStandardGravitationalAcceleration setup)
    (hVacuum : UsesStandardVacuumPermeability setup)
    (hMagnetic : SatisfiesParallelWireMagneticForceLaw setup)
    (hEquilibrium : SatisfiesStaticCordEquilibrium setup) :
    ∀ wire,
      currentInAmperes (setup.currentMagnitude wire) ^ 2 =
        49000 * Real.sin (Real.pi / 30) *
          Real.tan (Real.pi / 30) := by
  intro wire
  have hLength : lengthInMeters setup.cordLength = 1 / 25 := by
    have h := hProblem.cordLengthIsFourCentimeters
    unfold lengthInCentimeters at h
    linarith
  have hDensity :
      linearMassDensityInKilogramsPerMeter
          (setup.linearMassDensity wire) = 1 / 80 :=
    hProblem.bothLinearMassDensitiesArePointZeroOneTwoFive wire
  have hAngle :
      setup.commonDeflectionAngleRadians = Real.pi / 30 :=
    hProblem.commonAngleIsSixDegrees
  have hAcceleration :
      accelerationInMetersPerSecondSquared
          setup.gravitationalAcceleration = 49 / 5 :=
    hGravity.standardGravityReadout
  have hPermeability :
      permeabilityInNewtonsPerAmpereSquared setup.vacuumPermeability =
        4 * Real.pi / 10 ^ 7 :=
    hVacuum.standardSIReadout
  have hEqualReadouts :
      currentInAmperes (setup.currentMagnitude .upperInFigure) =
        currentInAmperes (setup.currentMagnitude .lowerInFigure) :=
    congrArg currentInAmperes hProblem.equalCurrentMagnitudes
  have hWireReadout :
      currentInAmperes (setup.currentMagnitude wire) =
        currentInAmperes (setup.currentMagnitude .upperInFigure) := by
    cases wire with
    | upperInFigure => rfl
    | lowerInFigure => exact hEqualReadouts.symm
  have hSeparation :
      lengthInMeters setup.wireSeparation =
        2 * (1 / 25) * Real.sin (Real.pi / 30) := by
    rw [hGeometry.separationLaw, hLength, hAngle]
  have hAnglePos : 0 < Real.pi / 30 := by
    rw [← hAngle]
    exact hPhysical.angleIsAcute.1
  have hAngleLtHalf : Real.pi / 30 < Real.pi / 2 := by
    rw [← hAngle]
    exact hPhysical.angleIsAcute.2
  have hSinPos : 0 < Real.sin (Real.pi / 30) :=
    Real.sin_pos_of_pos_of_lt_pi hAnglePos
      (lt_trans hAngleLtHalf (half_lt_self Real.pi_pos))
  have hCosPos : 0 < Real.cos (Real.pi / 30) :=
    Real.cos_pos_of_mem_Ioo ⟨by linarith [Real.pi_pos], hAngleLtHalf⟩
  have hVertical := hEquilibrium.verticalForceBalance wire
  have hHorizontal := hEquilibrium.horizontalForceBalance wire
  have hForce := hMagnetic.forceMagnitudeLaw wire
  rw [hAngle, hDensity, hAcceleration] at hVertical
  rw [hAngle] at hHorizontal
  rw [hPermeability, hSeparation, ← hEqualReadouts] at hForce
  field_simp [Real.pi_ne_zero, ne_of_gt hSinPos] at hForce
  rw [Real.tan_eq_sin_div_cos]
  field_simp [ne_of_gt hCosPos]
  rw [hWireReadout]
  linear_combination
    (-Real.cos (Real.pi / 30) / 100) * hForce -
      400000 * Real.sin (Real.pi / 30) *
        Real.cos (Real.pi / 30) * hHorizontal +
      400000 * Real.sin (Real.pi / 30) ^ 2 * hVertical

/-- Labels of the four current-valued answer choices. -/
inductive AnswerChoice where
  | A
  | B
  | C
  | D
  deriving DecidableEq, Fintype, Repr

/-- Current in amperes printed beside each displayed answer label. -/
def AnswerChoice.displayedCurrentInAmperes : AnswerChoice → ℝ
  | .A => 58 / 5
  | .B => 116 / 5
  | .C => 209 / 25
  | .D => 232 / 5

/-- Dataset-recorded answer label. -/
def recordedDatasetAnswer : AnswerChoice := .B

/-- The actual current rounds to a displayed value at `0.1 A` precision. -/
def RoundsToNearestTenthAmpere (actual displayed : ℝ) : Prop :=
  |actual - displayed| < 1 / 20

/-- A displayed choice is strictly closer than every distinct alternative. -/
def IsUniqueClosestDisplayedAnswer
    (actual : ℝ) (choice : AnswerChoice) : Prop :=
  ∀ otherChoice, otherChoice ≠ choice →
    |actual - choice.displayedCurrentInAmperes| <
      |actual - otherChoice.displayedCurrentInAmperes|

/-!
Blueprint declaration `thm:physics:phyx_mini_0965:target`.

Each wire carries the positive current

`sqrt (49000 sin(pi/30) tan(pi/30)) A`,

which is approximately `23.202 A`.  It therefore rounds to the displayed
`23.2 A` value and uniquely selects answer B.
-/
theorem problem_phyx_mini_0965
    (setup : SuspendedParallelWiresSetup)
    (_figure : MatchesPrimarySuspendedWiresFigure setup)
    (hProblem : MatchesSuspendedParallelWiresProblem setup)
    (hPhysical : HasPhysicalSuspendedWireParameters setup)
    (hGeometry : SatisfiesSymmetricSuspensionGeometry setup)
    (hGravity : UsesStandardGravitationalAcceleration setup)
    (hVacuum : UsesStandardVacuumPermeability setup)
    (hMagnetic : SatisfiesParallelWireMagneticForceLaw setup)
    (hEquilibrium : SatisfiesStaticCordEquilibrium setup) :
    (∀ wire,
      currentInAmperes (setup.currentMagnitude wire) =
        Real.sqrt
          (49000 * Real.sin (Real.pi / 30) *
            Real.tan (Real.pi / 30))) ∧
    (∀ wire,
      RoundsToNearestTenthAmpere
        (currentInAmperes (setup.currentMagnitude wire))
        AnswerChoice.B.displayedCurrentInAmperes) ∧
    (∀ wire,
      IsUniqueClosestDisplayedAnswer
        (currentInAmperes (setup.currentMagnitude wire)) .B) := by
  have hSquared := currentInAmperes_sq setup hProblem hPhysical hGeometry
    hGravity hVacuum hMagnetic hEquilibrium
  have hExact : ∀ wire,
      currentInAmperes (setup.currentMagnitude wire) =
        Real.sqrt
          (49000 * Real.sin (Real.pi / 30) *
            Real.tan (Real.pi / 30)) := by
    intro wire
    rw [← hSquared wire, Real.sqrt_sq_eq_abs,
      abs_of_pos (hPhysical.currentMagnitudePositive wire)]
  let angle : ℝ := Real.pi / 30
  let sine : ℝ := Real.sin angle
  let cosine : ℝ := Real.cos angle
  have hAnglePos : 0 < angle := by
    dsimp [angle]
    positivity
  have hAngleLower : (1047 / 10000 : ℝ) < angle := by
    dsimp [angle]
    nlinarith only [Real.pi_gt_d4]
  have hAngleUpper : angle < (1309 / 12500 : ℝ) := by
    dsimp [angle]
    nlinarith only [Real.pi_lt_d4]
  have hAngleAbs : |angle| ≤ 1 := by
    rw [abs_of_pos hAnglePos]
    linarith only [hAngleUpper]
  have hAngleSqLower :
      (1047 / 10000 : ℝ) ^ 2 < angle ^ 2 := by
    exact pow_lt_pow_left₀ hAngleLower (by norm_num) (by norm_num)
  have hAngleSqUpper :
      angle ^ 2 < (1309 / 12500 : ℝ) ^ 2 := by
    exact pow_lt_pow_left₀ hAngleUpper hAnglePos.le (by norm_num)
  have hAngleCubeUpper :
      angle ^ 3 < (1309 / 12500 : ℝ) ^ 3 := by
    exact pow_lt_pow_left₀ hAngleUpper hAnglePos.le (by norm_num)
  have hAngleFourthUpper :
      angle ^ 4 < (1309 / 12500 : ℝ) ^ 4 := by
    exact pow_lt_pow_left₀ hAngleUpper hAnglePos.le (by norm_num)
  have hSineError := Real.sin_bound hAngleAbs
  rw [abs_of_pos hAnglePos] at hSineError
  have hSineLowerCore :
      angle - angle ^ 3 / 6 - angle ^ 4 * (5 / 96) ≤ sine := by
    dsimp [sine]
    have hErrorLower := neg_le_of_abs_le hSineError
    linarith only [hErrorLower]
  have hSineLower : (209 / 2000 : ℝ) < sine := by
    nlinarith only [hSineLowerCore, hAngleCubeUpper,
      hAngleFourthUpper, hAngleLower]
  have hSineUpper : sine < (1309 / 12500 : ℝ) := by
    exact (Real.sin_lt hAnglePos).trans hAngleUpper
  have hCosineError := Real.cos_bound hAngleAbs
  rw [abs_of_pos hAnglePos] at hCosineError
  have hCosineLowerCore : 1 - angle ^ 2 / 2 ≤ cosine := by
    simpa [cosine] using
      (Real.one_sub_sq_div_two_le_cos (x := angle))
  have hCosineLower : (1243 / 1250 : ℝ) < cosine := by
    nlinarith only [hCosineLowerCore, hAngleSqUpper]
  have hCosineUpperCore :
      cosine ≤ 1 - angle ^ 2 / 2 + angle ^ 4 * (5 / 96) := by
    dsimp [cosine]
    have hErrorUpper := le_of_abs_le hCosineError
    linarith only [hErrorUpper]
  have hCosineUpper : cosine < (4973 / 5000 : ℝ) := by
    nlinarith only [hCosineUpperCore, hAngleSqLower,
      hAngleFourthUpper]
  have hSineSqLower :
      (209 / 2000 : ℝ) ^ 2 < sine ^ 2 := by
    have hProduct :
        0 < (sine - 209 / 2000) * (sine + 209 / 2000) :=
      mul_pos (sub_pos.mpr hSineLower)
        (by nlinarith only [hSineLower])
    nlinarith only [hProduct]
  have hSineSqUpper :
      sine ^ 2 < (1309 / 12500 : ℝ) ^ 2 := by
    have hProduct :
        0 < (1309 / 12500 - sine) * (1309 / 12500 + sine) :=
      mul_pos (sub_pos.mpr hSineUpper)
        (by nlinarith only [hSineLower])
    nlinarith only [hProduct]
  have hCosinePos : 0 < cosine := by
    linarith only [hCosineLower]
  have hRadicandAsQuotient :
      49000 * Real.sin (Real.pi / 30) *
          Real.tan (Real.pi / 30) =
        49000 * sine ^ 2 / cosine := by
    dsimp [sine, cosine, angle]
    rw [Real.tan_eq_sin_div_cos]
    ring
  have hRadicandLower :
      (463 / 20 : ℝ) ^ 2 <
        49000 * Real.sin (Real.pi / 30) *
          Real.tan (Real.pi / 30) := by
    rw [hRadicandAsQuotient, lt_div_iff₀ hCosinePos]
    nlinarith only [hSineSqLower, hCosineUpper]
  have hRadicandUpper :
      49000 * Real.sin (Real.pi / 30) *
          Real.tan (Real.pi / 30) <
        (93 / 4 : ℝ) ^ 2 := by
    rw [hRadicandAsQuotient, div_lt_iff₀ hCosinePos]
    nlinarith only [hSineSqUpper, hCosineLower]
  have hCurrentBounds : ∀ wire,
      (463 / 20 : ℝ) <
          currentInAmperes (setup.currentMagnitude wire) ∧
        currentInAmperes (setup.currentMagnitude wire) <
          (93 / 4 : ℝ) := by
    intro wire
    have hCurrentPos := hPhysical.currentMagnitudePositive wire
    constructor
    · apply (sq_lt_sq₀ (by norm_num) hCurrentPos.le).mp
      calc
        (463 / 20 : ℝ) ^ 2 <
            49000 * Real.sin (Real.pi / 30) *
              Real.tan (Real.pi / 30) := hRadicandLower
        _ = currentInAmperes (setup.currentMagnitude wire) ^ 2 :=
          (hSquared wire).symm
    · apply (sq_lt_sq₀ hCurrentPos.le (by norm_num)).mp
      calc
        currentInAmperes (setup.currentMagnitude wire) ^ 2 =
            49000 * Real.sin (Real.pi / 30) *
              Real.tan (Real.pi / 30) := hSquared wire
        _ < (93 / 4 : ℝ) ^ 2 := hRadicandUpper
  refine ⟨hExact, ?_, ?_⟩
  · intro wire
    unfold RoundsToNearestTenthAmpere
    rcases hCurrentBounds wire with ⟨hCurrentLower, hCurrentUpper⟩
    change
      |currentInAmperes (setup.currentMagnitude wire) - 116 / 5| <
        1 / 20
    rw [abs_lt]
    constructor <;> linarith only [hCurrentLower, hCurrentUpper]
  · intro wire
    unfold IsUniqueClosestDisplayedAnswer
    intro otherChoice hOther
    rcases hCurrentBounds wire with ⟨hCurrentLower, hCurrentUpper⟩
    have hNear :
        |currentInAmperes (setup.currentMagnitude wire) - 116 / 5| <
          1 / 20 := by
      rw [abs_lt]
      constructor <;> linarith only [hCurrentLower, hCurrentUpper]
    cases otherChoice with
    | A =>
        change
          |currentInAmperes (setup.currentMagnitude wire) - 116 / 5| <
            |currentInAmperes (setup.currentMagnitude wire) - 58 / 5|
        calc
          _ < 1 / 20 := hNear
          _ < _ := by
            rw [abs_of_pos (by linarith only [hCurrentLower])]
            linarith only [hCurrentLower]
    | B => exact (hOther rfl).elim
    | C =>
        change
          |currentInAmperes (setup.currentMagnitude wire) - 116 / 5| <
            |currentInAmperes (setup.currentMagnitude wire) - 209 / 25|
        calc
          _ < 1 / 20 := hNear
          _ < _ := by
            rw [abs_of_pos (by linarith only [hCurrentLower])]
            linarith only [hCurrentLower]
    | D =>
        change
          |currentInAmperes (setup.currentMagnitude wire) - 116 / 5| <
            |currentInAmperes (setup.currentMagnitude wire) - 232 / 5|
        calc
          _ < 1 / 20 := hNear
          _ < _ := by
            rw [abs_of_neg (by linarith only [hCurrentUpper])]
            linarith only [hCurrentUpper]

end PhyXMiniProblems.ProblemPhyXMini0965
