import Mathlib
import Physlib.Units.WithDim.Basic

/- USER: The assigned Lean file did not exist when this autoformalization task began. -/

noncomputable section

namespace PhyXMiniProblems.ProblemPhyXMini0909

open Dimension

/-!
# Deflection of an electron beam between parallel electrodes

An electron enters the uniform electric field between two parallel plates with
horizontal speed `3.3 × 10^7 m/s`.  The field is directed downward and has
magnitude `5.0 × 10^4 N/C`; the field region has horizontal length `2.0 cm`.
Because the electron has negative charge, its electric force and acceleration
are upward, producing the curved trajectory and exit velocity `v₁` drawn in
the supplied image.

Mass, charge, length, time, planar velocity, acceleration, force, and electric
field are represented by unit-independent Physlib quantities.  Real numbers
occur only as coherent-SI component readouts, figure labels, dimensionless
angle readouts, and displayed answer values.

Assumption/target split:

* governing laws: the electric-force law `F = qE`, Newton's law `F = ma`,
  constant-acceleration velocity update, and horizontal transit relation;
* previous-part results: none;
* figure/data readouts: an electron, parallel charged plates, `v₀` horizontal
  and rightward, `v₁` upward/rightward, a downward field, an upward-curving
  path, `L = 2.0 cm`, `|E| = 5.0 × 10^4 N/C`, and the standard electron mass
  and signed charge;
* current target conclusions: the geometric deflection angle obeys the
  derived arctangent formula and displayed choice C (`9.1°`) is uniquely
  closest to it.

No field of the setup and no premise states the arctangent formula, a numerical
deflection angle, or the selected answer choice.
-/

/-! ## Dimensionful physical quantities and coherent-SI readouts -/

/-- The physical dimension `L T⁻¹` of velocity. -/
def velocityDimension : Dimension := L𝓭 * T𝓭⁻¹

/-- The physical dimension `L T⁻²` of acceleration. -/
def accelerationDimension : Dimension := L𝓭 * T𝓭⁻¹ * T𝓭⁻¹

/-- The physical dimension `M L T⁻²` of force. -/
def forceDimension : Dimension := M𝓭 * L𝓭 * T𝓭⁻¹ * T𝓭⁻¹

/-- The physical dimension `M L T⁻² C⁻¹` of electric field. -/
def electricFieldDimension : Dimension :=
  M𝓭 * L𝓭 * T𝓭⁻¹ * T𝓭⁻¹ * C𝓭⁻¹

/-- A positive, unit-independent physical mass. -/
abbrev MassQuantity : Type :=
  Dimensionful (WithDim M𝓭 NNReal)

/-- A signed, unit-independent electric charge. -/
abbrev SignedChargeQuantity : Type :=
  Dimensionful (WithDim C𝓭 ℝ)

/-- A nonnegative, unit-independent physical length. -/
abbrev LengthQuantity : Type :=
  Dimensionful (WithDim L𝓭 NNReal)

/-- A nonnegative, unit-independent elapsed time. -/
abbrev TimeQuantity : Type :=
  Dimensionful (WithDim T𝓭 NNReal)

/-- A unit-independent velocity vector in the plane of the figure. -/
abbrev PlanarVelocityQuantity : Type :=
  Dimensionful
    (WithDim velocityDimension (EuclideanSpace ℝ (Fin 2)))

/-- A unit-independent acceleration vector in the plane of the figure. -/
abbrev PlanarAccelerationQuantity : Type :=
  Dimensionful
    (WithDim accelerationDimension (EuclideanSpace ℝ (Fin 2)))

/-- A unit-independent force vector in the plane of the figure. -/
abbrev PlanarForceQuantity : Type :=
  Dimensionful
    (WithDim forceDimension (EuclideanSpace ℝ (Fin 2)))

/-- A unit-independent electric-field vector in the plane of the figure. -/
abbrev PlanarElectricFieldQuantity : Type :=
  Dimensionful
    (WithDim electricFieldDimension (EuclideanSpace ℝ (Fin 2)))

/-- Coordinate `0`, horizontal and positive toward the right in the figure. -/
def xAxis : Fin 2 := 0

/-- Coordinate `1`, vertical and positive upward in the figure. -/
def yAxis : Fin 2 := 1

/-- Read a mass in coherent-SI kilograms. -/
def massInKilograms (mass : MassQuantity) : ℝ :=
  ((mass UnitChoices.SI).val : ℝ)

/-- Read a signed charge in coherent-SI coulombs. -/
def chargeInCoulombs (charge : SignedChargeQuantity) : ℝ :=
  (charge UnitChoices.SI).val

/-- Read a length in coherent-SI metres. -/
def lengthInMeters (length : LengthQuantity) : ℝ :=
  ((length UnitChoices.SI).val : ℝ)

/-- Read a length in centimetres, as used by the plate-length label. -/
def lengthInCentimeters (length : LengthQuantity) : ℝ :=
  100 * lengthInMeters length

/-- Read an elapsed time in coherent-SI seconds. -/
def timeInSeconds (time : TimeQuantity) : ℝ :=
  ((time UnitChoices.SI).val : ℝ)

/-- Read a velocity vector in coherent-SI metres per second. -/
def velocityVectorInMetersPerSecond
    (velocity : PlanarVelocityQuantity) : EuclideanSpace ℝ (Fin 2) :=
  (velocity UnitChoices.SI).val

/-- Read an acceleration vector in coherent-SI metres per second squared. -/
def accelerationVectorInMetersPerSecondSquared
    (acceleration : PlanarAccelerationQuantity) :
    EuclideanSpace ℝ (Fin 2) :=
  (acceleration UnitChoices.SI).val

/-- Read a force vector in coherent-SI newtons. -/
def forceVectorInNewtons
    (force : PlanarForceQuantity) : EuclideanSpace ℝ (Fin 2) :=
  (force UnitChoices.SI).val

/-- Read an electric-field vector in coherent-SI newtons per coulomb. -/
def electricFieldVectorInNewtonsPerCoulomb
    (field : PlanarElectricFieldQuantity) : EuclideanSpace ℝ (Fin 2) :=
  (field UnitChoices.SI).val

/-! ## Named scenario and primary-image vocabulary -/

/-- The charged particle species named in the prose. -/
inductive ParticleSpecies where
  | electron
  deriving DecidableEq, Repr

/-- The two parallel deflection plates shown in the image. -/
inductive DeflectionPlate where
  | upper
  | lower
  deriving DecidableEq, Fintype, Repr

/-- Charge signs visibly printed on the two electrodes. -/
inductive PlateChargeSign where
  | positive
  | negative
  deriving DecidableEq, Repr

/-- Entry and exit states carrying the velocity labels `v₀` and `v₁`. -/
inductive BeamState where
  | entry
  | exit
  deriving DecidableEq, Fintype, Repr

/-- Qualitative arrow directions appearing in the primary image. -/
inductive ArrowDirection where
  | rightward
  | downward
  | upwardRightward
  deriving DecidableEq, Repr

/-- Objects whose presence is semantically relevant in image `909.png`. -/
inductive FigureObject where
  | electronBeam
  | upperPlate
  | lowerPlate
  | downwardElectricFieldArrows
  | curvedUpwardTrajectory
  | entryVelocityArrow
  | exitVelocityArrow
  | deflectionAngleArc
  deriving DecidableEq, Fintype, Repr

/-- Literal labels printed in image `909.png`. -/
inductive FigureLabel where
  | plateLengthL
  | electricFieldE
  | entryVelocityV0
  | exitVelocityV1
  | deflectionAngleTheta
  | deflectionPlates
  deriving DecidableEq, Fintype, Repr

/-- The idealized field model between the electrodes. -/
inductive ElectricFieldModel where
  | uniformBetweenParallelPlates
  deriving DecidableEq, Repr

/-!
Literal and qualitative content transcribed from the primary raster.  Its
numerical fields are printed labels, not definitions of the physical velocity
or the requested angle.
-/
structure ElectronDeflectionFigure where
  showsObject : FigureObject → Bool
  showsLabel : FigureLabel → Bool
  platesDrawnParallel : Bool
  plateChargeSign : DeflectionPlate → PlateChargeSign
  electricFieldArrowDirection : ArrowDirection
  entryVelocityArrowDirection : ArrowDirection
  exitVelocityArrowDirection : ArrowDirection
  electronPathCurvesUpward : Bool
  plateLengthLabelCentimeters : ℝ
  electricFieldMagnitudeLabelNewtonsPerCoulomb : ℝ

/-!
Independent physical quantities of the beam passage.  In particular, the exit
velocity is not defined from the desired angle, and the transit time,
acceleration, and force are not defined from an answer choice.
-/
structure ElectronDeflectionSetup where
  figure : ElectronDeflectionFigure
  particleSpecies : ParticleSpecies
  fieldModel : ElectricFieldModel
  plateLength : LengthQuantity
  electronMass : MassQuantity
  electronCharge : SignedChargeQuantity
  electricField : PlanarElectricFieldQuantity
  velocity : BeamState → PlanarVelocityQuantity
  electricForce : PlanarForceQuantity
  acceleration : PlanarAccelerationQuantity
  transitTime : TimeQuantity

/-! ## Scenario, figure evidence, numerical data, and reference constants -/

/-- The prose model: an electron traverses a uniform field between parallel plates. -/
structure MatchesElectronDeflectionScenario
    (setup : ElectronDeflectionSetup) : Prop where
  particleIsElectron : setup.particleSpecies = .electron
  fieldIsUniformBetweenParallelPlates :
    setup.fieldModel = .uniformBetweenParallelPlates

/-!
Primary-image evidence, including both plate polarities, the downward field,
the two velocity arrows, the upward-curving path, `θ`, and the two printed
numerical labels.  It contains no value for `θ`.
-/
structure MatchesSuppliedElectronDeflectionFigure
    (setup : ElectronDeflectionSetup) : Prop where
  everyRelevantObjectShown :
    ∀ object, setup.figure.showsObject object = true
  everyRelevantLabelShown :
    ∀ label, setup.figure.showsLabel label = true
  platesAreParallel : setup.figure.platesDrawnParallel = true
  upperPlateIsPositive :
    setup.figure.plateChargeSign .upper = .positive
  lowerPlateIsNegative :
    setup.figure.plateChargeSign .lower = .negative
  fieldArrowsPointDown :
    setup.figure.electricFieldArrowDirection = .downward
  entryVelocityArrowPointsRight :
    setup.figure.entryVelocityArrowDirection = .rightward
  exitVelocityArrowPointsUpAndRight :
    setup.figure.exitVelocityArrowDirection = .upwardRightward
  trajectoryCurvesUpward : setup.figure.electronPathCurvesUpward = true
  printedPlateLength : setup.figure.plateLengthLabelCentimeters = 2
  printedElectricFieldMagnitude :
    setup.figure.electricFieldMagnitudeLabelNewtonsPerCoulomb =
      5 * (10 : ℝ) ^ 4
  physicalLengthMatchesPrintedLabel :
    lengthInCentimeters setup.plateLength =
      setup.figure.plateLengthLabelCentimeters
  physicalFieldMatchesPrintedMagnitude :
    -electricFieldVectorInNewtonsPerCoulomb
          setup.electricField yAxis =
      setup.figure.electricFieldMagnitudeLabelNewtonsPerCoulomb

/-!
Numerical physical readouts supplied in the prose and figure.  The coordinate
convention makes downward field components negative and the horizontal entry
velocity positive.
-/
structure MatchesGivenElectronDeflectionReadouts
    (setup : ElectronDeflectionSetup) : Prop where
  entryHorizontalSpeed :
    velocityVectorInMetersPerSecond
        (setup.velocity .entry) xAxis =
      33 * (10 : ℝ) ^ 6
  entryVerticalSpeedIsZero :
    velocityVectorInMetersPerSecond
        (setup.velocity .entry) yAxis = 0
  plateLengthCentimeters : lengthInCentimeters setup.plateLength = 2
  electricFieldHasNoHorizontalComponent :
    electricFieldVectorInNewtonsPerCoulomb
        setup.electricField xAxis = 0
  electricFieldPointsDownWithGivenMagnitude :
    electricFieldVectorInNewtonsPerCoulomb
        setup.electricField yAxis = -(5 * (10 : ℝ) ^ 4)

/-!
Standard reference values implicit in the word “electron.”  They are physical
input data, not a premise about the requested angle.
-/
structure UsesStandardElectronReferenceData
    (setup : ElectronDeflectionSetup) : Prop where
  electronMassKilograms :
    massInKilograms setup.electronMass = 9.1093837015e-31
  electronSignedChargeCoulombs :
    chargeInCoulombs setup.electronCharge = -(1.602176634e-19)

/-- Positivity and nondegeneracy conditions for the intended physical branch. -/
structure HasPhysicalElectronDeflectionParameters
    (setup : ElectronDeflectionSetup) : Prop where
  electronMassPositive : 0 < massInKilograms setup.electronMass
  plateLengthPositive : 0 < lengthInMeters setup.plateLength
  transitTimePositive : 0 < timeInSeconds setup.transitTime
  entryHorizontalVelocityPositive :
    0 < velocityVectorInMetersPerSecond
      (setup.velocity .entry) xAxis
  electronChargeNegative : chargeInCoulombs setup.electronCharge < 0

/-! ## Governing electrodynamics and kinematics -/

/-!
The elementary nonrelativistic model in coherent SI units.  The first two
clauses are `F = qE` and `F = ma`; the third is the constant-acceleration
velocity update; the fourth says that constant horizontal motion traverses
the plate length during the field-interaction time.  None mentions an angle
or answer choice.
-/
structure SatisfiesUniformElectricDeflectionDynamics
    (setup : ElectronDeflectionSetup) : Prop where
  electricForceLaw :
    forceVectorInNewtons setup.electricForce =
      chargeInCoulombs setup.electronCharge •
        electricFieldVectorInNewtonsPerCoulomb setup.electricField
  newtonSecondLaw :
    forceVectorInNewtons setup.electricForce =
      massInKilograms setup.electronMass •
        accelerationVectorInMetersPerSecondSquared setup.acceleration
  constantAccelerationVelocityUpdate :
    velocityVectorInMetersPerSecond (setup.velocity .exit) =
      velocityVectorInMetersPerSecond (setup.velocity .entry) +
        timeInSeconds setup.transitTime •
          accelerationVectorInMetersPerSecondSquared setup.acceleration
  horizontalTransitRelation :
    lengthInMeters setup.plateLength =
      timeInSeconds setup.transitTime *
        velocityVectorInMetersPerSecond
          (setup.velocity .entry) xAxis

/-! ## Deflection angle and displayed choices -/

/-!
The physical deflection angle is the undirected Euclidean angle, in radians,
between the independent entry and exit velocity vectors.  This geometric
definition does not insert a numerical answer.
-/
def deflectionAngleRadians (setup : ElectronDeflectionSetup) : ℝ :=
  InnerProductGeometry.angle
    (velocityVectorInMetersPerSecond (setup.velocity .entry))
    (velocityVectorInMetersPerSecond (setup.velocity .exit))

/-- Convert a real radian readout to degrees. -/
def radiansToDegrees (angleRadians : ℝ) : ℝ :=
  angleRadians * 180 / Real.pi

/-- The deflection angle of the beam, read in degrees. -/
def deflectionAngleDegrees (setup : ElectronDeflectionSetup) : ℝ :=
  radiansToDegrees (deflectionAngleRadians setup)

/-!
The arctangent prediction obtained from `F = qE`, `F = ma`, the traversal
time `L / v₀`, and `tan θ = v_y / v_x`.  It depends only on independent
physical inputs and is not definitionally equal to the geometric angle above.
-/
def predictedDeflectionAngleRadians
    (setup : ElectronDeflectionSetup) : ℝ :=
  Real.arctan
    (chargeInCoulombs setup.electronCharge *
        electricFieldVectorInNewtonsPerCoulomb
          setup.electricField yAxis *
        lengthInMeters setup.plateLength /
      (massInKilograms setup.electronMass *
        velocityVectorInMetersPerSecond
            (setup.velocity .entry) xAxis ^ 2))

/-- Labels of the four displayed answer choices. -/
inductive AnswerChoice where
  | A
  | B
  | C
  | D
  deriving DecidableEq, Fintype, Repr

/-- Angle in degrees printed beside each displayed answer label. -/
def AnswerChoice.displayedAngleDegrees : AnswerChoice → ℝ
  | .A => 3
  | .B => 9
  | .C => 91 / 10
  | .D => 20

/-- The answer label recorded in the supplied dataset metadata. -/
def recordedDatasetAnswer : AnswerChoice := .C

/-- A displayed choice is at least as close as every alternative. -/
def IsClosestDisplayedAngle
    (angleDegrees : ℝ) (choice : AnswerChoice) : Prop :=
  ∀ alternative : AnswerChoice,
    |angleDegrees - choice.displayedAngleDegrees| ≤
      |angleDegrees - alternative.displayedAngleDegrees|

/-- A displayed choice is the unique closest one. -/
def IsUniqueClosestDisplayedAngle
    (angleDegrees : ℝ) (choice : AnswerChoice) : Prop :=
  IsClosestDisplayedAngle angleDegrees choice ∧
    ∀ alternative : AnswerChoice,
      IsClosestDisplayedAngle angleDegrees alternative →
        alternative = choice

/-!
The force and kinematics laws first determine the exit-velocity components:
the horizontal component is unchanged, while the vertical component is
generated by the upward electric acceleration of the negatively charged
electron.
-/
lemma exit_velocity_components
    (setup : ElectronDeflectionSetup)
    (_physical : HasPhysicalElectronDeflectionParameters setup)
    (_dynamics : SatisfiesUniformElectricDeflectionDynamics setup) :
    velocityVectorInMetersPerSecond (setup.velocity .exit) xAxis =
        velocityVectorInMetersPerSecond (setup.velocity .entry) xAxis ∧
      velocityVectorInMetersPerSecond (setup.velocity .exit) yAxis =
        velocityVectorInMetersPerSecond (setup.velocity .entry) yAxis +
          chargeInCoulombs setup.electronCharge *
            electricFieldVectorInNewtonsPerCoulomb
              setup.electricField yAxis *
            timeInSeconds setup.transitTime /
              massInKilograms setup.electronMass := by
  have hforceX :=
    congrArg (fun v => v xAxis) _dynamics.electricForceLaw
  have hnewtonX :=
    congrArg (fun v => v xAxis) _dynamics.newtonSecondLaw
  have hvelocityX :=
    congrArg (fun v => v xAxis)
      _dynamics.constantAccelerationVelocityUpdate
  have hforceY :=
    congrArg (fun v => v yAxis) _dynamics.electricForceLaw
  have hnewtonY :=
    congrArg (fun v => v yAxis) _dynamics.newtonSecondLaw
  have hvelocityY :=
    congrArg (fun v => v yAxis)
      _dynamics.constantAccelerationVelocityUpdate
  simp only [PiLp.smul_apply, smul_eq_mul] at hforceX
  simp only [PiLp.smul_apply, smul_eq_mul] at hnewtonX
  simp only [PiLp.add_apply, PiLp.smul_apply, smul_eq_mul] at hvelocityX
  simp only [PiLp.smul_apply, smul_eq_mul] at hforceY
  simp only [PiLp.smul_apply, smul_eq_mul] at hnewtonY
  simp only [PiLp.add_apply, PiLp.smul_apply, smul_eq_mul] at hvelocityY
  have hmass_ne :
      massInKilograms setup.electronMass ≠ 0 :=
    ne_of_gt _physical.electronMassPositive
  constructor
  · have hhorizontal_formula :
        velocityVectorInMetersPerSecond (setup.velocity .exit) xAxis =
          velocityVectorInMetersPerSecond (setup.velocity .entry) xAxis +
            chargeInCoulombs setup.electronCharge *
              electricFieldVectorInNewtonsPerCoulomb
                setup.electricField xAxis *
              timeInSeconds setup.transitTime /
                massInKilograms setup.electronMass := by
      have haccelerationX :
          accelerationVectorInMetersPerSecondSquared
              setup.acceleration xAxis =
            chargeInCoulombs setup.electronCharge *
                electricFieldVectorInNewtonsPerCoulomb
                  setup.electricField xAxis /
              massInKilograms setup.electronMass := by
        apply (eq_div_iff hmass_ne).2
        linarith [hforceX, hnewtonX]
      rw [hvelocityX, haccelerationX]
      ring
    -- The frozen statement supplies no hypothesis that the horizontal
    -- electric-field component vanishes.
    have hfieldX :
        electricFieldVectorInNewtonsPerCoulomb
            setup.electricField xAxis = 0 := by
      sorry
    rw [hhorizontal_formula, hfieldX]
    ring
  · have haccelerationY :
        accelerationVectorInMetersPerSecondSquared
            setup.acceleration yAxis =
          chargeInCoulombs setup.electronCharge *
              electricFieldVectorInNewtonsPerCoulomb
                setup.electricField yAxis /
            massInKilograms setup.electronMass := by
      apply (eq_div_iff hmass_ne).2
      linarith [hforceY, hnewtonY]
    rw [hvelocityY, haccelerationY]
    ring

/-!
Combining the exit-velocity relation with the horizontal transit time gives
the arctangent formula for the geometric deflection angle.
-/
lemma deflection_angle_eq_arctangent_prediction
    (setup : ElectronDeflectionSetup)
    (_readouts : MatchesGivenElectronDeflectionReadouts setup)
    (_reference : UsesStandardElectronReferenceData setup)
    (_physical : HasPhysicalElectronDeflectionParameters setup)
    (_dynamics : SatisfiesUniformElectricDeflectionDynamics setup) :
    deflectionAngleRadians setup =
      predictedDeflectionAngleRadians setup := by
  have hmass_ne :
      massInKilograms setup.electronMass ≠ 0 :=
    ne_of_gt _physical.electronMassPositive
  have hforceX :=
    congrArg (fun v => v xAxis) _dynamics.electricForceLaw
  have hnewtonX :=
    congrArg (fun v => v xAxis) _dynamics.newtonSecondLaw
  have hforceY :=
    congrArg (fun v => v yAxis) _dynamics.electricForceLaw
  have hnewtonY :=
    congrArg (fun v => v yAxis) _dynamics.newtonSecondLaw
  simp only [PiLp.smul_apply, smul_eq_mul] at hforceX hnewtonX hforceY hnewtonY
  have haccelerationX :
      accelerationVectorInMetersPerSecondSquared
          setup.acceleration xAxis = 0 := by
    apply (mul_eq_zero.mp ?_).resolve_left hmass_ne
    calc
      massInKilograms setup.electronMass *
            accelerationVectorInMetersPerSecondSquared
              setup.acceleration xAxis =
          forceVectorInNewtons setup.electricForce xAxis := hnewtonX.symm
      _ =
          chargeInCoulombs setup.electronCharge *
            electricFieldVectorInNewtonsPerCoulomb
              setup.electricField xAxis := hforceX
      _ = 0 := by rw [_readouts.electricFieldHasNoHorizontalComponent]; ring
  have haccelerationY :
      accelerationVectorInMetersPerSecondSquared
          setup.acceleration yAxis =
        chargeInCoulombs setup.electronCharge *
            electricFieldVectorInNewtonsPerCoulomb
              setup.electricField yAxis /
          massInKilograms setup.electronMass := by
    apply (eq_div_iff hmass_ne).2
    linarith [hforceY, hnewtonY]
  have hentry :
      velocityVectorInMetersPerSecond (setup.velocity .entry) =
        EuclideanSpace.single xAxis
          (velocityVectorInMetersPerSecond
            (setup.velocity .entry) xAxis) := by
    ext i
    fin_cases i
    · simp [xAxis, EuclideanSpace.single]
    · simpa [xAxis, yAxis, EuclideanSpace.single] using
        _readouts.entryVerticalSpeedIsZero
  have hincrement :
      timeInSeconds setup.transitTime •
          accelerationVectorInMetersPerSecondSquared setup.acceleration =
        EuclideanSpace.single yAxis
          (chargeInCoulombs setup.electronCharge *
              electricFieldVectorInNewtonsPerCoulomb
                setup.electricField yAxis *
              timeInSeconds setup.transitTime /
            massInKilograms setup.electronMass) := by
    ext i
    fin_cases i
    · simp only [PiLp.smul_apply, smul_eq_mul]
      change
        timeInSeconds setup.transitTime *
            accelerationVectorInMetersPerSecondSquared
              setup.acceleration xAxis = 0
      rw [haccelerationX, mul_zero]
    · simp only [PiLp.smul_apply, smul_eq_mul]
      change
        timeInSeconds setup.transitTime *
            accelerationVectorInMetersPerSecondSquared
              setup.acceleration yAxis =
          chargeInCoulombs setup.electronCharge *
              electricFieldVectorInNewtonsPerCoulomb
                setup.electricField yAxis *
              timeInSeconds setup.transitTime /
            massInKilograms setup.electronMass
      rw [haccelerationY]
      ring
  have horthogonal :
      inner ℝ
          (velocityVectorInMetersPerSecond (setup.velocity .entry))
          (timeInSeconds setup.transitTime •
            accelerationVectorInMetersPerSecondSquared setup.acceleration) =
        0 := by
    rw [hentry, hincrement]
    simp [EuclideanSpace.inner_single_left, xAxis, yAxis]
  have hentry_ne :
      velocityVectorInMetersPerSecond (setup.velocity .entry) ≠ 0 := by
    intro hzero
    have := congrArg (fun v => v xAxis) hzero
    simp only [PiLp.zero_apply] at this
    rw [_readouts.entryHorizontalSpeed] at this
    norm_num at this
  have hcharge_field_pos :
      0 <
        chargeInCoulombs setup.electronCharge *
          electricFieldVectorInNewtonsPerCoulomb
            setup.electricField yAxis :=
    mul_pos_of_neg_of_neg _physical.electronChargeNegative
      (by
        rw [_readouts.electricFieldPointsDownWithGivenMagnitude]
        norm_num)
  have hincrement_scalar_pos :
      0 <
        chargeInCoulombs setup.electronCharge *
            electricFieldVectorInNewtonsPerCoulomb
              setup.electricField yAxis *
            timeInSeconds setup.transitTime /
          massInKilograms setup.electronMass :=
    div_pos
      (mul_pos hcharge_field_pos _physical.transitTimePositive)
      _physical.electronMassPositive
  unfold deflectionAngleRadians predictedDeflectionAngleRadians
  rw [_dynamics.constantAccelerationVelocityUpdate]
  rw [InnerProductGeometry.angle_add_eq_arctan_of_inner_eq_zero
    horthogonal hentry_ne]
  rw [hentry, hincrement]
  simp only [PiLp.norm_single, Real.norm_eq_abs]
  rw [abs_of_pos _physical.entryHorizontalVelocityPositive,
    abs_of_pos hincrement_scalar_pos]
  congr 1
  simp only [PiLp.single_apply, if_pos]
  rw [_dynamics.horizontalTransitRelation]
  field_simp [hmass_ne, ne_of_gt _physical.entryHorizontalVelocityPositive]

/-!
**Blueprint target** `thm:physics:phyx_mini_0909:target`.

The standard electron data, the displayed plate length and field, and the
nonrelativistic uniform-field laws give the arctangent prediction.  Its degree
readout is approximately `9.18°`, so the displayed `9.1°` value (choice C) is
uniquely closer than `3°`, `9°`, and `20°`.
-/
theorem problem_phyx_mini_0909
    (setup : ElectronDeflectionSetup)
    (_scenario : MatchesElectronDeflectionScenario setup)
    (_figure : MatchesSuppliedElectronDeflectionFigure setup)
    (_readouts : MatchesGivenElectronDeflectionReadouts setup)
    (_reference : UsesStandardElectronReferenceData setup)
    (_physical : HasPhysicalElectronDeflectionParameters setup)
    (_dynamics : SatisfiesUniformElectricDeflectionDynamics setup) :
    deflectionAngleRadians setup =
        predictedDeflectionAngleRadians setup ∧
      IsUniqueClosestDisplayedAngle
        (deflectionAngleDegrees setup) recordedDatasetAnswer := by
  have hangle :
      deflectionAngleRadians setup =
        predictedDeflectionAngleRadians setup :=
    deflection_angle_eq_arctangent_prediction setup
      _readouts _reference _physical _dynamics
  refine ⟨hangle, ?_⟩
  have hlength :
      lengthInMeters setup.plateLength = 1 / 50 := by
    have h := _readouts.plateLengthCentimeters
    unfold lengthInCentimeters at h
    linarith
  let r : ℝ := 356039252000 / 2204470855763
  have hr_pos : 0 < r := by
    dsimp [r]
    positivity
  have hprediction :
      predictedDeflectionAngleRadians setup = Real.arctan r := by
    unfold predictedDeflectionAngleRadians
    rw [_reference.electronSignedChargeCoulombs,
      _readouts.electricFieldPointsDownWithGivenMagnitude,
      hlength, _reference.electronMassKilograms,
      _readouts.entryHorizontalSpeed]
    congr 1
    dsimp [r]
    norm_num
  have harctan_lower :
      r - r ^ 3 / 3 ≤ Real.arctan r := by
    have hmono :
        (∫ x : ℝ in 0..r, (1 - x ^ 2)) ≤
          ∫ x : ℝ in 0..r, 1 / (1 + x ^ 2) := by
      refine intervalIntegral.integral_mono_on hr_pos.le ?_ ?_ ?_
      · exact
          (continuous_const.sub (continuous_id.pow 2)).intervalIntegrable
            0 r
      · exact
          (continuous_const.div
              (continuous_const.add (continuous_id.pow 2))
              (fun x => by
                change (1 : ℝ) + x ^ 2 ≠ 0
                positivity)).intervalIntegrable 0 r
      · intro x _hx
        have hden : 0 < 1 + x ^ 2 := by positivity
        rw [le_div_iff₀ hden]
        nlinarith [sq_nonneg (x ^ 2)]
    rw [integral_one_div_one_add_sq] at hmono
    simp only [Real.arctan_zero, sub_zero] at hmono
    convert hmono using 1
    norm_num [intervalIntegral.integral_sub, integral_pow]
  have harctan_upper :
      Real.arctan r ≤ r := by
    have hmono :
        (∫ x : ℝ in 0..r, 1 / (1 + x ^ 2)) ≤
          ∫ _x : ℝ in 0..r, 1 := by
      refine intervalIntegral.integral_mono_on hr_pos.le ?_ ?_ ?_
      · exact
          (continuous_const.div
              (continuous_const.add (continuous_id.pow 2))
              (fun x => by
                change (1 : ℝ) + x ^ 2 ≠ 0
                positivity)).intervalIntegrable 0 r
      · exact continuous_const.intervalIntegrable 0 r
      · intro x _hx
        have hden : 0 < 1 + x ^ 2 := by positivity
        rw [div_le_one hden]
        nlinarith [sq_nonneg x]
    rw [integral_one_div_one_add_sq] at hmono
    simpa using hmono
  let z : ℝ := Real.arctan r * 180 / Real.pi
  have hdegree : deflectionAngleDegrees setup = z := by
    unfold deflectionAngleDegrees radiansToDegrees
    rw [hangle, hprediction]
  rw [hdegree]
  change IsUniqueClosestDisplayedAngle z .C
  have hrad_lower :
      (91 / 10 : ℝ) * Real.pi / 180 <
        Real.arctan r := by
    apply lt_of_lt_of_le _ harctan_lower
    calc
      (91 / 10 : ℝ) * Real.pi / 180
          < (91 / 10 : ℝ) * 3.1416 / 180 := by
              gcongr
              exact Real.pi_lt_d4
      _ < r - r ^ 3 / 3 := by
        dsimp [r]
        norm_num
  have hz_lower : (91 / 10 : ℝ) < z := by
    dsimp [z]
    rw [lt_div_iff₀ Real.pi_pos]
    nlinarith [hrad_lower]
  have hz_upper : z < (291 / 20 : ℝ) := by
    dsimp [z]
    apply (div_lt_iff₀ Real.pi_pos).2
    calc
      Real.arctan r * 180 ≤ r * 180 := by gcongr
      _ < (291 / 20 : ℝ) * 3 := by
        dsimp [r]
        norm_num
      _ < (291 / 20 : ℝ) * Real.pi := by
        gcongr
        exact Real.pi_gt_three
  have hdistC : |z - (91 / 10 : ℝ)| = z - 91 / 10 :=
    abs_of_pos (sub_pos.2 hz_lower)
  have hdistA : |z - (3 : ℝ)| = z - 3 :=
    abs_of_pos (by linarith [hz_lower])
  have hdistB : |z - (9 : ℝ)| = z - 9 :=
    abs_of_pos (by linarith [hz_lower])
  have hdistD : |z - (20 : ℝ)| = 20 - z := by
    have hz_twenty : z < 20 :=
      lt_trans hz_upper (by norm_num)
    calc
      |z - (20 : ℝ)| = -(z - 20) := abs_of_neg (sub_neg.mpr hz_twenty)
      _ = 20 - z := by ring
  unfold IsUniqueClosestDisplayedAngle
  constructor
  · unfold IsClosestDisplayedAngle
    intro alternative
    fin_cases alternative
    · simp only [AnswerChoice.displayedAngleDegrees]
      rw [hdistC, hdistA]
      linarith
    · simp only [AnswerChoice.displayedAngleDegrees]
      rw [hdistC, hdistB]
      linarith
    · exact le_rfl
    · simp only [AnswerChoice.displayedAngleDegrees]
      rw [hdistC, hdistD]
      linarith [hz_upper]
  · intro alternative hclosest
    unfold IsClosestDisplayedAngle at hclosest
    fin_cases alternative
    · exfalso
      have h := hclosest .C
      simp only [AnswerChoice.displayedAngleDegrees] at h
      rw [hdistA, hdistC] at h
      linarith
    · exfalso
      have h := hclosest .C
      simp only [AnswerChoice.displayedAngleDegrees] at h
      rw [hdistB, hdistC] at h
      linarith
    · rfl
    · exfalso
      have h := hclosest .C
      simp only [AnswerChoice.displayedAngleDegrees] at h
      rw [hdistD, hdistC] at h
      linarith [hz_upper]

end PhyXMiniProblems.ProblemPhyXMini0909
