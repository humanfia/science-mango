import Mathlib
import Physlib.Units.WithDim.Area
import Physlib.Units.WithDim.Pressure

/- USER: The assigned source file did not exist when this autoformalization task began. -/

/-!
# Gas pressure above a stepped hydraulic piston

The primary figure shows a single vertical stepped piston joining cylinder
`A` below to cylinder `B` above.  The lower hydraulic chamber has diameter
`D_A = 100 mm` and is pumped to an absolute pressure of `500 kPa`; the upper
gas chamber has diameter `D_B = 25 mm`.  Atmospheric pressure
`P₀ = 100 kPa` acts downward on the exposed annular shoulder, and the
`25 kg` piston is subject to standard gravity.

Pressures and areas use Physlib's unit-independent dimensional quantities.
The other physical quantities are built from the same `Dimensionful` and
`WithDim` infrastructure.  Real numbers occur only in explicitly named SI
readouts, force-component readouts in newtons, and displayed answer values.
-/

noncomputable section

namespace PhyXMiniProblems.ProblemPhyXMini0395

open Dimension

/-! ## Dimensionful quantities and coherent-SI readouts -/

/-- A nonnegative physical length, independent of the unit used to read it. -/
abbrev LengthQuantity : Type :=
  Dimensionful (WithDim L𝓭 NNReal)

/-- A nonnegative physical mass. -/
abbrev MassQuantity : Type :=
  Dimensionful (WithDim M𝓭 NNReal)

/-- A nonnegative physical acceleration magnitude. -/
abbrev AccelerationQuantity : Type :=
  Dimensionful (WithDim (L𝓭 * T𝓭⁻¹ * T𝓭⁻¹) NNReal)

/-- A nonnegative physical cross-sectional area. -/
abbrev AreaQuantity : Type := DimArea

/-- A physical absolute pressure. -/
abbrev PressureQuantity : Type := DimPressure

/-- Coherent-SI metre readout of a physical length. -/
def lengthInMeters (length : LengthQuantity) : ℝ :=
  ((length UnitChoices.SI).val : ℝ)

/-- Millimetre readout used by the two diameter labels in the figure. -/
def lengthInMillimeters (length : LengthQuantity) : ℝ :=
  1000 * lengthInMeters length

/-- Coherent-SI kilogram readout of a physical mass. -/
def massInKilograms (mass : MassQuantity) : ℝ :=
  ((mass UnitChoices.SI).val : ℝ)

/-- Coherent-SI metre-per-second-squared readout of an acceleration. -/
def accelerationInMetersPerSecondSquared
    (acceleration : AccelerationQuantity) : ℝ :=
  ((acceleration UnitChoices.SI).val : ℝ)

/-- Coherent-SI square-metre readout of a physical area. -/
def areaInSquareMeters (area : AreaQuantity) : ℝ :=
  ((area UnitChoices.SI).val : ℝ)

/-- Coherent-SI pascal readout of an absolute pressure. -/
def pressureInPascals (pressure : PressureQuantity) : ℝ :=
  (pressure UnitChoices.SI).val

/-- Kilopascal readout used by the data printed in the problem. -/
def pressureInKilopascals (pressure : PressureQuantity) : ℝ :=
  pressureInPascals pressure / 1000

/-! ## Apparatus roles and primary-figure information -/

/-- The two cylinders labelled in the supplied image. -/
inductive CylinderLabel where
  | A
  | B
  deriving DecidableEq, Fintype, Repr

/-- Physical contents associated with a labelled cylinder. -/
inductive ChamberContents where
  | hydraulicFluid
  | gas
  deriving DecidableEq, Repr

/-- Exposed surfaces of the stepped piston that carry vertical pressure loads. -/
inductive PistonSurface where
  | lowerFaceA
  | upperFaceB
  | annularShoulder
  deriving DecidableEq, Repr

/-- Vertical direction of an arrow or force component in the image. -/
inductive VerticalDirection where
  | upward
  | downward
  deriving DecidableEq, Repr

/-- Qualitative labels and placements read directly from image `395.png`. -/
structure PrimaryHydraulicFigure where
  lowerCylinder : CylinderLabel
  upperCylinder : CylinderLabel
  pumpConnectedCylinder : CylinderLabel
  atmosphericPressureSurface : PistonSurface
  gravityArrowDirection : VerticalDirection
  diameterSymbol : CylinderLabel → String
  atmosphericPressureSymbol : String
  gravitySymbol : String

/--
The stepped piston and its independent physical observables.  In particular,
the pressure in cylinder `B` is an unconstrained physical pressure here; its
requested numerical value is not built into this structure.
-/
structure CompoundPistonSetup where
  figure : PrimaryHydraulicFigure
  chamberContents : CylinderLabel → ChamberContents
  cylinderDiameter : CylinderLabel → LengthQuantity
  pistonFaceArea : CylinderLabel → AreaQuantity
  chamberAbsolutePressure : CylinderLabel → PressureQuantity
  outsideAtmosphericPressureP0 : PressureQuantity
  pistonMass : MassQuantity
  gravitationalAcceleration : AccelerationQuantity
  pistonIsRigid : Bool
  pistonIsFrictionless : Bool
  chamberPressuresAreUniform : Bool
  pistonIsInStaticEquilibrium : Bool

/-! ## Figure/data readouts and qualitative physical conditions -/

/-- The labels and spatial roles visible in the supplied primary figure. -/
structure MatchesPrimaryFigure (setup : CompoundPistonSetup) : Prop where
  cylinderAIsLower : setup.figure.lowerCylinder = .A
  cylinderBIsUpper : setup.figure.upperCylinder = .B
  pumpFeedsCylinderA : setup.figure.pumpConnectedCylinder = .A
  atmosphereActsOnAnnularShoulder :
    setup.figure.atmosphericPressureSurface = .annularShoulder
  gravityPointsDownward : setup.figure.gravityArrowDirection = .downward
  diameterSymbolA : setup.figure.diameterSymbol .A = "D_A"
  diameterSymbolB : setup.figure.diameterSymbol .B = "D_B"
  atmosphericPressureSymbol :
    setup.figure.atmosphericPressureSymbol = "P_0"
  gravitySymbol : setup.figure.gravitySymbol = "g"
  cylinderAContainsHydraulicFluid :
    setup.chamberContents .A = .hydraulicFluid
  cylinderBContainsGas : setup.chamberContents .B = .gas

/--
Numerical information supplied by the prose and image.  The value
`196133 / 20000 m/s²` is standard gravity `9.80665 m/s²`.  The pressure in
cylinder `B` is deliberately absent.
-/
structure MatchesProblemData (setup : CompoundPistonSetup) : Prop where
  cylinderADiameterMillimeters :
    lengthInMillimeters (setup.cylinderDiameter .A) = 100
  cylinderBDiameterMillimeters :
    lengthInMillimeters (setup.cylinderDiameter .B) = 25
  cylinderAPressureKilopascals :
    pressureInKilopascals (setup.chamberAbsolutePressure .A) = 500
  atmosphericPressureKilopascals :
    pressureInKilopascals setup.outsideAtmosphericPressureP0 = 100
  pistonMassKilograms : massInKilograms setup.pistonMass = 25
  standardGravityMetersPerSecondSquared :
    accelerationInMetersPerSecondSquared
        setup.gravitationalAcceleration = 196133 / 20000

/-- Positivity and ordering assumptions selecting the depicted physical branch. -/
structure HasPhysicalParameters (setup : CompoundPistonSetup) : Prop where
  cylinderADiameterPositive :
    0 < lengthInMeters (setup.cylinderDiameter .A)
  cylinderBDiameterPositive :
    0 < lengthInMeters (setup.cylinderDiameter .B)
  cylinderAFaceAreaPositive :
    0 < areaInSquareMeters (setup.pistonFaceArea .A)
  cylinderBFaceAreaPositive :
    0 < areaInSquareMeters (setup.pistonFaceArea .B)
  cylinderBFaceSmaller :
    areaInSquareMeters (setup.pistonFaceArea .B) <
      areaInSquareMeters (setup.pistonFaceArea .A)
  cylinderAPressurePositive :
    0 < pressureInPascals (setup.chamberAbsolutePressure .A)
  cylinderBPressurePositive :
    0 < pressureInPascals (setup.chamberAbsolutePressure .B)
  atmosphericPressurePositive :
    0 < pressureInPascals setup.outsideAtmosphericPressureP0
  pistonMassPositive : 0 < massInKilograms setup.pistonMass
  gravityPositive :
    0 < accelerationInMetersPerSecondSquared
      setup.gravitationalAcceleration

/-! ## Governing geometry and statics -/

/--
Both load-bearing piston faces are circular.  This is a generic geometry law
relating each physical area to its corresponding figure diameter; it contains
no pressure value and no answer choice.
-/
structure SatisfiesCircularFaceGeometry
    (setup : CompoundPistonSetup) : Prop where
  circularFaceArea : ∀ cylinder : CylinderLabel,
    areaInSquareMeters (setup.pistonFaceArea cylinder) =
      Real.pi * (lengthInMeters (setup.cylinderDiameter cylinder) / 2) ^ 2

/-- Qualitative idealizations used in the static pressure-force model. -/
structure MatchesIdealStaticModel (setup : CompoundPistonSetup) : Prop where
  rigidPiston : setup.pistonIsRigid = true
  frictionlessPiston : setup.pistonIsFrictionless = true
  uniformFacePressures : setup.chamberPressuresAreUniform = true
  staticEquilibrium : setup.pistonIsInStaticEquilibrium = true

/-- Upward hydraulic pressure force on the large lower face, in newtons. -/
def upwardHydraulicForceInNewtons (setup : CompoundPistonSetup) : ℝ :=
  pressureInPascals (setup.chamberAbsolutePressure .A) *
    areaInSquareMeters (setup.pistonFaceArea .A)

/-- Downward gas pressure force on the small upper face, in newtons. -/
def downwardGasForceInNewtons (setup : CompoundPistonSetup) : ℝ :=
  pressureInPascals (setup.chamberAbsolutePressure .B) *
    areaInSquareMeters (setup.pistonFaceArea .B)

/-- Area of the exposed annular shoulder, read in square metres. -/
def annularShoulderAreaInSquareMeters (setup : CompoundPistonSetup) : ℝ :=
  areaInSquareMeters (setup.pistonFaceArea .A) -
    areaInSquareMeters (setup.pistonFaceArea .B)

/-- Downward atmospheric force on the annular shoulder, in newtons. -/
def downwardAtmosphericForceInNewtons (setup : CompoundPistonSetup) : ℝ :=
  pressureInPascals setup.outsideAtmosphericPressureP0 *
    annularShoulderAreaInSquareMeters setup

/-- Downward gravitational force on the piston, in newtons. -/
def pistonWeightInNewtons (setup : CompoundPistonSetup) : ℝ :=
  massInKilograms setup.pistonMass *
    accelerationInMetersPerSecondSquared setup.gravitationalAcceleration

/--
The ideal vertical force balance for the compound piston.  Cylinder `A`
pushes upward over the large face.  The gas in `B`, atmospheric pressure on
the annular shoulder, and the piston's weight act downward.  This governing
law contains no numerical value for the unknown gas pressure.
-/
structure SatisfiesStaticForceBalance
    (setup : CompoundPistonSetup) : Prop where
  verticalEquilibrium :
    upwardHydraulicForceInNewtons setup =
      downwardGasForceInNewtons setup +
        downwardAtmosphericForceInNewtons setup +
          pistonWeightInNewtons setup

/-! ## Displayed answers and requested conclusion -/

/-- Labels of the four answers printed with the problem. -/
inductive AnswerChoice where
  | A
  | B
  | C
  | D
  deriving DecidableEq, Fintype, Repr

/-- Absolute pressure in pascals printed beside each answer label. -/
def displayedPressureInPascals : AnswerChoice → ℝ
  | .A => 4000000
  | .B => 6000000
  | .C => 154000
  | .D => 10200

/-- The answer label recorded in the supplied dataset. -/
def recordedAnswerChoice : AnswerChoice := .B

/-- A displayed answer is the unique closest choice to a derived pressure. -/
def IsUniqueClosestAnswer
    (pressurePascals : ℝ) (choice : AnswerChoice) : Prop :=
  ∀ otherChoice,
    otherChoice ≠ choice →
      |pressurePascals - displayedPressureInPascals choice| <
        |pressurePascals - displayedPressureInPascals otherChoice|

/--
Static balance gives the exact cylinder-`B` pressure
`6 500 000 - 1 569 064 / π Pa`, approximately `6.00055 MPa`.  Hence the
unique closest displayed pressure is `6 MPa`, answer B.

Blueprint label: `thm:physics:phyx_mini_0395:target`.
-/
theorem gasPressureInCylinderB
    (setup : CompoundPistonSetup)
    (_figure : MatchesPrimaryFigure setup)
    (_data : MatchesProblemData setup)
    (_physical : HasPhysicalParameters setup)
    (_geometry : SatisfiesCircularFaceGeometry setup)
    (_model : MatchesIdealStaticModel setup)
    (_balance : SatisfiesStaticForceBalance setup) :
    pressureInPascals (setup.chamberAbsolutePressure .B) =
        6500000 - 1569064 / Real.pi ∧
      IsUniqueClosestAnswer
        (pressureInPascals (setup.chamberAbsolutePressure .B)) .B := by
  have h_diameterA :
      lengthInMeters (setup.cylinderDiameter .A) = 1 / 10 := by
    have h := _data.cylinderADiameterMillimeters
    dsimp [lengthInMillimeters] at h
    linarith
  have h_diameterB :
      lengthInMeters (setup.cylinderDiameter .B) = 1 / 40 := by
    have h := _data.cylinderBDiameterMillimeters
    dsimp [lengthInMillimeters] at h
    linarith
  have h_pressureA :
      pressureInPascals (setup.chamberAbsolutePressure .A) = 500000 := by
    have h := _data.cylinderAPressureKilopascals
    dsimp [pressureInKilopascals] at h
    linarith
  have h_pressure0 :
      pressureInPascals setup.outsideAtmosphericPressureP0 = 100000 := by
    have h := _data.atmosphericPressureKilopascals
    dsimp [pressureInKilopascals] at h
    linarith
  have h_areaA :
      areaInSquareMeters (setup.pistonFaceArea .A) = Real.pi / 400 := by
    rw [_geometry.circularFaceArea, h_diameterA]
    ring
  have h_areaB :
      areaInSquareMeters (setup.pistonFaceArea .B) = Real.pi / 6400 := by
    rw [_geometry.circularFaceArea, h_diameterB]
    ring
  have h_balance := _balance.verticalEquilibrium
  dsimp [upwardHydraulicForceInNewtons, downwardGasForceInNewtons,
    downwardAtmosphericForceInNewtons, annularShoulderAreaInSquareMeters,
    pistonWeightInNewtons] at h_balance
  rw [h_pressureA, h_pressure0, h_areaA, h_areaB,
    _data.pistonMassKilograms,
    _data.standardGravityMetersPerSecondSquared] at h_balance
  have h_pressureB :
      pressureInPascals (setup.chamberAbsolutePressure .B) =
        6500000 - 1569064 / Real.pi := by
    field_simp [Real.pi_ne_zero]
    nlinarith [h_balance]
  have h_fraction_lt :
      1569064 / Real.pi < 500000 := by
    apply (div_lt_iff₀ Real.pi_pos).2
    nlinarith [Real.pi_gt_d4]
  have h_fraction_gt :
      499000 < 1569064 / Real.pi := by
    apply (lt_div_iff₀ Real.pi_pos).2
    nlinarith [Real.pi_lt_d4]
  have h_pressureB_lower :
      6000000 < pressureInPascals (setup.chamberAbsolutePressure .B) := by
    rw [h_pressureB]
    linarith
  have h_pressureB_upper :
      pressureInPascals (setup.chamberAbsolutePressure .B) < 6001000 := by
    rw [h_pressureB]
    linarith
  refine ⟨h_pressureB, ?_⟩
  unfold IsUniqueClosestAnswer
  intro otherChoice h_other
  fin_cases otherChoice
  · simp only [displayedPressureInPascals]
    rw [abs_of_pos (by linarith), abs_of_pos (by linarith)]
    linarith
  · exact (h_other rfl).elim
  · simp only [displayedPressureInPascals]
    rw [abs_of_pos (by linarith), abs_of_pos (by linarith)]
    linarith
  · simp only [displayedPressureInPascals]
    rw [abs_of_pos (by linarith), abs_of_pos (by linarith)]
    linarith

end PhyXMiniProblems.ProblemPhyXMini0395
