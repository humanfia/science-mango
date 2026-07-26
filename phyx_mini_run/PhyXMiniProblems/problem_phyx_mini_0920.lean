import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Physlib.Electromagnetism.Basic
import Physlib.Units.WithDim.Basic

/- USER: The assigned Lean file did not exist when this autoformalization task began. -/

noncomputable section

namespace PhyXMiniProblems.ProblemPhyXMini0920

open Dimension

/-!
# Center-to-rim EMF of a rotating conducting disk

A conducting disk of radius `R` lies in the `xy`-plane and rotates with
constant angular speed `ω` about the `z`-axis.  A uniform, constant magnetic
field is directed along that same axis.  The primary raster highlights a
radial element of length `dr` at radius `r`, gives its tangential speed as
`v = ω r`, and gives its local motional EMF as
`dℰ = v B dr = ω B r dr`.

Length, angular speed, tangential speed, magnetic-flux density, motional-EMF
density, EMF, current, and resistance are unit-independent Physlib
`Dimensionful` quantities.  Real numbers occur only in explicitly named SI
readouts, the radial metre coordinate used by the displayed differential law,
and the displayed answer expressions.

Assumption/target split:

* governing laws: the spacetime magnetic field is uniform and axial, rigid
  rotation gives `v(r) = ω r`, the perpendicular motional-EMF density is
  `v(r) B`, and the center-to-rim EMF is the radial interval integral of this
  density;
* previous-part results: none;
* figure/data readouts: the three coordinate axes, disk and radius, four
  magnetic-field arrows, the labelled `r`/`dr` segment, tangential velocity,
  angular-speed arrow, two brushes, resistor, and external current arrow;
* current target: the center-to-rim EMF is `(1 / 2) * ω * B * R^2`, answer C.

No setup, figure, scenario, or law field states this closed-form target.
-/

/-! ## Dimensionful physical quantities and coherent-SI readouts -/

/-- Angular speed has dimension `T⁻¹`; radians are dimensionless. -/
def angularSpeedDimension : Dimension :=
  T𝓭⁻¹

/-- Tangential speed has dimension `L T⁻¹`. -/
def speedDimension : Dimension :=
  L𝓭 * T𝓭⁻¹

/-- Magnetic flux density has dimension `M T⁻¹ C⁻¹`. -/
def magneticFluxDensityDimension : Dimension :=
  M𝓭 * T𝓭⁻¹ * C𝓭⁻¹

/-- Motional-EMF density has electric-field dimension `M L T⁻² C⁻¹`. -/
def motionalEmfDensityDimension : Dimension :=
  M𝓭 * L𝓭 * T𝓭⁻¹ * T𝓭⁻¹ * C𝓭⁻¹

/-- EMF has electric-potential dimension `M L² T⁻² C⁻¹`. -/
def emfDimension : Dimension :=
  M𝓭 * L𝓭 * L𝓭 * T𝓭⁻¹ * T𝓭⁻¹ * C𝓭⁻¹

/-- Electric current has dimension `C T⁻¹`. -/
def electricCurrentDimension : Dimension :=
  C𝓭 * T𝓭⁻¹

/-- Electrical resistance has dimension `M L² T⁻¹ C⁻²`. -/
def electricalResistanceDimension : Dimension :=
  M𝓭 * L𝓭 * L𝓭 * T𝓭⁻¹ * C𝓭⁻¹ * C𝓭⁻¹

/-- A nonnegative, unit-independent physical length. -/
abbrev LengthQuantity : Type :=
  Dimensionful (WithDim L𝓭 NNReal)

/-- A nonnegative, unit-independent angular-speed magnitude. -/
abbrev AngularSpeedMagnitude : Type :=
  Dimensionful (WithDim angularSpeedDimension NNReal)

/-- A nonnegative, unit-independent tangential-speed magnitude. -/
abbrev SpeedMagnitude : Type :=
  Dimensionful (WithDim speedDimension NNReal)

/-- A nonnegative, unit-independent magnetic-flux-density magnitude. -/
abbrev MagneticFluxDensityMagnitude : Type :=
  Dimensionful (WithDim magneticFluxDensityDimension NNReal)

/-- A nonnegative local motional-EMF density, measured in volts per metre. -/
abbrev MotionalEmfDensityMagnitude : Type :=
  Dimensionful (WithDim motionalEmfDensityDimension NNReal)

/-- A nonnegative induced-EMF magnitude. -/
abbrev EmfMagnitude : Type :=
  Dimensionful (WithDim emfDimension NNReal)

/-- A nonnegative electric-current magnitude in the depicted external circuit. -/
abbrev ElectricCurrentMagnitude : Type :=
  Dimensionful (WithDim electricCurrentDimension NNReal)

/-- A nonnegative electrical resistance for the depicted load. -/
abbrev ResistanceMagnitude : Type :=
  Dimensionful (WithDim electricalResistanceDimension NNReal)

/-- Read a nonnegative dimensionful quantity in coherent SI units. -/
def nonnegativeSIReadout {d : Dimension}
    (quantity : Dimensionful (WithDim d NNReal)) : ℝ :=
  ((quantity UnitChoices.SI).val : ℝ)

/-- Read a physical length in metres. -/
def lengthInMeters (length : LengthQuantity) : ℝ :=
  nonnegativeSIReadout length

/-- Read angular speed in radians per second. -/
def angularSpeedInRadiansPerSecond
    (angularSpeed : AngularSpeedMagnitude) : ℝ :=
  nonnegativeSIReadout angularSpeed

/-- Read tangential speed in metres per second. -/
def speedInMetersPerSecond (speed : SpeedMagnitude) : ℝ :=
  nonnegativeSIReadout speed

/-- Read magnetic flux density in teslas. -/
def magneticFluxDensityInTeslas
    (field : MagneticFluxDensityMagnitude) : ℝ :=
  nonnegativeSIReadout field

/-- Read local motional-EMF density in volts per metre. -/
def motionalEmfDensityInVoltsPerMeter
    (density : MotionalEmfDensityMagnitude) : ℝ :=
  nonnegativeSIReadout density

/-- Read an induced-EMF magnitude in volts. -/
def emfInVolts (emf : EmfMagnitude) : ℝ :=
  nonnegativeSIReadout emf

/-- Read current magnitude in amperes. -/
def currentInAmperes (current : ElectricCurrentMagnitude) : ℝ :=
  nonnegativeSIReadout current

/-- Read electrical resistance in ohms. -/
def resistanceInOhms (resistance : ResistanceMagnitude) : ℝ :=
  nonnegativeSIReadout resistance

/-! ## Spatial roles, figure vocabulary, and independent setup -/

/-- The three Cartesian axes explicitly labelled in the supplied raster. -/
inductive CoordinateAxis where
  | x
  | y
  | z
  deriving DecidableEq, Fintype, Repr

/-- Coordinate plane occupied by the idealized disk. -/
inductive CoordinatePlane where
  | xy
  deriving DecidableEq, Repr

/-- Axial direction shared by the displayed rotation and magnetic field. -/
inductive AxialDirection where
  | positiveZ
  | negativeZ
  deriving DecidableEq, Repr

/-- Material idealization assigned to the rotating object. -/
inductive DiskMaterialModel where
  | conducting
  | insulating
  deriving DecidableEq, Repr

/-- The two electrical contacts between which the EMF is requested. -/
inductive DiskContact where
  | center
  | rim
  deriving DecidableEq, Fintype, Repr

/-- Direction of conventional current shown in the external load branch. -/
inductive ExternalCurrentDirection where
  | rimThroughLoadToCenter
  | centerThroughLoadToRim
  deriving DecidableEq, Repr

/-- Symbolic quantity labels visible in image `920.png`. -/
inductive FigureQuantityLabel where
  | diskRadius
  | angularSpeed
  | magneticField
  | localRadius
  | radialElementLength
  | tangentialSpeed
  | externalCurrent
  | brush
  deriving DecidableEq, Fintype, Repr

/-- Printed symbol expected for each labelled quantity in the raster. -/
def expectedPrintedSymbol : FigureQuantityLabel → String
  | .diskRadius => "R"
  | .angularSpeed => "ω"
  | .magneticField => "B"
  | .localRadius => "r"
  | .radialElementLength => "dr"
  | .tangentialSpeed => "v"
  | .externalCurrent => "I"
  | .brush => "b"

/-- Literal presentation facts transcribed from the primary raster. -/
structure RotatingDiskFigure where
  coordinateAxisShown : CoordinateAxis → Bool
  diskShown : Bool
  diskRenderedCircular : Bool
  quantityLabelShown : FigureQuantityLabel → Bool
  printedSymbol : FigureQuantityLabel → String
  magneticFieldArrowCount : ℕ
  rotationArrowShown : Bool
  highlightedRadialElementShown : Bool
  velocityArrowShown : Bool
  velocityArrowTangentialToRadius : Bool
  brushShownAt : DiskContact → Bool
  brushLabelCount : ℕ
  externalCircuitShown : Bool
  resistorShown : Bool
  currentArrowShown : Bool
  currentArrowDirection : ExternalCurrentDirection

/-!
Independent physical quantities and profiles of the rotating-disk apparatus.
The induced EMF is an observable indexed by its contacts; it is not defined
from an answer expression.  The radius-indexed speed and EMF-density fields
return dimensionful quantities, with the index explicitly interpreted in
metres by the governing laws below.
-/
structure RotatingConductingDiskSetup where
  materialModel : DiskMaterialModel
  diskPlane : CoordinatePlane
  rotationAxis : CoordinateAxis
  angularVelocityDirection : AxialDirection
  magneticFieldDirection : AxialDirection
  angularSpeedIsConstant : Bool
  magneticFieldIsUniform : Bool
  magneticFieldIsConstant : Bool
  diskRadius : LengthQuantity
  angularSpeed : AngularSpeedMagnitude
  magneticFluxDensity : MagneticFluxDensityMagnitude
  magneticField : Electromagnetism.MagneticField 3
  tangentialSpeedAtRadiusMeter : ℝ → SpeedMagnitude
  motionalEmfDensityAtRadiusMeter : ℝ → MotionalEmfDensityMagnitude
  inducedEmfBetween : DiskContact → DiskContact → EmfMagnitude
  externalCurrentMagnitude : ElectricCurrentMagnitude
  externalLoadResistance : ResistanceMagnitude
  figure : RotatingDiskFigure

/-- The standard `z` component in Physlib's three-dimensional field vectors. -/
def zAxisIndex : Fin 3 := 2

/-! ## Scenario, primary-image evidence, and governing laws -/

/-- Qualitative assumptions stated in the problem prose. -/
structure MatchesRotatingConductingDiskDescription
    (setup : RotatingConductingDiskSetup) : Prop where
  diskIsConducting : setup.materialModel = .conducting
  diskLiesInXYPlane : setup.diskPlane = .xy
  rotationIsAboutZAxis : setup.rotationAxis = .z
  rotationPointsAlongPositiveZ :
    setup.angularVelocityDirection = .positiveZ
  magneticFieldPointsAlongPositiveZ :
    setup.magneticFieldDirection = .positiveZ
  rotationIsConstant : setup.angularSpeedIsConstant = true
  fieldIsUniform : setup.magneticFieldIsUniform = true
  fieldIsConstant : setup.magneticFieldIsConstant = true

/-!
Facts read from the primary image: all axes and symbolic labels, four axial
field arrows, the local radial element and tangential velocity, and the
two-brush external circuit.  No EMF value or answer formula occurs here.
-/
structure MatchesSuppliedRotatingDiskFigure
    (setup : RotatingConductingDiskSetup) : Prop where
  allCoordinateAxesShown :
    ∀ axis, setup.figure.coordinateAxisShown axis = true
  diskIsShown : setup.figure.diskShown = true
  diskIsRenderedCircular : setup.figure.diskRenderedCircular = true
  allQuantityLabelsShown :
    ∀ label, setup.figure.quantityLabelShown label = true
  printedQuantitySymbols :
    ∀ label, setup.figure.printedSymbol label = expectedPrintedSymbol label
  fourMagneticFieldArrows : setup.figure.magneticFieldArrowCount = 4
  angularSpeedArrowIsShown : setup.figure.rotationArrowShown = true
  radialElementIsHighlighted :
    setup.figure.highlightedRadialElementShown = true
  tangentialVelocityArrowIsShown : setup.figure.velocityArrowShown = true
  velocityIsTangential :
    setup.figure.velocityArrowTangentialToRadius = true
  bothContactBrushesAreShown :
    ∀ contact, setup.figure.brushShownAt contact = true
  twoBrushLabels : setup.figure.brushLabelCount = 2
  externalCircuitIsShown : setup.figure.externalCircuitShown = true
  resistorIsShown : setup.figure.resistorShown = true
  currentArrowIsShown : setup.figure.currentArrowShown = true
  externalCurrentRunsFromRimToCenter :
    setup.figure.currentArrowDirection = .rimThroughLoadToCenter

/-- Positivity conditions selecting the nondegenerate physical apparatus. -/
structure HasPhysicalRotatingDiskParameters
    (setup : RotatingConductingDiskSetup) : Prop where
  radiusPositive : 0 < lengthInMeters setup.diskRadius
  angularSpeedPositive :
    0 < angularSpeedInRadiansPerSecond setup.angularSpeed
  magneticFluxDensityPositive :
    0 < magneticFluxDensityInTeslas setup.magneticFluxDensity
  loadResistancePositive :
    0 < resistanceInOhms setup.externalLoadResistance
  displayedCurrentPositive :
    0 < currentInAmperes setup.externalCurrentMagnitude

/-!
The Physlib magnetic field is spatially uniform, time independent, and equal
to `B` in its `z` component.  This uses Physlib's spacetime-dependent
`Electromagnetism.MagneticField 3` rather than replacing the physical field by
a bare scalar.
-/
structure SatisfiesUniformAxialMagneticField
    (setup : RotatingConductingDiskSetup) : Prop where
  uniformConstantAxialField : ∀ time position component,
    setup.magneticField time position component =
      if component = zAxisIndex then
        magneticFluxDensityInTeslas setup.magneticFluxDensity
      else 0

/-!
Governing kinematic and motional-induction laws used by the displayed
derivation.

* Rigid rotation gives the local tangential speed `v(r) = ω r`.
* With `v` perpendicular to the axial field, the local motional-EMF density is
  `v(r) B`, exactly the coefficient of `dr` in the raster's
  `dℰ = v B dr`.
* The requested center-to-rim EMF is the radial line integral of that density.

These are local and integral laws.  They contain no evaluated `R² / 2` and no
displayed answer choice.
-/
structure SatisfiesRotatingDiskMotionalEmfLaws
    (setup : RotatingConductingDiskSetup) : Prop where
  rigidRotationTangentialSpeed : ∀ radiusMeters : ℝ,
    0 ≤ radiusMeters →
    radiusMeters ≤ lengthInMeters setup.diskRadius →
      speedInMetersPerSecond
          (setup.tangentialSpeedAtRadiusMeter radiusMeters) =
        angularSpeedInRadiansPerSecond setup.angularSpeed * radiusMeters
  localMotionalEmfDensity : ∀ radiusMeters : ℝ,
    0 ≤ radiusMeters →
    radiusMeters ≤ lengthInMeters setup.diskRadius →
      motionalEmfDensityInVoltsPerMeter
          (setup.motionalEmfDensityAtRadiusMeter radiusMeters) =
        speedInMetersPerSecond
            (setup.tangentialSpeedAtRadiusMeter radiusMeters) *
          magneticFluxDensityInTeslas setup.magneticFluxDensity
  centerToRimEmfIsRadialIntegral :
    emfInVolts (setup.inducedEmfBetween .center .rim) =
      ∫ radiusMeters in 0..lengthInMeters setup.diskRadius,
        motionalEmfDensityInVoltsPerMeter
          (setup.motionalEmfDensityAtRadiusMeter radiusMeters)

/-! ## Displayed choices and target conclusions -/

/-- Labels of the four answer choices printed with the problem. -/
inductive AnswerChoice where
  | A
  | B
  | C
  | D
  deriving DecidableEq, Fintype, Repr

/-!
The scalar expression printed beside each answer label, evaluated on coherent
SI readouts.  Choice B is transcribed faithfully even though its printed
expression has the wrong physical dimension for an EMF.
-/
def AnswerChoice.displayedExpressionInSI
    (choice : AnswerChoice) (setup : RotatingConductingDiskSetup) : ℝ :=
  let omega := angularSpeedInRadiansPerSecond setup.angularSpeed
  let field := magneticFluxDensityInTeslas setup.magneticFluxDensity
  let radius := lengthInMeters setup.diskRadius
  match choice with
  | .A => (1 / 4) * omega * field * radius ^ 2
  | .B => (1 / 2) * omega * field * radius
  | .C => (1 / 2) * omega * field * radius ^ 2
  | .D => omega * field * radius ^ 2

/-- The answer label recorded in the supplied dataset metadata. -/
def recordedDatasetAnswer : AnswerChoice := .C

/-!
Combining the two local laws gives the differential coefficient
`dℰ/dr = ω B r` on the disk.  This is an intermediate consequence, not a
premise containing the requested integrated answer.
-/
lemma motionalEmfDensity_eq_angularSpeed_mul_field_mul_radius
    (setup : RotatingConductingDiskSetup)
    (laws : SatisfiesRotatingDiskMotionalEmfLaws setup)
    (radiusMeters : ℝ)
    (radiusNonnegative : 0 ≤ radiusMeters)
    (radiusWithinDisk : radiusMeters ≤ lengthInMeters setup.diskRadius) :
    motionalEmfDensityInVoltsPerMeter
        (setup.motionalEmfDensityAtRadiusMeter radiusMeters) =
      angularSpeedInRadiansPerSecond setup.angularSpeed *
        magneticFluxDensityInTeslas setup.magneticFluxDensity *
        radiusMeters := by
  rw [laws.localMotionalEmfDensity radiusMeters radiusNonnegative radiusWithinDisk,
    laws.rigidRotationTangentialSpeed radiusMeters radiusNonnegative radiusWithinDisk]
  ac_rfl

/-!
Integrating `ω B r` from the center (`r = 0`) to the rim (`r = R`) gives

`ℰ_center→rim = (1 / 2) ω B R²`,

which is displayed answer C.  This is the Lean declaration corresponding to
`thm:physics:phyx_mini_0920:target`.
-/
theorem problem_phyx_mini_0920
    (setup : RotatingConductingDiskSetup)
    (_scenario : MatchesRotatingConductingDiskDescription setup)
    (_figure : MatchesSuppliedRotatingDiskFigure setup)
    (_physical : HasPhysicalRotatingDiskParameters setup)
    (_fieldLaw : SatisfiesUniformAxialMagneticField setup)
    (_motionalLaws : SatisfiesRotatingDiskMotionalEmfLaws setup) :
    emfInVolts (setup.inducedEmfBetween .center .rim) =
      (1 / 2) * angularSpeedInRadiansPerSecond setup.angularSpeed *
        magneticFluxDensityInTeslas setup.magneticFluxDensity *
        lengthInMeters setup.diskRadius ^ 2 := by
  rw [_motionalLaws.centerToRimEmfIsRadialIntegral]
  calc
    (∫ radiusMeters in 0..lengthInMeters setup.diskRadius,
        motionalEmfDensityInVoltsPerMeter
          (setup.motionalEmfDensityAtRadiusMeter radiusMeters)) =
        ∫ radiusMeters in 0..lengthInMeters setup.diskRadius,
          angularSpeedInRadiansPerSecond setup.angularSpeed *
            magneticFluxDensityInTeslas setup.magneticFluxDensity *
            radiusMeters := by
      apply intervalIntegral.integral_congr
      intro radiusMeters radiusInInterval
      have radiusInDisk :
          radiusMeters ∈ Set.Icc (0 : ℝ) (lengthInMeters setup.diskRadius) := by
        simpa [Set.uIcc_of_le (le_of_lt _physical.radiusPositive)] using
          radiusInInterval
      exact motionalEmfDensity_eq_angularSpeed_mul_field_mul_radius
        setup _motionalLaws radiusMeters radiusInDisk.1 radiusInDisk.2
    _ = (1 / 2) * angularSpeedInRadiansPerSecond setup.angularSpeed *
          magneticFluxDensityInTeslas setup.magneticFluxDensity *
          lengthInMeters setup.diskRadius ^ 2 := by
      rw [show (fun radiusMeters : ℝ =>
          angularSpeedInRadiansPerSecond setup.angularSpeed *
            magneticFluxDensityInTeslas setup.magneticFluxDensity *
            radiusMeters) =
          fun radiusMeters =>
            (angularSpeedInRadiansPerSecond setup.angularSpeed *
              magneticFluxDensityInTeslas setup.magneticFluxDensity) *
              radiusMeters ^ 1 by
        funext radiusMeters
        simp only [pow_one]]
      rw [intervalIntegral.integral_const_mul, integral_pow]
      ring

end PhyXMiniProblems.ProblemPhyXMini0920
