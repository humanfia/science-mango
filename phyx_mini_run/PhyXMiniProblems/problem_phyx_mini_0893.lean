import Mathlib
import Physlib.Electromagnetism.Basic
import Physlib.Units.WithDim.Basic

/- USER: The assigned Lean file did not exist when this autoformalization task began. -/

noncomputable section

namespace PhyXMiniProblems.ProblemPhyXMini0893

open Dimension
open scoped BigOperators

/-!
# Net electrostatic force at a vertex of an equilateral triangle

The primary image shows three positive point charges at the vertices of an
equilateral triangle.  The top charge is `1.0 nC`, each lower charge is
`2.0 nC`, every side is `1.0 cm`, and the two displayed base angles are
`60 degrees`.  The requested quantity is the magnitude of the vector sum of
the two forces exerted on the top charge.

Physical magnitudes below are unit-independent Physlib `Dimensionful`
quantities.  The planar force vectors are dimensionful too; ordinary real
vectors occur only at explicit coherent-unit readout boundaries.

Assumption/target split:

* governing laws: Coulomb's repulsive point-charge law, vector
  superposition, and the norm relation between the net vector and magnitude;
* previous-part results: none;
* figure/data readouts: three positive charge markers, the `1.0 nC` and two
  `2.0 nC` labels, three `1.0 cm` sides, the two visible `60 degree` arcs,
  equilateral direction geometry, and the textbook vacuum Coulomb constant;
* current target: the net-force magnitude rounds to `3.1 × 10⁻⁴ N` and is
  uniquely closest to displayed answer C.

No setup field, premise field, or helper definition assigns the requested
net force or its magnitude the answer value.
-/

/-! ## Dimensionful physical quantities and unit readouts -/

/-- The physical dimension `M L T⁻²` of force. -/
def forceDimension : Dimension :=
  M𝓭 * L𝓭 * T𝓭⁻¹ * T𝓭⁻¹

/-- The physical dimension `M L³ T⁻² C⁻²` of Coulomb's constant. -/
def coulombConstantDimension : Dimension :=
  forceDimension * L𝓭 * L𝓭 * C𝓭⁻¹ * C𝓭⁻¹

/-- A two-dimensional real vector in the plane of the figure. -/
abbrev PlanarVector : Type :=
  EuclideanSpace ℝ (Fin 2)

/-- A nonnegative, unit-independent physical length. -/
abbrev LengthQuantity : Type :=
  Dimensionful (WithDim L𝓭 NNReal)

/-- A nonnegative, unit-independent electric-charge magnitude. -/
abbrev ChargeMagnitudeQuantity : Type :=
  Dimensionful (WithDim C𝓭 NNReal)

/-- A nonnegative, unit-independent magnitude of force. -/
abbrev ForceMagnitudeQuantity : Type :=
  Dimensionful (WithDim forceDimension NNReal)

/-- A unit-independent planar force vector. -/
abbrev ForceVectorQuantity : Type :=
  Dimensionful (WithDim forceDimension PlanarVector)

/-- A nonnegative, dimensionful value of Coulomb's constant. -/
abbrev CoulombConstantQuantity : Type :=
  Dimensionful (WithDim coulombConstantDimension NNReal)

/-- Read a physical length in the coherent length unit selected by `units`. -/
def lengthReadout (units : UnitChoices) (length : LengthQuantity) : ℝ :=
  ((length units).val : ℝ)

/-- Read a charge magnitude in the coherent charge unit selected by `units`. -/
def chargeMagnitudeReadout
    (units : UnitChoices) (charge : ChargeMagnitudeQuantity) : ℝ :=
  ((charge units).val : ℝ)

/-- Read a force magnitude in the coherent force unit selected by `units`. -/
def forceMagnitudeReadout
    (units : UnitChoices) (force : ForceMagnitudeQuantity) : ℝ :=
  ((force units).val : ℝ)

/-- Read a planar force vector in the coherent force unit selected by `units`. -/
def forceVectorReadout
    (units : UnitChoices) (force : ForceVectorQuantity) : PlanarVector :=
  (force units).val

/-- Read Coulomb's constant in the coherent unit system selected by `units`. -/
def coulombConstantReadout
    (units : UnitChoices) (constant : CoulombConstantQuantity) : ℝ :=
  ((constant units).val : ℝ)

/-- Read a physical length in coherent-SI metres. -/
def lengthInMeters (length : LengthQuantity) : ℝ :=
  lengthReadout UnitChoices.SI length

/-- Read a physical length in centimetres. -/
def lengthInCentimeters (length : LengthQuantity) : ℝ :=
  100 * lengthInMeters length

/-- Read a charge magnitude in coherent-SI coulombs. -/
def chargeMagnitudeInCoulombs (charge : ChargeMagnitudeQuantity) : ℝ :=
  chargeMagnitudeReadout UnitChoices.SI charge

/-- Read a charge magnitude in nanocoulombs. -/
def chargeMagnitudeInNanocoulombs (charge : ChargeMagnitudeQuantity) : ℝ :=
  10 ^ 9 * chargeMagnitudeInCoulombs charge

/-- Read a force magnitude in coherent-SI newtons. -/
def forceMagnitudeInNewtons (force : ForceMagnitudeQuantity) : ℝ :=
  forceMagnitudeReadout UnitChoices.SI force

/-- Read a planar force vector in coherent-SI newtons. -/
def forceVectorInNewtons (force : ForceVectorQuantity) : PlanarVector :=
  forceVectorReadout UnitChoices.SI force

/-- Read Coulomb's constant in coherent SI `N m² / C²`. -/
def coulombConstantInNewtonMetersSquaredPerCoulombSquared
    (constant : CoulombConstantQuantity) : ℝ :=
  coulombConstantReadout UnitChoices.SI constant

/-! ## Vertex, edge, and figure labels -/

/-- The three labelled vertices of the triangular charge configuration. -/
inductive TriangleVertex where
  | top
  | bottomLeft
  | bottomRight
  deriving DecidableEq, Fintype, Repr

/-- The three sides of the triangle, named by their placement in the image. -/
inductive TriangleEdge where
  | leftSloping
  | rightSloping
  | horizontalBase
  deriving DecidableEq, Fintype, Repr

/-- The two lower charges that exert force on the requested top charge. -/
inductive LowerCharge where
  | bottomLeft
  | bottomRight
  deriving DecidableEq, Fintype, Repr

/-- Regard a lower-charge label as its corresponding triangle vertex. -/
def LowerCharge.vertex : LowerCharge → TriangleVertex
  | .bottomLeft => .bottomLeft
  | .bottomRight => .bottomRight

/-- The side separating a lower source charge from the top charge. -/
def LowerCharge.edgeToTop : LowerCharge → TriangleEdge
  | .bottomLeft => .leftSloping
  | .bottomRight => .rightSloping

/-- Sign of an electric charge in the physical model. -/
inductive ChargeSign where
  | positive
  | negative
  deriving DecidableEq, Repr

/-- Electrostatic environment used by the ideal point-charge model. -/
inductive ElectrostaticEnvironment where
  | vacuum
  | other
  deriving DecidableEq, Repr

/-- Coordinate convention for components of the dimensionless directions. -/
inductive CoordinateConvention where
  | horizontalRightVerticalUp
  deriving DecidableEq, Repr

/-!
Literal presentation data from `893.png`.  Numerical fields are explicitly
unit-labelled scalar readouts from the raster and do not replace the physical
quantities in `EquilateralThreeChargeSetup`.
-/
structure ThreeChargeTriangleFigure where
  chargeMarkerShown : TriangleVertex → Bool
  plusGlyphShown : TriangleVertex → Bool
  printedChargeNanocoulombs : TriangleVertex → ℝ
  dashedEdgeShown : TriangleEdge → Bool
  printedSideLengthCentimeters : TriangleEdge → ℝ
  angleArcShown : TriangleVertex → Bool
  printedInteriorAngleDegrees : TriangleVertex → Option ℝ

/-!
Independent physical data for the configuration.  The individual force
vectors, net force vector, and net-force magnitude are fields constrained by
the laws below; no field is assigned a displayed answer value.
-/
structure EquilateralThreeChargeSetup where
  environment : ElectrostaticEnvironment
  coordinateConvention : CoordinateConvention
  chargeSign : TriangleVertex → ChargeSign
  chargeMagnitude : TriangleVertex → ChargeMagnitudeQuantity
  edgeLength : TriangleEdge → LengthQuantity
  interiorAngleDegrees : TriangleVertex → ℝ
  electromagneticSystem : Electromagnetism.EMSystem
  coulombConstant : CoulombConstantQuantity
  unitDirectionFromLowerChargeToTop : LowerCharge → PlanarVector
  forceOnTopFromLowerCharge : LowerCharge → ForceVectorQuantity
  netForceOnTop : ForceVectorQuantity
  netForceMagnitudeOnTop : ForceMagnitudeQuantity
  figure : ThreeChargeTriangleFigure

/-! ## Assumptions: image data, geometry, and governing physical laws -/

/-- Qualitative point-charge and sign assumptions stated by the problem. -/
structure MatchesThreePositivePointChargeScenario
    (setup : EquilateralThreeChargeSetup) : Prop where
  chargesAreInVacuum : setup.environment = .vacuum
  componentsUseFigureOrientation :
    setup.coordinateConvention = .horizontalRightVerticalUp
  everyDisplayedChargeIsPositive : ∀ vertex,
    setup.chargeSign vertex = .positive

/-!
All label, glyph, and geometry evidence read from the primary raster.  The
top angle is not explicitly drawn, so its raster fields are `false` and
`none`; its physical `60 degree` value follows from equilateral geometry.
-/
structure MatchesSuppliedThreeChargeTriangleFigure
    (setup : EquilateralThreeChargeSetup) : Prop where
  everyChargeMarkerShown : ∀ vertex,
    setup.figure.chargeMarkerShown vertex = true
  everyPlusGlyphShown : ∀ vertex,
    setup.figure.plusGlyphShown vertex = true
  printedTopCharge :
    setup.figure.printedChargeNanocoulombs .top = 1
  printedBottomLeftCharge :
    setup.figure.printedChargeNanocoulombs .bottomLeft = 2
  printedBottomRightCharge :
    setup.figure.printedChargeNanocoulombs .bottomRight = 2
  everyDashedSideShown : ∀ edge,
    setup.figure.dashedEdgeShown edge = true
  everyPrintedSideLengthIsOneCentimeter : ∀ edge,
    setup.figure.printedSideLengthCentimeters edge = 1
  noTopAngleArc : setup.figure.angleArcShown .top = false
  bottomLeftAngleArcShown :
    setup.figure.angleArcShown .bottomLeft = true
  bottomRightAngleArcShown :
    setup.figure.angleArcShown .bottomRight = true
  noPrintedTopAngle :
    setup.figure.printedInteriorAngleDegrees .top = none
  printedBottomLeftAngle :
    setup.figure.printedInteriorAngleDegrees .bottomLeft = some 60
  printedBottomRightAngle :
    setup.figure.printedInteriorAngleDegrees .bottomRight = some 60
  chargeLabelsCalibratePhysicalCharges : ∀ vertex,
    chargeMagnitudeInNanocoulombs (setup.chargeMagnitude vertex) =
      setup.figure.printedChargeNanocoulombs vertex
  sideLabelsCalibratePhysicalLengths : ∀ edge,
    lengthInCentimeters (setup.edgeLength edge) =
      setup.figure.printedSideLengthCentimeters edge
  displayedAnglesCalibrateGeometry : ∀ vertex degrees,
    setup.figure.printedInteriorAngleDegrees vertex = some degrees →
      setup.interiorAngleDegrees vertex = degrees

/-!
The equilateral geometry and the two unit directions from the lower vertices
toward the top vertex.  Component zero points right and component one points
up.  These are figure-derived geometric relations, not force magnitudes.
-/
structure UsesEquilateralTriangleGeometry
    (setup : EquilateralThreeChargeSetup) : Prop where
  everyInteriorAngleIsSixtyDegrees : ∀ vertex,
    setup.interiorAngleDegrees vertex = 60
  everySideHasSameLength : ∀ edge,
    lengthInMeters (setup.edgeLength edge) =
      lengthInMeters (setup.edgeLength .horizontalBase)
  directionFromBottomLeft :
    setup.unitDirectionFromLowerChargeToTop .bottomLeft =
      ![(1 / 2 : ℝ), Real.sqrt 3 / 2]
  directionFromBottomRight :
    setup.unitDirectionFromLowerChargeToTop .bottomRight =
      ![-(1 / 2 : ℝ), Real.sqrt 3 / 2]
  eachDirectionHasUnitNorm : ∀ source,
    ‖setup.unitDirectionFromLowerChargeToTop source‖ = 1

/-- Positivity and nondegeneracy conditions for the physical parameters. -/
structure HasPhysicalThreeChargeParameters
    (setup : EquilateralThreeChargeSetup) : Prop where
  everyChargeMagnitudePositive : ∀ vertex,
    0 < chargeMagnitudeInCoulombs (setup.chargeMagnitude vertex)
  everyEdgeLengthPositive : ∀ edge,
    0 < lengthInMeters (setup.edgeLength edge)
  coulombConstantPositive :
    0 < coulombConstantInNewtonMetersSquaredPerCoulombSquared
      setup.coulombConstant

/-!
The unit-independent Coulomb constant is connected to Physlib's
`Electromagnetism.EMSystem.coulombConstant`.  The rounded value is the
standard textbook calibration and contains no requested force magnitude.
-/
structure UsesTextbookVacuumCoulombConstant
    (setup : EquilateralThreeChargeSetup) : Prop where
  agreesWithPhyslibElectromagneticSystem :
    coulombConstantInNewtonMetersSquaredPerCoulombSquared
        setup.coulombConstant =
      setup.electromagneticSystem.coulombConstant
  textbookCoulombConstantValue :
    coulombConstantInNewtonMetersSquaredPerCoulombSquared
        setup.coulombConstant =
      (899 : ℝ) / 100 * 10 ^ 9

/-!
Coulomb's repulsive point-charge law in vector form, force superposition, and
the defining norm relation between the net vector and its magnitude.  These
equations contain no numerical value of the requested net force.
-/
structure SatisfiesCoulombForceLawAndSuperposition
    (setup : EquilateralThreeChargeSetup) : Prop where
  pairwiseCoulombForce : ∀ units source,
    forceVectorReadout units (setup.forceOnTopFromLowerCharge source) =
      (coulombConstantReadout units setup.coulombConstant *
          chargeMagnitudeReadout units (setup.chargeMagnitude .top) *
          chargeMagnitudeReadout units
            (setup.chargeMagnitude source.vertex) /
          lengthReadout units (setup.edgeLength source.edgeToTop) ^ 2) •
        setup.unitDirectionFromLowerChargeToTop source
  vectorSuperposition : ∀ units,
    forceVectorReadout units setup.netForceOnTop =
      ∑ source : LowerCharge,
        forceVectorReadout units (setup.forceOnTopFromLowerCharge source)
  netMagnitudeIsVectorNorm : ∀ units,
    forceMagnitudeReadout units setup.netForceMagnitudeOnTop =
      ‖forceVectorReadout units setup.netForceOnTop‖

/-! ## Requested net-force magnitude and displayed answer choices -/

/-- The requested magnitude of the net force on the top charge, in newtons. -/
def netForceMagnitudeInNewtons (setup : EquilateralThreeChargeSetup) : ℝ :=
  forceMagnitudeInNewtons setup.netForceMagnitudeOnTop

/-- The four answer labels printed with the problem. -/
inductive AnswerChoice where
  | A
  | B
  | C
  | D
  deriving DecidableEq, Fintype, Repr

/-- The force magnitude printed beside an answer choice, in newtons. -/
def AnswerChoice.displayedForceInNewtons : AnswerChoice → ℝ
  | .A => 125 / 100000
  | .B => 135 / 100000
  | .C => 31 / 100000
  | .D => 133 / 100000

/-- The answer label recorded by the source dataset. -/
def recordedDatasetAnswer : AnswerChoice := .C

/-- A physical value rounds to `displayed` at the stated positive resolution. -/
def RoundsToNearestResolution
    (value displayed resolution : ℝ) : Prop :=
  0 < resolution ∧ |value - displayed| ≤ resolution / 2

/-- A choice is uniquely closest to the calculated physical force magnitude. -/
def IsUniqueClosestDisplayedAnswer
    (setup : EquilateralThreeChargeSetup) (choice : AnswerChoice) : Prop :=
  ∀ other, other ≠ choice →
    |netForceMagnitudeInNewtons setup - choice.displayedForceInNewtons| <
      |netForceMagnitudeInNewtons setup - other.displayedForceInNewtons|

/-!
The two equal pairwise forces have opposing horizontal components and equal
upward components.  Coulomb's law and the equilateral geometry therefore put
the net magnitude between `3.05 × 10⁻⁴ N` and `3.15 × 10⁻⁴ N`.
-/
lemma netForceMagnitude_roundingBounds
    (setup : EquilateralThreeChargeSetup)
    (_scenario : MatchesThreePositivePointChargeScenario setup)
    (_figure : MatchesSuppliedThreeChargeTriangleFigure setup)
    (_geometry : UsesEquilateralTriangleGeometry setup)
    (_physical : HasPhysicalThreeChargeParameters setup)
    (_constant : UsesTextbookVacuumCoulombConstant setup)
    (_coulomb : SatisfiesCoulombForceLawAndSuperposition setup) :
    (305 : ℝ) / 1000000 ≤ netForceMagnitudeInNewtons setup ∧
      netForceMagnitudeInNewtons setup < (315 : ℝ) / 1000000 := by
  have hTopCharge :
      chargeMagnitudeInCoulombs (setup.chargeMagnitude .top) =
        (1 : ℝ) / 10 ^ 9 := by
    have h :=
      _figure.chargeLabelsCalibratePhysicalCharges .top
    rw [_figure.printedTopCharge] at h
    norm_num [chargeMagnitudeInNanocoulombs] at h ⊢
    linarith only [h]
  have hBottomLeftCharge :
      chargeMagnitudeInCoulombs (setup.chargeMagnitude .bottomLeft) =
        (2 : ℝ) / 10 ^ 9 := by
    have h :=
      _figure.chargeLabelsCalibratePhysicalCharges .bottomLeft
    rw [_figure.printedBottomLeftCharge] at h
    norm_num [chargeMagnitudeInNanocoulombs] at h ⊢
    linarith only [h]
  have hBottomRightCharge :
      chargeMagnitudeInCoulombs (setup.chargeMagnitude .bottomRight) =
        (2 : ℝ) / 10 ^ 9 := by
    have h :=
      _figure.chargeLabelsCalibratePhysicalCharges .bottomRight
    rw [_figure.printedBottomRightCharge] at h
    norm_num [chargeMagnitudeInNanocoulombs] at h ⊢
    linarith only [h]
  have hLeftLength :
      lengthInMeters (setup.edgeLength .leftSloping) =
        (1 : ℝ) / 100 := by
    have h :=
      _figure.sideLabelsCalibratePhysicalLengths .leftSloping
    rw [_figure.everyPrintedSideLengthIsOneCentimeter] at h
    norm_num [lengthInCentimeters] at h ⊢
    linarith only [h]
  have hRightLength :
      lengthInMeters (setup.edgeLength .rightSloping) =
        (1 : ℝ) / 100 := by
    have h :=
      _figure.sideLabelsCalibratePhysicalLengths .rightSloping
    rw [_figure.everyPrintedSideLengthIsOneCentimeter] at h
    norm_num [lengthInCentimeters] at h ⊢
    linarith only [h]
  have hConstant :
      coulombConstantInNewtonMetersSquaredPerCoulombSquared
          setup.coulombConstant =
        (899 : ℝ) / 100 * 10 ^ 9 :=
    _constant.textbookCoulombConstantValue
  have hLeftDirection :
      setup.unitDirectionFromLowerChargeToTop .bottomLeft =
        (!₂[(1 / 2 : ℝ), Real.sqrt 3 / 2] : PlanarVector) := by
    apply PiLp.ext
    intro i
    exact congrFun _geometry.directionFromBottomLeft i
  have hRightDirection :
      setup.unitDirectionFromLowerChargeToTop .bottomRight =
        (!₂[-(1 / 2 : ℝ), Real.sqrt 3 / 2] : PlanarVector) := by
    apply PiLp.ext
    intro i
    exact congrFun _geometry.directionFromBottomRight i
  have hLeftForce :
      forceVectorInNewtons
          (setup.forceOnTopFromLowerCharge .bottomLeft) =
        (899 / 5000000 : ℝ) •
          (!₂[(1 / 2 : ℝ), Real.sqrt 3 / 2] : PlanarVector) := by
    have h :=
      _coulomb.pairwiseCoulombForce UnitChoices.SI .bottomLeft
    change
      forceVectorInNewtons
          (setup.forceOnTopFromLowerCharge .bottomLeft) =
        (coulombConstantInNewtonMetersSquaredPerCoulombSquared
              setup.coulombConstant *
            chargeMagnitudeInCoulombs (setup.chargeMagnitude .top) *
            chargeMagnitudeInCoulombs
              (setup.chargeMagnitude .bottomLeft) /
            lengthInMeters (setup.edgeLength .leftSloping) ^ 2) •
          setup.unitDirectionFromLowerChargeToTop .bottomLeft at h
    rw [hConstant, hTopCharge, hBottomLeftCharge, hLeftLength,
      hLeftDirection] at h
    norm_num at h ⊢
    exact h
  have hRightForce :
      forceVectorInNewtons
          (setup.forceOnTopFromLowerCharge .bottomRight) =
        (899 / 5000000 : ℝ) •
          (!₂[-(1 / 2 : ℝ), Real.sqrt 3 / 2] : PlanarVector) := by
    have h :=
      _coulomb.pairwiseCoulombForce UnitChoices.SI .bottomRight
    change
      forceVectorInNewtons
          (setup.forceOnTopFromLowerCharge .bottomRight) =
        (coulombConstantInNewtonMetersSquaredPerCoulombSquared
              setup.coulombConstant *
            chargeMagnitudeInCoulombs (setup.chargeMagnitude .top) *
            chargeMagnitudeInCoulombs
              (setup.chargeMagnitude .bottomRight) /
            lengthInMeters (setup.edgeLength .rightSloping) ^ 2) •
          setup.unitDirectionFromLowerChargeToTop .bottomRight at h
    rw [hConstant, hTopCharge, hBottomRightCharge, hRightLength,
      hRightDirection] at h
    norm_num at h ⊢
    exact h
  have hSourceSum (f : LowerCharge → PlanarVector) :
      ∑ source : LowerCharge, f source =
        f .bottomLeft + f .bottomRight := by
    rw [show (Finset.univ : Finset LowerCharge) =
      {.bottomLeft, .bottomRight} by decide]
    simp
  have hNet :
      forceVectorInNewtons setup.netForceOnTop =
        (!₂[(0 : ℝ), (899 / 5000000 : ℝ) * Real.sqrt 3] :
          PlanarVector) := by
    have h := _coulomb.vectorSuperposition UnitChoices.SI
    change
      forceVectorInNewtons setup.netForceOnTop =
        ∑ source : LowerCharge,
          forceVectorInNewtons (setup.forceOnTopFromLowerCharge source) at h
    rw [hSourceSum] at h
    rw [hLeftForce, hRightForce] at h
    rw [h]
    ext i
    fin_cases i <;> simp
    all_goals ring
  have hMagnitude :
      netForceMagnitudeInNewtons setup =
        ‖(!₂[(0 : ℝ), (899 / 5000000 : ℝ) * Real.sqrt 3] :
          PlanarVector)‖ := by
    have h := _coulomb.netMagnitudeIsVectorNorm UnitChoices.SI
    change
      netForceMagnitudeInNewtons setup =
        ‖forceVectorInNewtons setup.netForceOnTop‖ at h
    rw [hNet] at h
    exact h
  have hMagnitudeSq :
      netForceMagnitudeInNewtons setup ^ 2 =
        (899 / 5000000 : ℝ) ^ 2 * 3 := by
    have hSqrtSq : Real.sqrt (3 : ℝ) ^ 2 = 3 :=
      Real.sq_sqrt (by norm_num)
    have hProductNonnegative :
        0 ≤ (899 / 5000000 : ℝ) * Real.sqrt 3 :=
      mul_nonneg (by norm_num) (Real.sqrt_nonneg _)
    rw [hMagnitude, EuclideanSpace.norm_sq_eq]
    rw [Fin.sum_univ_two]
    change
      ‖(0 : ℝ)‖ ^ 2 +
          ‖(899 / 5000000 : ℝ) * Real.sqrt 3‖ ^ 2 =
        (899 / 5000000 : ℝ) ^ 2 * 3
    rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_zero,
      abs_of_nonneg hProductNonnegative]
    calc
      (0 : ℝ) ^ 2 +
          ((899 / 5000000 : ℝ) * Real.sqrt 3) ^ 2 =
        (899 / 5000000 : ℝ) ^ 2 * Real.sqrt 3 ^ 2 := by ring
      _ = (899 / 5000000 : ℝ) ^ 2 * 3 := by rw [hSqrtSq]
  have hMagnitudeNonnegative :
      0 ≤ netForceMagnitudeInNewtons setup := by
    rw [hMagnitude]
    exact norm_nonneg _
  constructor
  · apply
      (sq_le_sq₀ (show (0 : ℝ) ≤ 305 / 1000000 by norm_num)
        hMagnitudeNonnegative).mp
    rw [hMagnitudeSq]
    norm_num
  · apply
      (sq_lt_sq₀ hMagnitudeNonnegative
        (show (0 : ℝ) ≤ 315 / 1000000 by norm_num)).mp
    rw [hMagnitudeSq]
    norm_num

/-!
Thus the requested force magnitude rounds to `3.1 × 10⁻⁴ N` and is uniquely
closest to recorded answer C.

This declaration formalizes `thm:physics:phyx_mini_0893:target`.  No premise,
setup field, governing-law field, or helper definition assigns the requested
net force its answer value.
-/
theorem problem_phyx_mini_0893
    (setup : EquilateralThreeChargeSetup)
    (_scenario : MatchesThreePositivePointChargeScenario setup)
    (_figure : MatchesSuppliedThreeChargeTriangleFigure setup)
    (_geometry : UsesEquilateralTriangleGeometry setup)
    (_physical : HasPhysicalThreeChargeParameters setup)
    (_constant : UsesTextbookVacuumCoulombConstant setup)
    (_coulomb : SatisfiesCoulombForceLawAndSuperposition setup) :
    (305 : ℝ) / 1000000 ≤ netForceMagnitudeInNewtons setup ∧
      netForceMagnitudeInNewtons setup < (315 : ℝ) / 1000000 ∧
      RoundsToNearestResolution
        (netForceMagnitudeInNewtons setup)
        recordedDatasetAnswer.displayedForceInNewtons
        (1 / 100000) ∧
      IsUniqueClosestDisplayedAnswer setup recordedDatasetAnswer := by
  have hBounds :=
    netForceMagnitude_roundingBounds setup _scenario _figure _geometry
      _physical _constant _coulomb
  rcases hBounds with ⟨hLower, hUpper⟩
  refine ⟨hLower, hUpper, ?_, ?_⟩
  · change
      0 < (1 / 100000 : ℝ) ∧
        |netForceMagnitudeInNewtons setup - 31 / 100000| ≤
          (1 / 100000 : ℝ) / 2
    constructor
    · norm_num
    · rw [abs_le]
      constructor <;> linarith only [hLower, hUpper]
  · intro other hOther
    fin_cases other
    · change
        |netForceMagnitudeInNewtons setup - 31 / 100000| <
          |netForceMagnitudeInNewtons setup - 125 / 100000|
      have hOtherNonpositive :
          netForceMagnitudeInNewtons setup - 125 / 100000 ≤ 0 := by
        linarith only [hUpper]
      rw [abs_of_nonpos hOtherNonpositive, abs_lt]
      constructor <;> linarith only [hLower, hUpper]
    · change
        |netForceMagnitudeInNewtons setup - 31 / 100000| <
          |netForceMagnitudeInNewtons setup - 135 / 100000|
      have hOtherNonpositive :
          netForceMagnitudeInNewtons setup - 135 / 100000 ≤ 0 := by
        linarith only [hUpper]
      rw [abs_of_nonpos hOtherNonpositive, abs_lt]
      constructor <;> linarith only [hLower, hUpper]
    · exact (hOther rfl).elim
    · change
        |netForceMagnitudeInNewtons setup - 31 / 100000| <
          |netForceMagnitudeInNewtons setup - 133 / 100000|
      have hOtherNonpositive :
          netForceMagnitudeInNewtons setup - 133 / 100000 ≤ 0 := by
        linarith only [hUpper]
      rw [abs_of_nonpos hOtherNonpositive, abs_lt]
      constructor <;> linarith only [hLower, hUpper]

end PhyXMiniProblems.ProblemPhyXMini0893
