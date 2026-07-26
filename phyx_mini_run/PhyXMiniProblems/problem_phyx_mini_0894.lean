import Mathlib
import Physlib.Electromagnetism.Basic
import Physlib.Units.WithDim.Basic

noncomputable section

namespace PhyXMiniProblems.ProblemPhyXMini0894

open Dimension

/-!
# Net electric force on the top charge of an equilateral triangle

The primary image places a positive `1.0 nC` point charge at the top of an
equilateral triangle, a positive `2.0 nC` charge at the bottom-left vertex,
and a negative `-2.0 nC` charge at the bottom-right vertex.  Every side is
labelled `1.0 cm`; the two lower angles are labelled `60 degrees`.

Lengths, signed charges, positions, and force vectors below are
unit-independent Physlib quantities.  Real scalars and planar vectors occur
only as explicitly named coherent-SI or figure-label readouts.

Assumption/target split:

* governing laws: the vector point-charge form of Coulomb's law and vector
  superposition of the two forces acting on the top charge;
* previous-part results: none;
* figure/data readouts: the three signed nanocoulomb labels, red/teal charge
  colours and sign glyphs, the three `1.0 cm` side labels, the two `60 degree`
  labels, dashed triangle edges, an equilateral coordinate realization, and
  the rounded textbook value of Coulomb's constant;
* current target conclusions: the force vector on the top charge is
  `(1.8 * 10^-4, 0) N`, hence its magnitude is `1.8 * 10^-4 N` and the
  recorded answer is choice C.

No target force value or answer label occurs in a setup field or theorem
premise.
-/

/-! ## Dimensionful quantities and coherent-SI readouts -/

/-- A planar scalar readout, used for metre coordinates and force components. -/
abbrev PlanarVector : Type := EuclideanSpace ℝ (Fin 2)

/-- The physical dimension of force, `M L T^-2`. -/
def forceDimension : Dimension := M𝓭 * L𝓭 * T𝓭⁻¹ * T𝓭⁻¹

/-- A nonnegative, unit-independent physical length. -/
abbrev LengthQuantity : Type := Dimensionful (WithDim L𝓭 NNReal)

/-- A signed, unit-independent physical electric charge. -/
abbrev SignedChargeQuantity : Type := Dimensionful (WithDim C𝓭 ℝ)

/-- A unit-independent planar position carrying the dimension of length. -/
abbrev PlanarPositionQuantity : Type :=
  Dimensionful (WithDim L𝓭 PlanarVector)

/-- A unit-independent planar physical force vector. -/
abbrev PlanarForceQuantity : Type :=
  Dimensionful (WithDim forceDimension PlanarVector)

/-- Coherent-SI metre readout of a physical length. -/
def lengthInMeters (length : LengthQuantity) : ℝ :=
  ((length UnitChoices.SI).val : ℝ)

/-- Centimetre readout used by the three printed side labels. -/
def lengthInCentimeters (length : LengthQuantity) : ℝ :=
  100 * lengthInMeters length

/-- Coherent-SI coulomb readout of a signed electric charge. -/
def chargeInCoulombs (charge : SignedChargeQuantity) : ℝ :=
  (charge UnitChoices.SI).val

/-- Nanocoulomb readout used by the three printed charge labels. -/
def chargeInNanocoulombs (charge : SignedChargeQuantity) : ℝ :=
  (10 : ℝ) ^ 9 * chargeInCoulombs charge

/-- Coherent-SI planar metre readout of a physical position. -/
def positionInMeters (position : PlanarPositionQuantity) : PlanarVector :=
  (position UnitChoices.SI).val

/-- Coherent-SI planar newton readout of a physical force vector. -/
def forceVectorInNewtons (force : PlanarForceQuantity) : PlanarVector :=
  (force UnitChoices.SI).val

/-- Magnitude in newtons of a dimensionful planar force vector. -/
def forceMagnitudeInNewtons (force : PlanarForceQuantity) : ℝ :=
  ‖forceVectorInNewtons force‖

/-! ## Primary-image vocabulary -/

/-- The three charge sites in image `894.png`. -/
inductive TriangleVertex where
  | top
  | bottomLeft
  | bottomRight
  deriving DecidableEq, Fintype, Repr

/-- The two lower charges that exert force on the top charge. -/
inductive LowerSource where
  | bottomLeft
  | bottomRight
  deriving DecidableEq, Fintype, Repr

/-- Vertex occupied by each source charge acting on the top charge. -/
def LowerSource.vertex : LowerSource → TriangleVertex
  | .bottomLeft => .bottomLeft
  | .bottomRight => .bottomRight

/-- The three dashed sides of the triangular diagram. -/
inductive TriangleEdge where
  | left
  | right
  | base
  deriving DecidableEq, Fintype, Repr

/-- Ordered endpoints of each triangle side. -/
def TriangleEdge.endpoints : TriangleEdge → TriangleVertex × TriangleVertex
  | .left => (.bottomLeft, .top)
  | .right => (.top, .bottomRight)
  | .base => (.bottomLeft, .bottomRight)

/-- The two lower vertices carrying explicit `60 degree` arcs in the bitmap. -/
inductive PrintedAngleSite where
  | bottomLeft
  | bottomRight
  deriving DecidableEq, Fintype, Repr

/-- Fill colours used by the charge circles in the primary image. -/
inductive ChargeCircleColor where
  | lightRed
  | lightTeal
  deriving DecidableEq, Repr

/-- Sign glyph drawn inside a charge circle. -/
inductive ChargeSignGlyph where
  | plus
  | minus
  deriving DecidableEq, Repr

/-- Expected signed nanocoulomb label at each figure vertex. -/
def expectedChargeInNanocoulombs : TriangleVertex → ℝ
  | .top => 1
  | .bottomLeft => 2
  | .bottomRight => -2

/-- Expected charge-circle colour at each figure vertex. -/
def expectedChargeColor : TriangleVertex → ChargeCircleColor
  | .top => .lightRed
  | .bottomLeft => .lightRed
  | .bottomRight => .lightTeal

/-- Expected sign glyph at each figure vertex. -/
def expectedChargeGlyph : TriangleVertex → ChargeSignGlyph
  | .top => .plus
  | .bottomLeft => .plus
  | .bottomRight => .minus

/-!
Literal presentation data transcribed from the supplied raster.  It contains
no force magnitude or answer-choice field.
-/
structure EquilateralChargeFigure where
  chargeCircleShown : TriangleVertex → Bool
  chargeColor : TriangleVertex → ChargeCircleColor
  chargeGlyph : TriangleVertex → ChargeSignGlyph
  printedChargeNanocoulombs : TriangleVertex → ℝ
  dashedEdgeShown : TriangleEdge → Bool
  printedSideLengthCentimeters : TriangleEdge → ℝ
  printedAngleDegrees : PrintedAngleSite → ℝ

/-!
Independent physical quantities in the electrostatic setup.  The net force
and both pair forces are stored as independent dimensionful vectors; none is
defined from a displayed answer.
-/
structure EquilateralPointChargeSetup where
  figure : EquilateralChargeFigure
  sideLength : LengthQuantity
  position : TriangleVertex → PlanarPositionQuantity
  charge : TriangleVertex → SignedChargeQuantity
  electromagneticSystem : Electromagnetism.EMSystem
  forceOnTopFrom : LowerSource → PlanarForceQuantity
  netForceOnTop : PlanarForceQuantity

/-- Displacement in metres from a lower source to the top charge. -/
def displacementFromSourceToTopInMeters
    (setup : EquilateralPointChargeSetup)
    (source : LowerSource) : PlanarVector :=
  positionInMeters (setup.position .top) -
    positionInMeters (setup.position source.vertex)

/-- Metre distance between the endpoints of a named triangle edge. -/
def edgeLengthInMeters
    (setup : EquilateralPointChargeSetup) (edge : TriangleEdge) : ℝ :=
  ‖positionInMeters (setup.position edge.endpoints.2) -
    positionInMeters (setup.position edge.endpoints.1)‖

/-! ## Figure evidence and physical parameters -/

/-!
Exact qualitative and numerical evidence from image `894.png`, including the
association of printed scalar labels with physical dimensionful quantities.
-/
structure MatchesSuppliedEquilateralChargeFigure
    (setup : EquilateralPointChargeSetup) : Prop where
  everyChargeCircleShown : ∀ vertex,
    setup.figure.chargeCircleShown vertex = true
  chargeColors : ∀ vertex,
    setup.figure.chargeColor vertex = expectedChargeColor vertex
  chargeGlyphs : ∀ vertex,
    setup.figure.chargeGlyph vertex = expectedChargeGlyph vertex
  printedChargeLabels : ∀ vertex,
    setup.figure.printedChargeNanocoulombs vertex =
      expectedChargeInNanocoulombs vertex
  physicalChargesMatchLabels : ∀ vertex,
    chargeInNanocoulombs (setup.charge vertex) =
      setup.figure.printedChargeNanocoulombs vertex
  everyTriangleEdgeDashed : ∀ edge,
    setup.figure.dashedEdgeShown edge = true
  everySideLabelIsOneCentimeter : ∀ edge,
    setup.figure.printedSideLengthCentimeters edge = 1
  physicalSideLengthMatchesLabels : ∀ edge,
    lengthInCentimeters setup.sideLength =
      setup.figure.printedSideLengthCentimeters edge
  lowerAngleLabels : ∀ site,
    setup.figure.printedAngleDegrees site = 60

/-!
An oriented metre-coordinate realization of the equilateral triangle shown
in the image: the base is horizontal, the top charge lies above its midpoint,
and every edge has the common physical side length.
-/
structure HasEquilateralTriangleGeometry
    (setup : EquilateralPointChargeSetup) : Prop where
  bottomLeftCoordinates :
    positionInMeters (setup.position .bottomLeft) = !₂[0, 0]
  bottomRightCoordinates :
    positionInMeters (setup.position .bottomRight) =
      !₂[lengthInMeters setup.sideLength, 0]
  topCoordinates :
    positionInMeters (setup.position .top) =
      !₂[lengthInMeters setup.sideLength / 2,
        Real.sqrt 3 * lengthInMeters setup.sideLength / 2]
  allEdgesHavePhysicalSideLength : ∀ edge,
    edgeLengthInMeters setup edge = lengthInMeters setup.sideLength

/-- Positivity and separation conditions selecting the physical branch. -/
structure HasPhysicalPointChargeParameters
    (setup : EquilateralPointChargeSetup) : Prop where
  sideLengthPositive : 0 < lengthInMeters setup.sideLength
  sourcesSeparatedFromTop : ∀ source,
    0 < ‖displacementFromSourceToTopInMeters setup source‖
  coulombConstantPositive :
    0 < setup.electromagneticSystem.coulombConstant

/-!
The rounded constant `9.0 * 10^9 N m^2/C^2` used in the textbook
multiple-choice calculation.  This is an independent calibration, not a
force answer.
-/
structure UsesRoundedCoulombConstant
    (setup : EquilateralPointChargeSetup) : Prop where
  coulombConstantCalibration :
    setup.electromagneticSystem.coulombConstant =
      (9 : ℝ) * 10 ^ (9 : ℕ)

/-! ## Governing electrostatic laws -/

/-!
For displacement `r` from a source to the top charge, Coulomb's vector law is
`F = k q_top q_source r / ‖r‖^3`.  Its signed charge product gives repulsion
from the positive lower-left charge and attraction toward the negative
lower-right charge.  This premise contains no numerical net-force result.
-/
structure SatisfiesPointChargeCoulombForceLaw
    (setup : EquilateralPointChargeSetup) : Prop where
  forceFromEachLowerCharge : ∀ source,
    forceVectorInNewtons (setup.forceOnTopFrom source) =
      (setup.electromagneticSystem.coulombConstant *
          chargeInCoulombs (setup.charge .top) *
          chargeInCoulombs (setup.charge source.vertex) /
        ‖displacementFromSourceToTopInMeters setup source‖ ^ 3) •
          displacementFromSourceToTopInMeters setup source

/-- The force on the top charge is the vector sum of the two pair forces. -/
structure SatisfiesElectricForceSuperposition
    (setup : EquilateralPointChargeSetup) : Prop where
  netForceIsPairSum :
    forceVectorInNewtons setup.netForceOnTop =
      forceVectorInNewtons (setup.forceOnTopFrom .bottomLeft) +
        forceVectorInNewtons (setup.forceOnTopFrom .bottomRight)

/-! ## Derived net force and displayed answer -/

/-- The four force magnitudes printed in the answer list. -/
inductive AnswerChoice where
  | A
  | B
  | C
  | D
  deriving DecidableEq, Fintype, Repr

/-- Literal force magnitude in newtons printed beside an answer choice. -/
def AnswerChoice.forceInNewtons : AnswerChoice → ℝ
  | .A => (1.25 : ℝ) * 10 ^ (-3 : ℤ)
  | .B => (1.35 : ℝ) * 10 ^ (-3 : ℤ)
  | .C => (1.8 : ℝ) * 10 ^ (-4 : ℤ)
  | .D => (1.33 : ℝ) * 10 ^ (-3 : ℤ)

/-- Answer label recorded by the supplied dataset metadata. -/
def recordedDatasetAnswer : AnswerChoice := .C

/-!
The equal-magnitude pair forces have opposite vertical components and equal
rightward horizontal components.  Coulomb's law and superposition therefore
give the following derived force vector on the top charge.
-/
lemma netForceVectorOnTopInNewtons
    (setup : EquilateralPointChargeSetup)
    (_figure : MatchesSuppliedEquilateralChargeFigure setup)
    (_geometry : HasEquilateralTriangleGeometry setup)
    (_physical : HasPhysicalPointChargeParameters setup)
    (_constant : UsesRoundedCoulombConstant setup)
    (_coulomb : SatisfiesPointChargeCoulombForceLaw setup)
    (_superposition : SatisfiesElectricForceSuperposition setup) :
    forceVectorInNewtons setup.netForceOnTop =
      !₂[(1.8 : ℝ) * 10 ^ (-4 : ℤ), 0] := by
  have hcharge (vertex : TriangleVertex) :
      chargeInNanocoulombs (setup.charge vertex) =
        expectedChargeInNanocoulombs vertex := by
    rw [_figure.physicalChargesMatchLabels,
      _figure.printedChargeLabels]
  have hchargeTop :
      chargeInCoulombs (setup.charge .top) =
        (1 : ℝ) / 10 ^ (9 : ℕ) := by
    have h := hcharge .top
    norm_num [chargeInNanocoulombs, expectedChargeInNanocoulombs] at h ⊢
    linarith
  have hchargeLeft :
      chargeInCoulombs (setup.charge .bottomLeft) =
        (2 : ℝ) / 10 ^ (9 : ℕ) := by
    have h := hcharge .bottomLeft
    norm_num [chargeInNanocoulombs, expectedChargeInNanocoulombs] at h ⊢
    linarith
  have hchargeRight :
      chargeInCoulombs (setup.charge .bottomRight) =
        (-2 : ℝ) / 10 ^ (9 : ℕ) := by
    have h := hcharge .bottomRight
    norm_num [chargeInNanocoulombs, expectedChargeInNanocoulombs] at h ⊢
    linarith
  have hside :
      lengthInMeters setup.sideLength = (1 : ℝ) / 100 := by
    have hlabel :=
      _figure.physicalSideLengthMatchesLabels TriangleEdge.left
    rw [_figure.everySideLabelIsOneCentimeter TriangleEdge.left] at hlabel
    norm_num [lengthInCentimeters] at hlabel ⊢
    linarith
  have hnormLeft :
      ‖displacementFromSourceToTopInMeters setup .bottomLeft‖ =
        (1 : ℝ) / 100 := by
    rw [← hside]
    simpa [edgeLengthInMeters, displacementFromSourceToTopInMeters,
      LowerSource.vertex, TriangleEdge.endpoints] using
      _geometry.allEdgesHavePhysicalSideLength TriangleEdge.left
  have hnormRight :
      ‖displacementFromSourceToTopInMeters setup .bottomRight‖ =
        (1 : ℝ) / 100 := by
    rw [← hside]
    simpa [edgeLengthInMeters, displacementFromSourceToTopInMeters,
      LowerSource.vertex, TriangleEdge.endpoints, norm_sub_rev] using
      _geometry.allEdgesHavePhysicalSideLength TriangleEdge.right
  have hdisplacementLeft :
      displacementFromSourceToTopInMeters setup .bottomLeft =
        !₂[(1 : ℝ) / 200, Real.sqrt 3 / 200] := by
    rw [displacementFromSourceToTopInMeters]
    simp only [LowerSource.vertex]
    rw [_geometry.topCoordinates, _geometry.bottomLeftCoordinates, hside]
    ext i
    fin_cases i
    all_goals norm_num
    all_goals ring
  have hdisplacementRight :
      displacementFromSourceToTopInMeters setup .bottomRight =
        !₂[-(1 : ℝ) / 200, Real.sqrt 3 / 200] := by
    rw [displacementFromSourceToTopInMeters]
    simp only [LowerSource.vertex]
    rw [_geometry.topCoordinates, _geometry.bottomRightCoordinates, hside]
    ext i
    fin_cases i
    all_goals norm_num
    all_goals ring
  have hforceLeft :
      forceVectorInNewtons (setup.forceOnTopFrom .bottomLeft) =
        !₂[(9 : ℝ) / 100000, 9 * Real.sqrt 3 / 100000] := by
    rw [_coulomb.forceFromEachLowerCharge .bottomLeft,
      _constant.coulombConstantCalibration, hchargeTop]
    simp only [LowerSource.vertex]
    rw [hchargeLeft, hnormLeft, hdisplacementLeft]
    ext i
    fin_cases i
    all_goals norm_num
    all_goals ring
  have hforceRight :
      forceVectorInNewtons (setup.forceOnTopFrom .bottomRight) =
        !₂[(9 : ℝ) / 100000, -(9 * Real.sqrt 3 / 100000)] := by
    rw [_coulomb.forceFromEachLowerCharge .bottomRight,
      _constant.coulombConstantCalibration, hchargeTop]
    simp only [LowerSource.vertex]
    rw [hchargeRight, hnormRight, hdisplacementRight]
    ext i
    fin_cases i
    all_goals norm_num
    all_goals ring
  rw [_superposition.netForceIsPairSum, hforceLeft, hforceRight]
  ext i
  fin_cases i <;> norm_num

/-!
The magnitude of the force on the `1.0 nC` top charge is
`1.8 * 10^-4 N`, which is answer C.

This is the Lean declaration corresponding to
`thm:physics:phyx_mini_0894:target`.
-/
theorem problem_phyx_mini_0894
    (setup : EquilateralPointChargeSetup)
    (_figure : MatchesSuppliedEquilateralChargeFigure setup)
    (_geometry : HasEquilateralTriangleGeometry setup)
    (_physical : HasPhysicalPointChargeParameters setup)
    (_constant : UsesRoundedCoulombConstant setup)
    (_coulomb : SatisfiesPointChargeCoulombForceLaw setup)
    (_superposition : SatisfiesElectricForceSuperposition setup) :
    forceMagnitudeInNewtons setup.netForceOnTop =
        (1.8 : ℝ) * 10 ^ (-4 : ℤ) ∧
      recordedDatasetAnswer = .C := by
  constructor
  · rw [forceMagnitudeInNewtons,
      netForceVectorOnTopInNewtons setup _figure _geometry _physical
        _constant _coulomb _superposition]
    rw [EuclideanSpace.norm_eq]
    norm_num [Fin.sum_univ_two, Real.norm_eq_abs]
  · rfl

end PhyXMiniProblems.ProblemPhyXMini0894
