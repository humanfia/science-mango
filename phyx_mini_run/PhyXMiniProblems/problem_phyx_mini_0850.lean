import Mathlib
import Physlib.Electromagnetism.Basic
import Physlib.SpaceAndTime.Space.LengthUnit
import Physlib.Units.WithDim.Basic

noncomputable section

namespace PhyXMiniProblems.ProblemPhyXMini0850

open Dimension

/-!
# Net electric flux through four sides of a cube

The primary raster `850.png` is a top view of a `3.0 cm × 3.0 cm ×
3.0 cm` cube. Its four visible vertical faces are called out by the labels
1 through 4. Parallel, equally spaced electric-field arrows point 30° above
the positive horizontal direction and are labeled `500 N/C`.

The full electric field is Physlib's spacetime-dependent vector field.
Lengths, areas, field strength, and signed electric flux are unit-independent
dimensionful quantities. Real numbers occur only as explicit unit readouts,
dimensionless vector components, angles, and answer-choice values. The net
four-side flux is an independent observable constrained by the planar-flux
and boundary-additivity laws below; it is not defined to be zero.
-/

/-! ## Dimensionful quantities and named readouts -/

/-- The dimension `M L T⁻² C⁻¹` of electric-field strength (`N/C`). -/
def electricFieldStrengthDimension : Dimension :=
  M𝓭 * L𝓭 * T𝓭⁻¹ * T𝓭⁻¹ * C𝓭⁻¹

/-- The physical dimension `L²` of one square side of the cube. -/
def areaDimension : Dimension := L𝓭 * L𝓭

/-!
Electric flux has dimension `M L³ T⁻² C⁻¹`, equivalently `N m²/C` in
coherent SI units.
-/
def electricFluxDimension : Dimension :=
  electricFieldStrengthDimension * areaDimension

/-- A nonnegative, unit-independent physical length. -/
abbrev LengthQuantity : Type := Dimensionful (WithDim L𝓭 NNReal)

/-- A nonnegative, unit-independent physical area. -/
abbrev AreaQuantity : Type := Dimensionful (WithDim areaDimension NNReal)

/-- A nonnegative, unit-independent electric-field magnitude. -/
abbrev ElectricFieldStrengthQuantity : Type :=
  Dimensionful (WithDim electricFieldStrengthDimension NNReal)

/-!
A signed, unit-independent electric flux. Its sign is determined by the
outward orientation of the relevant cube side.
-/
abbrev ElectricFluxQuantity : Type :=
  Dimensionful (WithDim electricFluxDimension ℝ)

/-- Read a physical length in metres. -/
def lengthInMeters (length : LengthQuantity) : ℝ :=
  ((length UnitChoices.SI).val : ℝ)

/-- Read a physical length in centimetres. -/
def lengthInCentimeters (length : LengthQuantity) : ℝ :=
  ((length {UnitChoices.SI with length := LengthUnit.centimeters}).val : ℝ)

/-- Read a physical area in square metres. -/
def areaInSquareMeters (area : AreaQuantity) : ℝ :=
  ((area UnitChoices.SI).val : ℝ)

/-- Read electric-field strength in newtons per coulomb. -/
def electricFieldStrengthInNewtonsPerCoulomb
    (strength : ElectricFieldStrengthQuantity) : ℝ :=
  ((strength UnitChoices.SI).val : ℝ)

/-- Read signed electric flux in newton-square-metres per coulomb. -/
def electricFluxInNewtonSquareMetersPerCoulomb
    (flux : ElectricFluxQuantity) : ℝ :=
  (flux UnitChoices.SI).val

/-! ## The numbered sides and top-view geometry -/

/-!
The four vertical cube faces visible in the top view. The constructors retain
the circled labels 1 through 4 printed around the square in the raster.
-/
inductive LateralFace where
  | side1
  | side2
  | side3
  | side4
  deriving DecidableEq, Fintype, Repr

/-!
The callouts identify side 1 as the left face, side 2 as the upper face,
side 3 as the right face, and side 4 as the lower face in the top view.
-/
inductive TopViewSide where
  | left
  | upper
  | right
  | lower
  deriving DecidableEq, Fintype, Repr

/-- Placement of each numbered callout in the supplied top view. -/
def figureSidePlacement : LateralFace → TopViewSide
  | .side1 => .left
  | .side2 => .upper
  | .side3 => .right
  | .side4 => .lower

/-!
Dimensionless outward unit normals in top-view coordinates `(x,y,z)`. The
third coordinate is perpendicular to the page.
-/
def figureOutwardUnitNormal :
    LateralFace → EuclideanSpace ℝ (Fin 3)
  | .side1 => WithLp.toLp 2 ![(-1 : ℝ), 0, 0]
  | .side2 => WithLp.toLp 2 ![(0 : ℝ), 1, 0]
  | .side3 => WithLp.toLp 2 ![(1 : ℝ), 0, 0]
  | .side4 => WithLp.toLp 2 ![(0 : ℝ), -1, 0]

/-- Convert a numerical degree readout into a physical angle. -/
def degrees (value : ℝ) : Real.Angle :=
  ((value * Real.pi / 180 : ℝ) : Real.Angle)

/-!
The dimensionless direction in the top-view plane making `angle` with the
positive horizontal axis.
-/
def topViewDirection (angle : Real.Angle) :
    EuclideanSpace ℝ (Fin 3) :=
  WithLp.toLp 2 ![Real.cos angle.toReal, Real.sin angle.toReal, 0]

/-!
The cubical geometry relevant to the requested four lateral faces. The side
regions and sample points keep the flux law tied to actual subsets and points
of Physlib's three-dimensional space.
-/
structure CubeGeometry where
  center : Space 3
  edgeLength : LengthQuantity
  sideArea : AreaQuantity
  sideRegion : LateralFace → Set (Space 3)
  representativePoint : LateralFace → Space 3
  outwardUnitNormal : LateralFace → EuclideanSpace ℝ (Fin 3)

/-!
Typed evidence transcribed from the primary raster. The length and field
labels are physical quantities rather than bare scalar aliases.
-/
structure SuppliedTopViewFigure where
  topViewCaptionShown : Bool
  cubeOutlineShown : Bool
  sideCalloutShown : LateralFace → Bool
  sidePlacement : LateralFace → TopViewSide
  edgeLengthLabel : LengthQuantity
  fieldStrengthLabel : ElectricFieldStrengthQuantity
  fieldAngleLabel : Real.Angle
  electricFieldSymbolShown : Bool
  fieldArrowsParallel : Bool
  fieldArrowsUniformlySpaced : Bool
  containsNumericalFluxReadout : Bool

/-!
The physical setup and its independent observables. `electricField` is the
full Physlib field. Its vector components below are interpreted as coherent
SI `N/C` readouts, while `electricFieldStrength` supplies the corresponding
dimensionful magnitude. Neither `fluxThrough` nor `netFourSideFlux` is
defined from an answer choice.
-/
structure UniformFieldCubeSetup where
  cube : CubeGeometry
  observationTime : Time
  electricField : Electromagnetism.ElectricField 3
  electricFieldStrength : ElectricFieldStrengthQuantity
  electricFieldAngleFromPositiveHorizontal : Real.Angle
  fluxThrough : LateralFace → ElectricFluxQuantity
  netFourSideFlux : ElectricFluxQuantity
  figure : SuppliedTopViewFigure

/-! ## Figure/data readouts and governing assumptions -/

/-!
Facts read from `850.png`: a 3.0 cm cube, four numbered side callouts, a
uniform-looking family of parallel arrows labeled `500 N/C`, and a 30° angle.
The image contains no numerical flux readout, so no requested answer is
introduced here.
-/
structure MatchesSuppliedTopViewFigure
    (setup : UniformFieldCubeSetup) : Prop where
  topViewCaptionShown : setup.figure.topViewCaptionShown = true
  cubeOutlineShown : setup.figure.cubeOutlineShown = true
  everySideCalloutShown :
    ∀ face : LateralFace, setup.figure.sideCalloutShown face = true
  sideCalloutsHaveFigurePlacement :
    ∀ face : LateralFace,
      setup.figure.sidePlacement face = figureSidePlacement face
  edgeLabelDescribesCube :
    setup.figure.edgeLengthLabel = setup.cube.edgeLength
  fieldLabelDescribesMagnitude :
    setup.figure.fieldStrengthLabel = setup.electricFieldStrength
  angleLabelDescribesPhysicalDirection :
    setup.figure.fieldAngleLabel =
      setup.electricFieldAngleFromPositiveHorizontal
  cubeEdgeReadout : lengthInCentimeters setup.cube.edgeLength = 3
  fieldStrengthReadout :
    electricFieldStrengthInNewtonsPerCoulomb
      setup.electricFieldStrength = 500
  fieldAngleReadout :
    setup.electricFieldAngleFromPositiveHorizontal = degrees 30
  electricFieldSymbolShown :
    setup.figure.electricFieldSymbolShown = true
  arrowsParallel : setup.figure.fieldArrowsParallel = true
  arrowsUniformlySpaced :
    setup.figure.fieldArrowsUniformlySpaced = true
  noNumericalFluxReadout :
    setup.figure.containsNumericalFluxReadout = false

/-!
Geometric facts about the four congruent square faces. Their common area is
the square of the positive cube edge; each representative point lies on its
face; and the outward normals agree with the numbered top-view callouts.
-/
structure IsPhysicalFourSideCubeGeometry
    (setup : UniformFieldCubeSetup) : Prop where
  edgeLengthPositive : 0 < lengthInMeters setup.cube.edgeLength
  sideAreaIsEdgeSquared :
    areaInSquareMeters setup.cube.sideArea =
      lengthInMeters setup.cube.edgeLength ^ 2
  representativePointOnSide : ∀ face : LateralFace,
    setup.cube.representativePoint face ∈ setup.cube.sideRegion face
  outwardNormalsMatchFigure : ∀ face : LateralFace,
    setup.cube.outwardUnitNormal face = figureOutwardUnitNormal face

/-!
The field is spatially uniform at the observation time and has the magnitude
and in-plane direction recorded by the setup. This is a governing property
of the depicted field, not a statement about electric flux.
-/
structure IsUniformTopViewElectricField
    (setup : UniformFieldCubeSetup) : Prop where
  fieldStrengthPositive :
    0 < electricFieldStrengthInNewtonsPerCoulomb
      setup.electricFieldStrength
  fieldReadoutAtEveryPosition : ∀ position : Space 3,
    setup.electricField setup.observationTime position =
      electricFieldStrengthInNewtonsPerCoulomb
          setup.electricFieldStrength •
        topViewDirection
          setup.electricFieldAngleFromPositiveHorizontal

/-!
For a constant field on a planar side, oriented flux is
`A * inner(E,n_out)`. The second field is additivity over the four-side
boundary partition. Both are general physical laws and neither asserts the
requested zero value.
-/
structure SatisfiesFourSidePlanarFluxLaws
    (setup : UniformFieldCubeSetup) : Prop where
  planarSideFlux : ∀ face : LateralFace,
    electricFluxInNewtonSquareMetersPerCoulomb
        (setup.fluxThrough face) =
      areaInSquareMeters setup.cube.sideArea *
        inner ℝ
          (setup.electricField setup.observationTime
            (setup.cube.representativePoint face))
          (setup.cube.outwardUnitNormal face)
  netFluxIsFourSideSum :
    electricFluxInNewtonSquareMetersPerCoulomb
        setup.netFourSideFlux =
      ∑ face : LateralFace,
        electricFluxInNewtonSquareMetersPerCoulomb
          (setup.fluxThrough face)

/-! ## Derived cancellation and the current target -/

/-!
Opposite side normals are negatives of one another. Uniformity and the
planar-face flux law therefore make the side 1/3 and side 2/4 contributions
cancel pairwise.
-/
lemma oppositeSideFluxContributions_cancel
    (setup : UniformFieldCubeSetup)
    (hGeometry : IsPhysicalFourSideCubeGeometry setup)
    (hUniformField : IsUniformTopViewElectricField setup)
    (hFlux : SatisfiesFourSidePlanarFluxLaws setup) :
    electricFluxInNewtonSquareMetersPerCoulomb
          (setup.fluxThrough .side1) +
        electricFluxInNewtonSquareMetersPerCoulomb
          (setup.fluxThrough .side3) = 0 ∧
      electricFluxInNewtonSquareMetersPerCoulomb
          (setup.fluxThrough .side2) +
        electricFluxInNewtonSquareMetersPerCoulomb
          (setup.fluxThrough .side4) = 0 := by
  constructor
  · rw [hFlux.planarSideFlux .side1, hFlux.planarSideFlux .side3]
    rw [hUniformField.fieldReadoutAtEveryPosition,
      hUniformField.fieldReadoutAtEveryPosition]
    rw [hGeometry.outwardNormalsMatchFigure,
      hGeometry.outwardNormalsMatchFigure]
    rw [show figureOutwardUnitNormal .side1 =
      -figureOutwardUnitNormal .side3 by
        ext i
        fin_cases i <;> simp [figureOutwardUnitNormal]]
    simp
  · rw [hFlux.planarSideFlux .side2, hFlux.planarSideFlux .side4]
    rw [hUniformField.fieldReadoutAtEveryPosition,
      hUniformField.fieldReadoutAtEveryPosition]
    rw [hGeometry.outwardNormalsMatchFigure,
      hGeometry.outwardNormalsMatchFigure]
    rw [show figureOutwardUnitNormal .side2 =
      -figureOutwardUnitNormal .side4 by
        ext i
        fin_cases i <;> simp [figureOutwardUnitNormal]]
    simp

/-- Labels of the four electric-flux choices printed in the source. -/
inductive AnswerChoice where
  | A
  | B
  | C
  | D
  deriving DecidableEq, Fintype, Repr

/-- Flux readout in `N m²/C` printed beside each answer label. -/
def answerFluxInNewtonSquareMetersPerCoulomb : AnswerChoice → ℝ
  | .A => 80
  | .B => 10
  | .C => 20
  | .D => 0

/-- The answer label recorded by the source dataset. -/
def recordedDatasetAnswer : AnswerChoice := .D

/-!
A displayed choice agrees with the independently modeled net four-side flux.
This relation does not define the net flux from the choice.
-/
def AnswerMatchesNetFourSideFlux
    (setup : UniformFieldCubeSetup) (choice : AnswerChoice) : Prop :=
  electricFluxInNewtonSquareMetersPerCoulomb setup.netFourSideFlux =
    answerFluxInNewtonSquareMetersPerCoulomb choice

/-!
The uniform field has equal and opposite flux through each pair of opposite
vertical faces. Hence the net flux through the four numbered sides is
`0 N m²/C`, agreeing with answer D.

This declaration formalizes blueprint label
`thm:physics:phyx_mini_0850:target`. The zero net flux is absent from the
setup, figure predicate, geometry assumptions, uniform-field assumptions,
and governing-law fields.
-/
theorem problem_phyx_mini_0850
    (setup : UniformFieldCubeSetup)
    (hFigure : MatchesSuppliedTopViewFigure setup)
    (hGeometry : IsPhysicalFourSideCubeGeometry setup)
    (hUniformField : IsUniformTopViewElectricField setup)
    (hFlux : SatisfiesFourSidePlanarFluxLaws setup) :
    electricFluxInNewtonSquareMetersPerCoulomb
          setup.netFourSideFlux = 0 ∧
      AnswerMatchesNetFourSideFlux setup recordedDatasetAnswer := by
  have hCancel :=
    oppositeSideFluxContributions_cancel setup hGeometry hUniformField hFlux
  rcases hCancel with ⟨h13, h24⟩
  have hNet :
      electricFluxInNewtonSquareMetersPerCoulomb
          setup.netFourSideFlux = 0 := by
    rw [hFlux.netFluxIsFourSideSum]
    rw [show (Finset.univ : Finset LateralFace) =
      {.side1, .side2, .side3, .side4} by decide]
    simp
    linarith
  exact ⟨hNet, by
    simpa [AnswerMatchesNetFourSideFlux, recordedDatasetAnswer,
      answerFluxInNewtonSquareMetersPerCoulomb] using hNet⟩

end PhyXMiniProblems.ProblemPhyXMini0850
