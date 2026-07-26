import Mathlib
import Physlib.Electromagnetism.Basic
import Physlib.Units.WithDim.Basic

noncomputable section

namespace PhyXMiniProblems.ProblemPhyXMini0999

open Dimension

/-!
# Electric flux through a rotated cube in a uniform field

An imaginary cube of side length `L` lies in a uniform electric field of
magnitude `E` and is turned through the dimensionless angle `theta` about its
vertical axis.  The primary raster labels the outward face normals `n1`
through `n6`.  The horizontal field has signed normal components
`-E cos theta`, `E cos theta`, `-E sin theta`, `E sin theta`, `0`, and `0`
on those faces, respectively.  Opposite-face contributions therefore cancel.

Physical length, area, electric-field magnitude, and signed electric flux are
unit-independent Physlib `Dimensionful` quantities.  Real numbers below are
only coherent-SI readouts, unit-vector components, or the dimensionless angle.
The full electric field retains Physlib's spacetime-dependent vector-field
type `Electromagnetism.ElectricField 3`.

Assumption/target split:

* governing laws: uniformity of the vector field on the cube, the planar-face
  law `Phi = (E dot n) A`, and additivity of the six outward face fluxes;
* previous-part results: none;
* figure/data readouts: the six labelled outward normal arrows, horizontal
  parallel field arrows, `theta` at `n1`, `pi / 2 - theta` at `n4`, and the
  three opposite normal pairs of a cube turned about the `n5`/`n6` axis;
* current target conclusions: the six signed face-flux formulas and total
  outward flux zero, corresponding to recorded answer B.

No setup field or premise fixes any face flux to one of the requested formulas
or fixes the total flux to zero.
-/

/-! ## Dimensionful electrostatic quantities and SI readouts -/

/-- The physical dimension `M L T^-2 C^-1` of electric-field strength. -/
def electricFieldStrengthDimension : Dimension :=
  M𝓭 * L𝓭 * T𝓭⁻¹ * T𝓭⁻¹ * C𝓭⁻¹

/-- The dimension `M L^3 T^-2 C^-1` of electric flux `E * area`. -/
def electricFluxDimension : Dimension :=
  electricFieldStrengthDimension * L𝓭 * L𝓭

/-- A nonnegative, unit-independent physical length. -/
abbrev LengthQuantity : Type :=
  Dimensionful (WithDim L𝓭 NNReal)

/-- A nonnegative, unit-independent physical area. -/
abbrev AreaQuantity : Type :=
  Dimensionful (WithDim (L𝓭 * L𝓭) NNReal)

/-- A nonnegative, unit-independent electric-field magnitude. -/
abbrev ElectricFieldMagnitudeQuantity : Type :=
  Dimensionful (WithDim electricFieldStrengthDimension NNReal)

/-- A signed outward electric flux through a face or closed surface. -/
abbrev SignedElectricFluxQuantity : Type :=
  Dimensionful (WithDim electricFluxDimension ℝ)

/-- Coherent-SI readout of a physical length, in metres. -/
def lengthInMeters (length : LengthQuantity) : ℝ :=
  ((length UnitChoices.SI).val : ℝ)

/-- Coherent-SI readout of a physical area, in square metres. -/
def areaInSquareMeters (area : AreaQuantity) : ℝ :=
  ((area UnitChoices.SI).val : ℝ)

/-- Coherent-SI readout of field magnitude, in newtons per coulomb. -/
def fieldMagnitudeInNewtonsPerCoulomb
    (magnitude : ElectricFieldMagnitudeQuantity) : ℝ :=
  ((magnitude UnitChoices.SI).val : ℝ)

/-- Coherent-SI readout of signed flux, in newton-square-metres per coulomb. -/
def electricFluxInNewtonSquareMetersPerCoulomb
    (flux : SignedElectricFluxQuantity) : ℝ :=
  (flux UnitChoices.SI).val

/-! ## Figure labels and the independent physical setup -/

/-- The six outward-normal labels printed in the primary raster. -/
inductive CubeFace where
  | n1
  | n2
  | n3
  | n4
  | n5
  | n6
  deriving DecidableEq, Fintype, Repr

/-!
Typed content of the supplied raster.  Direction vectors are dimensionless;
physical field magnitude is stored independently in the setup.
-/
structure RotatedCubeFigure where
  cubeShown : Bool
  normalArrowShown : CubeFace → Bool
  normalArrowDirection : CubeFace → EuclideanSpace ℝ (Fin 3)
  electricFieldArrowsShown : Bool
  electricFieldArrowsParallel : Bool
  electricFieldArrowDirection : EuclideanSpace ℝ (Fin 3)
  thetaLabelShown : Bool
  thetaLabelReferenceNormal : CubeFace
  thetaLabelRadians : ℝ
  complementaryAngleLabelShown : Bool
  complementaryAngleReferenceNormal : CubeFace
  complementaryAngleLabelRadians : ℝ

/-!
Independent physical data for the rotated cube.  The face and total fluxes
are unconstrained physical quantities here; their values are related to the
field only by `SatisfiesElectricFluxLaw` below.
-/
structure RotatedCubeInUniformFieldSetup where
  sideLength : LengthQuantity
  faceArea : CubeFace → AreaQuantity
  electricFieldMagnitude : ElectricFieldMagnitudeQuantity
  electricField : Electromagnetism.ElectricField 3
  observationTime : Time
  cubeRegion : Set (Space 3)
  faceRegion : CubeFace → Set (Space 3)
  representativePoint : CubeFace → Space 3
  fieldDirection : EuclideanSpace ℝ (Fin 3)
  rotationAxisDirection : EuclideanSpace ℝ (Fin 3)
  outwardUnitNormal : CubeFace → EuclideanSpace ℝ (Fin 3)
  turnAngleRadians : ℝ
  faceFlux : CubeFace → SignedElectricFluxQuantity
  totalOutwardFlux : SignedElectricFluxQuantity
  figure : RotatedCubeFigure

/-! ## Scenario, primary-image evidence, geometry, and governing laws -/

/-- Positivity conditions for the physical parameters named in the problem. -/
structure HasPhysicalCubeAndFieldParameters
    (setup : RotatedCubeInUniformFieldSetup) : Prop where
  sideLengthPositive : 0 < lengthInMeters setup.sideLength
  fieldMagnitudePositive :
    0 < fieldMagnitudeInNewtonsPerCoulomb setup.electricFieldMagnitude
  everyFaceAreaPositive :
    ∀ face, 0 < areaInSquareMeters (setup.faceArea face)

/-!
Primary-image evidence.  It records all six normal labels, the family of
parallel field arrows, and the two printed angle annotations.  It contains no
flux value.
-/
structure MatchesPrimaryRotatedCubeFigure
    (setup : RotatedCubeInUniformFieldSetup) : Prop where
  cubeIsShown : setup.figure.cubeShown = true
  allNormalArrowsShown : ∀ face, setup.figure.normalArrowShown face = true
  normalArrowsMatchPhysicalNormals : ∀ face,
    setup.figure.normalArrowDirection face = setup.outwardUnitNormal face
  fieldArrowsShown : setup.figure.electricFieldArrowsShown = true
  fieldArrowsAreParallel : setup.figure.electricFieldArrowsParallel = true
  fieldArrowMatchesPhysicalDirection :
    setup.figure.electricFieldArrowDirection = setup.fieldDirection
  thetaShown : setup.figure.thetaLabelShown = true
  thetaIsDrawnAtN1 : setup.figure.thetaLabelReferenceNormal = .n1
  thetaLabelMatchesTurn :
    setup.figure.thetaLabelRadians = setup.turnAngleRadians
  complementaryAngleShown :
    setup.figure.complementaryAngleLabelShown = true
  complementaryAngleIsDrawnAtN4 :
    setup.figure.complementaryAngleReferenceNormal = .n4
  complementaryAngleMatchesTurn :
    setup.figure.complementaryAngleLabelRadians =
      Real.pi / 2 - setup.turnAngleRadians

/-!
Geometry of the rotated cube.  The component equations formalize the two
angles read from the raster: `n1` makes angle `theta` with the direction
opposite the field, while `n4` makes angle `pi/2 - theta` with the field.
They are geometric facts about unit directions, not assumptions about flux.
-/
structure SatisfiesRotatedCubeGeometry
    (setup : RotatedCubeInUniformFieldSetup) : Prop where
  turnAngleInFigureRange :
    0 ≤ setup.turnAngleRadians ∧ setup.turnAngleRadians ≤ Real.pi / 2
  everyFaceHasSquareArea : ∀ face,
    areaInSquareMeters (setup.faceArea face) =
      lengthInMeters setup.sideLength ^ 2
  representativePointOnFace : ∀ face,
    setup.representativePoint face ∈ setup.faceRegion face
  faceLiesInUniformFieldRegion : ∀ face point,
    point ∈ setup.faceRegion face → point ∈ setup.cubeRegion
  fieldDirectionIsUnit : ‖setup.fieldDirection‖ = 1
  rotationAxisIsUnit : ‖setup.rotationAxisDirection‖ = 1
  everyOutwardNormalIsUnit : ∀ face,
    ‖setup.outwardUnitNormal face‖ = 1
  n1n2AreOpposite :
    setup.outwardUnitNormal .n2 = -setup.outwardUnitNormal .n1
  n3n4AreOpposite :
    setup.outwardUnitNormal .n4 = -setup.outwardUnitNormal .n3
  n5n6AreOpposite :
    setup.outwardUnitNormal .n6 = -setup.outwardUnitNormal .n5
  rotationAxisIsVerticalN5 :
    setup.rotationAxisDirection = setup.outwardUnitNormal .n5
  fieldIsPerpendicularToRotationAxis :
    inner ℝ setup.fieldDirection setup.rotationAxisDirection = 0
  n1FieldComponent :
    inner ℝ setup.fieldDirection (setup.outwardUnitNormal .n1) =
      -Real.cos setup.turnAngleRadians
  n2FieldComponent :
    inner ℝ setup.fieldDirection (setup.outwardUnitNormal .n2) =
      Real.cos setup.turnAngleRadians
  n3FieldComponent :
    inner ℝ setup.fieldDirection (setup.outwardUnitNormal .n3) =
      -Real.sin setup.turnAngleRadians
  n4FieldComponent :
    inner ℝ setup.fieldDirection (setup.outwardUnitNormal .n4) =
      Real.sin setup.turnAngleRadians
  n5FieldComponent :
    inner ℝ setup.fieldDirection (setup.outwardUnitNormal .n5) = 0
  n6FieldComponent :
    inner ℝ setup.fieldDirection (setup.outwardUnitNormal .n6) = 0

/-!
The stated electric field is uniform throughout the region containing the
cube.  The Physlib field vector is calibrated to the independent dimensionful
magnitude and unit direction in coherent SI components.
-/
structure IsUniformElectricFieldOnCube
    (setup : RotatedCubeInUniformFieldSetup) : Prop where
  fieldIsUniform : ∀ time point,
    point ∈ setup.cubeRegion →
      setup.electricField time point =
        fieldMagnitudeInNewtonsPerCoulomb setup.electricFieldMagnitude •
          setup.fieldDirection

/-!
The planar-surface electric-flux law and finite additivity over the closed
cube.  Neither field states any requested trigonometric face formula or the
zero-total-flux conclusion.
-/
structure SatisfiesElectricFluxLaw
    (setup : RotatedCubeInUniformFieldSetup) : Prop where
  planarFaceFlux : ∀ face,
    electricFluxInNewtonSquareMetersPerCoulomb (setup.faceFlux face) =
      inner ℝ
          (setup.electricField setup.observationTime
            (setup.representativePoint face))
          (setup.outwardUnitNormal face) *
        areaInSquareMeters (setup.faceArea face)
  totalFluxIsSumOfFaceFluxes :
    electricFluxInNewtonSquareMetersPerCoulomb setup.totalOutwardFlux =
      ∑ face : CubeFace,
        electricFluxInNewtonSquareMetersPerCoulomb (setup.faceFlux face)

/-! ## Displayed choices and formalized conclusions -/

/-- Labels of the four electric-flux choices printed in the source. -/
inductive AnswerChoice where
  | A
  | B
  | C
  | D
  deriving DecidableEq, Repr

/-!
Flux readout printed beside each answer label, with the source's `A`
interpreted as the square face area `L^2`.
-/
def AnswerChoice.displayedFluxInNewtonSquareMetersPerCoulomb
    (setup : RotatedCubeInUniformFieldSetup) : AnswerChoice → ℝ
  | .A =>
      fieldMagnitudeInNewtonsPerCoulomb setup.electricFieldMagnitude *
        lengthInMeters setup.sideLength ^ 2 *
          Real.cos setup.turnAngleRadians
  | .B => 0
  | .C =>
      6 * fieldMagnitudeInNewtonsPerCoulomb setup.electricFieldMagnitude *
        lengthInMeters setup.sideLength ^ 2 *
          Real.cos setup.turnAngleRadians
  | .D =>
      fieldMagnitudeInNewtonsPerCoulomb setup.electricFieldMagnitude *
        lengthInMeters setup.sideLength ^ 2 *
          (1 - Real.cos setup.turnAngleRadians)

/-- The answer label recorded in the dataset. -/
def recordedDatasetAnswer : AnswerChoice := .B

/-!
The six requested signed outward face fluxes.  Faces `n1` and `n2` cancel,
as do `n3` and `n4`; the vertical faces `n5` and `n6` carry no flux.
-/
lemma flux_through_each_face
    (setup : RotatedCubeInUniformFieldSetup)
    (hGeometry : SatisfiesRotatedCubeGeometry setup)
    (hUniform : IsUniformElectricFieldOnCube setup)
    (hFluxLaw : SatisfiesElectricFluxLaw setup) :
    electricFluxInNewtonSquareMetersPerCoulomb (setup.faceFlux .n1) =
        -(fieldMagnitudeInNewtonsPerCoulomb setup.electricFieldMagnitude *
          lengthInMeters setup.sideLength ^ 2 *
            Real.cos setup.turnAngleRadians) ∧
      electricFluxInNewtonSquareMetersPerCoulomb (setup.faceFlux .n2) =
        fieldMagnitudeInNewtonsPerCoulomb setup.electricFieldMagnitude *
          lengthInMeters setup.sideLength ^ 2 *
            Real.cos setup.turnAngleRadians ∧
      electricFluxInNewtonSquareMetersPerCoulomb (setup.faceFlux .n3) =
        -(fieldMagnitudeInNewtonsPerCoulomb setup.electricFieldMagnitude *
          lengthInMeters setup.sideLength ^ 2 *
            Real.sin setup.turnAngleRadians) ∧
      electricFluxInNewtonSquareMetersPerCoulomb (setup.faceFlux .n4) =
        fieldMagnitudeInNewtonsPerCoulomb setup.electricFieldMagnitude *
          lengthInMeters setup.sideLength ^ 2 *
            Real.sin setup.turnAngleRadians ∧
      electricFluxInNewtonSquareMetersPerCoulomb (setup.faceFlux .n5) = 0 ∧
      electricFluxInNewtonSquareMetersPerCoulomb (setup.faceFlux .n6) = 0 := by
  have hRepresentativePointInCube (face : CubeFace) :
      setup.representativePoint face ∈ setup.cubeRegion :=
    hGeometry.faceLiesInUniformFieldRegion face _
      (hGeometry.representativePointOnFace face)
  have hFaceFlux (face : CubeFace) :
      electricFluxInNewtonSquareMetersPerCoulomb (setup.faceFlux face) =
        fieldMagnitudeInNewtonsPerCoulomb setup.electricFieldMagnitude *
          inner ℝ setup.fieldDirection (setup.outwardUnitNormal face) *
            lengthInMeters setup.sideLength ^ 2 := by
    rw [hFluxLaw.planarFaceFlux,
      hUniform.fieldIsUniform _ _ (hRepresentativePointInCube face),
      real_inner_smul_left, hGeometry.everyFaceHasSquareArea]
  simpa only [hFaceFlux, hGeometry.n1FieldComponent,
    hGeometry.n2FieldComponent, hGeometry.n3FieldComponent,
    hGeometry.n4FieldComponent, hGeometry.n5FieldComponent,
    hGeometry.n6FieldComponent, mul_zero] using
    And.intro (show _ = _ by ring)
      (And.intro (show _ = _ by ring)
        (And.intro (show _ = _ by ring)
          (And.intro (show _ = _ by ring)
            (And.intro (show _ = _ by ring) (show _ = _ by ring)))))

/-!
Finite additivity and opposite-face cancellation make the total outward flux
zero for every turn angle.
-/
lemma total_outward_flux_is_zero
    (setup : RotatedCubeInUniformFieldSetup)
    (hGeometry : SatisfiesRotatedCubeGeometry setup)
    (hUniform : IsUniformElectricFieldOnCube setup)
    (hFluxLaw : SatisfiesElectricFluxLaw setup) :
    electricFluxInNewtonSquareMetersPerCoulomb setup.totalOutwardFlux = 0 := by
  rcases flux_through_each_face setup hGeometry hUniform hFluxLaw with
    ⟨hn1, hn2, hn3, hn4, hn5, hn6⟩
  rw [hFluxLaw.totalFluxIsSumOfFaceFluxes]
  rw [show (Finset.univ : Finset CubeFace) =
    {.n1, .n2, .n3, .n4, .n5, .n6} by decide]
  simp [hn1, hn2, hn3, hn4, hn5, hn6]

/-!
The primary figure's six face fluxes have the stated signed trigonometric
values, and the total flux agrees with recorded answer B (`0`).

This declaration formalizes `thm:physics:phyx_mini_0999:target`.  None of the
six face formulas, their pairwise cancellation, the zero total, or the choice
B equality occurs in any premise.
-/
theorem problem_phyx_mini_0999
    (setup : RotatedCubeInUniformFieldSetup)
    (hPhysical : HasPhysicalCubeAndFieldParameters setup)
    (hFigure : MatchesPrimaryRotatedCubeFigure setup)
    (hGeometry : SatisfiesRotatedCubeGeometry setup)
    (hUniform : IsUniformElectricFieldOnCube setup)
    (hFluxLaw : SatisfiesElectricFluxLaw setup) :
    electricFluxInNewtonSquareMetersPerCoulomb (setup.faceFlux .n1) =
        -(fieldMagnitudeInNewtonsPerCoulomb setup.electricFieldMagnitude *
          lengthInMeters setup.sideLength ^ 2 *
            Real.cos setup.turnAngleRadians) ∧
      electricFluxInNewtonSquareMetersPerCoulomb (setup.faceFlux .n2) =
        fieldMagnitudeInNewtonsPerCoulomb setup.electricFieldMagnitude *
          lengthInMeters setup.sideLength ^ 2 *
            Real.cos setup.turnAngleRadians ∧
      electricFluxInNewtonSquareMetersPerCoulomb (setup.faceFlux .n3) =
        -(fieldMagnitudeInNewtonsPerCoulomb setup.electricFieldMagnitude *
          lengthInMeters setup.sideLength ^ 2 *
            Real.sin setup.turnAngleRadians) ∧
      electricFluxInNewtonSquareMetersPerCoulomb (setup.faceFlux .n4) =
        fieldMagnitudeInNewtonsPerCoulomb setup.electricFieldMagnitude *
          lengthInMeters setup.sideLength ^ 2 *
            Real.sin setup.turnAngleRadians ∧
      electricFluxInNewtonSquareMetersPerCoulomb (setup.faceFlux .n5) = 0 ∧
      electricFluxInNewtonSquareMetersPerCoulomb (setup.faceFlux .n6) = 0 ∧
      electricFluxInNewtonSquareMetersPerCoulomb setup.totalOutwardFlux =
        recordedDatasetAnswer.displayedFluxInNewtonSquareMetersPerCoulomb setup := by
  rcases flux_through_each_face setup hGeometry hUniform hFluxLaw with
    ⟨hn1, hn2, hn3, hn4, hn5, hn6⟩
  refine ⟨hn1, hn2, hn3, hn4, hn5, hn6, ?_⟩
  have hTotal :=
    total_outward_flux_is_zero setup hGeometry hUniform hFluxLaw
  simpa [recordedDatasetAnswer,
    AnswerChoice.displayedFluxInNewtonSquareMetersPerCoulomb] using hTotal

end PhyXMiniProblems.ProblemPhyXMini0999
