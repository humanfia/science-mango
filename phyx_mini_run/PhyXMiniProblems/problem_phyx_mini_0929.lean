import Mathlib
import Physlib.Electromagnetism.Basic
import Physlib.SpaceAndTime.Space.LengthUnit
import Physlib.Units.WithDim.Area

/- USER: The assigned Lean file did not exist when this autoformalization task began. -/

noncomputable section

namespace PhyXMiniProblems.ProblemPhyXMini0929

open Dimension

/-!
# Magnetic flux through a square loop bent through 90 degrees

The primary raster shows a `10 cm × 10 cm` wire loop folded along its
midline into two perpendicular `10 cm × 5 cm` rectangular panels.  A uniform
magnetic field has magnitude `0.050 T` and points down and to the right along
the bisector of the two oriented panel normals, making `45°` with each.

Dimensionful lengths, areas, magnetic-flux-density magnitudes, and magnetic
fluxes use Physlib's unit-independent `Dimensionful` quantities.  The full
field is Physlib's spacetime-dependent `Electromagnetism.MagneticField`.
Real numbers occur only as named-unit readouts, angles, dimensionless
directions, and displayed multiple-choice values.

Assumption/target split:

* governing laws: rectangular panel area, spatially uniform field
  calibration, planar flux `Phi = A (B dot n)`, and additivity over the two
  panels;
* previous-part results: none;
* figure/data readouts: the original `10 cm × 10 cm` square, two `5 cm` panel
  widths, the `90°` fold, the `0.050 T` field, and the figure-derived `45°`
  field-to-normal angles;
* current target conclusions: the exact idealized flux is `sqrt 2 / 4000 Wb`
  and its displayed-precision value uniquely matches choice B,
  `3.5 × 10⁻⁴ Wb`.

Neither target conclusion occurs in a setup field, premise structure, or
governing-law field.
-/

/-! ## Dimensionful quantities and coherent-SI readouts -/

/-- Magnetic flux density (tesla) has dimension `M T⁻¹ C⁻¹`. -/
def magneticFluxDensityDimension : Dimension :=
  M𝓭 * T𝓭⁻¹ * C𝓭⁻¹

/-- Magnetic flux (weber) has dimension magnetic flux density times area. -/
def magneticFluxDimension : Dimension :=
  magneticFluxDensityDimension * L𝓭 * L𝓭

/-- A nonnegative, unit-independent physical length. -/
abbrev LengthQuantity : Type :=
  Dimensionful (WithDim L𝓭 NNReal)

/-- A nonnegative, unit-independent physical area. -/
abbrev AreaQuantity : Type := DimArea

/-- A nonnegative, unit-independent magnetic-flux-density magnitude. -/
abbrev MagneticFluxDensityMagnitude : Type :=
  Dimensionful (WithDim magneticFluxDensityDimension NNReal)

/-- Signed magnetic flux through a coherently oriented spanning surface. -/
abbrev MagneticFluxQuantity : Type :=
  Dimensionful (WithDim magneticFluxDimension ℝ)

/-- Read a physical length in a selected named length unit. -/
def lengthReadout (unit : LengthUnit) (length : LengthQuantity) : ℝ :=
  ((length {UnitChoices.SI with length := unit}).val : ℝ)

/-- Read a physical area in the square of a selected named length unit. -/
def areaReadout (unit : LengthUnit) (area : AreaQuantity) : ℝ :=
  ((area {UnitChoices.SI with length := unit}).val : ℝ)

/-- Read a physical length in metres. -/
def lengthInMeters (length : LengthQuantity) : ℝ :=
  lengthReadout LengthUnit.meters length

/-- Read a physical length in centimetres, as used in the raster. -/
def lengthInCentimeters (length : LengthQuantity) : ℝ :=
  lengthReadout LengthUnit.centimeters length

/-- Read a physical area in square metres. -/
def areaInSquareMeters (area : AreaQuantity) : ℝ :=
  areaReadout LengthUnit.meters area

/-- Read magnetic flux density in coherent-SI teslas. -/
def magneticFluxDensityInTeslas
    (magnitude : MagneticFluxDensityMagnitude) : ℝ :=
  ((magnitude UnitChoices.SI).val : ℝ)

/-- Read signed magnetic flux in coherent-SI webers. -/
def magneticFluxInWebers (flux : MagneticFluxQuantity) : ℝ :=
  (flux UnitChoices.SI).val

/-- Convert the degree readings used by the problem and raster to radians. -/
def degreesToRadians (degrees : ℝ) : ℝ :=
  degrees * Real.pi / 180

/-! ## Bent-loop geometry and primary-raster vocabulary -/

/-- The two rectangular halves created by folding the square at its midline. -/
inductive LoopPanel where
  | leftFiveCentimeterPanel
  | rightFiveCentimeterPanel
  deriving DecidableEq, Fintype, Repr

/-- Qualitative direction of the blue field arrows in the supplied view. -/
inductive DiagramArrowDirection where
  | downAndRight
  | upAndLeft
  | other
  deriving DecidableEq, Repr

/-- Named visual features visible in `phyx_data/test_image/929.png`. -/
inductive FigureFeature where
  | orangeBentWireLoop
  | twoRectangularPanels
  | leftFiveCentimeterLabel
  | rightFiveCentimeterLabel
  | tenCentimeterLabel
  | repeatedBlueFieldArrows
  | magneticFieldVectorLabel
  | dashedAngleReference
  | fortyFiveDegreeMarker
  deriving DecidableEq, Fintype, Repr

/-!
Literal diagram and problem-statement data.  The field strength and right-angle
fold are supplied in the prose; the other fields record labels and qualitative
features visible in the raster.  No magnetic-flux answer is stored here.
-/
structure BentLoopProblemFigure where
  shows : FigureFeature → Bool
  printedLongSideCentimeters : ℝ
  printedPanelWidthCentimeters : LoopPanel → ℝ
  statedBendAngleDegrees : ℝ
  statedFieldStrengthTeslas : ℝ
  printedFieldAngleDegrees : ℝ
  fieldArrowDirection : DiagramArrowDirection
  fieldArrowsParallel : Bool
  fieldArrowsUniformlySpaced : Bool
  containsNumericalFluxReadout : Bool

/-!
The two planar patches form a spanning surface for the bent wire loop.
`orientedUnitNormal` uses one coherent orientation on that spanning surface.
-/
structure BentSquareLoopGeometry where
  originalSquareSide : LengthQuantity
  panelWidth : LoopPanel → LengthQuantity
  panelArea : LoopPanel → AreaQuantity
  panelSurface : LoopPanel → Set (Space 3)
  representativePoint : LoopPanel → Space 3
  orientedUnitNormal : LoopPanel → EuclideanSpace ℝ (Fin 3)
  bendAngleRadians : ℝ

/-!
Independent physical quantities and observables for the experiment.  In
particular, neither `panelFlux` nor `netMagneticFlux` is defined from an answer
choice or from the requested numerical result.
-/
structure BentLoopMagneticFluxSetup where
  loop : BentSquareLoopGeometry
  observationTime : Time
  magneticField : Electromagnetism.MagneticField 3
  magneticFluxDensityMagnitude : MagneticFluxDensityMagnitude
  fieldDirection : EuclideanSpace ℝ (Fin 3)
  panelFlux : LoopPanel → MagneticFluxQuantity
  netMagneticFlux : MagneticFluxQuantity
  figure : BentLoopProblemFigure

/-! ## Figure/data readouts and physical assumptions -/

/-!
Direct source and raster readouts.  The two `5 cm` widths sum to the second
`10 cm` side of the original square.  The source gives the field strength and
right-angle bend, while the dashed marker gives the `45°` directional datum.
No flux value or answer label occurs in this structure.
-/
structure MatchesProblemAndPrimaryFigure
    (setup : BentLoopMagneticFluxSetup) : Prop where
  everyNamedFeatureShown :
    ∀ feature, setup.figure.shows feature = true
  longSideLabel : setup.figure.printedLongSideCentimeters = 10
  panelWidthLabels : ∀ panel,
    setup.figure.printedPanelWidthCentimeters panel = 5
  longSideLabelCalibration :
    lengthInCentimeters setup.loop.originalSquareSide =
      setup.figure.printedLongSideCentimeters
  panelWidthLabelCalibration : ∀ panel,
    lengthInCentimeters (setup.loop.panelWidth panel) =
      setup.figure.printedPanelWidthCentimeters panel
  bendAngleStatement : setup.figure.statedBendAngleDegrees = 90
  bendAngleCalibration :
    setup.loop.bendAngleRadians =
      degreesToRadians setup.figure.statedBendAngleDegrees
  fieldStrengthStatement : setup.figure.statedFieldStrengthTeslas = 1 / 20
  fieldStrengthCalibration :
    magneticFluxDensityInTeslas setup.magneticFluxDensityMagnitude =
      setup.figure.statedFieldStrengthTeslas
  fieldAngleLabel : setup.figure.printedFieldAngleDegrees = 45
  fieldPointsDownAndRight :
    setup.figure.fieldArrowDirection = .downAndRight
  parallelFieldArrows : setup.figure.fieldArrowsParallel = true
  uniformlySpacedFieldArrows :
    setup.figure.fieldArrowsUniformlySpaced = true
  noFluxValueInFigure :
    setup.figure.containsNumericalFluxReadout = false

/-- Positivity, non-vacuity, and unit-direction conditions for the setup. -/
structure HasPhysicalBentLoopConfiguration
    (setup : BentLoopMagneticFluxSetup) : Prop where
  originalSidePositive :
    0 < lengthInMeters setup.loop.originalSquareSide
  panelWidthsPositive : ∀ panel,
    0 < lengthInMeters (setup.loop.panelWidth panel)
  panelAreasPositive : ∀ panel,
    0 < areaInSquareMeters (setup.loop.panelArea panel)
  fieldMagnitudePositive :
    0 < magneticFluxDensityInTeslas setup.magneticFluxDensityMagnitude
  fieldDirectionIsUnit : ‖setup.fieldDirection‖ = 1
  panelSurfacesNonempty : ∀ panel,
    (setup.loop.panelSurface panel).Nonempty

/-!
Geometric laws for folding a `10 cm × 10 cm` square along its midline.  Each
panel is a rectangle with the original side as its long side, the two widths
make the other original side, the sample points lie on their panels, and the
oriented normals meet at the stated bend angle.
-/
structure SatisfiesBentSquareGeometry
    (setup : BentLoopMagneticFluxSetup) : Prop where
  panelAreaIsRectangleArea : ∀ unit panel,
    areaReadout unit (setup.loop.panelArea panel) =
      lengthReadout unit setup.loop.originalSquareSide *
        lengthReadout unit (setup.loop.panelWidth panel)
  panelWidthsMakeOriginalSide :
    (∑ panel : LoopPanel,
        lengthInMeters (setup.loop.panelWidth panel)) =
      lengthInMeters setup.loop.originalSquareSide
  representativePointOnPanel : ∀ panel,
    setup.loop.representativePoint panel ∈ setup.loop.panelSurface panel
  panelNormalsAreUnit : ∀ panel,
    ‖setup.loop.orientedUnitNormal panel‖ = 1
  normalsMeetAtBendAngle :
    InnerProductGeometry.angle
        (setup.loop.orientedUnitNormal .leftFiveCentimeterPanel)
        (setup.loop.orientedUnitNormal .rightFiveCentimeterPanel) =
      setup.loop.bendAngleRadians

/-!
Figure-derived three-dimensional orientation.  The right-angle fold and the
blue arrow's `45°` bisector placement make the field direction meet each
coherently oriented panel normal at the displayed acute angle.
-/
structure SatisfiesFigureDerivedFieldPanelGeometry
    (setup : BentLoopMagneticFluxSetup) : Prop where
  fieldAngleToEachPanelNormal : ∀ panel,
    InnerProductGeometry.angle setup.fieldDirection
        (setup.loop.orientedUnitNormal panel) =
      degreesToRadians setup.figure.printedFieldAngleDegrees

/-!
Uniform-field idealization on the time slice containing the loop.  Physlib's
field components are calibrated as tesla readouts by the independent
dimensionful magnitude and unit direction.  This premise mentions no flux.
-/
structure SatisfiesUniformMagneticFieldModel
    (setup : BentLoopMagneticFluxSetup) : Prop where
  fieldIsSpatiallyUniform : ∀ position : Space 3,
    setup.magneticField setup.observationTime position =
      magneticFluxDensityInTeslas setup.magneticFluxDensityMagnitude •
        setup.fieldDirection

/-!
For each planar panel, `Phi = A (B dot n)` in coherent SI units.  The net
signed flux through the coherently oriented bent spanning surface is the sum
of the two panel contributions.  These are general governing laws, not the
requested numerical result.
-/
structure SatisfiesTwoPanelMagneticFluxLaws
    (setup : BentLoopMagneticFluxSetup) : Prop where
  planarPanelFlux : ∀ panel,
    magneticFluxInWebers (setup.panelFlux panel) =
      areaInSquareMeters (setup.loop.panelArea panel) *
        inner ℝ
          (setup.magneticField setup.observationTime
            (setup.loop.representativePoint panel))
          (setup.loop.orientedUnitNormal panel)
  netFluxIsPanelSum :
    magneticFluxInWebers setup.netMagneticFlux =
      ∑ panel : LoopPanel,
        magneticFluxInWebers (setup.panelFlux panel)

/-! ## Exact flux, displayed choices, and target -/

/-!
Each panel has area `0.10 m × 0.05 m`, and each receives the normal field
component `0.050 T × cos 45°`.  Adding both panel contributions gives the
exact idealized flux `sqrt 2 / 4000 Wb`.
-/
lemma bentLoopMagneticFlux_exact
    (setup : BentLoopMagneticFluxSetup)
    (hFigure : MatchesProblemAndPrimaryFigure setup)
    (hPhysical : HasPhysicalBentLoopConfiguration setup)
    (hLoopGeometry : SatisfiesBentSquareGeometry setup)
    (hFieldGeometry : SatisfiesFigureDerivedFieldPanelGeometry setup)
    (hUniformField : SatisfiesUniformMagneticFieldModel setup)
    (hFluxLaws : SatisfiesTwoPanelMagneticFluxLaws setup) :
    magneticFluxInWebers setup.netMagneticFlux =
      Real.sqrt 2 / 4000 := by
  have length_centimeters_eq (length : LengthQuantity) :
      lengthInCentimeters length = 100 * lengthInMeters length := by
    have h := congrArg (fun value ↦ ((value.val : NNReal) : ℝ))
      (length.2 UnitChoices.SI
        {UnitChoices.SI with length := LengthUnit.centimeters})
    norm_num [lengthInCentimeters, lengthInMeters, lengthReadout,
      UnitChoices.dimScale, LengthUnit.centimeters, LengthUnit.meters,
      LengthUnit.scale, LengthUnit.div_eq_val, NNReal.smul_def,
      smul_eq_mul] at h ⊢
    exact h
  have hLongSide :
      lengthInMeters setup.loop.originalSquareSide = 1 / 10 := by
    have h := length_centimeters_eq setup.loop.originalSquareSide
    rw [hFigure.longSideLabelCalibration, hFigure.longSideLabel] at h
    norm_num at h ⊢
    linarith
  have hPanelWidth (panel : LoopPanel) :
      lengthInMeters (setup.loop.panelWidth panel) = 1 / 20 := by
    have h := length_centimeters_eq (setup.loop.panelWidth panel)
    rw [hFigure.panelWidthLabelCalibration panel,
      hFigure.panelWidthLabels panel] at h
    norm_num at h ⊢
    linarith
  have hPanelArea (panel : LoopPanel) :
      areaInSquareMeters (setup.loop.panelArea panel) = 1 / 200 := by
    have h := hLoopGeometry.panelAreaIsRectangleArea LengthUnit.meters panel
    change
      areaInSquareMeters (setup.loop.panelArea panel) =
        lengthInMeters setup.loop.originalSquareSide *
          lengthInMeters (setup.loop.panelWidth panel) at h
    rw [hLongSide, hPanelWidth panel] at h
    norm_num at h ⊢
    exact h
  have hFieldMagnitude :
      magneticFluxDensityInTeslas setup.magneticFluxDensityMagnitude =
        1 / 20 := by
    rw [hFigure.fieldStrengthCalibration, hFigure.fieldStrengthStatement]
  have hPanelAngle (panel : LoopPanel) :
      InnerProductGeometry.angle setup.fieldDirection
          (setup.loop.orientedUnitNormal panel) =
        Real.pi / 4 := by
    rw [hFieldGeometry.fieldAngleToEachPanelNormal,
      hFigure.fieldAngleLabel]
    norm_num [degreesToRadians]
    ring
  have hDirectionInnerNormal (panel : LoopPanel) :
      inner ℝ setup.fieldDirection
          (setup.loop.orientedUnitNormal panel) =
        Real.sqrt 2 / 2 := by
    rw [InnerProductGeometry.inner_eq_cos_angle_of_norm_eq_one
      hPhysical.fieldDirectionIsUnit
      (hLoopGeometry.panelNormalsAreUnit panel),
      hPanelAngle panel, Real.cos_pi_div_four]
  have hPanelFlux (panel : LoopPanel) :
      magneticFluxInWebers (setup.panelFlux panel) =
        Real.sqrt 2 / 8000 := by
    rw [hFluxLaws.planarPanelFlux, hPanelArea panel,
      hUniformField.fieldIsSpatiallyUniform, hFieldMagnitude,
      real_inner_smul_left, hDirectionInnerNormal panel]
    ring
  rw [hFluxLaws.netFluxIsPanelSum]
  rw [show (Finset.univ : Finset LoopPanel) =
      {.leftFiveCentimeterPanel, .rightFiveCentimeterPanel} by
    ext panel
    fin_cases panel <;> simp]
  rw [Finset.sum_insert (by simp), Finset.sum_singleton]
  rw [hPanelFlux, hPanelFlux]
  ring

/-- Labels of the four magnetic-flux choices printed with the question. -/
inductive AnswerChoice where
  | A
  | B
  | C
  | D
  deriving DecidableEq, Fintype, Repr

/-- Magnetic-flux magnitude in webers displayed beside an answer choice. -/
def displayedMagneticFluxInWebers : AnswerChoice → ℝ
  | .A => 42 / 100000
  | .B => 35 / 100000
  | .C => 31 / 100000
  | .D => 16 / 100000

/-- The answer label recorded by the source dataset, retained as metadata. -/
def recordedDatasetAnswer : AnswerChoice := .B

/-!
The choices are displayed to a resolution of `0.1 × 10⁻⁴ Wb`; matching at
that precision means lying within half that resolution.  Absolute flux makes
the comparison independent of which coherent loop orientation was selected.
-/
def MatchesDisplayedFluxAtShownPrecision
    (setup : BentLoopMagneticFluxSetup) (choice : AnswerChoice) : Prop :=
  abs
      (abs (magneticFluxInWebers setup.netMagneticFlux) -
        displayedMagneticFluxInWebers choice) ≤
    1 / 200000

/-- A choice is the sole displayed value matching the modeled physical flux. -/
def IsUniqueMatchingDisplayedChoice
    (setup : BentLoopMagneticFluxSetup) (choice : AnswerChoice) : Prop :=
  MatchesDisplayedFluxAtShownPrecision setup choice ∧
    ∀ other : AnswerChoice,
      MatchesDisplayedFluxAtShownPrecision setup other → other = choice

/-!
The exact idealized flux is `sqrt 2 / 4000 Wb`, approximately
`3.5 × 10⁻⁴ Wb` at the precision of the displayed choices.  Thus choice B is
the unique matching answer.

This declaration formalizes blueprint label
`thm:physics:phyx_mini_0929:target`.
-/
theorem problem_phyx_mini_0929
    (setup : BentLoopMagneticFluxSetup)
    (hFigure : MatchesProblemAndPrimaryFigure setup)
    (hPhysical : HasPhysicalBentLoopConfiguration setup)
    (hLoopGeometry : SatisfiesBentSquareGeometry setup)
    (hFieldGeometry : SatisfiesFigureDerivedFieldPanelGeometry setup)
    (hUniformField : SatisfiesUniformMagneticFieldModel setup)
    (hFluxLaws : SatisfiesTwoPanelMagneticFluxLaws setup) :
    magneticFluxInWebers setup.netMagneticFlux =
        Real.sqrt 2 / 4000 ∧
      IsUniqueMatchingDisplayedChoice setup recordedDatasetAnswer := by
  have hExact :=
    bentLoopMagneticFlux_exact setup hFigure hPhysical hLoopGeometry
      hFieldGeometry hUniformField hFluxLaws
  refine ⟨hExact, ?_⟩
  have hSqrtNonnegative : 0 ≤ Real.sqrt 2 := Real.sqrt_nonneg 2
  have hSqrtSquared : (Real.sqrt 2) ^ 2 = 2 := by
    norm_num
  have hSqrtLower : (69 : ℝ) / 50 ≤ Real.sqrt 2 := by
    nlinarith
  have hSqrtUpper : Real.sqrt 2 ≤ (71 : ℝ) / 50 := by
    nlinarith
  have hFluxNonnegative :
      0 ≤ magneticFluxInWebers setup.netMagneticFlux := by
    rw [hExact]
    positivity
  unfold IsUniqueMatchingDisplayedChoice
  constructor
  · unfold MatchesDisplayedFluxAtShownPrecision
    rw [abs_of_nonneg hFluxNonnegative, hExact, abs_le]
    norm_num [displayedMagneticFluxInWebers, recordedDatasetAnswer]
    constructor <;> nlinarith
  · intro other hOther
    unfold MatchesDisplayedFluxAtShownPrecision at hOther
    rw [abs_of_nonneg hFluxNonnegative, hExact, abs_le] at hOther
    fin_cases other
    · norm_num [displayedMagneticFluxInWebers] at hOther
      nlinarith
    · rfl
    · norm_num [displayedMagneticFluxInWebers] at hOther
      nlinarith
    · norm_num [displayedMagneticFluxInWebers] at hOther
      nlinarith

end PhyXMiniProblems.ProblemPhyXMini0929
