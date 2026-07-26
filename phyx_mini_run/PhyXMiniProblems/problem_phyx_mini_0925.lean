import Mathlib
import Physlib.Electromagnetism.Basic
import Physlib.Units.WithDim.Area

/- USER: The assigned source file did not exist when this autoformalization task began. -/

noncomputable section

namespace PhyXMiniProblems.ProblemPhyXMini0925

open Dimension

/-!
# Magnetic flux through a tilted loop around a solenoid

A `2.0 cm`-diameter solenoid passes through the center of a circular
`6.0 cm`-diameter loop.  Its magnetic field has magnitude `0.20 T` inside the
solenoid and is taken to vanish outside.  In the primary raster the loop is
shown edge-on in orange, the solenoid is horizontal, and an arc marks `60°`
between the loop plane and a transverse reference line.

Tilting does not insert a net cosine factor into the answer.  The area of the
loop surface lying inside the solenoid grows by the reciprocal projection
factor, while its component perpendicular to the field is exactly the
solenoid cross-section.  Thus the flux is the field magnitude times the
solenoid cross-sectional area, not the field magnitude times the full area of
the larger loop.

Physical lengths, areas, magnetic-flux density, and magnetic flux are
unit-independent Physlib `Dimensionful` quantities.  Real numbers occur only
as coherent-unit readouts, dimensionless angle/cosine data, vector
coordinates, and answer-choice readouts.

Assumption/target split:

* governing laws: circular disk-area geometry, the cosine projection relation
  for the threaded part of the tilted loop, equality of that projection with
  the solenoid cross-section, spatially uniform field inside and zero field
  outside the solenoid, and the uniform-field magnetic surface-flux law;
* previous-part results: none;
* figure/data readouts: solenoid diameter `2.0 cm`, loop diameter `6.0 cm`,
  interior field `0.20 T`, common center, the two visible orange loop pieces,
  the transverse reference line, angle arc, and displayed `60°`;
* current target conclusions: the exact flux is `π / 50000 Wb`, it rounds to
  `6.3 * 10⁻⁵ Wb`, and choice B is closest among the displayed choices.

No target conclusion is a field or premise of a setup, data, geometry, field,
or flux-law structure.
-/

/-! ## Dimensionful physical quantities and coherent-SI readouts -/

/-- Magnetic flux density (tesla) has physical dimension `M T⁻¹ C⁻¹`. -/
def magneticFluxDensityDimension : Dimension :=
  M𝓭 * T𝓭⁻¹ * C𝓭⁻¹

/-- Magnetic flux (weber) has physical dimension `M L² T⁻¹ C⁻¹`. -/
def magneticFluxDimension : Dimension :=
  magneticFluxDensityDimension * L𝓭 * L𝓭

/-- A nonnegative, unit-independent physical length. -/
abbrev LengthMagnitude : Type :=
  Dimensionful (WithDim L𝓭 NNReal)

/-- A nonnegative, unit-independent magnetic-flux-density magnitude. -/
abbrev MagneticFluxDensityMagnitude : Type :=
  Dimensionful (WithDim magneticFluxDensityDimension NNReal)

/-- Signed magnetic flux relative to the selected loop area normal. -/
abbrev SignedMagneticFlux : Type :=
  Dimensionful (WithDim magneticFluxDimension ℝ)

/-- Coherent-SI readout of a nonnegative dimensionful quantity. -/
def nonnegativeSIReadout {d : Dimension}
    (quantity : Dimensionful (WithDim d NNReal)) : ℝ :=
  ((quantity UnitChoices.SI).val : ℝ)

/-- Read a physical length in coherent-SI metres. -/
def lengthInMeters (length : LengthMagnitude) : ℝ :=
  nonnegativeSIReadout length

/-- Read a physical length in centimetres. -/
def lengthInCentimeters (length : LengthMagnitude) : ℝ :=
  100 * lengthInMeters length

/-- Read a physical area in coherent-SI square metres. -/
def areaInSquareMeters (area : DimArea) : ℝ :=
  nonnegativeSIReadout area

/-- Read magnetic flux density in coherent-SI teslas. -/
def magneticFluxDensityInTeslas
    (field : MagneticFluxDensityMagnitude) : ℝ :=
  nonnegativeSIReadout field

/-- Read signed magnetic flux in coherent-SI webers. -/
def magneticFluxInWebers (flux : SignedMagneticFlux) : ℝ :=
  (flux UnitChoices.SI).val

/-- Convert the dimensionless degree readout used in the figure to radians. -/
def degreesToRadians (angleDegrees : ℝ) : ℝ :=
  angleDegrees * Real.pi / 180

/-! ## Apparatus and primary-raster labels -/

/-- The two pieces of the orange loop visible on opposite sides of the body. -/
inductive VisibleLoopSection where
  | upperRight
  | lowerLeft
  deriving DecidableEq, Fintype, Repr

/-- The line from which the raster's marked tilt angle is measured. -/
inductive TiltAngleReference where
  | solenoidTransverseNormal
  deriving DecidableEq, Repr

/-- Topology asserted for the larger conductor. -/
inductive LoopTopology where
  | singleClosedCircularLoop
  deriving DecidableEq, Repr

/-- Idealized support of the solenoid field used by this problem. -/
inductive SolenoidFieldSupport where
  | confinedToInterior
  deriving DecidableEq, Repr

/-!
Literal, typed content read from image `925.png`.  The numerical angle is a
dimensionless displayed readout rather than a physical magnetic quantity.
-/
structure TiltedSolenoidLoopFigure where
  horizontalSolenoidBodyShown : Bool
  visibleLoopSectionShown : VisibleLoopSection → Bool
  loopSectionsColoredOrange : Bool
  loopPassesBehindSolenoidBody : Bool
  loopPassesThroughBodyCenter : Bool
  transverseReferenceLineShown : Bool
  tiltAngleArcShown : Bool
  tiltAngleReference : TiltAngleReference
  displayedTiltAngleDegrees : ℝ

/-!
Independent apparatus data.  In particular, `loopMagneticFlux` and all four
areas are observables; none is defined from an answer choice or from the
requested numerical flux.
-/
structure TiltedSolenoidLoopSetup where
  loopTopology : LoopTopology
  fieldSupport : SolenoidFieldSupport
  solenoidDiameter : LengthMagnitude
  loopDiameter : LengthMagnitude
  solenoidCrossSectionArea : DimArea
  fullLoopDiskArea : DimArea
  threadedLoopSurfaceArea : DimArea
  projectedThreadedArea : DimArea
  magneticFluxDensityMagnitude : MagneticFluxDensityMagnitude
  loopMagneticFlux : SignedMagneticFlux
  magneticField : Electromagnetism.MagneticField 3
  solenoidInterior : Set (Space 3)
  loopSurface : Set (Space 3)
  threadedLoopRegion : Set (Space 3)
  solenoidCenter : Space 3
  loopCenter : Space 3
  solenoidAxisUnit : EuclideanSpace ℝ (Fin 3)
  positiveLoopAreaNormalUnit : EuclideanSpace ℝ (Fin 3)
  fieldNormalAngleRadians : ℝ
  figure : TiltedSolenoidLoopFigure

/-! ## Problem data, image evidence, and governing laws -/

/-- Numerical and qualitative information supplied by the problem prose. -/
structure MatchesProblemDescription
    (setup : TiltedSolenoidLoopSetup) : Prop where
  topologyIsClosedCircularLoop :
    setup.loopTopology = .singleClosedCircularLoop
  fieldIsConfinedToSolenoid :
    setup.fieldSupport = .confinedToInterior
  solenoidDiameterInCentimeters :
    lengthInCentimeters setup.solenoidDiameter = 2
  loopDiameterInCentimeters :
    lengthInCentimeters setup.loopDiameter = 6
  magneticFluxDensityInTeslas :
    magneticFluxDensityInTeslas setup.magneticFluxDensityMagnitude = 1 / 5
  loopAndSolenoidHaveCommonCenter :
    setup.loopCenter = setup.solenoidCenter

/-- Facts transcribed from the supplied raster rather than its noisy caption. -/
structure MatchesPrimaryTiltFigure
    (setup : TiltedSolenoidLoopSetup) : Prop where
  solenoidShownHorizontally :
    setup.figure.horizontalSolenoidBodyShown = true
  upperLoopSectionShown :
    setup.figure.visibleLoopSectionShown .upperRight = true
  lowerLoopSectionShown :
    setup.figure.visibleLoopSectionShown .lowerLeft = true
  loopIsOrange : setup.figure.loopSectionsColoredOrange = true
  loopOccludedByBody : setup.figure.loopPassesBehindSolenoidBody = true
  loopShownThroughCenter :
    setup.figure.loopPassesThroughBodyCenter = true
  transverseReferenceShown :
    setup.figure.transverseReferenceLineShown = true
  angleArcShown : setup.figure.tiltAngleArcShown = true
  angleMeasuredFromTransverseNormal :
    setup.figure.tiltAngleReference = .solenoidTransverseNormal
  displayedAngleIsSixtyDegrees :
    setup.figure.displayedTiltAngleDegrees = 60

/-- Positivity and fit conditions for the stated physical apparatus. -/
structure HasPhysicalSolenoidLoopParameters
    (setup : TiltedSolenoidLoopSetup) : Prop where
  positiveSolenoidDiameter : 0 < lengthInMeters setup.solenoidDiameter
  positiveLoopDiameter : 0 < lengthInMeters setup.loopDiameter
  solenoidFitsWithinLoop :
    lengthInMeters setup.solenoidDiameter <
      lengthInMeters setup.loopDiameter
  positiveInteriorField :
    0 < magneticFluxDensityInTeslas setup.magneticFluxDensityMagnitude

/-- Both stated diameters determine ordinary circular-disk areas. -/
structure SatisfiesCircularAreaGeometry
    (setup : TiltedSolenoidLoopSetup) : Prop where
  solenoidCrossSectionIsCircular :
    areaInSquareMeters setup.solenoidCrossSectionArea =
      Real.pi * (lengthInMeters setup.solenoidDiameter / 2) ^ 2
  fullLoopAreaIsCircular :
    areaInSquareMeters setup.fullLoopDiskArea =
      Real.pi * (lengthInMeters setup.loopDiameter / 2) ^ 2

/-!
The marked plane angle equals the angle between the solenoid axis and the loop
area normal.  Orthogonal projection multiplies the threaded surface area by
the corresponding cosine.  Centering and containment make that projection
exactly the solenoid cross-section.  These are geometric laws; they do not
mention magnetic flux or an answer value.
-/
structure SatisfiesTiltedThreadingGeometry
    (setup : TiltedSolenoidLoopSetup) : Prop where
  solenoidAxisIsUnit : ‖setup.solenoidAxisUnit‖ = 1
  loopAreaNormalIsUnit : ‖setup.positiveLoopAreaNormalUnit‖ = 1
  markedAngleDeterminesFieldNormalAngle :
    setup.fieldNormalAngleRadians =
      degreesToRadians setup.figure.displayedTiltAngleDegrees
  axisNormalInnerProduct :
    inner ℝ setup.solenoidAxisUnit setup.positiveLoopAreaNormalUnit =
      Real.cos setup.fieldNormalAngleRadians
  threadedRegionIsFieldIntersection :
    setup.threadedLoopRegion = setup.loopSurface ∩ setup.solenoidInterior
  obliqueAreaProjectionLaw :
    areaInSquareMeters setup.projectedThreadedArea =
      inner ℝ setup.solenoidAxisUnit setup.positiveLoopAreaNormalUnit *
        areaInSquareMeters setup.threadedLoopSurfaceArea
  projectionCoversSolenoidCrossSection :
    areaInSquareMeters setup.projectedThreadedArea =
      areaInSquareMeters setup.solenoidCrossSectionArea
  threadedRegionFitsInLoop :
    areaInSquareMeters setup.threadedLoopSurfaceArea ≤
      areaInSquareMeters setup.fullLoopDiskArea

/-!
Physlib's vector field is interpreted in tesla coordinates.  It is uniform
and axial throughout the solenoid interior and vanishes outside, faithfully
encoding the field-confinement idealization responsible for using the small
solenoid cross-section rather than the full loop area.
-/
structure ModelsUniformConfinedSolenoidField
    (setup : TiltedSolenoidLoopSetup) : Prop where
  uniformAxialFieldInside : ∀ time position,
    position ∈ setup.solenoidInterior →
      setup.magneticField time position =
        magneticFluxDensityInTeslas setup.magneticFluxDensityMagnitude •
          setup.solenoidAxisUnit
  zeroFieldOutside : ∀ time position,
    position ∉ setup.solenoidInterior →
      setup.magneticField time position = 0

/-!
For a uniform field, the oriented surface flux is the field magnitude times
the normal cosine times the actual threaded surface area.  The law is stated
before substituting either the projection geometry or any numerical data.
-/
structure SatisfiesUniformMagneticSurfaceFluxLaw
    (setup : TiltedSolenoidLoopSetup) : Prop where
  fluxOfThreadedLoopSurface :
    magneticFluxInWebers setup.loopMagneticFlux =
      magneticFluxDensityInTeslas setup.magneticFluxDensityMagnitude *
        inner ℝ setup.solenoidAxisUnit setup.positiveLoopAreaNormalUnit *
          areaInSquareMeters setup.threadedLoopSurfaceArea

/-! ## Displayed answer choices -/

/-- Multiple-choice labels in the source problem. -/
inductive AnswerChoice where
  | A
  | B
  | C
  | D
  deriving DecidableEq, Fintype, Repr

/-- Magnetic-flux readout in webers printed beside each answer choice. -/
def displayedFluxInWebers : AnswerChoice → ℝ
  | .A => 63 / 10000000
  | .B => 63 / 1000000
  | .C => 63 / 100000
  | .D => 63 / 100000000

/-- Resolution of the final displayed digit of each two-significant-figure value. -/
def displayedFluxResolutionInWebers : AnswerChoice → ℝ
  | .A => 1 / 10000000
  | .B => 1 / 1000000
  | .C => 1 / 100000
  | .D => 1 / 100000000

/-- The physical flux rounds to a displayed choice at its stated resolution. -/
def RoundsToDisplayedFlux
    (setup : TiltedSolenoidLoopSetup) (choice : AnswerChoice) : Prop :=
  |magneticFluxInWebers setup.loopMagneticFlux -
      displayedFluxInWebers choice| ≤
    displayedFluxResolutionInWebers choice / 2

/-- A selected answer is no farther from the physical flux than any other. -/
def IsClosestDisplayedChoice
    (setup : TiltedSolenoidLoopSetup) (choice : AnswerChoice) : Prop :=
  ∀ otherChoice,
    |magneticFluxInWebers setup.loopMagneticFlux -
        displayedFluxInWebers choice| ≤
      |magneticFluxInWebers setup.loopMagneticFlux -
        displayedFluxInWebers otherChoice|

/-- The answer label recorded in the dataset metadata. -/
def recordedDatasetAnswer : AnswerChoice := .B

/-!
Blueprint label: `thm:physics:phyx_mini_0925:target`.

The exact flux is `0.20 * π * (0.010)^2 = π / 50000 Wb`.  Its two-significant-
figure readout is `6.3 * 10⁻⁵ Wb`, answer B.  The 60-degree tilt remains in
the premises through the independent surface-area and projection laws; it is
not discarded or used to multiply the solenoid cross-section by an extra
cosine.
-/
theorem problem_phyx_mini_0925
    (setup : TiltedSolenoidLoopSetup)
    (_description : MatchesProblemDescription setup)
    (_figure : MatchesPrimaryTiltFigure setup)
    (_physical : HasPhysicalSolenoidLoopParameters setup)
    (_circularGeometry : SatisfiesCircularAreaGeometry setup)
    (_tiltGeometry : SatisfiesTiltedThreadingGeometry setup)
    (_fieldModel : ModelsUniformConfinedSolenoidField setup)
    (_fluxLaw : SatisfiesUniformMagneticSurfaceFluxLaw setup) :
    magneticFluxInWebers setup.loopMagneticFlux = Real.pi / 50000 ∧
      RoundsToDisplayedFlux setup .B ∧
        IsClosestDisplayedChoice setup .B := by
  have hSolenoidDiameterMeters :
      lengthInMeters setup.solenoidDiameter = 1 / 50 := by
    have hDiameter :=
      _description.solenoidDiameterInCentimeters
    rw [lengthInCentimeters] at hDiameter
    linarith only [hDiameter]
  have hSolenoidCrossSection :
      areaInSquareMeters setup.solenoidCrossSectionArea =
        Real.pi / 10000 := by
    rw [_circularGeometry.solenoidCrossSectionIsCircular,
      hSolenoidDiameterMeters]
    ring
  have hExactFlux :
      magneticFluxInWebers setup.loopMagneticFlux =
        Real.pi / 50000 := by
    calc
      magneticFluxInWebers setup.loopMagneticFlux =
          magneticFluxDensityInTeslas
              setup.magneticFluxDensityMagnitude *
            inner ℝ setup.solenoidAxisUnit
              setup.positiveLoopAreaNormalUnit *
            areaInSquareMeters setup.threadedLoopSurfaceArea :=
        _fluxLaw.fluxOfThreadedLoopSurface
      _ =
          magneticFluxDensityInTeslas
              setup.magneticFluxDensityMagnitude *
            areaInSquareMeters setup.projectedThreadedArea := by
        rw [mul_assoc,
          ← _tiltGeometry.obliqueAreaProjectionLaw]
      _ =
          magneticFluxDensityInTeslas
              setup.magneticFluxDensityMagnitude *
            areaInSquareMeters setup.solenoidCrossSectionArea := by
        rw [_tiltGeometry.projectionCoversSolenoidCrossSection]
      _ = (1 / 5 : ℝ) * (Real.pi / 10000) := by
        rw [_description.magneticFluxDensityInTeslas,
          hSolenoidCrossSection]
      _ = Real.pi / 50000 := by ring
  have hRounds :
      RoundsToDisplayedFlux setup .B := by
    unfold RoundsToDisplayedFlux
    rw [hExactFlux]
    simp only [displayedFluxInWebers,
      displayedFluxResolutionInWebers]
    rw [abs_le]
    constructor <;>
      linarith only [Real.pi_gt_d2, Real.pi_lt_d2]
  refine ⟨hExactFlux, hRounds, ?_⟩
  unfold IsClosestDisplayedChoice
  intro otherChoice
  rw [hExactFlux]
  fin_cases otherChoice
  · simp only [displayedFluxInWebers]
    rw [abs_of_neg (by linarith only [Real.pi_lt_d2]),
      abs_of_pos (by linarith only [Real.pi_gt_d2])]
    linarith only [Real.pi_gt_d2, Real.pi_lt_d2]
  · rfl
  · simp only [displayedFluxInWebers]
    rw [abs_of_neg (by linarith only [Real.pi_lt_d2]),
      abs_of_neg (by linarith only [Real.pi_lt_d2])]
    linarith only [Real.pi_gt_d2, Real.pi_lt_d2]
  · simp only [displayedFluxInWebers]
    rw [abs_of_neg (by linarith only [Real.pi_lt_d2]),
      abs_of_pos (by linarith only [Real.pi_gt_d2])]
    linarith only [Real.pi_gt_d2, Real.pi_lt_d2]

end PhyXMiniProblems.ProblemPhyXMini0925
