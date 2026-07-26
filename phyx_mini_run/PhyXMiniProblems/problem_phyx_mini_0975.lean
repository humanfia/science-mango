import Mathlib
import Physlib.Electromagnetism.Basic
import Physlib.Units.WithDim.Basic

/- USER: The assigned Lean file did not exist when this autoformalization task began. -/

noncomputable section

namespace PhyXMiniProblems.ProblemPhyXMini0975

open Dimension

/-!
# Magnetic flux through a radial-longitudinal rectangle inside a solid wire

A very long cylindrical wire of radius `R` carries total current `I₀`,
uniformly distributed over its circular cross section.  The primary image
shows a red rectangle whose axial side of length `W` runs along the wire axis
and whose radial side of length `R` reaches the cylindrical surface.  The
textbook phrase "very long" is represented below by an exact infinite-cylinder
model: its axis is parametrized by every real axial coordinate, and the field
law is imposed on every axial translate of the selected radial half-plane.
Thus the theorem is exact within that model and is not an uncontrolled
finite-wire approximation.

Physical scalar magnitudes are unit-independent Physlib `Dimensionful`
quantities.  Real numbers occur only as coherent-SI readouts, radial and axial
coordinates measured in metres, and scalar integrands.  The underlying
current density and magnetic field retain Physlib's spacetime field types.

Assumption/target split:

* governing laws: exact axially unbounded cylindrical geometry, uniform axial
  current density, current obtained by integrating that density over circular
  cross sections, cylindrical Ampere's law at every axial coordinate, the
  azimuthal field profile, and magnetic flux as the surface integral over the
  radial-longitudinal rectangle;
* previous-part results: none;
* figure/data readouts: the long transparent cylinder, current label `I₀`,
  radius label `R`, axial-length label `W`, and the centered red rectangular
  strip extending from the axis to the wire surface;
* current target conclusion: the flux magnitude is
  `μ₀ I₀ W / (4 * pi)` in webers, corresponding to source choice B (where the
  choice writes the same total current as `I`).

The target flux value does not occur in the setup or in any premise structure.
-/

/-! ## Physical dimensions and coherent-SI readouts -/

/-- Electric current has dimension `C T⁻¹` (ampere). -/
def electricCurrentDimension : Dimension :=
  C𝓭 * T𝓭⁻¹

/-- Current density has dimension electric current per area. -/
def currentDensityDimension : Dimension :=
  electricCurrentDimension * L𝓭⁻¹ * L𝓭⁻¹

/-- Magnetic flux density has dimension `M T⁻¹ C⁻¹` (tesla). -/
def magneticFluxDensityDimension : Dimension :=
  M𝓭 * T𝓭⁻¹ * C𝓭⁻¹

/-- Magnetic flux has dimension magnetic flux density times area (weber). -/
def magneticFluxDimension : Dimension :=
  magneticFluxDensityDimension * L𝓭 * L𝓭

/-- Magnetic permeability has dimension `M L C⁻²` (henry per metre). -/
def magneticPermeabilityDimension : Dimension :=
  M𝓭 * L𝓭 * C𝓭⁻¹ * C𝓭⁻¹

/-- A nonnegative, unit-independent physical length. -/
abbrev LengthQuantity : Type :=
  Dimensionful (WithDim L𝓭 NNReal)

/-- A nonnegative, unit-independent electric-current magnitude. -/
abbrev ElectricCurrentMagnitude : Type :=
  Dimensionful (WithDim electricCurrentDimension NNReal)

/-- A nonnegative, unit-independent current-density magnitude. -/
abbrev CurrentDensityMagnitude : Type :=
  Dimensionful (WithDim currentDensityDimension NNReal)

/-- A nonnegative, unit-independent magnetic-flux-density magnitude. -/
abbrev MagneticFluxDensityMagnitude : Type :=
  Dimensionful (WithDim magneticFluxDensityDimension NNReal)

/-- A nonnegative magnetic-flux magnitude through the displayed rectangle. -/
abbrev MagneticFluxMagnitude : Type :=
  Dimensionful (WithDim magneticFluxDimension NNReal)

/-- A nonnegative, unit-independent magnetic permeability. -/
abbrev MagneticPermeabilityMagnitude : Type :=
  Dimensionful (WithDim magneticPermeabilityDimension NNReal)

/-- Read a nonnegative dimensionful quantity in coherent SI units. -/
def nonnegativeSIReadout {dimension : Dimension}
    (quantity : Dimensionful (WithDim dimension NNReal)) : ℝ :=
  ((quantity UnitChoices.SI).val : ℝ)

/-- Read a length in metres. -/
def lengthInMeters (length : LengthQuantity) : ℝ :=
  nonnegativeSIReadout length

/-- Read an electric-current magnitude in amperes. -/
def currentInAmperes (current : ElectricCurrentMagnitude) : ℝ :=
  nonnegativeSIReadout current

/-- Read a current-density magnitude in amperes per square metre. -/
def currentDensityInAmperesPerSquareMeter
    (density : CurrentDensityMagnitude) : ℝ :=
  nonnegativeSIReadout density

/-- Read a magnetic-flux-density magnitude in teslas. -/
def magneticFluxDensityInTeslas
    (field : MagneticFluxDensityMagnitude) : ℝ :=
  nonnegativeSIReadout field

/-- Read magnetic flux in webers. -/
def magneticFluxInWebers (flux : MagneticFluxMagnitude) : ℝ :=
  nonnegativeSIReadout flux

/-- Read magnetic permeability in henries per metre. -/
def permeabilityInHenriesPerMeter
    (permeability : MagneticPermeabilityMagnitude) : ℝ :=
  nonnegativeSIReadout permeability

/-! ## Primary-image vocabulary -/

/-- Named physical features visible in `phyx_data/test_image/975.png`. -/
inductive FigureFeature where
  | longTransparentCylinder
  | circularEndFace
  | centeredRedRectangularStrip
  | currentDirectionArrow
  | radialDimensionArrow
  | axialDimensionArrow
  deriving DecidableEq, Fintype, Repr

/-- The three labels printed in the source image. -/
inductive FigureLabel where
  | I₀
  | R
  | W
  deriving DecidableEq, Fintype, Repr

/-- Physical role of each printed label. -/
inductive FigureLabelRole where
  | totalWireCurrent
  | wireRadiusAndRectangleRadialExtent
  | rectangleAxialLength
  deriving DecidableEq, Repr

/-- Literal and qualitative evidence transcribed from the primary image. -/
structure CylindricalWireFigure where
  featureShown : FigureFeature → Bool
  labelShown : FigureLabel → Bool
  labelRole : FigureLabel → FigureLabelRole
  redStripCentrallyAligned : Bool
  redStripRunsLongitudinally : Bool
  containsNumericalFluxReadout : Bool

/-! ## Wire, rectangle, and electromagnetic observables -/

/-!
The ambient radial-longitudinal half-plane is parametrized by radial distance
and axial distance in metres.  Restricting the first coordinate to `[0, R]`
and the second to `[0, W]` gives the red spanning surface.  Keeping the map
defined for every axial coordinate also lets the infinite-wire field law state
exact axial translation invariance.
-/
structure RadialLongitudinalRectangle where
  surface : Set (Space 3)
  pointAtMeters : ℝ → ℝ → Space 3
  radialExtentR : LengthQuantity
  axialLengthW : LengthQuantity
  radialDirection : EuclideanSpace ℝ (Fin 3)
  axialDirection : EuclideanSpace ℝ (Fin 3)
  orientedNormal : EuclideanSpace ℝ (Fin 3)

/-!
Independent physical data and observables.  The scalar radial profiles are
dimensionful magnitudes used to calibrate Physlib's vector fields in SI units.
Neither `rectangleFlux` nor either field profile is defined by the requested
closed-form answer.
-/
structure InfiniteCylindricalWireFluxSetup where
  figure : CylindricalWireFigure
  wireRadiusR : LengthQuantity
  wireAxis : Set (Space 3)
  wireInterior : Set (Space 3)
  wireBoundary : Set (Space 3)
  axisPointAtMeters : ℝ → Space 3
  axialCoordinateInMeters : Space 3 → ℝ
  radialDistanceFromAxisInMeters : Space 3 → ℝ
  rectangle : RadialLongitudinalRectangle
  observationTime : Time
  axialCurrentDirection : EuclideanSpace ℝ (Fin 3)
  totalCurrentI₀ : ElectricCurrentMagnitude
  uniformCurrentDensityMagnitude : CurrentDensityMagnitude
  vacuumPermeabilityμ₀ : MagneticPermeabilityMagnitude
  currentDensity : Electromagnetism.CurrentDensity
  enclosedCurrentAtRadiusMeters : ℝ → ElectricCurrentMagnitude
  magneticField : Electromagnetism.MagneticField 3
  fluxDensityMagnitudeAtRadiusMeters :
    ℝ → MagneticFluxDensityMagnitude
  rectangleFlux : MagneticFluxMagnitude

/-! ## Problem, figure, and geometry readouts -/

/-!
The prose supplies the uniform-current scenario; the bitmap supplies the
named features and label roles.  The phrase "very long" is handled separately
by `SatisfiesExactInfiniteCylindricalGeometry`, rather than by a qualitative
regime field in this readout structure.  The side marked `R` is identified
with the physical wire radius, and the side marked `W` is the rectangle's
axial length.  No magnetic-flux result is stored here.
-/
structure MatchesProblemAndPrimaryFigure
    (setup : InfiniteCylindricalWireFluxSetup) : Prop where
  everyNamedFeatureShown :
    ∀ feature : FigureFeature, setup.figure.featureShown feature = true
  everyPrintedLabelShown :
    ∀ label : FigureLabel, setup.figure.labelShown label = true
  labelI₀IsTotalWireCurrent :
    setup.figure.labelRole .I₀ = .totalWireCurrent
  labelRHasRadialRole :
    setup.figure.labelRole .R = .wireRadiusAndRectangleRadialExtent
  labelWHasAxialRole :
    setup.figure.labelRole .W = .rectangleAxialLength
  stripIsCentered : setup.figure.redStripCentrallyAligned = true
  stripIsLongitudinal : setup.figure.redStripRunsLongitudinally = true
  noFluxValuePrinted : setup.figure.containsNumericalFluxReadout = false
  radialSideHasLengthR :
    setup.rectangle.radialExtentR = setup.wireRadiusR

/-- Positivity and non-vacuity conditions for the physical configuration. -/
structure HasPhysicalInfiniteWireConfiguration
    (setup : InfiniteCylindricalWireFluxSetup) : Prop where
  radiusPositive : 0 < lengthInMeters setup.wireRadiusR
  axialLengthPositive :
    0 < lengthInMeters setup.rectangle.axialLengthW
  totalCurrentPositive : 0 < currentInAmperes setup.totalCurrentI₀
  currentDensityPositive :
    0 < currentDensityInAmperesPerSquareMeter
      setup.uniformCurrentDensityMagnitude
  permeabilityPositive :
    0 < permeabilityInHenriesPerMeter setup.vacuumPermeabilityμ₀
  rectangleSurfaceNonempty : setup.rectangle.surface.Nonempty
  wireInteriorNonempty : setup.wireInterior.Nonempty

/-!
Exact geometric contract replacing the source's informal "very long" phrase.
The axis contains a point at every real axial coordinate, and the solid
cylinder has no axial cutoff: interior and boundary membership depend only on
distance from the axis.  This is an exact infinite-cylinder model, not a
finite-length regime flag used to assert an approximate field as an equality.
-/
structure SatisfiesExactInfiniteCylindricalGeometry
    (setup : InfiniteCylindricalWireFluxSetup) : Prop where
  axisIsParametrizedByAllRealAxialCoordinates :
    setup.wireAxis = Set.range setup.axisPointAtMeters
  axisCoordinateOfAxisPoint : ∀ axialMeters : ℝ,
    setup.axialCoordinateInMeters (setup.axisPointAtMeters axialMeters) =
      axialMeters
  axisIsExactlyZeroRadialDistance :
    setup.wireAxis =
      {point |
        setup.radialDistanceFromAxisInMeters point = 0}
  radialDistanceNonnegative : ∀ point : Space 3,
    0 ≤ setup.radialDistanceFromAxisInMeters point
  interiorIsExactUnboundedOpenCylinder :
    setup.wireInterior =
      {point |
        setup.radialDistanceFromAxisInMeters point <
          lengthInMeters setup.wireRadiusR}
  boundaryIsExactUnboundedCylindricalSurface :
    setup.wireBoundary =
      {point |
        setup.radialDistanceFromAxisInMeters point =
          lengthInMeters setup.wireRadiusR}

/-!
Geometric meaning of the centered radial-longitudinal rectangle.  The edge at
radial coordinate zero lies on the wire axis; the opposite edge lies on the
cylindrical boundary at radius `R`.  Its oriented normal is perpendicular to
both in-surface directions.
-/
structure SatisfiesRadialLongitudinalRectangleGeometry
    (setup : InfiniteCylindricalWireFluxSetup) : Prop where
  allParameterPointsOnRectangle : ∀ radialMeters axialMeters,
    radialMeters ∈ Set.Icc 0 (lengthInMeters setup.wireRadiusR) →
    axialMeters ∈
      Set.Icc 0 (lengthInMeters setup.rectangle.axialLengthW) →
    setup.rectangle.pointAtMeters radialMeters axialMeters ∈
      setup.rectangle.surface
  axialSideRunsDownWireCenter : ∀ axialMeters,
    axialMeters ∈
      Set.Icc 0 (lengthInMeters setup.rectangle.axialLengthW) →
    setup.rectangle.pointAtMeters 0 axialMeters ∈ setup.wireAxis
  outerAxialSideLiesOnWireBoundary : ∀ axialMeters,
    axialMeters ∈
      Set.Icc 0 (lengthInMeters setup.rectangle.axialLengthW) →
      setup.rectangle.pointAtMeters
        (lengthInMeters setup.wireRadiusR) axialMeters ∈
      setup.wireBoundary
  parameterRadialDistance : ∀ radialMeters axialMeters,
    radialMeters ∈ Set.Icc 0 (lengthInMeters setup.wireRadiusR) →
    setup.radialDistanceFromAxisInMeters
        (setup.rectangle.pointAtMeters radialMeters axialMeters) =
      radialMeters
  parameterAxialCoordinate : ∀ radialMeters axialMeters,
    radialMeters ∈ Set.Icc 0 (lengthInMeters setup.wireRadiusR) →
    setup.axialCoordinateInMeters
        (setup.rectangle.pointAtMeters radialMeters axialMeters) =
      axialMeters
  radialDirectionIsUnit : ‖setup.rectangle.radialDirection‖ = 1
  axialDirectionIsUnit : ‖setup.rectangle.axialDirection‖ = 1
  normalIsUnit : ‖setup.rectangle.orientedNormal‖ = 1
  radialAndAxialDirectionsPerpendicular :
    inner ℝ setup.rectangle.radialDirection
      setup.rectangle.axialDirection = 0
  normalPerpendicularToRadialDirection :
    inner ℝ setup.rectangle.orientedNormal
      setup.rectangle.radialDirection = 0
  normalPerpendicularToAxialDirection :
    inner ℝ setup.rectangle.orientedNormal
      setup.rectangle.axialDirection = 0
  currentRunsAxially :
    setup.axialCurrentDirection = setup.rectangle.axialDirection

/-! ## Governing electromagnetic laws -/

/-!
Uniform axial current density inside the solid wire and its circular-area
integrals.  The total-current relation uses the full disk of radius `R`; the
enclosed-current relation uses a concentric disk of arbitrary interior radius.
These are general current-distribution laws and mention no magnetic flux.
-/
structure SatisfiesUniformCrossSectionCurrentLaws
    (setup : InfiniteCylindricalWireFluxSetup) : Prop where
  currentDensitySpatiallyUniformInsideWire : ∀ p q : Space 3,
    p ∈ setup.wireInterior → q ∈ setup.wireInterior →
    setup.currentDensity setup.observationTime p =
      setup.currentDensity setup.observationTime q
  currentDensityCalibration : ∀ p : Space 3,
    p ∈ setup.wireInterior →
    setup.currentDensity setup.observationTime p =
      currentDensityInAmperesPerSquareMeter
          setup.uniformCurrentDensityMagnitude •
        setup.axialCurrentDirection
  totalCurrentFromUniformDensity :
    currentInAmperes setup.totalCurrentI₀ =
      currentDensityInAmperesPerSquareMeter
          setup.uniformCurrentDensityMagnitude *
        Real.pi * lengthInMeters setup.wireRadiusR ^ 2
  enclosedCurrentFromUniformDensity : ∀ radialMeters : ℝ,
    0 ≤ radialMeters →
    radialMeters ≤ lengthInMeters setup.wireRadiusR →
    currentInAmperes
        (setup.enclosedCurrentAtRadiusMeters radialMeters) =
      currentDensityInAmperesPerSquareMeter
          setup.uniformCurrentDensityMagnitude *
        Real.pi * radialMeters ^ 2

/-!
Cylindrical symmetry and Ampere's law inside the wire.  On the selected
radial-longitudinal half-plane, the azimuthal magnetic field is parallel to
the rectangle's oriented normal and is independent of axial position.  At
positive radius the circular Amperian loop has circumference `2 pi r`.
-/
structure SatisfiesInteriorInfiniteWireAmpereLaws
    (setup : InfiniteCylindricalWireFluxSetup) : Prop where
  fieldOnEveryAxialTranslateIsAzimuthal : ∀ radialMeters axialMeters,
    radialMeters ∈ Set.Icc 0 (lengthInMeters setup.wireRadiusR) →
    setup.magneticField setup.observationTime
        (setup.rectangle.pointAtMeters radialMeters axialMeters) =
      magneticFluxDensityInTeslas
          (setup.fluxDensityMagnitudeAtRadiusMeters radialMeters) •
        setup.rectangle.orientedNormal
  ampereLawOnInteriorCircles : ∀ radialMeters : ℝ,
    0 < radialMeters →
    radialMeters ≤ lengthInMeters setup.wireRadiusR →
    magneticFluxDensityInTeslas
          (setup.fluxDensityMagnitudeAtRadiusMeters radialMeters) *
        (2 * Real.pi * radialMeters) =
      permeabilityInHenriesPerMeter setup.vacuumPermeabilityμ₀ *
        currentInAmperes
          (setup.enclosedCurrentAtRadiusMeters radialMeters)
  fieldMagnitudeAtAxisIsZero :
    magneticFluxDensityInTeslas
      (setup.fluxDensityMagnitudeAtRadiusMeters 0) = 0
  radialProfileIntervalIntegrable :
    IntervalIntegrable
      (fun radialMeters =>
        magneticFluxDensityInTeslas
          (setup.fluxDensityMagnitudeAtRadiusMeters radialMeters))
      MeasureTheory.volume 0 (lengthInMeters setup.wireRadiusR)

/-!
For the radial-longitudinal surface, `dA = d radial * d axial`.  Axial
translation invariance makes the surface integral equal to `W` times the
radial integral of the aligned azimuthal field magnitude.  This is the general
definition/law for the observable flux, not its requested evaluated value.
-/
structure SatisfiesRadialRectangleMagneticFluxLaw
    (setup : InfiniteCylindricalWireFluxSetup) : Prop where
  fluxIsSurfaceIntegral :
    magneticFluxInWebers setup.rectangleFlux =
      lengthInMeters setup.rectangle.axialLengthW *
        (∫ radialMeters in
          (0 : ℝ)..lengthInMeters setup.wireRadiusR,
          magneticFluxDensityInTeslas
            (setup.fluxDensityMagnitudeAtRadiusMeters radialMeters))

/-! ## Formalization target -/

/-!
For the exact infinite solid cylinder with uniform cross-sectional current
density, Ampere's law gives a field growing linearly from the axis to the surface.
Integrating that field over the radial-longitudinal rectangle yields
`μ₀ I₀ W / (4 pi)` webers.  The radius cancels only after applying the
governing laws; the result is not assumed or introduced by a local definition.
This is recorded as choice B in the source, whose `I` is interpreted as the
scenario's total current `I₀`; answer-choice metadata is deliberately not a
premise or an unfoldable helper declaration.

This declaration corresponds to blueprint label
`thm:physics:phyx_mini_0975:target`.
-/
theorem problem_phyx_mini_0975
    (setup : InfiniteCylindricalWireFluxSetup)
    (hFigure : MatchesProblemAndPrimaryFigure setup)
    (hPhysical : HasPhysicalInfiniteWireConfiguration setup)
    (hInfiniteGeometry : SatisfiesExactInfiniteCylindricalGeometry setup)
    (hGeometry : SatisfiesRadialLongitudinalRectangleGeometry setup)
    (hCurrent : SatisfiesUniformCrossSectionCurrentLaws setup)
    (hAmpere : SatisfiesInteriorInfiniteWireAmpereLaws setup)
    (hFlux : SatisfiesRadialRectangleMagneticFluxLaw setup) :
    magneticFluxInWebers setup.rectangleFlux =
      permeabilityInHenriesPerMeter setup.vacuumPermeabilityμ₀ *
        currentInAmperes setup.totalCurrentI₀ *
        lengthInMeters setup.rectangle.axialLengthW /
        (4 * Real.pi) := by
  let R : ℝ := lengthInMeters setup.wireRadiusR
  let W : ℝ := lengthInMeters setup.rectangle.axialLengthW
  let I : ℝ := currentInAmperes setup.totalCurrentI₀
  let J : ℝ :=
    currentDensityInAmperesPerSquareMeter
      setup.uniformCurrentDensityMagnitude
  let μ : ℝ :=
    permeabilityInHenriesPerMeter setup.vacuumPermeabilityμ₀
  let B : ℝ → ℝ := fun r =>
    magneticFluxDensityInTeslas
      (setup.fluxDensityMagnitudeAtRadiusMeters r)
  have hR : 0 < R := by
    exact hPhysical.radiusPositive
  have hpi : 0 < Real.pi := Real.pi_pos
  have hI : I = J * Real.pi * R ^ 2 := by
    exact hCurrent.totalCurrentFromUniformDensity
  have hB : ∀ r ∈ Set.Icc (0 : ℝ) R, B r = μ * J * r / 2 := by
    intro r hr
    rcases hr with ⟨hr_nonneg, hr_le⟩
    rcases eq_or_lt_of_le hr_nonneg with rfl | hr_pos
    · simpa [B] using hAmpere.fieldMagnitudeAtAxisIsZero
    · have hEnclosed :
          currentInAmperes
              (setup.enclosedCurrentAtRadiusMeters r) =
            J * Real.pi * r ^ 2 := by
        exact hCurrent.enclosedCurrentFromUniformDensity r hr_nonneg hr_le
      have hAmpereAtR :
          B r * (2 * Real.pi * r) =
            μ *
              currentInAmperes
                (setup.enclosedCurrentAtRadiusMeters r) := by
        exact hAmpere.ampereLawOnInteriorCircles r hr_pos hr_le
      rw [hEnclosed] at hAmpereAtR
      have hr_ne : r ≠ 0 := ne_of_gt hr_pos
      have hpi_ne : Real.pi ≠ 0 := ne_of_gt hpi
      calc
        B r = B r * (2 * Real.pi * r) / (2 * Real.pi * r) := by
          field_simp [hpi_ne, hr_ne]
        _ = μ * (J * Real.pi * r ^ 2) / (2 * Real.pi * r) := by
          rw [hAmpereAtR]
        _ = μ * J * r / 2 := by
          field_simp [hpi_ne, hr_ne]
  have hIntegral :
      (∫ r in (0 : ℝ)..R, B r) = μ * J * R ^ 2 / 4 := by
    calc
      (∫ r in (0 : ℝ)..R, B r) =
          ∫ r in (0 : ℝ)..R, μ * J * r / 2 := by
            apply intervalIntegral.integral_congr
            intro r hr
            apply hB r
            simpa [Set.uIcc_of_le hR.le] using hr
      _ = μ * J * R ^ 2 / 4 := by
        simp only [intervalIntegral.integral_div]
        rw [intervalIntegral.integral_const_mul,
          integral_id]
        ring
  rw [hFlux.fluxIsSurfaceIntegral, hIntegral]
  change W * (μ * J * R ^ 2 / 4) = μ * I * W / (4 * Real.pi)
  rw [hI]
  field_simp

end PhyXMiniProblems.ProblemPhyXMini0975
