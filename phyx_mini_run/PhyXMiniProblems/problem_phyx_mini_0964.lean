import Mathlib
import Physlib.Electromagnetism.Basic
import Physlib.Units.WithDim.Basic

/- USER: The assigned Lean file did not exist when this autoformalization task began. -/

noncomputable section

namespace PhyXMiniProblems.ProblemPhyXMini0964

open Dimension

/-!
# Far magnetic field of two oppositely directed parallel wires

Two ideal long wires are perpendicular to the displayed `xy`-plane.  Their
end-view positions are `(0, a)` and `(0, -a)`.  Both carry the same current
magnitude `I`, but the upper current points out of the page and the lower
current points into the page.  The observation point `P` is `(x, 0)`.

Lengths, current magnitude, and vacuum permeability are unit-independent
Physlib `Dimensionful` quantities.  The magnetic fields use Physlib's
spacetime-dependent vector-field type.  Real numbers occur only as explicitly
named coherent-SI coordinate or component readouts and in the displayed
answer formulas.

Assumption/target split:

* governing laws: the vector magnetic-field law for an ideal infinite
  straight wire and linear superposition of the two wire fields;
* previous-part results: none;
* figure/data readouts: axes `x` and `y`, origin `O`, point `P = (x,0)`, wire
  centers `(0,a)` and `(0,-a)`, two `a` guides, the `x` guide, equal `I`
  labels, and the upper dot/lower cross current glyphs;
* current target conclusions: cancellation of the transverse components, the
  exact finite-distance magnitude `μ₀ I a / (π (x² + a²))`, and the
  far-field asymptotic magnitude `μ₀ I a / (π x²)`, answer B.

No exact net-field formula, far-field approximation, or answer choice occurs
in a scenario, figure, or governing-law premise.
-/

/-! ## Dimensionful quantities and coherent-SI readouts -/

/-- Electric current has physical dimension `C T⁻¹`. -/
def electricCurrentDimension : Dimension :=
  C𝓭 * T𝓭⁻¹

/-- Magnetic permeability has SI dimension `M L C⁻²`. -/
def magneticPermeabilityDimension : Dimension :=
  M𝓭 * L𝓭 * C𝓭⁻¹ * C𝓭⁻¹

/-- Magnetic flux density has SI dimension `M T⁻¹ C⁻¹`. -/
def magneticFluxDensityDimension : Dimension :=
  M𝓭 * T𝓭⁻¹ * C𝓭⁻¹

/-- A nonnegative, unit-independent physical length. -/
abbrev LengthQuantity : Type :=
  Dimensionful (WithDim L𝓭 NNReal)

/-- A nonnegative, unit-independent electric-current magnitude. -/
abbrev ElectricCurrentMagnitude : Type :=
  Dimensionful (WithDim electricCurrentDimension NNReal)

/-- A nonnegative, unit-independent magnetic permeability. -/
abbrev MagneticPermeabilityQuantity : Type :=
  Dimensionful (WithDim magneticPermeabilityDimension NNReal)

/-- Read a nonnegative dimensionful quantity in coherent SI units. -/
def nonnegativeSIReadout {d : Dimension}
    (quantity : Dimensionful (WithDim d NNReal)) : ℝ :=
  ((quantity UnitChoices.SI).val : ℝ)

/-- Read a physical length in metres. -/
def lengthInMeters (length : LengthQuantity) : ℝ :=
  nonnegativeSIReadout length

/-- Read an electric-current magnitude in amperes. -/
def currentInAmperes (current : ElectricCurrentMagnitude) : ℝ :=
  nonnegativeSIReadout current

/-- Read permeability in tesla-metres per ampere. -/
def permeabilityInTeslaMetersPerAmpere
    (permeability : MagneticPermeabilityQuantity) : ℝ :=
  nonnegativeSIReadout permeability

/-! ## Spatial geometry and primary-figure vocabulary -/

/-- A three-dimensional spatial vector used for directions and SI components. -/
abbrev SpatialVector : Type :=
  EuclideanSpace ℝ (Fin 3)

/-- The coordinate axes; only `x` and `y` appear in the end-view raster. -/
inductive CoordinateAxis where
  | x
  | y
  | z
  deriving DecidableEq, Fintype, Repr

/-- Unit vector associated with a coordinate axis. -/
def axisDirection : CoordinateAxis → SpatialVector
  | .x => EuclideanSpace.single (0 : Fin 3) 1
  | .y => EuclideanSpace.single (1 : Fin 3) 1
  | .z => EuclideanSpace.single (2 : Fin 3) 1

/-!
Mathlib's coordinate cross product transported to the Euclidean-space type
used by Physlib magnetic fields.
-/
def spatialCrossProduct (a b : SpatialVector) : SpatialVector :=
  (WithLp.equiv 2 (Fin 3 → ℝ)).symm
    (crossProduct (WithLp.equiv 2 (Fin 3 → ℝ) a)
      (WithLp.equiv 2 (Fin 3 → ℝ) b))

/-- The spatial point with coherent-SI coordinates `(x, 0, 0)`. -/
def pointOnXAxisMeters (xMeters : ℝ) : Space 3 :=
  Space.vectorToSpace (xMeters • axisDirection .x)

/-- The upper and lower long wires in the primary figure. -/
inductive Wire where
  | upper
  | lower
  deriving DecidableEq, Fintype, Repr

/-- Idealization assigned to each current-carrying source. -/
inductive WireModel where
  | idealInfiniteStraightWire
  | other
  deriving DecidableEq, Repr

/-- End-view glyph for a page-normal current direction. -/
inductive CurrentGlyph where
  | dot
  | cross
  deriving DecidableEq, Repr

/-- Labeled points and wire centers visible in image `964.png`. -/
inductive FigurePoint where
  | originO
  | upperWireCenter
  | lowerWireCenter
  | observationP
  deriving DecidableEq, Fintype, Repr

/-- The three double-arrow distance guides shown in the raster. -/
inductive DistanceGuide where
  | upperOffsetA
  | lowerOffsetA
  | observationDistanceX
  deriving DecidableEq, Fintype, Repr

/-- Printed symbol beside each distance guide. -/
def expectedDistanceSymbol : DistanceGuide → String
  | .upperOffsetA => "a"
  | .lowerOffsetA => "a"
  | .observationDistanceX => "x"

/-!
Literal presentation data from the primary raster.  Coordinate values are
coherent-SI metre readouts; the physical lengths that calibrate them live in
`OpposedParallelWireSetup`.
-/
structure OpposedParallelWireFigure where
  axisShown : CoordinateAxis → Bool
  axisPrintedSymbol : CoordinateAxis → String
  originLabelShown : Bool
  observationLabelShown : Bool
  wireCurrentLabelShown : Wire → Bool
  wireCurrentPrintedSymbol : Wire → String
  wireCurrentGlyph : Wire → CurrentGlyph
  pointPositionMeters : FigurePoint → Space 3
  distanceGuideShown : DistanceGuide → Bool
  distanceGuidePrintedSymbol : DistanceGuide → String
  distanceGuideStart : DistanceGuide → FigurePoint
  distanceGuideEnd : DistanceGuide → FigurePoint

/-!
Independent physical quantities, source fields, and the total observable
field.  None of these fields is defined from an answer formula.
-/
structure OpposedParallelWireSetup where
  wireModel : Wire → WireModel
  wireAxis : Wire → CoordinateAxis
  wirePositionMeters : Wire → Space 3
  wireCurrentUnitDirection : Wire → SpatialVector
  wireOffsetA : LengthQuantity
  observationDistanceX : LengthQuantity
  currentMagnitudeI : ElectricCurrentMagnitude
  vacuumPermeabilityMu0 : MagneticPermeabilityQuantity
  magneticFieldDueToWire : Wire → Electromagnetism.MagneticField 3
  totalMagneticField : Electromagnetism.MagneticField 3
  observationTime : Time
  figure : OpposedParallelWireFigure

/-- The field due to one wire at `(x,0,0)`, read as a vector in teslas. -/
def magneticFieldVectorDueToWireOnXAxisInTeslas
    (setup : OpposedParallelWireSetup) (wire : Wire)
    (xMeters : ℝ) : SpatialVector :=
  setup.magneticFieldDueToWire wire setup.observationTime
    (pointOnXAxisMeters xMeters)

/-- The total magnetic-field vector at `(x,0,0)`, in teslas. -/
def magneticFieldVectorOnXAxisInTeslas
    (setup : OpposedParallelWireSetup) (xMeters : ℝ) : SpatialVector :=
  setup.totalMagneticField setup.observationTime
    (pointOnXAxisMeters xMeters)

/-- The magnitude of the total field at `(x,0,0)`, in teslas. -/
def magneticFieldMagnitudeOnXAxisInTeslas
    (setup : OpposedParallelWireSetup) (xMeters : ℝ) : ℝ :=
  ‖magneticFieldVectorOnXAxisInTeslas setup xMeters‖

/-! ## Scenario facts, figure readouts, and governing laws -/

/-!
The prose-level idealizations, page-normal orientations, and positivity of the
physical magnitudes.  A single current-magnitude field records that both
wires carry the same `I`; the signed unit directions record that the currents
are opposite.
-/
structure MatchesOpposedParallelWireScenario
    (setup : OpposedParallelWireSetup) : Prop where
  bothWiresAreIdealAndLong : ∀ wire,
    setup.wireModel wire = .idealInfiniteStraightWire
  bothWiresArePerpendicularToXYPlane : ∀ wire,
    setup.wireAxis wire = .z
  upperCurrentPointsOutOfPage :
    setup.wireCurrentUnitDirection .upper = axisDirection .z
  lowerCurrentPointsIntoPage :
    setup.wireCurrentUnitDirection .lower = -axisDirection .z
  currentDirectionVectorsAreUnit : ∀ wire,
    ‖setup.wireCurrentUnitDirection wire‖ = 1
  wireOffsetPositive :
    0 < lengthInMeters setup.wireOffsetA
  displayedObservationDistancePositive :
    0 < lengthInMeters setup.observationDistanceX
  currentMagnitudePositive :
    0 < currentInAmperes setup.currentMagnitudeI
  vacuumPermeabilityPositive :
    0 < permeabilityInTeslaMetersPerAmpere setup.vacuumPermeabilityMu0

/-!
The axes, symbols, dot/cross convention, guide endpoints, and metric
coordinates transcribed from the supplied image.  This fixes the wire centers
at `(0, ±a)` and the displayed point `P` at `(x,0)` without asserting any
magnetic-field value.
-/
structure MatchesPrimaryOpposedWireFigure
    (setup : OpposedParallelWireSetup) : Prop where
  xAxisShown : setup.figure.axisShown .x = true
  yAxisShown : setup.figure.axisShown .y = true
  zAxisNotDrawnInEndView : setup.figure.axisShown .z = false
  xAxisSymbol : setup.figure.axisPrintedSymbol .x = "x"
  yAxisSymbol : setup.figure.axisPrintedSymbol .y = "y"
  originOIsLabeled : setup.figure.originLabelShown = true
  observationPIsLabeled : setup.figure.observationLabelShown = true
  bothCurrentLabelsShown : ∀ wire,
    setup.figure.wireCurrentLabelShown wire = true
  bothCurrentLabelsAreI : ∀ wire,
    setup.figure.wireCurrentPrintedSymbol wire = "I"
  upperWireUsesDotGlyph :
    setup.figure.wireCurrentGlyph .upper = .dot
  lowerWireUsesCrossGlyph :
    setup.figure.wireCurrentGlyph .lower = .cross
  everyDistanceGuideShown : ∀ guide,
    setup.figure.distanceGuideShown guide = true
  distanceGuideSymbols : ∀ guide,
    setup.figure.distanceGuidePrintedSymbol guide =
      expectedDistanceSymbol guide
  upperGuideRunsFromOToUpperWire :
    setup.figure.distanceGuideStart .upperOffsetA = .originO ∧
      setup.figure.distanceGuideEnd .upperOffsetA = .upperWireCenter
  lowerGuideRunsFromLowerWireToO :
    setup.figure.distanceGuideStart .lowerOffsetA = .lowerWireCenter ∧
      setup.figure.distanceGuideEnd .lowerOffsetA = .originO
  horizontalGuideRunsFromOToP :
    setup.figure.distanceGuideStart .observationDistanceX = .originO ∧
      setup.figure.distanceGuideEnd .observationDistanceX = .observationP
  originCoordinates :
    setup.figure.pointPositionMeters .originO =
      Space.vectorToSpace (0 : SpatialVector)
  upperWireCoordinates :
    setup.wirePositionMeters .upper =
      Space.vectorToSpace
        (lengthInMeters setup.wireOffsetA • axisDirection .y)
  lowerWireCoordinates :
    setup.wirePositionMeters .lower =
      Space.vectorToSpace
        ((-lengthInMeters setup.wireOffsetA) • axisDirection .y)
  upperFigurePointMatchesWire :
    setup.figure.pointPositionMeters .upperWireCenter =
      setup.wirePositionMeters .upper
  lowerFigurePointMatchesWire :
    setup.figure.pointPositionMeters .lowerWireCenter =
      setup.wirePositionMeters .lower
  observationCoordinates :
    setup.figure.pointPositionMeters .observationP =
      pointOnXAxisMeters (lengthInMeters setup.observationDistanceX)

/-!
The governing electromagnetic laws used in the intended derivation.

For a wire with unit current direction `k` and displacement vector `r` from
the wire to the observation point, the vector field is

`B = μ₀ I / (2 π ‖r‖²) • (k × r)`.

This is the general infinite-straight-wire law, not the requested net or
far-field result.  The second field records ordinary magnetic superposition.
-/
structure SatisfiesOpposedWireMagneticFieldLaws
    (setup : OpposedParallelWireSetup) : Prop where
  infiniteStraightWireField :
    ∀ (wire : Wire) (time : Time) (position : Space 3),
      position ≠ setup.wirePositionMeters wire →
      setup.magneticFieldDueToWire wire time position =
        (permeabilityInTeslaMetersPerAmpere setup.vacuumPermeabilityMu0 *
            currentInAmperes setup.currentMagnitudeI /
          (2 * Real.pi *
            ‖position -ᵥ setup.wirePositionMeters wire‖ ^ 2)) •
          spatialCrossProduct (setup.wireCurrentUnitDirection wire)
            (position -ᵥ setup.wirePositionMeters wire)
  magneticFieldSuperposition :
    ∀ (time : Time) (position : Space 3),
      setup.totalMagneticField time position =
        setup.magneticFieldDueToWire .upper time position +
          setup.magneticFieldDueToWire .lower time position

/-! ## Exact field, far-field limit, and answer formulas -/

/-!
The right-hand rule and the symmetric geometry make the `y` components from
the two wires cancel and the `x` components add.  This exact vector identity
is a derived result, not a governing-law premise.
-/
lemma magneticFieldVectorOnXAxis_exact
    (setup : OpposedParallelWireSetup)
    (hScenario : MatchesOpposedParallelWireScenario setup)
    (hFigure : MatchesPrimaryOpposedWireFigure setup)
    (hLaws : SatisfiesOpposedWireMagneticFieldLaws setup)
    (xMeters : ℝ) (hx : 0 < xMeters) :
    magneticFieldVectorOnXAxisInTeslas setup xMeters =
      (permeabilityInTeslaMetersPerAmpere setup.vacuumPermeabilityMu0 *
          currentInAmperes setup.currentMagnitudeI *
          lengthInMeters setup.wireOffsetA /
        (Real.pi *
          (xMeters ^ 2 + lengthInMeters setup.wireOffsetA ^ 2))) •
        axisDirection .x := by
  have hUpper :
      pointOnXAxisMeters xMeters ≠ setup.wirePositionMeters .upper := by
    rw [hFigure.upperWireCoordinates]
    intro h
    have h0 := congrArg (fun p : Space 3 => p 0) h
    simp [pointOnXAxisMeters, axisDirection] at h0
    linarith
  have hLower :
      pointOnXAxisMeters xMeters ≠ setup.wirePositionMeters .lower := by
    rw [hFigure.lowerWireCoordinates]
    intro h
    have h0 := congrArg (fun p : Space 3 => p 0) h
    simp [pointOnXAxisMeters, axisDirection] at h0
    linarith
  have hDispUpper :
      pointOnXAxisMeters xMeters -ᵥ setup.wirePositionMeters .upper =
        xMeters • axisDirection .x -
          lengthInMeters setup.wireOffsetA • axisDirection .y := by
    rw [hFigure.upperWireCoordinates]
    ext i
    simp [pointOnXAxisMeters]
  have hDispLower :
      pointOnXAxisMeters xMeters -ᵥ setup.wirePositionMeters .lower =
        xMeters • axisDirection .x +
          lengthInMeters setup.wireOffsetA • axisDirection .y := by
    rw [hFigure.lowerWireCoordinates]
    ext i
    simp [pointOnXAxisMeters]
  have hNormUpper :
      ‖pointOnXAxisMeters xMeters -ᵥ setup.wirePositionMeters .upper‖ ^ 2 =
        xMeters ^ 2 + lengthInMeters setup.wireOffsetA ^ 2 := by
    rw [hDispUpper, EuclideanSpace.real_norm_sq_eq]
    simp [axisDirection, Fin.sum_univ_succ]
  have hNormLower :
      ‖pointOnXAxisMeters xMeters -ᵥ setup.wirePositionMeters .lower‖ ^ 2 =
        xMeters ^ 2 + lengthInMeters setup.wireOffsetA ^ 2 := by
    rw [hDispLower, EuclideanSpace.real_norm_sq_eq]
    simp [axisDirection, Fin.sum_univ_succ]
  have hCrossSubRight (u v w : SpatialVector) :
      spatialCrossProduct u (v - w) =
        spatialCrossProduct u v - spatialCrossProduct u w := by
    apply (WithLp.equiv 2 (Fin 3 → ℝ)).injective
    change
      crossProduct ((WithLp.equiv 2 (Fin 3 → ℝ)) u)
          ((WithLp.equiv 2 (Fin 3 → ℝ)) v -
            (WithLp.equiv 2 (Fin 3 → ℝ)) w) =
        crossProduct ((WithLp.equiv 2 (Fin 3 → ℝ)) u)
            ((WithLp.equiv 2 (Fin 3 → ℝ)) v) -
          crossProduct ((WithLp.equiv 2 (Fin 3 → ℝ)) u)
            ((WithLp.equiv 2 (Fin 3 → ℝ)) w)
    exact map_sub _ _ _
  have hCrossAddRight (u v w : SpatialVector) :
      spatialCrossProduct u (v + w) =
        spatialCrossProduct u v + spatialCrossProduct u w := by
    apply (WithLp.equiv 2 (Fin 3 → ℝ)).injective
    change
      crossProduct ((WithLp.equiv 2 (Fin 3 → ℝ)) u)
          ((WithLp.equiv 2 (Fin 3 → ℝ)) v +
            (WithLp.equiv 2 (Fin 3 → ℝ)) w) =
        crossProduct ((WithLp.equiv 2 (Fin 3 → ℝ)) u)
            ((WithLp.equiv 2 (Fin 3 → ℝ)) v) +
          crossProduct ((WithLp.equiv 2 (Fin 3 → ℝ)) u)
            ((WithLp.equiv 2 (Fin 3 → ℝ)) w)
    exact map_add _ _ _
  have hCrossSmulRight (u v : SpatialVector) (c : ℝ) :
      spatialCrossProduct u (c • v) =
        c • spatialCrossProduct u v := by
    apply (WithLp.equiv 2 (Fin 3 → ℝ)).injective
    change
      crossProduct ((WithLp.equiv 2 (Fin 3 → ℝ)) u)
          (c • (WithLp.equiv 2 (Fin 3 → ℝ)) v) =
        c • crossProduct ((WithLp.equiv 2 (Fin 3 → ℝ)) u)
          ((WithLp.equiv 2 (Fin 3 → ℝ)) v)
    exact map_smul _ _ _
  have hCrossNegLeft (u v : SpatialVector) :
      spatialCrossProduct (-u) v = -spatialCrossProduct u v := by
    apply (WithLp.equiv 2 (Fin 3 → ℝ)).injective
    change
      crossProduct (-(WithLp.equiv 2 (Fin 3 → ℝ)) u)
          ((WithLp.equiv 2 (Fin 3 → ℝ)) v) =
        -crossProduct ((WithLp.equiv 2 (Fin 3 → ℝ)) u)
          ((WithLp.equiv 2 (Fin 3 → ℝ)) v)
    simp only [map_neg, LinearMap.neg_apply]
  have hRawCrossZX :
      crossProduct (Pi.single (2 : Fin 3) 1)
          (Pi.single (0 : Fin 3) 1) =
        Pi.single (1 : Fin 3) (1 : ℝ) := by
    ext i
    fin_cases i <;> simp [cross_apply]
  have hRawCrossZY :
      crossProduct (Pi.single (2 : Fin 3) 1)
          (Pi.single (1 : Fin 3) 1) =
        -Pi.single (0 : Fin 3) (1 : ℝ) := by
    ext i
    fin_cases i <;> simp [cross_apply]
  have hCrossZX :
      spatialCrossProduct (axisDirection .z) (axisDirection .x) =
        axisDirection .y := by
    change
      WithLp.toLp 2
          (crossProduct (Pi.single (2 : Fin 3) 1)
            (Pi.single (0 : Fin 3) 1)) =
        WithLp.toLp 2 (Pi.single (1 : Fin 3) (1 : ℝ))
    rw [hRawCrossZX]
  have hCrossZY :
      spatialCrossProduct (axisDirection .z) (axisDirection .y) =
        -axisDirection .x := by
    change
      WithLp.toLp 2
          (crossProduct (Pi.single (2 : Fin 3) 1)
            (Pi.single (1 : Fin 3) 1)) =
        WithLp.toLp 2 (-Pi.single (0 : Fin 3) (1 : ℝ))
    rw [hRawCrossZY]
  have hCrossUpper :
      spatialCrossProduct (axisDirection .z)
          (pointOnXAxisMeters xMeters -ᵥ setup.wirePositionMeters .upper) =
        lengthInMeters setup.wireOffsetA • axisDirection .x +
          xMeters • axisDirection .y := by
    rw [hDispUpper, hCrossSubRight, hCrossSmulRight, hCrossSmulRight,
      hCrossZX, hCrossZY]
    module
  have hCrossLower :
      spatialCrossProduct (-axisDirection .z)
          (pointOnXAxisMeters xMeters -ᵥ setup.wirePositionMeters .lower) =
        lengthInMeters setup.wireOffsetA • axisDirection .x -
          xMeters • axisDirection .y := by
    rw [hDispLower, hCrossNegLeft, hCrossAddRight, hCrossSmulRight,
      hCrossSmulRight, hCrossZX, hCrossZY]
    module
  rw [show magneticFieldVectorOnXAxisInTeslas setup xMeters =
      setup.totalMagneticField setup.observationTime
        (pointOnXAxisMeters xMeters) by rfl,
    hLaws.magneticFieldSuperposition,
    hLaws.infiniteStraightWireField .upper _ _ hUpper,
    hLaws.infiniteStraightWireField .lower _ _ hLower,
    hScenario.upperCurrentPointsOutOfPage,
    hScenario.lowerCurrentPointsIntoPage,
    hNormUpper, hNormLower, hCrossUpper, hCrossLower]
  let mu : ℝ :=
    permeabilityInTeslaMetersPerAmpere setup.vacuumPermeabilityMu0
  let current : ℝ := currentInAmperes setup.currentMagnitudeI
  let offset : ℝ := lengthInMeters setup.wireOffsetA
  let distanceSq : ℝ := xMeters ^ 2 + offset ^ 2
  let coefficient : ℝ := mu * current / (2 * Real.pi * distanceSq)
  change
    coefficient •
          (offset • axisDirection .x + xMeters • axisDirection .y) +
        coefficient •
          (offset • axisDirection .x - xMeters • axisDirection .y) =
      (mu * current * offset / (Real.pi * distanceSq)) •
        axisDirection .x
  have hDistanceSq : distanceSq ≠ 0 := by
    dsimp [distanceSq, offset]
    exact ne_of_gt
      (add_pos_of_pos_of_nonneg (sq_pos_of_pos hx)
        (sq_nonneg (lengthInMeters setup.wireOffsetA)))
  have hCoefficient :
      2 * coefficient * offset =
        mu * current * offset / (Real.pi * distanceSq) := by
    dsimp [coefficient]
    field_simp [Real.pi_ne_zero, hDistanceSq]
  rw [← hCoefficient]
  module

/-- Exact finite-distance magnitude before making the `x ≫ a` approximation. -/
lemma magneticFieldMagnitudeOnXAxis_exact
    (setup : OpposedParallelWireSetup)
    (hScenario : MatchesOpposedParallelWireScenario setup)
    (hFigure : MatchesPrimaryOpposedWireFigure setup)
    (hLaws : SatisfiesOpposedWireMagneticFieldLaws setup)
    (xMeters : ℝ) (hx : 0 < xMeters) :
    magneticFieldMagnitudeOnXAxisInTeslas setup xMeters =
      permeabilityInTeslaMetersPerAmpere setup.vacuumPermeabilityMu0 *
          currentInAmperes setup.currentMagnitudeI *
          lengthInMeters setup.wireOffsetA /
        (Real.pi *
          (xMeters ^ 2 + lengthInMeters setup.wireOffsetA ^ 2)) := by
  have hMu := hScenario.vacuumPermeabilityPositive
  have hCurrent := hScenario.currentMagnitudePositive
  have hOffset := hScenario.wireOffsetPositive
  have hCoefficientPositive :
      0 <
        permeabilityInTeslaMetersPerAmpere setup.vacuumPermeabilityMu0 *
            currentInAmperes setup.currentMagnitudeI *
            lengthInMeters setup.wireOffsetA /
          (Real.pi *
            (xMeters ^ 2 + lengthInMeters setup.wireOffsetA ^ 2)) := by
    positivity
  unfold magneticFieldMagnitudeOnXAxisInTeslas
  rw [magneticFieldVectorOnXAxis_exact setup hScenario hFigure hLaws
    xMeters hx, norm_smul, Real.norm_eq_abs,
    abs_of_pos hCoefficientPositive]
  simp [axisDirection]

/-- Labels of the four formulas displayed in the multiple-choice question. -/
inductive AnswerChoice where
  | A
  | B
  | C
  | D
  deriving DecidableEq, Fintype, Repr

/-!
Scalar coherent-SI readings of the four printed formulas.  Some distractors
are dimensionally invalid as physical formulas; recording them as displayed
scalar expressions does not promote them to governing laws.
-/
def displayedFarFieldFormulaInTeslas
    (setup : OpposedParallelWireSetup) (choice : AnswerChoice)
    (xMeters : ℝ) : ℝ :=
  match choice with
  | .A =>
      permeabilityInTeslaMetersPerAmpere setup.vacuumPermeabilityMu0 *
          currentInAmperes setup.currentMagnitudeI /
        (2 * Real.pi * xMeters)
  | .B =>
      permeabilityInTeslaMetersPerAmpere setup.vacuumPermeabilityMu0 *
          currentInAmperes setup.currentMagnitudeI *
          lengthInMeters setup.wireOffsetA /
        (Real.pi * xMeters ^ 2)
  | .C =>
      permeabilityInTeslaMetersPerAmpere setup.vacuumPermeabilityMu0 *
          currentInAmperes setup.currentMagnitudeI *
          lengthInMeters setup.wireOffsetA ^ 2 /
        (Real.pi * xMeters ^ 3)
  | .D =>
      permeabilityInTeslaMetersPerAmpere setup.vacuumPermeabilityMu0 *
          currentInAmperes setup.currentMagnitudeI /
        (Real.pi *
          (xMeters ^ 2 + lengthInMeters setup.wireOffsetA ^ 2))

/-!
The phrase `x ≫ a` is formalized as `x → +∞` with the fixed wire offset `a`.
The actual field magnitude is asymptotically equivalent to

`μ₀ I a / (π x²)`,

which is answer choice B.  Unlike a finite-`x` equality, this statement keeps
the approximation mathematically honest.
-/
theorem magneticFieldMagnitude_farField_eq_answer_B
    (setup : OpposedParallelWireSetup)
    (hScenario : MatchesOpposedParallelWireScenario setup)
    (hFigure : MatchesPrimaryOpposedWireFigure setup)
    (hLaws : SatisfiesOpposedWireMagneticFieldLaws setup) :
    Asymptotics.IsEquivalent Filter.atTop
      (fun xMeters : ℝ =>
        magneticFieldMagnitudeOnXAxisInTeslas setup xMeters)
      (fun xMeters : ℝ =>
        permeabilityInTeslaMetersPerAmpere setup.vacuumPermeabilityMu0 *
            currentInAmperes setup.currentMagnitudeI *
            lengthInMeters setup.wireOffsetA /
          (Real.pi * xMeters ^ 2)) := by
  have hEventuallyExact :
      (fun xMeters : ℝ =>
          magneticFieldMagnitudeOnXAxisInTeslas setup xMeters) =ᶠ[
        Filter.atTop]
        (fun xMeters : ℝ =>
          permeabilityInTeslaMetersPerAmpere
                setup.vacuumPermeabilityMu0 *
              currentInAmperes setup.currentMagnitudeI *
              lengthInMeters setup.wireOffsetA /
            (Real.pi *
              (xMeters ^ 2 + lengthInMeters setup.wireOffsetA ^ 2))) := by
    filter_upwards [Filter.eventually_gt_atTop (0 : ℝ)] with xMeters hx
    exact magneticFieldMagnitudeOnXAxis_exact setup hScenario hFigure hLaws
      xMeters hx
  have hLinearLittleOQuadratic :
      (fun xMeters : ℝ => xMeters) =o[Filter.atTop]
        (fun xMeters : ℝ => xMeters ^ 2) := by
    simpa only [pow_one] using
      (Asymptotics.isLittleO_pow_pow_atTop_of_lt
        (show 1 < 2 by norm_num) :
        (fun xMeters : ℝ => xMeters ^ 1) =o[Filter.atTop]
          (fun xMeters : ℝ => xMeters ^ 2))
  have hConstantLittleOQuadratic :
      (fun _ : ℝ => lengthInMeters setup.wireOffsetA ^ 2) =o[
        Filter.atTop] (fun xMeters : ℝ => xMeters ^ 2) :=
    (Asymptotics.isLittleO_const_id_atTop
      (lengthInMeters setup.wireOffsetA ^ 2)).trans
      hLinearLittleOQuadratic
  have hQuadraticEquivalent :
      Asymptotics.IsEquivalent Filter.atTop
        (fun xMeters : ℝ =>
          xMeters ^ 2 + lengthInMeters setup.wireOffsetA ^ 2)
        (fun xMeters : ℝ => xMeters ^ 2) :=
    Asymptotics.IsEquivalent.refl.add_isLittleO
      hConstantLittleOQuadratic
  have hDenominatorEquivalent :
      Asymptotics.IsEquivalent Filter.atTop
        (fun xMeters : ℝ =>
          Real.pi *
            (xMeters ^ 2 + lengthInMeters setup.wireOffsetA ^ 2))
        (fun xMeters : ℝ => Real.pi * xMeters ^ 2) := by
    have hPi :
        Asymptotics.IsEquivalent Filter.atTop
          (fun _ : ℝ => Real.pi) (fun _ : ℝ => Real.pi) :=
      Asymptotics.IsEquivalent.refl
    have hProduct := hPi.mul hQuadraticEquivalent
    refine (hProduct.congr_left ?_).congr_right ?_
    · exact Filter.Eventually.of_forall (fun _ => rfl)
    · exact Filter.Eventually.of_forall (fun _ => rfl)
  have hFormulaEquivalent :
      Asymptotics.IsEquivalent Filter.atTop
        (fun xMeters : ℝ =>
          permeabilityInTeslaMetersPerAmpere
                setup.vacuumPermeabilityMu0 *
              currentInAmperes setup.currentMagnitudeI *
              lengthInMeters setup.wireOffsetA /
            (Real.pi *
              (xMeters ^ 2 + lengthInMeters setup.wireOffsetA ^ 2)))
        (fun xMeters : ℝ =>
          permeabilityInTeslaMetersPerAmpere
                setup.vacuumPermeabilityMu0 *
              currentInAmperes setup.currentMagnitudeI *
              lengthInMeters setup.wireOffsetA /
            (Real.pi * xMeters ^ 2)) := by
    have hNumerator :
        Asymptotics.IsEquivalent Filter.atTop
          (fun _ : ℝ =>
            permeabilityInTeslaMetersPerAmpere
                setup.vacuumPermeabilityMu0 *
              currentInAmperes setup.currentMagnitudeI *
              lengthInMeters setup.wireOffsetA)
          (fun _ : ℝ =>
            permeabilityInTeslaMetersPerAmpere
                setup.vacuumPermeabilityMu0 *
              currentInAmperes setup.currentMagnitudeI *
              lengthInMeters setup.wireOffsetA) :=
      Asymptotics.IsEquivalent.refl
    have hQuotient := hNumerator.div hDenominatorEquivalent
    refine (hQuotient.congr_left ?_).congr_right ?_
    · exact Filter.Eventually.of_forall (fun _ => rfl)
    · exact Filter.Eventually.of_forall (fun _ => rfl)
  exact hFormulaEquivalent.congr_left hEventuallyExact.symm

end PhyXMiniProblems.ProblemPhyXMini0964
