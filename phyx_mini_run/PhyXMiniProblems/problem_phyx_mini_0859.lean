import Mathlib.Geometry.Euclidean.Simplex
import Physlib.Electromagnetism.Basic
import Physlib.Units.WithDim.Basic

/- USER: The assigned source file did not exist when this autoformalization task began. -/

noncomputable section

namespace PhyXMiniProblems.ProblemPhyXMini0859

open Dimension
open scoped BigOperators

/-!
# Electric potential at the center of an equilateral charge triangle

The primary image shows an equilateral triangle of side `3.0 cm`.  Its top
vertex carries `+1.0 nC`, its bottom-left and bottom-right vertices each carry
`-2.0 nC`, and a black observation dot marks the triangle's centroid.  All
three sides are dashed and each carries a `3.0 cm` label.

Charges, side length, and electric potentials are unit-independent Physlib
dimensionful quantities.  Real numbers below are used only for coherent-SI
readouts, nanocoulomb/centimetre figure labels, and displayed volt choices.
The geometry is represented by Mathlib's `Affine.Triangle`; in particular,
equilateralness and the centroid retain their standard geometric meanings.

Assumption/target split:

* governing laws: the inverse-distance potential of a point charge and scalar
  potential superposition;
* previous-part results: none;
* figure/data readouts: the three signed nanocoulomb labels, the three
  `3.0 cm` side labels, the equilateral geometry, the centroid dot, dashed
  sides, sign glyphs and colours, and the vacuum Coulomb constant;
* current conclusions: the potential at the dot rounds to `-1600 V`, and D is
  the unique nearest displayed choice.

No numerical potential or answer label occurs in the setup, figure predicate,
physical-parameter predicate, or governing-law predicate.
-/

/-! ## Dimensionful physical quantities and coherent-SI readouts -/

/-- The physical dimension `M L² T⁻² C⁻¹` of electric potential. -/
def electricPotentialDimension : Dimension :=
  M𝓭 * L𝓭 * L𝓭 * T𝓭⁻¹ * T𝓭⁻¹ * C𝓭⁻¹

/-- A nonnegative, unit-independent physical length. -/
abbrev LengthQuantity : Type :=
  Dimensionful (WithDim L𝓭 NNReal)

/-- A signed, unit-independent physical electric charge. -/
abbrev SignedChargeQuantity : Type :=
  Dimensionful (WithDim C𝓭 ℝ)

/-- A signed, unit-independent physical electric potential. -/
abbrev ElectricPotentialQuantity : Type :=
  Dimensionful (WithDim electricPotentialDimension ℝ)

/-- Coherent-SI metre readout of a physical length. -/
def lengthInMeters (length : LengthQuantity) : ℝ :=
  ((length UnitChoices.SI).val : ℝ)

/-- Centimetre readout used by the three printed side labels. -/
def lengthInCentimeters (length : LengthQuantity) : ℝ :=
  100 * lengthInMeters length

/-- Coherent-SI coulomb readout of a signed physical charge. -/
def chargeInCoulombs (charge : SignedChargeQuantity) : ℝ :=
  (charge UnitChoices.SI).val

/-- Nanocoulomb readout used by the three printed charge labels. -/
def chargeInNanocoulombs (charge : SignedChargeQuantity) : ℝ :=
  10 ^ 9 * chargeInCoulombs charge

/-- Coherent-SI volt readout of a signed physical electric potential. -/
def electricPotentialInVolts
    (potential : ElectricPotentialQuantity) : ℝ :=
  (potential UnitChoices.SI).val

/-! ## Named vertices, sides, and primary-image vocabulary -/

/-- The three point charges, named by their locations in the image. -/
inductive SourceCharge where
  | top
  | bottomLeft
  | bottomRight
  deriving DecidableEq, Fintype, Repr

/-- Vertex index used for each named source in Mathlib's affine triangle. -/
def sourceVertexIndex : SourceCharge → Fin 3
  | .top => 0
  | .bottomLeft => 1
  | .bottomRight => 2

/-- The three dashed sides of the equilateral triangle. -/
inductive TriangleSide where
  | left
  | right
  | bottom
  deriving DecidableEq, Fintype, Repr

/-- The pair of charged vertices joined by each named side. -/
def sideEndpoints : TriangleSide → SourceCharge × SourceCharge
  | .left => (.top, .bottomLeft)
  | .right => (.top, .bottomRight)
  | .bottom => (.bottomLeft, .bottomRight)

/-- The red and cyan fills used for positive and negative charges. -/
inductive FigureChargeColor where
  | red
  | cyan
  deriving DecidableEq, Repr

/-- The sign glyph drawn inside each coloured charge circle. -/
inductive FigureChargeSign where
  | plus
  | minus
  deriving DecidableEq, Repr

/-- Expected source-circle colour read from the primary image. -/
def expectedChargeColor : SourceCharge → FigureChargeColor
  | .top => .red
  | .bottomLeft => .cyan
  | .bottomRight => .cyan

/-- Expected sign glyph read from the primary image. -/
def expectedChargeSign : SourceCharge → FigureChargeSign
  | .top => .plus
  | .bottomLeft => .minus
  | .bottomRight => .minus

/-- Signed nanocoulomb number printed beside each source circle. -/
def expectedChargeInNanocoulombs : SourceCharge → ℝ
  | .top => 1
  | .bottomLeft => -2
  | .bottomRight => -2

/-- Literal presentation data transcribed from image `859.png`. -/
structure EquilateralChargeFigure where
  sourceColor : SourceCharge → FigureChargeColor
  sourceSign : SourceCharge → FigureChargeSign
  printedChargeNanocoulombs : SourceCharge → ℝ
  printedSideLengthCentimeters : TriangleSide → ℝ
  chargeCircleShown : SourceCharge → Bool
  dashedSideShown : TriangleSide → Bool
  blackObservationDotShown : Bool
  blackObservationDotAtCenter : Bool

/-! ## Physical setup and geometric readouts -/

/-!
The independent electrostatic system.  `sourcePotential` and `totalPotential`
are physical scalar fields on the plane; their relationship is imposed only
by the governing laws below.  Neither field is defined from an answer choice.
-/
structure EquilateralPointChargeSetup where
  triangle : Affine.Triangle ℝ (Space 2)
  sideLength : LengthQuantity
  sourceCharge : SourceCharge → SignedChargeQuantity
  electromagneticSystem : Electromagnetism.EMSystem
  sourcePotential : SourceCharge → Space 2 → ElectricPotentialQuantity
  totalPotential : Space 2 → ElectricPotentialQuantity
  observationPoint : Space 2
  figure : EquilateralChargeFigure

/-- Spatial position of a named source charge. -/
def sourcePosition
    (setup : EquilateralPointChargeSetup) (source : SourceCharge) : Space 2 :=
  setup.triangle.points (sourceVertexIndex source)

/-- Metre-coordinate distance between the endpoints of a named side. -/
def sideLengthInMeters
    (setup : EquilateralPointChargeSetup) (side : TriangleSide) : ℝ :=
  dist (sourcePosition setup (sideEndpoints side).1)
    (sourcePosition setup (sideEndpoints side).2)

/-- Metre-coordinate distance from a source charge to the observation dot. -/
def sourceDistanceToObservationInMeters
    (setup : EquilateralPointChargeSetup) (source : SourceCharge) : ℝ :=
  dist (sourcePosition setup source) setup.observationPoint

/-- Volt readout of the resultant potential at the black dot. -/
def potentialAtObservationInVolts
    (setup : EquilateralPointChargeSetup) : ℝ :=
  electricPotentialInVolts (setup.totalPotential setup.observationPoint)

/-! ## Figure evidence, reference data, and governing laws -/

/-!
All numerical and qualitative information read from the primary image.  The
physical observation point is identified with Mathlib's triangle centroid.
No electric-potential value or answer choice occurs in this predicate.
-/
structure MatchesPrimaryFigure859
    (setup : EquilateralPointChargeSetup) : Prop where
  triangleIsEquilateral : setup.triangle.Equilateral
  observationPointIsCentroid :
    setup.observationPoint = setup.triangle.centroid
  sourceColors : ∀ source,
    setup.figure.sourceColor source = expectedChargeColor source
  sourceSignGlyphs : ∀ source,
    setup.figure.sourceSign source = expectedChargeSign source
  everyChargeCircleShown : ∀ source,
    setup.figure.chargeCircleShown source = true
  printedChargeLabels : ∀ source,
    setup.figure.printedChargeNanocoulombs source =
      expectedChargeInNanocoulombs source
  physicalChargesMatchPrintedLabels : ∀ source,
    chargeInNanocoulombs (setup.sourceCharge source) =
      setup.figure.printedChargeNanocoulombs source
  everyDashedSideShown : ∀ side,
    setup.figure.dashedSideShown side = true
  printedSideLabelsAreThreeCentimeters : ∀ side,
    setup.figure.printedSideLengthCentimeters side = 3
  physicalSideLengthMatchesPrintedLabels : ∀ side,
    lengthInCentimeters setup.sideLength =
      setup.figure.printedSideLengthCentimeters side
  geometricSidesMatchPhysicalSideLength : ∀ side,
    sideLengthInMeters setup side = lengthInMeters setup.sideLength
  blackDotShown : setup.figure.blackObservationDotShown = true
  blackDotMarkedAtCenter : setup.figure.blackObservationDotAtCenter = true

/-- Standard vacuum calibration of Physlib's Coulomb constant, in SI units. -/
structure UsesVacuumCoulombConstant
    (setup : EquilateralPointChargeSetup) : Prop where
  vacuumSIReadout :
    setup.electromagneticSystem.coulombConstant =
      (89875517923 : ℝ) / 10

/-- Positivity and noncoincidence conditions for the depicted setup. -/
structure HasPhysicalTriangleParameters
    (setup : EquilateralPointChargeSetup) : Prop where
  sideLengthPositive : 0 < lengthInMeters setup.sideLength
  coulombConstantPositive :
    0 < setup.electromagneticSystem.coulombConstant
  observationAwayFromSources : ∀ source,
    setup.observationPoint ≠ sourcePosition setup source

/-!
For a point charge `q`, the electrostatic potential at a point a distance `r`
away is `k q / r`.  Potentials superpose as signed scalars.  The first field
states the point-charge law at every nonsource point, and the second states
superposition at every point; neither mentions the requested numerical value.
-/
structure SatisfiesPointChargePotentialAndSuperpositionLaws
    (setup : EquilateralPointChargeSetup) : Prop where
  pointChargePotential : ∀ source point,
    point ≠ sourcePosition setup source →
      electricPotentialInVolts (setup.sourcePotential source point) =
        setup.electromagneticSystem.coulombConstant *
          chargeInCoulombs (setup.sourceCharge source) /
          dist (sourcePosition setup source) point
  scalarPotentialSuperposition : ∀ point,
    electricPotentialInVolts (setup.totalPotential point) =
      ∑ source : SourceCharge,
        electricPotentialInVolts (setup.sourcePotential source point)

/-! ## Derived geometric, electrostatic, and numerical targets -/

/-!
In an equilateral triangle, the centroid is also the circumcenter, and its
distance from every vertex is the side length divided by `√3`.
-/
lemma sourceDistanceToCentroid_eq_side_div_sqrtThree
    (setup : EquilateralPointChargeSetup)
    (hFigure : MatchesPrimaryFigure859 setup)
    (hPhysical : HasPhysicalTriangleParameters setup) :
    ∀ source,
      sourceDistanceToObservationInMeters setup source =
        lengthInMeters setup.sideLength / Real.sqrt 3 := by
  have radius_formula (A B C G : Space 2) (L : ℝ)
      (hL : 0 < L)
      (hG :
        G -ᵥ A =
          (1 / 3 : ℝ) • (B -ᵥ A) + (1 / 3 : ℝ) • (C -ᵥ A))
      (hAB : dist A B = L)
      (hAC : dist A C = L)
      (hBC : dist B C = L) :
      dist A G = L / Real.sqrt 3 := by
    let u := B -ᵥ A
    let v := C -ᵥ A
    have hu : ‖u‖ = L := by
      simpa only [u, ← dist_eq_norm_vsub (EuclideanSpace ℝ (Fin 2)),
        dist_comm] using hAB
    have hv : ‖v‖ = L := by
      simpa only [v, ← dist_eq_norm_vsub (EuclideanSpace ℝ (Fin 2)),
        dist_comm] using hAC
    have hvsubu : ‖v - u‖ = L := by
      dsimp only [u, v]
      rw [vsub_sub_vsub_cancel_right]
      simpa only [← dist_eq_norm_vsub (EuclideanSpace ℝ (Fin 2)),
        dist_comm] using hBC
    have hsub := norm_sub_sq_real v u
    rw [hvsubu, hv, hu] at hsub
    have hadd := norm_add_sq_real u v
    rw [hu, hv] at hadd
    have hinner : 2 * inner ℝ u v = L ^ 2 := by
      rw [real_inner_comm] at hsub
      nlinarith
    have huv_sq : ‖u + v‖ ^ 2 = 3 * L ^ 2 := by
      nlinarith
    have hG' : G -ᵥ A = (1 / 3 : ℝ) • (u + v) := by
      rw [hG]
      simp only [u, v, smul_add]
    apply
      (sq_eq_sq₀ dist_nonneg
        (div_nonneg hL.le (Real.sqrt_nonneg 3))).mp
    rw [dist_comm A G, dist_eq_norm_vsub, hG', norm_smul,
      Real.norm_eq_abs,
      abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 1 / 3), mul_pow,
      huv_sq]
    have hsqrt : Real.sqrt 3 ^ 2 = (3 : ℝ) :=
      Real.sq_sqrt (by norm_num)
    field_simp
    nlinarith
  have h01 :
      dist (setup.triangle.points 0) (setup.triangle.points 1) =
        lengthInMeters setup.sideLength := by
    simpa [sideLengthInMeters, sourcePosition, sideEndpoints,
      sourceVertexIndex] using
      hFigure.geometricSidesMatchPhysicalSideLength TriangleSide.left
  have h02 :
      dist (setup.triangle.points 0) (setup.triangle.points 2) =
        lengthInMeters setup.sideLength := by
    simpa [sideLengthInMeters, sourcePosition, sideEndpoints,
      sourceVertexIndex] using
      hFigure.geometricSidesMatchPhysicalSideLength TriangleSide.right
  have h12 :
      dist (setup.triangle.points 1) (setup.triangle.points 2) =
        lengthInMeters setup.sideLength := by
    simpa [sideLengthInMeters, sourcePosition, sideEndpoints,
      sourceVertexIndex] using
      hFigure.geometricSidesMatchPhysicalSideLength TriangleSide.bottom
  have hc0 := setup.triangle.centroid_vsub_eq (setup.triangle.points 0)
  have hc1 := setup.triangle.centroid_vsub_eq (setup.triangle.points 1)
  have hc2 := setup.triangle.centroid_vsub_eq (setup.triangle.points 2)
  rw [Fin.sum_univ_three] at hc0 hc1 hc2
  simp only [vsub_self, zero_add, add_zero] at hc0 hc1 hc2
  norm_num at hc0 hc1 hc2
  have h0 :
      dist (setup.triangle.points 0) setup.triangle.centroid =
        lengthInMeters setup.sideLength / Real.sqrt 3 :=
    radius_formula _ _ _ _ _ hPhysical.sideLengthPositive hc0
      h01 h02 h12
  have h1 :
      dist (setup.triangle.points 1) setup.triangle.centroid =
        lengthInMeters setup.sideLength / Real.sqrt 3 :=
    radius_formula _ _ _ _ _ hPhysical.sideLengthPositive hc1
      (by
        calc
          dist (setup.triangle.points 1) (setup.triangle.points 0) =
              dist (setup.triangle.points 0) (setup.triangle.points 1) :=
            dist_comm _ _
          _ = lengthInMeters setup.sideLength := h01)
      h12 h02
  have h2 :
      dist (setup.triangle.points 2) setup.triangle.centroid =
        lengthInMeters setup.sideLength / Real.sqrt 3 :=
    radius_formula _ _ _ _ _ hPhysical.sideLengthPositive hc2
      (by
        calc
          dist (setup.triangle.points 2) (setup.triangle.points 0) =
              dist (setup.triangle.points 0) (setup.triangle.points 2) :=
            dist_comm _ _
          _ = lengthInMeters setup.sideLength := h02)
      (by
        calc
          dist (setup.triangle.points 2) (setup.triangle.points 1) =
              dist (setup.triangle.points 1) (setup.triangle.points 2) :=
            dist_comm _ _
          _ = lengthInMeters setup.sideLength := h12)
      h01
  intro source
  fin_cases source
  · simpa [sourceDistanceToObservationInMeters, sourcePosition,
      sourceVertexIndex, hFigure.observationPointIsCentroid] using h0
  · simpa [sourceDistanceToObservationInMeters, sourcePosition,
      sourceVertexIndex, hFigure.observationPointIsCentroid] using h1
  · simpa [sourceDistanceToObservationInMeters, sourcePosition,
      sourceVertexIndex, hFigure.observationPointIsCentroid] using h2

/-!
The inverse-distance law and scalar superposition express the potential at the
dot as the sum of the three source contributions.
-/
lemma potentialAtObservation_eq_pointChargeSum
    (setup : EquilateralPointChargeSetup)
    (hPhysical : HasPhysicalTriangleParameters setup)
    (hLaws : SatisfiesPointChargePotentialAndSuperpositionLaws setup) :
    potentialAtObservationInVolts setup =
      ∑ source : SourceCharge,
        setup.electromagneticSystem.coulombConstant *
          chargeInCoulombs (setup.sourceCharge source) /
          sourceDistanceToObservationInMeters setup source := by
  unfold potentialAtObservationInVolts
  rw [hLaws.scalarPotentialSuperposition]
  apply Finset.sum_congr rfl
  intro source _
  rw [hLaws.pointChargePotential source setup.observationPoint
    (hPhysical.observationAwayFromSources source)]
  rfl

/-!
With the image charges, side length, and vacuum calibration, the actual
potential lies strictly between `-1650 V` and `-1550 V`.
-/
lemma potentialAtObservation_numericalBounds
    (setup : EquilateralPointChargeSetup)
    (hFigure : MatchesPrimaryFigure859 setup)
    (hVacuum : UsesVacuumCoulombConstant setup)
    (hPhysical : HasPhysicalTriangleParameters setup)
    (hLaws : SatisfiesPointChargePotentialAndSuperpositionLaws setup) :
    (-1650 : ℝ) < potentialAtObservationInVolts setup ∧
      potentialAtObservationInVolts setup < (-1550 : ℝ) := by
  have hLengthLabel :=
    hFigure.physicalSideLengthMatchesPrintedLabels TriangleSide.left
  rw [hFigure.printedSideLabelsAreThreeCentimeters TriangleSide.left] at hLengthLabel
  have hLength :
      lengthInMeters setup.sideLength = (3 : ℝ) / 100 := by
    unfold lengthInCentimeters at hLengthLabel
    linarith
  have hCharge (source : SourceCharge) :
      chargeInCoulombs (setup.sourceCharge source) =
        expectedChargeInNanocoulombs source / (10 : ℝ) ^ 9 := by
    have h := hFigure.physicalChargesMatchPrintedLabels source
    rw [hFigure.printedChargeLabels source] at h
    unfold chargeInNanocoulombs at h
    norm_num at h ⊢
    linarith
  have hDistance :=
    sourceDistanceToCentroid_eq_side_div_sqrtThree setup hFigure hPhysical
  rw [potentialAtObservation_eq_pointChargeSum setup hPhysical hLaws]
  have huniv : (Finset.univ : Finset SourceCharge) =
      {.top, .bottomLeft, .bottomRight} := by
    decide
  rw [huniv]
  simp only [Finset.mem_insert, reduceCtorEq, Finset.mem_singleton,
    or_self, not_false_eq_true, Finset.sum_insert, Finset.sum_singleton]
  rw [hVacuum.vacuumSIReadout]
  rw [hCharge, hCharge, hCharge]
  simp only [expectedChargeInNanocoulombs]
  rw [hDistance, hDistance, hDistance, hLength]
  have hsqrt_pos : 0 < Real.sqrt 3 :=
    Real.sqrt_pos.2 (by norm_num)
  have hsqrt_sq : Real.sqrt 3 ^ 2 = (3 : ℝ) :=
    Real.sq_sqrt (by norm_num)
  have hsqrt_lower : (173 : ℝ) / 100 < Real.sqrt 3 := by
    apply (sq_lt_sq₀ (by norm_num) (Real.sqrt_nonneg 3)).mp
    rw [hsqrt_sq]
    norm_num
  have hsqrt_upper : Real.sqrt 3 < (7 : ℝ) / 4 := by
    apply (sq_lt_sq₀ (Real.sqrt_nonneg 3) (by norm_num)).mp
    rw [hsqrt_sq]
    norm_num
  field_simp
  constructor <;> nlinarith

/-- Labels of the four electric-potential choices printed in the question. -/
inductive AnswerChoice where
  | A
  | B
  | C
  | D
  deriving DecidableEq, Fintype, Repr

/-- Electric potential in volts printed beside each answer label. -/
def displayedPotentialInVolts : AnswerChoice → ℝ
  | .A => -1100
  | .B => 1600
  | .C => -800
  | .D => -1600

/-- A computed voltage rounds to a displayed value at the nearest `100 V`. -/
def RoundsToNearestHundredVolts (actual displayed : ℝ) : Prop :=
  |actual - displayed| < 50

/-- A displayed choice is strictly nearer to the computed voltage than every alternative. -/
def IsUniqueNearestDisplayedPotential
    (actual : ℝ) (choice : AnswerChoice) : Prop :=
  ∀ other, other ≠ choice →
    |actual - displayedPotentialInVolts choice| <
      |actual - displayedPotentialInVolts other|

/-!
Blueprint declaration `thm:physics:phyx_mini_0859:target`.

The potential at the centroid rounds to `-1600 V`, and this uniquely selects
answer D among the four displayed choices.
-/
theorem problem_phyx_mini_0859
    (setup : EquilateralPointChargeSetup)
    (hFigure : MatchesPrimaryFigure859 setup)
    (hVacuum : UsesVacuumCoulombConstant setup)
    (hPhysical : HasPhysicalTriangleParameters setup)
    (hLaws : SatisfiesPointChargePotentialAndSuperpositionLaws setup) :
    (-1650 : ℝ) < potentialAtObservationInVolts setup ∧
      potentialAtObservationInVolts setup < (-1550 : ℝ) ∧
      RoundsToNearestHundredVolts
        (potentialAtObservationInVolts setup)
        (displayedPotentialInVolts .D) ∧
      IsUniqueNearestDisplayedPotential
        (potentialAtObservationInVolts setup) .D := by
  have hBounds :=
    potentialAtObservation_numericalBounds
      setup hFigure hVacuum hPhysical hLaws
  rcases hBounds with ⟨hlower, hupper⟩
  refine ⟨hlower, hupper, ?_, ?_⟩
  · rw [RoundsToNearestHundredVolts, displayedPotentialInVolts, abs_lt]
    constructor <;> linarith
  · intro other hother
    have hD :
        |potentialAtObservationInVolts setup -
          displayedPotentialInVolts .D| < 50 := by
      rw [displayedPotentialInVolts, abs_lt]
      constructor <;> linarith
    simp only [displayedPotentialInVolts] at hD
    fin_cases other
    · rw [displayedPotentialInVolts, displayedPotentialInVolts]
      have hA :
          potentialAtObservationInVolts setup - (-1100 : ℝ) ≤ 0 := by
        linarith
      rw [abs_of_nonpos hA]
      linarith
    · rw [displayedPotentialInVolts, displayedPotentialInVolts]
      have hB :
          potentialAtObservationInVolts setup - (1600 : ℝ) ≤ 0 := by
        linarith
      rw [abs_of_nonpos hB]
      linarith
    · rw [displayedPotentialInVolts, displayedPotentialInVolts]
      have hC :
          potentialAtObservationInVolts setup - (-800 : ℝ) ≤ 0 := by
        linarith
      rw [abs_of_nonpos hC]
      linarith
    · exact (hother rfl).elim

end PhyXMiniProblems.ProblemPhyXMini0859
