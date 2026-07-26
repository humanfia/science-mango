import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Order.Filter.Extr
import Physlib.Units.WithDim.Basic

noncomputable section

namespace PhyXMiniProblems.ProblemPhyXMini0265

open Dimension
open scoped Topology

/-!
# Minimum-period suspension point of a rectangular block

A uniform rectangular block has face dimensions `a = 35 cm` and `b = 45 cm`.
A thin horizontal rod passes through a narrow hole in the block and provides
the pivot axis.  The illustrated hole is at a distance labelled `r` from the
center, on the segment from the center to a corner.  For small oscillations,
the block is modeled as a physical pendulum.

The dimensional quantities below use Physlib's unit-independent
`Dimensionful` type.  Real scalars are used only for named unit readouts and
for coordinates explicitly measured in meters.

Assumption/target boundary:

* The problem and figure supply the side lengths, the center/corner/hole
  geometry, the horizontal thin rod, and the small-amplitude regime.
* The governing interface supplies the uniform-rectangle centroidal moment of
  inertia, the parallel-axis theorem, radial invariance, and a right-hand
  zero-amplitude limit connecting actual oscillation periods to the linearized
  physical-pendulum period law.
* The radius that minimizes the period, its numerical value, answer C, and the
  circle of equally minimizing holes are conclusions only.
-/

/-! ## Dimensionful physical quantities and coherent readouts -/

/-- A nonnegative unit-independent physical mass. -/
abbrev MassQuantity : Type := Dimensionful (WithDim M𝓭 NNReal)

/-- A nonnegative unit-independent physical length. -/
abbrev LengthQuantity : Type := Dimensionful (WithDim L𝓭 NNReal)

/-- A nonnegative unit-independent duration. -/
abbrev TimeQuantity : Type := Dimensionful (WithDim T𝓭 NNReal)

/-- A nonnegative acceleration magnitude, carrying dimension `L T⁻²`. -/
abbrev AccelerationMagnitudeQuantity : Type :=
  Dimensionful (WithDim (L𝓭 * T𝓭⁻¹ * T𝓭⁻¹) NNReal)

/-- A scalar moment of inertia, carrying dimension `M L²`. -/
abbrev MomentOfInertiaQuantity : Type :=
  Dimensionful (WithDim (M𝓭 * L𝓭 * L𝓭) NNReal)

/-- Read a physical length in a selected length unit. -/
def lengthReadout (unit : LengthUnit) (length : LengthQuantity) : ℝ :=
  ((length {UnitChoices.SI with length := unit}).val : ℝ)

/-- Meter readout of a physical length. -/
def lengthInMeters (length : LengthQuantity) : ℝ :=
  lengthReadout LengthUnit.meters length

/-- Centimeter readout of a physical length. -/
def lengthInCentimeters (length : LengthQuantity) : ℝ :=
  lengthReadout LengthUnit.centimeters length

/-- Kilogram readout of a physical mass. -/
def massInKilograms (mass : MassQuantity) : ℝ :=
  ((mass UnitChoices.SI).val : ℝ)

/-- Second readout of a physical duration. -/
def timeInSeconds (duration : TimeQuantity) : ℝ :=
  ((duration UnitChoices.SI).val : ℝ)

/-- Meter-per-second-squared readout of an acceleration magnitude. -/
def accelerationInMetersPerSecondSquared
    (acceleration : AccelerationMagnitudeQuantity) : ℝ :=
  ((acceleration UnitChoices.SI).val : ℝ)

/-- Kilogram-meter-squared readout of a scalar moment of inertia. -/
def momentOfInertiaInKilogramMetersSquared
    (inertia : MomentOfInertiaQuantity) : ℝ :=
  ((inertia UnitChoices.SI).val : ℝ)

/-!
Coordinates in `FacePointInMeters` are scalar meter readouts in the plane of
the rectangular face.  This is a coordinate space, not an alias for a
physical length quantity.
-/
abbrev FacePointInMeters : Type := EuclideanSpace ℝ (Fin 2)

/-! ## Apparatus roles and primary-figure labels -/

/-- The two side dimensions printed as `a` and `b`. -/
inductive RectangleFaceSide where
  | a
  | b
  deriving DecidableEq, Repr

/-- Distinguished points in the supplied diagram. -/
inductive FigurePoint where
  | center
  | chosenCorner
  | pivotHole
  deriving DecidableEq, Repr

/-- Length labels visible in the figure. -/
inductive FigureLengthLabel where
  | a
  | b
  | r
  deriving DecidableEq, Repr

/-- Qualitative features visible in, or directly specified with, the figure. -/
inductive FigureFeature where
  | rectangularBlock
  | centerPoint
  | chosenCorner
  | narrowPivotHole
  | centerToCornerLine
  | distanceArrowR
  | sideDimensionA
  | sideDimensionB
  deriving DecidableEq, Repr

/-- Shape assigned to the swinging face of the block. -/
inductive BlockFaceShape where
  | rectangle
  deriving DecidableEq, Repr

/-- Idealized distribution of the block mass. -/
inductive BlockMassDistribution where
  | uniform
  deriving DecidableEq, Repr

/-- Mechanical idealization of the suspension rod. -/
inductive SuspensionRodModel where
  | thinRigidRod
  deriving DecidableEq, Repr

/-- Orientation of the pivot axis relative to gravity. -/
inductive PivotAxisOrientation where
  | horizontal
  deriving DecidableEq, Repr

/-- Relation between the rod axis and the pictured rectangular face. -/
inductive PivotAxisRelativeToFace where
  | normalToFace
  deriving DecidableEq, Repr

/-- Dynamical approximation requested in the problem. -/
inductive OscillationRegime where
  | smallAmplitudeSimpleHarmonicApproximation
  deriving DecidableEq, Repr

/-!
Qualitative and coordinate information in the supplied figure.  The face
region and point coordinates are given in meter readouts in the plane normal
to the rod.
-/
structure RectangularBlockFigure where
  faceShape : BlockFaceShape
  shows : FigureFeature → Bool
  pointCoordinatesMeters : FigurePoint → FacePointInMeters
  blockFaceRegionMeters : Set FacePointInMeters
  faceSideLabel : RectangleFaceSide → FigureLengthLabel
  centerToHoleLabel : FigureLengthLabel

/-!
Independent physical quantities for the rectangular-block pendulum.

The illustrated offset is the generic distance marked `r`; it is not assigned
the value that minimizes the period.  The finite-amplitude period depends on
both the offset and a dimensionless angular-amplitude readout in radians.  Its
small-amplitude limiting period is stored independently, so the governing
laws must relate the nonlinear measurements to their zero-amplitude limit.
This prevents the phrase "small angles" from silently globalizing the
linearized formula to every oscillation amplitude.
-/
structure RectangularBlockPendulumSetup where
  figure : RectangularBlockFigure
  faceSideLength : RectangleFaceSide → LengthQuantity
  blockMass : MassQuantity
  massDistribution : BlockMassDistribution
  suspensionRodModel : SuspensionRodModel
  suspensionRodPassesThrough : FigurePoint
  pivotAxisOrientation : PivotAxisOrientation
  pivotAxisRelativeToFace : PivotAxisRelativeToFace
  oscillationRegime : OscillationRegime
  illustratedPivotOffset : LengthQuantity
  gravitationalAccelerationMagnitude : AccelerationMagnitudeQuantity
  centroidalMomentOfInertia : MomentOfInertiaQuantity
  pivotMomentOfInertiaAtOffsetMeters : ℝ → MomentOfInertiaQuantity
  oscillationPeriodAtOffsetAndAmplitudeRadians : ℝ → ℝ → TimeQuantity
  smallAmplitudeLimitPeriodAtOffsetMeters : ℝ → TimeQuantity
  smallAmplitudeLimitPeriodAtFacePoint : FacePointInMeters → TimeQuantity

/-! ## Geometric and optimization domains -/

/-- Half the diagonal of the rectangular face, as a meter readout. -/
def rectangleHalfDiagonalMeters
    (setup : RectangularBlockPendulumSetup) : ℝ :=
  Real.sqrt
    ((lengthInMeters (setup.faceSideLength .a) / 2) ^ 2 +
      (lengthInMeters (setup.faceSideLength .b) / 2) ^ 2)

/-- Positive offsets along a center-to-corner segment. -/
def admissiblePivotOffsetMeters
    (setup : RectangularBlockPendulumSetup) : Set ℝ :=
  Set.Ioc 0 (rectangleHalfDiagonalMeters setup)

/-- Points of the block face distinct from its center. -/
def admissiblePivotPoints
    (setup : RectangularBlockPendulumSetup) : Set FacePointInMeters :=
  {point |
    point ∈ setup.figure.blockFaceRegionMeters ∧
      0 < dist (setup.figure.pointCoordinatesMeters .center) point}

/-- Actual period readout at a positive angular amplitude, measured in radians. -/
def oscillationPeriodSecondsAtOffsetAndAmplitudeRadians
    (setup : RectangularBlockPendulumSetup)
    (offsetMeters amplitudeRadians : ℝ) : ℝ :=
  timeInSeconds
    (setup.oscillationPeriodAtOffsetAndAmplitudeRadians
      offsetMeters amplitudeRadians)

/-- Zero-amplitude limiting period used for the offset optimization. -/
def smallAmplitudeLimitPeriodSecondsAtOffsetMeters
    (setup : RectangularBlockPendulumSetup) (offsetMeters : ℝ) : ℝ :=
  timeInSeconds (setup.smallAmplitudeLimitPeriodAtOffsetMeters offsetMeters)

/-- Zero-amplitude limiting period for a hole specified by face coordinates. -/
def smallAmplitudeLimitPeriodSecondsAtFacePoint
    (setup : RectangularBlockPendulumSetup)
    (point : FacePointInMeters) : ℝ :=
  timeInSeconds (setup.smallAmplitudeLimitPeriodAtFacePoint point)

/-!
The radius of gyration about the centroidal axis parallel to the rod.  This is
a standard derived physical quantity.  Its role as the minimizing offset is
proved below rather than built into this definition.
-/
def radiusOfGyrationMeters
    (setup : RectangularBlockPendulumSetup) : ℝ :=
  Real.sqrt
    (momentOfInertiaInKilogramMetersSquared
        setup.centroidalMomentOfInertia /
      massInKilograms setup.blockMass)

/-! ## Figure/data readouts and governing laws -/

/-!
Primary-image geometry.  The hole is on the segment from the center to the
chosen corner and the arrow labelled `r` measures its distance from the
center.  The disk inclusions record elementary centered-rectangle geometry:
the inscribed disk lies in the face, and the face lies in its circumscribed
disk.
-/
structure MatchesPrimaryFigure
    (setup : RectangularBlockPendulumSetup) : Prop where
  rectangularFace : setup.figure.faceShape = .rectangle
  everyFeatureShown : ∀ feature, setup.figure.shows feature = true
  sideALabel : setup.figure.faceSideLabel .a = .a
  sideBLabel : setup.figure.faceSideLabel .b = .b
  offsetLabel : setup.figure.centerToHoleLabel = .r
  centerBelongsToFace :
    setup.figure.pointCoordinatesMeters .center ∈
      setup.figure.blockFaceRegionMeters
  cornerBelongsToFace :
    setup.figure.pointCoordinatesMeters .chosenCorner ∈
      setup.figure.blockFaceRegionMeters
  holeBelongsToFace :
    setup.figure.pointCoordinatesMeters .pivotHole ∈
      setup.figure.blockFaceRegionMeters
  holeOnCenterCornerSegment :
    ∃ t : ℝ, t ∈ Set.Icc 0 1 ∧
      setup.figure.pointCoordinatesMeters .pivotHole =
        setup.figure.pointCoordinatesMeters .center +
          t • (setup.figure.pointCoordinatesMeters .chosenCorner -
            setup.figure.pointCoordinatesMeters .center)
  offsetRMeasuresCenterToHole :
    dist (setup.figure.pointCoordinatesMeters .center)
        (setup.figure.pointCoordinatesMeters .pivotHole) =
      lengthInMeters setup.illustratedPivotOffset
  cornerDistanceIsHalfDiagonal :
    dist (setup.figure.pointCoordinatesMeters .center)
        (setup.figure.pointCoordinatesMeters .chosenCorner) =
      rectangleHalfDiagonalMeters setup
  centeredInscribedDiskWithinFace :
    Metric.closedBall
        (setup.figure.pointCoordinatesMeters .center)
        (min (lengthInMeters (setup.faceSideLength .a) / 2)
          (lengthInMeters (setup.faceSideLength .b) / 2)) ⊆
      setup.figure.blockFaceRegionMeters
  faceWithinCircumscribedDisk :
    setup.figure.blockFaceRegionMeters ⊆
      Metric.closedBall
        (setup.figure.pointCoordinatesMeters .center)
        (rectangleHalfDiagonalMeters setup)

/-!
Numerical and qualitative data stated in the problem.  Both centimeter and
meter readouts are retained explicitly, as in the source and the displayed
answers.  No minimizing value occurs here.
-/
structure MatchesProblemData
    (setup : RectangularBlockPendulumSetup) : Prop where
  sideACentimeters :
    lengthInCentimeters (setup.faceSideLength .a) = 35
  sideBCentimeters :
    lengthInCentimeters (setup.faceSideLength .b) = 45
  sideAMeters : lengthInMeters (setup.faceSideLength .a) = 35 / 100
  sideBMeters : lengthInMeters (setup.faceSideLength .b) = 45 / 100
  uniformBlock : setup.massDistribution = .uniform
  thinRod : setup.suspensionRodModel = .thinRigidRod
  rodThroughHole : setup.suspensionRodPassesThrough = .pivotHole
  horizontalAxis : setup.pivotAxisOrientation = .horizontal
  rodNormalToPicturedFace : setup.pivotAxisRelativeToFace = .normalToFace
  smallAmplitudeSHMApproximation :
    setup.oscillationRegime = .smallAmplitudeSimpleHarmonicApproximation

/-- Positivity and nondegeneracy of the physical parameters. -/
structure HasPhysicalParameters
    (setup : RectangularBlockPendulumSetup) : Prop where
  sideAPositive : 0 < lengthInMeters (setup.faceSideLength .a)
  sideBPositive : 0 < lengthInMeters (setup.faceSideLength .b)
  massPositive : 0 < massInKilograms setup.blockMass
  gravityPositive :
    0 < accelerationInMetersPerSecondSquared
      setup.gravitationalAccelerationMagnitude
  centroidalInertiaPositive :
    0 < momentOfInertiaInKilogramMetersSquared
      setup.centroidalMomentOfInertia
  illustratedOffsetPositive :
    0 < lengthInMeters setup.illustratedPivotOffset

/-!
Governing laws for the uniform rectangular physical pendulum:

* `I_cm = M (a² + b²) / 12` about the centroidal rod direction;
* `I_p(r) = I_cm + M r²` by the parallel-axis theorem;
* for each admissible `r`, the actual period tends from positive angular
  amplitudes to a stored zero-amplitude limiting period;
* that limiting period is `2π √(I_p(r) / (M g r))`;
* holes at equal center distance have equal limiting periods.

These fields relate independently stored quantities.  They do not state the
radius of gyration, the minimizing offset, the value `0.16 m`, or an answer
choice.  In particular, the physical-pendulum formula is not asserted as an
exact finite-amplitude law merely because a regime tag says "small angle".
-/
structure SatisfiesRectangularPhysicalPendulumLaws
    (setup : RectangularBlockPendulumSetup) : Prop where
  uniformRectangleCentroidalInertia :
    momentOfInertiaInKilogramMetersSquared
        setup.centroidalMomentOfInertia =
      massInKilograms setup.blockMass *
        (lengthInMeters (setup.faceSideLength .a) ^ 2 +
          lengthInMeters (setup.faceSideLength .b) ^ 2) / 12
  parallelAxisLaw : ∀ offsetMeters : ℝ, 0 ≤ offsetMeters →
    momentOfInertiaInKilogramMetersSquared
        (setup.pivotMomentOfInertiaAtOffsetMeters offsetMeters) =
      momentOfInertiaInKilogramMetersSquared
          setup.centroidalMomentOfInertia +
        massInKilograms setup.blockMass * offsetMeters ^ 2
  actualPeriodConvergesToSmallAmplitudeLimit :
    ∀ offsetMeters ∈ admissiblePivotOffsetMeters setup,
      Filter.Tendsto
        (fun amplitudeRadians =>
          oscillationPeriodSecondsAtOffsetAndAmplitudeRadians
            setup offsetMeters amplitudeRadians)
        (nhdsWithin 0 (Set.Ioi 0))
        (𝓝 (smallAmplitudeLimitPeriodSecondsAtOffsetMeters
          setup offsetMeters))
  smallAmplitudeLimitPhysicalPendulumPeriodLaw :
    ∀ offsetMeters ∈ admissiblePivotOffsetMeters setup,
      smallAmplitudeLimitPeriodSecondsAtOffsetMeters setup offsetMeters =
        2 * Real.pi *
          Real.sqrt
            (momentOfInertiaInKilogramMetersSquared
                (setup.pivotMomentOfInertiaAtOffsetMeters offsetMeters) /
              (massInKilograms setup.blockMass *
                accelerationInMetersPerSecondSquared
                  setup.gravitationalAccelerationMagnitude *
                offsetMeters))
  limitingPeriodDependsOnlyOnCenterDistance :
    ∀ point ∈ admissiblePivotPoints setup,
      smallAmplitudeLimitPeriodSecondsAtFacePoint setup point =
        smallAmplitudeLimitPeriodSecondsAtOffsetMeters setup
          (dist (setup.figure.pointCoordinatesMeters .center) point)

/-! ## Displayed choices and formalization target -/

/-- Labels printed beside the four candidate offsets. -/
inductive AnswerChoice where
  | A
  | B
  | C
  | D
  deriving DecidableEq, Repr

/-- Offset in meters printed beside each answer label. -/
def AnswerChoice.offsetMeters : AnswerChoice → ℝ
  | .A => 12 / 100
  | .B => 14 / 100
  | .C => 16 / 100
  | .D => 18 / 100

/-- The answer label recorded in the supplied dataset. -/
def recordedAnswerChoice : AnswerChoice := .C

/-- Agreement with a displayed offset to the nearest hundredth of a meter. -/
def MatchesDisplayedOffset
    (offsetMeters : ℝ) (choice : AnswerChoice) : Prop :=
  |offsetMeters - choice.offsetMeters| < 1 / 200

/-- A displayed choice is at least as close as every listed alternative. -/
def IsClosestDisplayedOffset
    (offsetMeters : ℝ) (choice : AnswerChoice) : Prop :=
  ∀ alternative : AnswerChoice,
    |offsetMeters - choice.offsetMeters| ≤
      |offsetMeters - alternative.offsetMeters|

/-!
For a physical pendulum obeying the governing laws, the centroidal radius of
gyration is an admissible center-to-hole distance and globally minimizes the
small-angle period along the center-to-corner segment.  This derived lemma
contains no numerical answer-choice assertion.
-/
lemma radiusOfGyration_minimizesSmallAmplitudeLimitPeriod
    (setup : RectangularBlockPendulumSetup)
    (_data : MatchesProblemData setup)
    (_physical : HasPhysicalParameters setup)
    (_laws : SatisfiesRectangularPhysicalPendulumLaws setup) :
    radiusOfGyrationMeters setup ∈ admissiblePivotOffsetMeters setup ∧
      IsMinOn (smallAmplitudeLimitPeriodSecondsAtOffsetMeters setup)
        (admissiblePivotOffsetMeters setup)
        (radiusOfGyrationMeters setup) := by
  have hmass : 0 < massInKilograms setup.blockMass :=
    _physical.massPositive
  have hmass_ne : massInKilograms setup.blockMass ≠ 0 :=
    ne_of_gt hmass
  have hratio_pos :
      0 <
        momentOfInertiaInKilogramMetersSquared
            setup.centroidalMomentOfInertia /
          massInKilograms setup.blockMass :=
    div_pos _physical.centroidalInertiaPositive hmass
  have hr_pos : 0 < radiusOfGyrationMeters setup := by
    rw [radiusOfGyrationMeters]
    exact Real.sqrt_pos.2 hratio_pos
  have hr_sq :
      radiusOfGyrationMeters setup ^ 2 =
        momentOfInertiaInKilogramMetersSquared
            setup.centroidalMomentOfInertia /
          massInKilograms setup.blockMass := by
    rw [radiusOfGyrationMeters]
    exact Real.sq_sqrt (le_of_lt hratio_pos)
  have hr_value :
      radiusOfGyrationMeters setup =
        Real.sqrt
          ((((35 : ℝ) / 100) ^ 2 + ((45 : ℝ) / 100) ^ 2) / 12) := by
    rw [radiusOfGyrationMeters,
      _laws.uniformRectangleCentroidalInertia,
      _data.sideAMeters, _data.sideBMeters]
    congr 1
    field_simp
  have hr_mem :
      radiusOfGyrationMeters setup ∈
        admissiblePivotOffsetMeters setup := by
    rw [admissiblePivotOffsetMeters, Set.mem_Ioc]
    refine ⟨hr_pos, ?_⟩
    rw [rectangleHalfDiagonalMeters, _data.sideAMeters,
      _data.sideBMeters, hr_value]
    exact Real.sqrt_le_sqrt (by norm_num)
  refine ⟨hr_mem, ?_⟩
  intro x hx
  change
    smallAmplitudeLimitPeriodSecondsAtOffsetMeters setup
        (radiusOfGyrationMeters setup) ≤
      smallAmplitudeLimitPeriodSecondsAtOffsetMeters setup x
  rw [_laws.smallAmplitudeLimitPhysicalPendulumPeriodLaw _ hr_mem,
    _laws.smallAmplitudeLimitPhysicalPendulumPeriodLaw _ hx,
    _laws.parallelAxisLaw _ (le_of_lt hr_pos),
    _laws.parallelAxisLaw _ (le_of_lt hx.1)]
  apply mul_le_mul_of_nonneg_left _ (mul_nonneg (by norm_num) Real.pi_pos.le)
  apply Real.sqrt_le_sqrt
  have hgravity :
      0 <
        accelerationInMetersPerSecondSquared
          setup.gravitationalAccelerationMagnitude :=
    _physical.gravityPositive
  have hx_pos : 0 < x := hx.1
  have hdenr :
      0 <
        massInKilograms setup.blockMass *
            accelerationInMetersPerSecondSquared
              setup.gravitationalAccelerationMagnitude *
          radiusOfGyrationMeters setup := by
    positivity
  have hdenx :
      0 <
        massInKilograms setup.blockMass *
            accelerationInMetersPerSecondSquared
              setup.gravitationalAccelerationMagnitude *
          x := by
    positivity
  apply (div_le_div_iff₀ hdenr hdenx).2
  have hinertia :
      momentOfInertiaInKilogramMetersSquared
          setup.centroidalMomentOfInertia =
        massInKilograms setup.blockMass *
          radiusOfGyrationMeters setup ^ 2 := by
    calc
      _ =
          massInKilograms setup.blockMass *
            (momentOfInertiaInKilogramMetersSquared
                setup.centroidalMomentOfInertia /
              massInKilograms setup.blockMass) := by
            field_simp
      _ = _ := by rw [← hr_sq]
  have hcommon :
      0 <
        massInKilograms setup.blockMass *
          accelerationInMetersPerSecondSquared
            setup.gravitationalAccelerationMagnitude :=
    mul_pos hmass hgravity
  calc
    _ =
        (massInKilograms setup.blockMass *
            accelerationInMetersPerSecondSquared
              setup.gravitationalAccelerationMagnitude) *
          ((momentOfInertiaInKilogramMetersSquared
                setup.centroidalMomentOfInertia +
              massInKilograms setup.blockMass *
                radiusOfGyrationMeters setup ^ 2) *
            x) := by ring
    _ ≤
        (massInKilograms setup.blockMass *
            accelerationInMetersPerSecondSquared
              setup.gravitationalAccelerationMagnitude) *
          ((momentOfInertiaInKilogramMetersSquared
                setup.centroidalMomentOfInertia +
              massInKilograms setup.blockMass * x ^ 2) *
            radiusOfGyrationMeters setup) := by
      apply mul_le_mul_of_nonneg_left _ hcommon.le
      rw [hinertia]
      calc
        _ =
            massInKilograms setup.blockMass *
              ((radiusOfGyrationMeters setup ^ 2 +
                  radiusOfGyrationMeters setup ^ 2) * x) := by
              ring
        _ ≤
            massInKilograms setup.blockMass *
              ((radiusOfGyrationMeters setup ^ 2 + x ^ 2) *
                radiusOfGyrationMeters setup) := by
          apply mul_le_mul_of_nonneg_left _ hmass.le
          nlinarith
            [mul_nonneg hr_pos.le
              (sq_nonneg (x - radiusOfGyrationMeters setup))]
        _ = _ := by ring
    _ = _ := by ring

/-!
For `a = 0.35 m` and `b = 0.45 m`, the minimizing distance is
`√((a²+b²)/12)`, approximately `0.1646 m`.  It matches and is closest to
the displayed `0.16 m`, answer C.  Moreover, the metric circle at that radius
lies inside the rectangular face, and every point on it globally minimizes
the pointwise period among admissible holes.

This formalizes `thm:physics:phyx_mini_0265:target`.
-/
theorem minimumPeriodPivotOffset_matches_recordedAnswerC
    (setup : RectangularBlockPendulumSetup)
    (_figure : MatchesPrimaryFigure setup)
    (_data : MatchesProblemData setup)
    (_physical : HasPhysicalParameters setup)
    (_laws : SatisfiesRectangularPhysicalPendulumLaws setup) :
    radiusOfGyrationMeters setup =
        Real.sqrt
          ((((35 : ℝ) / 100) ^ 2 + ((45 : ℝ) / 100) ^ 2) / 12) ∧
      radiusOfGyrationMeters setup ∈ admissiblePivotOffsetMeters setup ∧
      IsMinOn (smallAmplitudeLimitPeriodSecondsAtOffsetMeters setup)
        (admissiblePivotOffsetMeters setup)
        (radiusOfGyrationMeters setup) ∧
      MatchesDisplayedOffset
        (radiusOfGyrationMeters setup) recordedAnswerChoice ∧
      IsClosestDisplayedOffset
        (radiusOfGyrationMeters setup) recordedAnswerChoice ∧
      ∀ point ∈ Metric.sphere
          (setup.figure.pointCoordinatesMeters .center)
          (radiusOfGyrationMeters setup),
        point ∈ setup.figure.blockFaceRegionMeters ∧
          IsMinOn (smallAmplitudeLimitPeriodSecondsAtFacePoint setup)
            (admissiblePivotPoints setup) point := by
  rcases
      radiusOfGyration_minimizesSmallAmplitudeLimitPeriod
        setup _data _physical _laws with
    ⟨hr_mem, hmin⟩
  have hmass_ne : massInKilograms setup.blockMass ≠ 0 :=
    ne_of_gt _physical.massPositive
  have hr_value :
      radiusOfGyrationMeters setup =
        Real.sqrt
          ((((35 : ℝ) / 100) ^ 2 + ((45 : ℝ) / 100) ^ 2) / 12) := by
    rw [radiusOfGyrationMeters,
      _laws.uniformRectangleCentroidalInertia,
      _data.sideAMeters, _data.sideBMeters]
    congr 1
    field_simp
  refine ⟨hr_value, hr_mem, hmin, ?_, ?_, ?_⟩
  · rw [MatchesDisplayedOffset, recordedAnswerChoice,
      AnswerChoice.offsetMeters, hr_value, abs_lt]
    constructor <;>
      nlinarith
        [Real.sq_sqrt
          (show
            (0 : ℝ) ≤
              (((35 / 100) ^ 2 + (45 / 100) ^ 2) / 12) by
            norm_num),
          Real.sqrt_nonneg
            ((((35 : ℝ) / 100) ^ 2 + ((45 : ℝ) / 100) ^ 2) / 12)]
  · have hs_nonneg :
        0 ≤
          Real.sqrt
            ((((35 : ℝ) / 100) ^ 2 + ((45 : ℝ) / 100) ^ 2) / 12) :=
      Real.sqrt_nonneg _
    have hs_sq :
        Real.sqrt
              ((((35 : ℝ) / 100) ^ 2 + ((45 : ℝ) / 100) ^ 2) / 12) ^
            2 =
          (((35 : ℝ) / 100) ^ 2 + ((45 : ℝ) / 100) ^ 2) / 12 :=
      Real.sq_sqrt (by norm_num)
    have hs_ge_16 :
        (16 : ℝ) / 100 ≤
          Real.sqrt
            ((((35 : ℝ) / 100) ^ 2 + ((45 : ℝ) / 100) ^ 2) / 12) := by
      nlinarith
    have hs_le_17 :
        Real.sqrt
            ((((35 : ℝ) / 100) ^ 2 + ((45 : ℝ) / 100) ^ 2) / 12) ≤
          (17 : ℝ) / 100 := by
      nlinarith
    rw [IsClosestDisplayedOffset, recordedAnswerChoice, hr_value]
    intro alternative
    cases alternative <;> simp only [AnswerChoice.offsetMeters]
    · rw [abs_of_nonneg (by nlinarith),
        abs_of_nonneg (by nlinarith)]
      linarith
    · rw [abs_of_nonneg (by nlinarith),
        abs_of_nonneg (by nlinarith)]
      linarith
    · exact le_refl _
    · rw [abs_of_nonneg (by nlinarith),
        abs_of_nonpos (by nlinarith)]
      nlinarith
  · have hr_pos : 0 < radiusOfGyrationMeters setup := hr_mem.1
    have hr_le_inradius :
        radiusOfGyrationMeters setup ≤
          min
            (lengthInMeters (setup.faceSideLength .a) / 2)
            (lengthInMeters (setup.faceSideLength .b) / 2) := by
      rw [_data.sideAMeters, _data.sideBMeters, hr_value]
      have hs_nonneg :
          0 ≤
            Real.sqrt
              ((((35 : ℝ) / 100) ^ 2 + ((45 : ℝ) / 100) ^ 2) /
                12) :=
        Real.sqrt_nonneg _
      have hs_sq :
          Real.sqrt
                ((((35 : ℝ) / 100) ^ 2 + ((45 : ℝ) / 100) ^ 2) /
                  12) ^
              2 =
            (((35 : ℝ) / 100) ^ 2 + ((45 : ℝ) / 100) ^ 2) / 12 :=
        Real.sq_sqrt (by norm_num)
      rw [min_eq_left (by norm_num)]
      nlinarith
    intro point hpoint_sphere
    have hpoint_dist_rev :
        dist point (setup.figure.pointCoordinatesMeters .center) =
          radiusOfGyrationMeters setup :=
      Metric.mem_sphere.mp hpoint_sphere
    have hpoint_dist :
        dist (setup.figure.pointCoordinatesMeters .center) point =
          radiusOfGyrationMeters setup := by
      simpa [dist_comm] using hpoint_dist_rev
    have hpoint_face :
        point ∈ setup.figure.blockFaceRegionMeters :=
      _figure.centeredInscribedDiskWithinFace
        (Metric.mem_closedBall.mpr
          (hpoint_dist_rev.trans_le hr_le_inradius))
    have hpoint_admissible :
        point ∈ admissiblePivotPoints setup :=
      ⟨hpoint_face, by rw [hpoint_dist]; exact hr_pos⟩
    refine ⟨hpoint_face, ?_⟩
    intro q hq
    change
      smallAmplitudeLimitPeriodSecondsAtFacePoint setup point ≤
        smallAmplitudeLimitPeriodSecondsAtFacePoint setup q
    rw [_laws.limitingPeriodDependsOnlyOnCenterDistance
        point hpoint_admissible,
      _laws.limitingPeriodDependsOnlyOnCenterDistance q hq,
      hpoint_dist]
    apply hmin
    rw [admissiblePivotOffsetMeters, Set.mem_Ioc]
    refine ⟨hq.2, ?_⟩
    have hq_ball :=
      _figure.faceWithinCircumscribedDisk hq.1
    simpa [Metric.mem_closedBall, dist_comm] using hq_ball

end PhyXMiniProblems.ProblemPhyXMini0265
