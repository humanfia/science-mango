import Mathlib
import Physlib.Units.WithDim.Speed

noncomputable section

namespace PhyXMiniProblems.ProblemPhyXMini0524

open Dimension

/-!
# Ether-wind velocity triangle

The primary image shows three planar velocity arrows.  The vacuum light
velocity `c` is the diagonal arrow, the ether-wind velocity `v` is the
leftward horizontal arrow, and their classical resultant is the upward
vertical arrow.  The angle `phi` lies between `c` and that resultant, while
the resultant is labelled with magnitude `sqrt (c^2 - v^2)`.

Velocity vectors and their speed magnitudes are unit-independent Physlib
quantities.  Euclidean vectors over `ℝ` occur only after choosing coherent
length and time units.  The displayed answers are dimensionless radian
readouts.
-/

/-! ## Dimensionful velocities and coherent readouts -/

/-- Velocity has physical dimension length divided by time. -/
def velocityDimension : Dimension := L𝓭 * T𝓭⁻¹

/-- A unit-independent two-dimensional physical velocity vector. -/
abbrev PlanarVelocityQuantity : Type :=
  Dimensionful
    (WithDim velocityDimension (EuclideanSpace ℝ (Fin 2)))

/-- A unit-independent signed speed readout with velocity dimension. -/
abbrev SpeedQuantity : Type :=
  Dimensionful (WithDim velocityDimension ℝ)

/-- Read a planar velocity in coherent selected length and time units. -/
def planarVelocityReadout
    (lengthUnit : LengthUnit) (timeUnit : TimeUnit)
    (velocity : PlanarVelocityQuantity) : EuclideanSpace ℝ (Fin 2) :=
  (velocity {UnitChoices.SI with
    length := lengthUnit, time := timeUnit}).val

/-- Read a speed in coherent selected length and time units. -/
def speedReadout
    (lengthUnit : LengthUnit) (timeUnit : TimeUnit)
    (speed : SpeedQuantity) : ℝ :=
  (speed {UnitChoices.SI with
    length := lengthUnit, time := timeUnit}).val

/-- Planar-velocity readout in the kilometres-per-second units of the source. -/
def planarVelocityInKilometersPerSecond
    (velocity : PlanarVelocityQuantity) : EuclideanSpace ℝ (Fin 2) :=
  planarVelocityReadout LengthUnit.kilometers TimeUnit.seconds velocity

/-- Speed readout in the kilometres-per-second units of the source. -/
def speedInKilometersPerSecond (speed : SpeedQuantity) : ℝ :=
  speedReadout LengthUnit.kilometers TimeUnit.seconds speed

/-! ## Figure labels and physical quantities -/

/-- The three arrows in the supplied velocity diagram. -/
inductive VelocityArrowLabel where
  /-- The diagonal arrow labelled `c`, the vacuum light velocity. -/
  | vacuumLight_c
  /-- The leftward horizontal arrow labelled `v`, the ether wind. -/
  | etherWind_v
  /-- The upward vertical resultant velocity if an ether existed. -/
  | resultantWithEther
  deriving DecidableEq, Fintype, Repr

/-!
The physical data represented in the image.  Speed magnitudes are independent
dimensionful quantities and are related to the velocity arrows only by the
explicit physical assumptions below.  In particular, `anglePhiRadians` is
not assigned an answer-choice value here.
-/
structure EtherWindVelocityDiagram where
  velocityArrow : VelocityArrowLabel → PlanarVelocityQuantity
  speedMagnitude : VelocityArrowLabel → SpeedQuantity
  anglePhiRadians : ℝ
  showsArrow : VelocityArrowLabel → Bool
  showsAnglePhi : Bool
  showsResultantMagnitudeLabel : Bool

/-! ## Problem data, figure readouts, and governing laws -/

/-!
The numerical speed data stated or standard in the problem.  The Earth/ether
speed is `29.8 km/s = 149/5 km/s`; the vacuum light-speed magnitude is
Physlib's exact dimensionful constant.
-/
structure MatchesProblemSpeedData
    (diagram : EtherWindVelocityDiagram) : Prop where
  vacuumLightSpeedIsPhysicalConstant :
    diagram.speedMagnitude .vacuumLight_c = DimSpeed.speedOfLight
  earthOrbitalSpeedInKilometersPerSecond :
    speedInKilometersPerSecond (diagram.speedMagnitude .etherWind_v) =
      149 / 5

/-!
A speed magnitude is the Euclidean norm of its corresponding velocity-vector
readout in every coherent unit system.  Positivity and nonzero arrows record
the nondegenerate physical branch of the diagram.
-/
structure HasPhysicalVelocityMagnitudes
    (diagram : EtherWindVelocityDiagram) : Prop where
  magnitudeIsEuclideanNorm :
    ∀ (label : VelocityArrowLabel)
      (lengthUnit : LengthUnit) (timeUnit : TimeUnit),
      ‖planarVelocityReadout lengthUnit timeUnit
          (diagram.velocityArrow label)‖ =
        speedReadout lengthUnit timeUnit (diagram.speedMagnitude label)
  everySpeedIsPositive :
    ∀ label,
      0 < speedInKilometersPerSecond (diagram.speedMagnitude label)
  everyArrowIsNonzero :
    ∀ label,
      planarVelocityInKilometersPerSecond
          (diagram.velocityArrow label) ≠ 0

/-!
Literal and geometric information read from the primary raster.  Coordinate
`0` is horizontal and coordinate `1` is vertical.  Thus `v` points left, the
resultant points upward, and `c` points diagonally upward and right.  The
symbolic magnitude written beside the resultant is imposed in every coherent
unit choice.  None of these fields assigns the requested numerical angle.
-/
structure MatchesSuppliedEtherWindFigure
    (diagram : EtherWindVelocityDiagram) : Prop where
  allThreeArrowsAreShown :
    ∀ label, diagram.showsArrow label = true
  phiLabelIsShown : diagram.showsAnglePhi = true
  resultantMagnitudeLabelIsShown :
    diagram.showsResultantMagnitudeLabel = true
  etherWindIsHorizontal :
    (planarVelocityInKilometersPerSecond
      (diagram.velocityArrow .etherWind_v)) 1 = 0
  etherWindPointsLeft :
    (planarVelocityInKilometersPerSecond
      (diagram.velocityArrow .etherWind_v)) 0 < 0
  resultantIsVertical :
    (planarVelocityInKilometersPerSecond
      (diagram.velocityArrow .resultantWithEther)) 0 = 0
  resultantPointsUp :
    0 < (planarVelocityInKilometersPerSecond
      (diagram.velocityArrow .resultantWithEther)) 1
  vacuumLightPointsRight :
    0 < (planarVelocityInKilometersPerSecond
      (diagram.velocityArrow .vacuumLight_c)) 0
  vacuumLightPointsUp :
    0 < (planarVelocityInKilometersPerSecond
      (diagram.velocityArrow .vacuumLight_c)) 1
  phiIsAngleBetweenVacuumAndResultantVelocities :
    diagram.anglePhiRadians =
      InnerProductGeometry.angle
        (planarVelocityInKilometersPerSecond
          (diagram.velocityArrow .vacuumLight_c))
        (planarVelocityInKilometersPerSecond
          (diagram.velocityArrow .resultantWithEther))
  displayedResultantMagnitude :
    ∀ (lengthUnit : LengthUnit) (timeUnit : TimeUnit),
      speedReadout lengthUnit timeUnit
          (diagram.speedMagnitude .resultantWithEther) =
        Real.sqrt
          (speedReadout lengthUnit timeUnit
              (diagram.speedMagnitude .vacuumLight_c) ^ 2 -
            speedReadout lengthUnit timeUnit
              (diagram.speedMagnitude .etherWind_v) ^ 2)

/-!
The governing classical ether model: velocities add by the parallelogram law.
The orientation agrees with the image, where following `c` and then the
leftward `v` reaches the head of the vertical resultant.  This law is stated
for every coherent unit choice and contains no angle value.
-/
structure SatisfiesClassicalEtherVelocityAddition
    (diagram : EtherWindVelocityDiagram) : Prop where
  resultantIsVectorSum :
    ∀ (lengthUnit : LengthUnit) (timeUnit : TimeUnit),
      planarVelocityReadout lengthUnit timeUnit
          (diagram.velocityArrow .resultantWithEther) =
        planarVelocityReadout lengthUnit timeUnit
            (diagram.velocityArrow .vacuumLight_c) +
          planarVelocityReadout lengthUnit timeUnit
            (diagram.velocityArrow .etherWind_v)

/-! ## Exact relation, answer choices, and current target -/

/-- Labels of the four dimensionless radian values printed in the source. -/
inductive AnswerChoice where
  | A
  | B
  | C
  | D
  deriving DecidableEq, Fintype, Repr

/-- Radian readout printed beside each answer label. -/
def displayedAngleRadians : AnswerChoice → ℝ
  | .A => 695 / 10000000
  | .B => 981 / 10000000
  | .C => 632 / 10000000
  | .D => 994 / 10000000

/-- The source dataset records answer label `D`. -/
def recordedDatasetAnswer : AnswerChoice := .D

/-!
Agreement with a value printed to the displayed precision.  Adjacent decimal
places at this precision differ by `10⁻⁷`, so the half-unit rounding radius is
`5 * 10⁻⁸ = 1/20000000` radians.
-/
def RoundsToDisplayedAngle (actual displayed : ℝ) : Prop :=
  displayed - 1 / 20000000 ≤ actual ∧
    actual < displayed + 1 / 20000000

/-!
The right-triangle geometry first gives `sin phi = v/c`.  This intermediate
statement is derived from the norm, figure, and velocity-addition assumptions;
it is not included in any premise structure.
-/
lemma etherWindAngleSineRelation
    (diagram : EtherWindVelocityDiagram)
    (hPhysical : HasPhysicalVelocityMagnitudes diagram)
    (hFigure : MatchesSuppliedEtherWindFigure diagram)
    (hAddition : SatisfiesClassicalEtherVelocityAddition diagram) :
    Real.sin diagram.anglePhiRadians =
      speedInKilometersPerSecond
          (diagram.speedMagnitude .etherWind_v) /
        speedInKilometersPerSecond
          (diagram.speedMagnitude .vacuumLight_c) := by
  let c :=
    planarVelocityInKilometersPerSecond
      (diagram.velocityArrow .vacuumLight_c)
  let v :=
    planarVelocityInKilometersPerSecond
      (diagram.velocityArrow .etherWind_v)
  let r :=
    planarVelocityInKilometersPerSecond
      (diagram.velocityArrow .resultantWithEther)
  have hNormC :
      ‖c‖ =
        speedInKilometersPerSecond
          (diagram.speedMagnitude .vacuumLight_c) := by
    simpa [c, planarVelocityInKilometersPerSecond,
      speedInKilometersPerSecond] using
      hPhysical.magnitudeIsEuclideanNorm
        .vacuumLight_c LengthUnit.kilometers TimeUnit.seconds
  have hNormV :
      ‖v‖ =
        speedInKilometersPerSecond
          (diagram.speedMagnitude .etherWind_v) := by
    simpa [v, planarVelocityInKilometersPerSecond,
      speedInKilometersPerSecond] using
      hPhysical.magnitudeIsEuclideanNorm
        .etherWind_v LengthUnit.kilometers TimeUnit.seconds
  have hResultantHorizontal : r 0 = 0 := by
    simpa [r] using hFigure.resultantIsVertical
  have hWindVertical : v 1 = 0 := by
    simpa [v] using hFigure.etherWindIsHorizontal
  have hOrthogonal : inner ℝ r v = 0 := by
    rw [PiLp.inner_apply, Fin.sum_univ_two]
    simp [hResultantHorizontal, hWindVertical]
  have hResultant : r = c + v := by
    simpa [r, c, v, planarVelocityInKilometersPerSecond] using
      hAddition.resultantIsVectorSum
        LengthUnit.kilometers TimeUnit.seconds
  have hLight : c = r - v := by
    rw [hResultant]
    abel
  have hWindNonzero : v ≠ 0 := by
    simpa [v] using hPhysical.everyArrowIsNonzero .etherWind_v
  have hPhi :
      diagram.anglePhiRadians = InnerProductGeometry.angle c r := by
    simpa [c, r] using
      hFigure.phiIsAngleBetweenVacuumAndResultantVelocities
  calc
    Real.sin diagram.anglePhiRadians =
        Real.sin (InnerProductGeometry.angle c r) :=
      congrArg Real.sin hPhi
    _ = Real.sin (InnerProductGeometry.angle r c) := by
      rw [InnerProductGeometry.angle_comm]
    _ = Real.sin (InnerProductGeometry.angle r (r - v)) := by
      rw [← hLight]
    _ = ‖v‖ / ‖r - v‖ :=
      InnerProductGeometry.sin_angle_sub_of_inner_eq_zero
        hOrthogonal (Or.inr hWindNonzero)
    _ =
        speedInKilometersPerSecond
            (diagram.speedMagnitude .etherWind_v) /
          speedInKilometersPerSecond
            (diagram.speedMagnitude .vacuumLight_c) := by
      rw [← hLight, hNormV, hNormC]

/-!
The acute figure angle is exactly `arcsin (v/c)`.  With `v = 29.8 km/s` and
Physlib's exact vacuum light speed, it rounds to `9.94 * 10⁻⁵` radians, and no
other displayed choice lies in that rounding interval.

This formalizes `thm:physics:phyx_mini_0524:target`.
-/
theorem problem_phyx_mini_0524
    (diagram : EtherWindVelocityDiagram)
    (hData : MatchesProblemSpeedData diagram)
    (hPhysical : HasPhysicalVelocityMagnitudes diagram)
    (hFigure : MatchesSuppliedEtherWindFigure diagram)
    (hAddition : SatisfiesClassicalEtherVelocityAddition diagram) :
    diagram.anglePhiRadians =
        Real.arcsin
          (speedInKilometersPerSecond
              (diagram.speedMagnitude .etherWind_v) /
            speedInKilometersPerSecond
              (diagram.speedMagnitude .vacuumLight_c)) ∧
      RoundsToDisplayedAngle
        diagram.anglePhiRadians (displayedAngleRadians .D) ∧
      ∀ choice : AnswerChoice,
        RoundsToDisplayedAngle
            diagram.anglePhiRadians (displayedAngleRadians choice) →
          choice = .D := by
  let c :=
    planarVelocityInKilometersPerSecond
      (diagram.velocityArrow .vacuumLight_c)
  let v :=
    planarVelocityInKilometersPerSecond
      (diagram.velocityArrow .etherWind_v)
  let r :=
    planarVelocityInKilometersPerSecond
      (diagram.velocityArrow .resultantWithEther)
  have hNormC :
      ‖c‖ =
        speedInKilometersPerSecond
          (diagram.speedMagnitude .vacuumLight_c) := by
    simpa [c, planarVelocityInKilometersPerSecond,
      speedInKilometersPerSecond] using
      hPhysical.magnitudeIsEuclideanNorm
        .vacuumLight_c LengthUnit.kilometers TimeUnit.seconds
  have hNormV :
      ‖v‖ =
        speedInKilometersPerSecond
          (diagram.speedMagnitude .etherWind_v) := by
    simpa [v, planarVelocityInKilometersPerSecond,
      speedInKilometersPerSecond] using
      hPhysical.magnitudeIsEuclideanNorm
        .etherWind_v LengthUnit.kilometers TimeUnit.seconds
  have hResultantHorizontal : r 0 = 0 := by
    simpa [r] using hFigure.resultantIsVertical
  have hWindVertical : v 1 = 0 := by
    simpa [v] using hFigure.etherWindIsHorizontal
  have hOrthogonal : inner ℝ r v = 0 := by
    rw [PiLp.inner_apply, Fin.sum_univ_two]
    simp [hResultantHorizontal, hWindVertical]
  have hResultant : r = c + v := by
    simpa [r, c, v, planarVelocityInKilometersPerSecond] using
      hAddition.resultantIsVectorSum
        LengthUnit.kilometers TimeUnit.seconds
  have hLight : c = r - v := by
    rw [hResultant]
    abel
  have hWindNonzero : v ≠ 0 := by
    simpa [v] using hPhysical.everyArrowIsNonzero .etherWind_v
  have hPhi :
      diagram.anglePhiRadians = InnerProductGeometry.angle c r := by
    simpa [c, r] using
      hFigure.phiIsAngleBetweenVacuumAndResultantVelocities
  have hAngle :
      diagram.anglePhiRadians =
        Real.arcsin
          (speedInKilometersPerSecond
              (diagram.speedMagnitude .etherWind_v) /
            speedInKilometersPerSecond
              (diagram.speedMagnitude .vacuumLight_c)) := by
    calc
      diagram.anglePhiRadians = InnerProductGeometry.angle c r := hPhi
      _ = InnerProductGeometry.angle r c :=
        InnerProductGeometry.angle_comm c r
      _ = InnerProductGeometry.angle r (r - v) := by rw [← hLight]
      _ = Real.arcsin (‖v‖ / ‖r - v‖) :=
        InnerProductGeometry.angle_sub_eq_arcsin_of_inner_eq_zero
          hOrthogonal (Or.inr hWindNonzero)
      _ =
          Real.arcsin
            (speedInKilometersPerSecond
                (diagram.speedMagnitude .etherWind_v) /
              speedInKilometersPerSecond
                (diagram.speedMagnitude .vacuumLight_c)) := by
        rw [← hLight, hNormV, hNormC]
  have hLightSpeed :
      speedInKilometersPerSecond
          (diagram.speedMagnitude .vacuumLight_c) =
        149896229 / 500 := by
    rw [hData.vacuumLightSpeedIsPhysicalConstant]
    simp [speedInKilometersPerSecond, speedReadout,
      DimSpeed.speedOfLight, CarriesDimension.toDimensionful_apply_apply,
      UnitChoices.dimScale, UnitChoices.SI, velocityDimension,
      LengthUnit.kilometers, TimeUnit.seconds, NNReal.smul_def, smul_eq_mul]
    norm_num [NNReal.toReal]
  have hRatio :
      speedInKilometersPerSecond
            (diagram.speedMagnitude .etherWind_v) /
          speedInKilometersPerSecond
            (diagram.speedMagnitude .vacuumLight_c) =
        (14900 : ℝ) / 149896229 := by
    rw [hData.earthOrbitalSpeedInKilometersPerSecond, hLightSpeed]
    norm_num
  have hRoundsD :
      RoundsToDisplayedAngle
        diagram.anglePhiRadians (displayedAngleRadians .D) := by
    rw [hAngle, hRatio]
    constructor
    · calc
        (994 : ℝ) / 10000000 - 1 / 20000000 ≤
            14900 / 149896229 := by norm_num
        _ = Real.sin (Real.arcsin (14900 / 149896229)) := by
          rw [Real.sin_arcsin] <;> norm_num
        _ ≤ Real.arcsin (14900 / 149896229) :=
          Real.sin_le ((Real.arcsin_nonneg).2 (by norm_num))
    · apply
        (Real.arcsin_lt_iff_lt_sin
          (x := (14900 : ℝ) / 149896229)
          (y := (994 : ℝ) / 10000000 + 1 / 20000000)
          (by constructor <;> norm_num) ?_).2
      · exact
          lt_trans (by norm_num)
            (Real.sin_gt_sub_cube
              (x := (994 : ℝ) / 10000000 + 1 / 20000000)
              (by norm_num) (by norm_num))
      · constructor
        · have hpi := Real.pi_pos
          norm_num
          linarith
        · have hpi := Real.two_le_pi
          norm_num
          linarith
  refine ⟨hAngle, hRoundsD, ?_⟩
  intro choice hChoice
  cases choice with
  | A =>
      norm_num [RoundsToDisplayedAngle, displayedAngleRadians] at hRoundsD hChoice
      linarith
  | B =>
      norm_num [RoundsToDisplayedAngle, displayedAngleRadians] at hRoundsD hChoice
      linarith
  | C =>
      norm_num [RoundsToDisplayedAngle, displayedAngleRadians] at hRoundsD hChoice
      linarith
  | D => rfl

end PhyXMiniProblems.ProblemPhyXMini0524
