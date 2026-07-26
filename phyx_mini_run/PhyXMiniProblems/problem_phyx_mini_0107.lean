import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Physlib.Units.WithDim.Speed

/- USER: The assigned source file did not exist when this autoformalization task began. -/

namespace PhyXMiniProblems.ProblemPhyXMini0107

noncomputable section

open Dimension

/-!
# Transit time and bend geometry of a step-index optical fiber

The written question compares travel over `1.00 km` in the core with travel
over the same physical distance in air.  The primary figure independently
shows a bent core: `c` is the bend center, `b` is the tangency point of the
limiting ray, `a` is its incidence point on the outer core--cladding
interface, `R = |cb|`, and the radial core thickness is `d`.

The source's answer choices are printed in centimeters even though the
written question asks for a time.  Consequently the formalization preserves
the centimeter table as source data, but does not identify a length with the
requested time delay.  It states both dimensionally meaningful consequences:
the straight-path time-delay formula and the critical bend-radius formula.
-/

/-- A physical length, represented independently of a unit choice. -/
abbrev DimLength : Type := Dimensionful (WithDim L𝓭 ℝ)

/-- A physical time interval, represented independently of a unit choice. -/
abbrev DimTime : Type := Dimensionful (WithDim T𝓭 ℝ)

/-- A real-valued physical speed, represented independently of a unit choice. -/
abbrev DimSpeedReal : Type := Dimensionful (WithDim (L𝓭 * T𝓭⁻¹) ℝ)

/-- SI units with centimeters selected as the length unit. -/
def centimeterUnitChoices : UnitChoices :=
  { UnitChoices.SI with length := LengthUnit.centimeters }

/-- The meter readout of a physical length. -/
def lengthInMeters (length : DimLength) : ℝ :=
  (length UnitChoices.SI).val

/-- The centimeter readout of a physical length. -/
def lengthInCentimeters (length : DimLength) : ℝ :=
  (length centimeterUnitChoices).val

/-- The second readout of a physical time interval. -/
def timeInSeconds (time : DimTime) : ℝ :=
  (time UnitChoices.SI).val

/-- The meters-per-second readout of a physical speed. -/
def speedInMetersPerSecond (speed : DimSpeedReal) : ℝ :=
  (speed UnitChoices.SI).val

/-- The three optical media relevant to the written question and the figure. -/
inductive OpticalMedium where
  | core
  | cladding
  | air
  deriving DecidableEq, Repr

/-- The two equal physical distances whose light-travel times are compared. -/
inductive TravelRoute where
  | throughCore
  | throughAir
  deriving DecidableEq, Repr

/-- The homogeneous medium traversed by each route. -/
def TravelRoute.medium : TravelRoute → OpticalMedium
  | .throughCore => .core
  | .throughAir => .air

/-- The point labels explicitly printed in the bent-fiber figure. -/
inductive FiberFigurePoint where
  | a
  | b
  | c
  deriving DecidableEq, Repr

/-- The three line segments used in reading the figure. -/
inductive FiberFigureSegment where
  /-- The limiting ray segment from tangency point `b` to incidence point `a`. -/
  | rayAB
  /-- The inner bend radius `R`, from center `c` to tangency point `b`. -/
  | innerRadiusCB
  /-- The outer core radius `R + d`, from center `c` to point `a`. -/
  | outerRadiusCA
  deriving DecidableEq, Repr

/-- Endpoints of each labeled segment in the primary figure. -/
def FiberFigureSegment.endpoints :
    FiberFigureSegment → FiberFigurePoint × FiberFigurePoint
  | .rayAB => (.a, .b)
  | .innerRadiusCB => (.c, .b)
  | .outerRadiusCA => (.c, .a)

/--
Physical quantities belonging to the cable, the two travel routes, and the
bent-fiber diagram.  Refractive indices and angle readouts are dimensionless;
lengths, times, and speeds retain their physical dimensions.

No requested delay, critical-radius formula, or answer choice is stored in
this structure.
-/
structure OpticalFiberSetup where
  /-- The dimensionless refractive index of each optical medium. -/
  refractiveIndex : OpticalMedium → ℝ
  /-- Figure label `d`, the radial thickness of the core. -/
  coreThickness : DimLength
  /-- Physical separation of every pair among the figure points `a`, `b`, `c`. -/
  pointDistance : FiberFigurePoint → FiberFigurePoint → DimLength
  /-- The physical distance traveled on each route in the timing comparison. -/
  comparisonDistance : DimLength
  /-- Elapsed light-travel time on each route. -/
  travelTime : TravelRoute → DimTime
  /-- Propagation speed of light in each homogeneous medium. -/
  lightSpeed : OpticalMedium → DimSpeedReal
  /-- Critical core-to-cladding incidence angle, measured from the normal. -/
  criticalAngleRadians : ℝ
  /-- Figure angle `θ` at `a`, measured between `ab` and radial normal `ac`. -/
  thetaRadians : ℝ

/-- Figure label `R = |cb|`, the inner bend radius. -/
def innerBendRadius (setup : OpticalFiberSetup) : DimLength :=
  setup.pointDistance .c .b

/-- The distance `|ca| = R + d` to the outer core--cladding interface. -/
def outerCoreRadius (setup : OpticalFiberSetup) : DimLength :=
  setup.pointDistance .c .a

/-- Length of any of the three segments identified in the primary figure. -/
def figureSegmentLength
    (setup : OpticalFiberSetup) : FiberFigureSegment → DimLength
  | .rayAB => setup.pointDistance .a .b
  | .innerRadiusCB => innerBendRadius setup
  | .outerRadiusCA => outerCoreRadius setup

/-- The excess core-route travel time over the equal-distance air route. -/
def cableDelaySeconds (setup : OpticalFiberSetup) : ℝ :=
  timeInSeconds (setup.travelTime .throughCore) -
    timeInSeconds (setup.travelTime .throughAir)

/--
Written numerical data and the standard air approximation used by the timing
question: both routes have length `1.00 km`, and air has refractive index one.
-/
structure MatchesTravelQuestion (setup : OpticalFiberSetup) : Prop where
  comparisonDistanceReadout :
    lengthInMeters setup.comparisonDistance = 1000
  airIndexReadout :
    setup.refractiveIndex .air = 1

/--
Direct readout of the concentric bent-core figure.  Radially, point `a` is one
core thickness beyond point `b`; hence `|ca| = |cb| + d` in every unit system.
-/
structure MatchesBentFiberFigure (setup : OpticalFiberSetup) : Prop where
  outerRadiusFromCoreThickness :
    ∀ units : UnitChoices,
      (outerCoreRadius setup units).val =
        (innerBendRadius setup units).val +
          (setup.coreThickness units).val

/--
Euclidean geometry of the limiting ray in the primary figure.  Segment `ab`
is tangent to the inner core circle at `b`, so triangle `cba` is right at `b`.
The displayed angle `θ` is at `a`, which gives `sin θ = |cb| / |ca|`.
-/
structure SatisfiesBentFiberGeometry (setup : OpticalFiberSetup) : Prop where
  coreThicknessPositive :
    0 < lengthInCentimeters setup.coreThickness
  innerRadiusPositive :
    0 < lengthInCentimeters (innerBendRadius setup)
  raySegmentPositive :
    0 < lengthInCentimeters (figureSegmentLength setup .rayAB)
  pointDistanceSymmetric :
    ∀ p q : FiberFigurePoint,
      setup.pointDistance p q = setup.pointDistance q p
  rightTriangleCBA :
    lengthInCentimeters (innerBendRadius setup) ^ 2 +
        lengthInCentimeters (figureSegmentLength setup .rayAB) ^ 2 =
      lengthInCentimeters (outerCoreRadius setup) ^ 2
  thetaAcute :
    0 < setup.thetaRadians ∧ setup.thetaRadians < Real.pi / 2
  thetaSineFromTangentTriangle :
    Real.sin setup.thetaRadians =
      lengthInCentimeters (innerBendRadius setup) /
        lengthInCentimeters (outerCoreRadius setup)

/--
Governing propagation laws for the written equal-distance timing comparison.
In every unit choice, propagation obeys `v n = c` and constant-speed travel
obeys `t v = L`.  These premises do not state the requested delay formula.
-/
structure SatisfiesHomogeneousPropagationLaws
    (setup : OpticalFiberSetup) : Prop where
  refractiveIndicesPositive :
    ∀ medium : OpticalMedium, 0 < setup.refractiveIndex medium
  airIndexLowerThanCore :
    setup.refractiveIndex .air < setup.refractiveIndex .core
  travelTimesNonnegative :
    ∀ route : TravelRoute, 0 ≤ timeInSeconds (setup.travelTime route)
  propagationSpeedsPositive :
    ∀ medium : OpticalMedium,
      0 < speedInMetersPerSecond (setup.lightSpeed medium)
  refractiveIndexSpeedLaw :
    ∀ (medium : OpticalMedium) (units : UnitChoices),
      (setup.lightSpeed medium units).val * setup.refractiveIndex medium =
        (DimSpeed.speedOfLight units).val
  constantSpeedTravel :
    ∀ (route : TravelRoute) (units : UnitChoices),
      (setup.travelTime route units).val *
          (setup.lightSpeed route.medium units).val =
        (setup.comparisonDistance units).val

/--
Governing optics for the limiting ray in the bent-fiber figure.  The pictured
ray meets the outer core--cladding interface at the critical angle, where
Snell's law gives a tangential transmitted ray.  This interface contains no
formula for the requested bend radius.
-/
structure SatisfiesCriticalBendOptics (setup : OpticalFiberSetup) : Prop where
  coreIndexPositive :
    0 < setup.refractiveIndex .core
  claddingIndexPositive :
    0 < setup.refractiveIndex .cladding
  claddingIndexLowerThanCore :
    setup.refractiveIndex .cladding < setup.refractiveIndex .core
  criticalAngleAcute :
    0 < setup.criticalAngleRadians ∧
      setup.criticalAngleRadians < Real.pi / 2
  limitingRayAtCriticalAngle :
    setup.thetaRadians = setup.criticalAngleRadians
  snellLawAtCriticalAngle :
    setup.refractiveIndex .core *
        Real.sin setup.criticalAngleRadians =
      setup.refractiveIndex .cladding * Real.sin (Real.pi / 2)

/-- The four labels attached to the source's centimeter-valued choices. -/
inductive AnswerChoice where
  | A
  | B
  | C
  | D
  deriving DecidableEq, Repr

/-- The length value, in centimeters, printed beside each source choice. -/
def answerChoiceCentimeters : AnswerChoice → ℝ
  | .A => 207 / 100
  | .B => 212 / 100
  | .C => 234 / 100
  | .D => 2

/-- The answer label recorded by the dataset, retained as metadata. -/
def recordedAnswerChoice : AnswerChoice := .A

/-- Agreement of a physical length with a choice printed to `0.01 cm`. -/
def MatchesCentimeterChoice
    (length : DimLength) (choice : AnswerChoice) : Prop :=
  |lengthInCentimeters length - answerChoiceCentimeters choice| ≤ 1 / 200

/--
The critical Snell relation and tangent-ray geometry determine the limiting
inner bend radius without assuming its value:
`R = d n₂ / (n₁ - n₂)`.
-/
lemma critical_bend_radius_formula
    (setup : OpticalFiberSetup)
    (figure : MatchesBentFiberFigure setup)
    (geometry : SatisfiesBentFiberGeometry setup)
    (optics : SatisfiesCriticalBendOptics setup) :
    lengthInCentimeters (innerBendRadius setup) =
      lengthInCentimeters setup.coreThickness *
        setup.refractiveIndex .cladding /
          (setup.refractiveIndex .core -
            setup.refractiveIndex .cladding) := by
  have h_outer :
      lengthInCentimeters (outerCoreRadius setup) =
        lengthInCentimeters (innerBendRadius setup) +
          lengthInCentimeters setup.coreThickness := by
    simpa [lengthInCentimeters] using
      figure.outerRadiusFromCoreThickness centimeterUnitChoices
  have h_outer_pos :
      0 < lengthInCentimeters (outerCoreRadius setup) := by
    rw [h_outer]
    exact add_pos geometry.innerRadiusPositive geometry.coreThicknessPositive
  have h_snell := optics.snellLawAtCriticalAngle
  rw [← optics.limitingRayAtCriticalAngle] at h_snell
  rw [geometry.thetaSineFromTangentTriangle] at h_snell
  norm_num at h_snell
  field_simp [ne_of_gt h_outer_pos] at h_snell
  rw [h_outer] at h_snell
  have h_index_difference :
      setup.refractiveIndex .core - setup.refractiveIndex .cladding ≠ 0 :=
    ne_of_gt (sub_pos.mpr optics.claddingIndexLowerThanCore)
  apply (eq_div_iff h_index_difference).2
  nlinarith

/--
For equal path lengths in homogeneous media, `v n = c` and `t v = L` give
`Δt = L (n₁ - n_air) / c`.  With the written `1.00 km` and `n_air = 1`
readouts, this is the dimensionally correct symbolic answer to the stated
timing question.

The source's recorded choice A is deliberately not asserted: every printed
choice has units of length, whereas this conclusion has units of seconds, and
no numerical core index was supplied.  The independently pictured bend
geometry is preserved above and supports `critical_bend_radius_formula`, but
it is not an assumption of this timing theorem.

Blueprint: `thm:physics:phyx_mini_0107:target`.
-/
theorem problem_phyx_mini_0107
    (setup : OpticalFiberSetup)
    (question : MatchesTravelQuestion setup)
    (laws : SatisfiesHomogeneousPropagationLaws setup) :
    cableDelaySeconds setup =
      1000 * (setup.refractiveIndex .core - 1) /
        speedInMetersPerSecond DimSpeed.speedOfLight := by
  have h_core_speed :
      speedInMetersPerSecond (setup.lightSpeed .core) *
          setup.refractiveIndex .core =
        speedInMetersPerSecond DimSpeed.speedOfLight := by
    simpa [speedInMetersPerSecond] using
      laws.refractiveIndexSpeedLaw .core UnitChoices.SI
  have h_air_speed :
      speedInMetersPerSecond (setup.lightSpeed .air) =
        speedInMetersPerSecond DimSpeed.speedOfLight := by
    have h := laws.refractiveIndexSpeedLaw .air UnitChoices.SI
    simpa [speedInMetersPerSecond, question.airIndexReadout] using h
  have h_core_travel :
      timeInSeconds (setup.travelTime .throughCore) *
          speedInMetersPerSecond (setup.lightSpeed .core) =
        1000 := by
    have h := laws.constantSpeedTravel .throughCore UnitChoices.SI
    change
      timeInSeconds (setup.travelTime .throughCore) *
          speedInMetersPerSecond (setup.lightSpeed .core) =
        lengthInMeters setup.comparisonDistance at h
    rw [question.comparisonDistanceReadout] at h
    exact h
  have h_air_travel :
      timeInSeconds (setup.travelTime .throughAir) *
          speedInMetersPerSecond (setup.lightSpeed .air) =
        1000 := by
    have h := laws.constantSpeedTravel .throughAir UnitChoices.SI
    change
      timeInSeconds (setup.travelTime .throughAir) *
          speedInMetersPerSecond (setup.lightSpeed .air) =
        lengthInMeters setup.comparisonDistance at h
    rw [question.comparisonDistanceReadout] at h
    exact h
  have h_light_speed_pos :
      0 < speedInMetersPerSecond DimSpeed.speedOfLight := by
    rw [← h_core_speed]
    exact mul_pos (laws.propagationSpeedsPositive .core)
      (laws.refractiveIndicesPositive .core)
  have h_core_time :
      timeInSeconds (setup.travelTime .throughCore) *
          speedInMetersPerSecond DimSpeed.speedOfLight =
        1000 * setup.refractiveIndex .core := by
    calc
      timeInSeconds (setup.travelTime .throughCore) *
            speedInMetersPerSecond DimSpeed.speedOfLight =
          timeInSeconds (setup.travelTime .throughCore) *
            (speedInMetersPerSecond (setup.lightSpeed .core) *
              setup.refractiveIndex .core) := by rw [h_core_speed]
      _ = (timeInSeconds (setup.travelTime .throughCore) *
            speedInMetersPerSecond (setup.lightSpeed .core)) *
              setup.refractiveIndex .core := by ring
      _ = 1000 * setup.refractiveIndex .core := by rw [h_core_travel]
  have h_air_time :
      timeInSeconds (setup.travelTime .throughAir) *
          speedInMetersPerSecond DimSpeed.speedOfLight =
        1000 := by
    rw [← h_air_speed]
    exact h_air_travel
  unfold cableDelaySeconds
  apply (eq_div_iff (ne_of_gt h_light_speed_pos)).2
  nlinarith

end

end PhyXMiniProblems.ProblemPhyXMini0107
