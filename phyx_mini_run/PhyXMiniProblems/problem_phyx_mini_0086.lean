import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Physlib.Units.WithDim.Speed

/- USER: The assigned source file did not exist when this autoformalization task began. -/

namespace PhyXMiniProblems.ProblemPhyXMini0086

noncomputable section

open Dimension

/-!
# Pulse spreading in a step-index optical fiber

The central plastic core has refractive index `n₁`, the surrounding plastic
sheath has the smaller index `n₂`, and the fiber has axial length `L`.
Dimensionful lengths, times, and speeds are represented with Physlib. Real
numbers are used only for dimensionless refractive indices, radian angle
readouts, and scalar readouts in explicitly chosen units.
-/

/-- A physical length, independent of any particular choice of units. -/
abbrev DimLength : Type := Dimensionful (WithDim L𝓭 ℝ)

/-- A physical time interval, independent of any particular choice of units. -/
abbrev DimTime : Type := Dimensionful (WithDim T𝓭 ℝ)

/-- A physical speed, independent of any particular choice of units. -/
abbrev DimSpeedReal : Type := Dimensionful (WithDim (L𝓭 * T𝓭⁻¹) ℝ)

/-- Unit choices in which time readouts are in nanoseconds and other units are SI. -/
def nanosecondUnitChoices : UnitChoices :=
  { UnitChoices.SI with time := TimeUnit.nanoseconds }

/-- The two homogeneous plastic regions identified by `n₁` and `n₂` in the figure. -/
inductive OpticalFiberRegion where
  | core
  | sheath
  deriving DecidableEq, Repr

/-- The two routes compared in the question. -/
inductive FiberRoute where
  /-- The straight route along the dashed central axis. -/
  | centralAxis
  /-- The unfolded length of the ray repeatedly reflected at the critical angle. -/
  | criticalReflections
  deriving DecidableEq, Repr

/--
The quantities belonging to the fiber and the two depicted light routes.

`criticalIncidenceAngleRadians` is measured from the normal to the
core--sheath interface. `criticalRayAngleToAxisRadians` is measured from the
dashed central axis. No numerical value for the requested travel-time
difference is stored in this structure.
-/
structure OpticalFiberPulseSetup where
  /-- The dimensionless refractive index of each labeled optical region. -/
  refractiveIndex : OpticalFiberRegion → ℝ
  /-- The axial length `L` of the fiber. -/
  fiberLength : DimLength
  /-- The physical distance traveled along each of the two routes. -/
  routePathLength : FiberRoute → DimLength
  /-- The elapsed physical time along each route. -/
  routeTravelTime : FiberRoute → DimTime
  /-- The propagation speed of light within the central plastic core. -/
  lightSpeedInCore : DimSpeedReal
  /-- Critical incidence angle at the core--sheath boundary, measured from its normal. -/
  criticalIncidenceAngleRadians : ℝ
  /-- Acute angle made by a critical reflected segment with the fiber axis. -/
  criticalRayAngleToAxisRadians : ℝ

/-- The scalar meter readout of a dimensionful length. -/
def lengthInMeters (length : DimLength) : ℝ :=
  (length UnitChoices.SI).val

/-- The scalar second readout of a dimensionful time interval. -/
def timeInSeconds (time : DimTime) : ℝ :=
  (time UnitChoices.SI).val

/-- The scalar nanosecond readout of a dimensionful time interval. -/
def timeInNanoseconds (time : DimTime) : ℝ :=
  (time nanosecondUnitChoices).val

/-- The scalar SI readout of a dimensionful speed, in meters per second. -/
def speedInMetersPerSecond (speed : DimSpeedReal) : ℝ :=
  (speed UnitChoices.SI).val

/-- The travel-time excess of the reflected route over the axial route, in seconds. -/
def travelTimeDifferenceSeconds (setup : OpticalFiberPulseSetup) : ℝ :=
  timeInSeconds (setup.routeTravelTime .criticalReflections) -
    timeInSeconds (setup.routeTravelTime .centralAxis)

/-- The same travel-time excess, read in nanoseconds. -/
def travelTimeDifferenceNanoseconds (setup : OpticalFiberPulseSetup) : ℝ :=
  timeInNanoseconds (setup.routeTravelTime .criticalReflections) -
    timeInNanoseconds (setup.routeTravelTime .centralAxis)

/--
Numerical and diagrammatic data supplied by the problem: `n₁ = 1.58`,
`n₂ = 1.53`, `L = 300 m`, and the direct ray follows the central axis.
-/
structure MatchesOpticalFiberFigure (setup : OpticalFiberPulseSetup) : Prop where
  coreIndexReadout :
    setup.refractiveIndex .core = (158 : ℝ) / 100
  sheathIndexReadout :
    setup.refractiveIndex .sheath = (153 : ℝ) / 100
  fiberLengthReadout :
    lengthInMeters setup.fiberLength = 300
  centralAxisPath :
    setup.routePathLength .centralAxis = setup.fiberLength

/--
The governing geometrical-optics and constant-speed laws for the two rays.

The critical Snell relation is stated at a tangential transmitted angle.
Unfolding the repeated specular reflections produces a straight segment whose
axial projection is the fiber length, giving `path * cos(angle-to-axis) = L`.
These laws do not state the requested time difference or any answer choice.
-/
structure SatisfiesOpticalFiberLaws (setup : OpticalFiberPulseSetup) : Prop where
  refractiveIndicesPositive :
    ∀ region : OpticalFiberRegion, 0 < setup.refractiveIndex region
  sheathIndexLowerThanCore :
    setup.refractiveIndex .sheath < setup.refractiveIndex .core
  fiberLengthPositive :
    0 < lengthInMeters setup.fiberLength
  routePathLengthsPositive :
    ∀ route : FiberRoute, 0 < lengthInMeters (setup.routePathLength route)
  routeTravelTimesNonnegative :
    ∀ route : FiberRoute, 0 ≤ timeInSeconds (setup.routeTravelTime route)
  coreSpeedPositive :
    0 < speedInMetersPerSecond setup.lightSpeedInCore
  criticalIncidenceAngleAcute :
    0 < setup.criticalIncidenceAngleRadians ∧
      setup.criticalIncidenceAngleRadians < Real.pi / 2
  criticalRayAngleToAxisAcute :
    0 < setup.criticalRayAngleToAxisRadians ∧
      setup.criticalRayAngleToAxisRadians < Real.pi / 2
  normalAndAxisAnglesComplementary :
    setup.criticalRayAngleToAxisRadians =
      Real.pi / 2 - setup.criticalIncidenceAngleRadians
  snellLawAtCriticalAngle :
    setup.refractiveIndex .core *
        Real.sin setup.criticalIncidenceAngleRadians =
      setup.refractiveIndex .sheath * Real.sin (Real.pi / 2)
  criticalRouteAxialProjection :
    ∀ units : UnitChoices,
      (setup.routePathLength .criticalReflections units).val *
          Real.cos setup.criticalRayAngleToAxisRadians =
        (setup.fiberLength units).val
  lightSpeedRefractiveIndexLaw :
    ∀ units : UnitChoices,
      (setup.lightSpeedInCore units).val * setup.refractiveIndex .core =
        (DimSpeed.speedOfLight units).val
  constantSpeedTravel :
    ∀ (route : FiberRoute) (units : UnitChoices),
      (setup.routeTravelTime route units).val *
          (setup.lightSpeedInCore units).val =
        (setup.routePathLength route units).val

/-- Labels of the four displayed multiple-choice answers. -/
inductive AnswerChoice where
  | A
  | B
  | C
  | D
  deriving DecidableEq, Repr

/-- The nanosecond value printed next to each answer choice. -/
def answerChoiceNanoseconds : AnswerChoice → ℝ
  | .A => 129 / 25
  | .B => 561 / 10
  | .C => 258 / 5
  | .D => 93 / 2

/-- A choice is uniquely closest to an actual nanosecond readout. -/
def IsClosestAnswerChoice (actualNanoseconds : ℝ) (choice : AnswerChoice) : Prop :=
  ∀ other : AnswerChoice, other ≠ choice →
    |actualNanoseconds - answerChoiceNanoseconds choice| <
      |actualNanoseconds - answerChoiceNanoseconds other|

/--
The critical-angle and projection laws give the exact excess travel time.
This is an intermediate physical conclusion, not a premise of the answer.
-/
lemma critical_reflection_delay_formula
    (setup : OpticalFiberPulseSetup)
    (figure : MatchesOpticalFiberFigure setup)
    (laws : SatisfiesOpticalFiberLaws setup) :
    travelTimeDifferenceSeconds setup =
      lengthInMeters setup.fiberLength * setup.refractiveIndex .core *
        (setup.refractiveIndex .core - setup.refractiveIndex .sheath) /
        (speedInMetersPerSecond DimSpeed.speedOfLight *
          setup.refractiveIndex .sheath) := by
  have hn₁ : setup.refractiveIndex .core ≠ 0 :=
    ne_of_gt (laws.refractiveIndicesPositive .core)
  have hn₂ : setup.refractiveIndex .sheath ≠ 0 :=
    ne_of_gt (laws.refractiveIndicesPositive .sheath)
  have hv : speedInMetersPerSecond setup.lightSpeedInCore ≠ 0 :=
    ne_of_gt laws.coreSpeedPositive
  have hcos :
      Real.cos setup.criticalRayAngleToAxisRadians =
        setup.refractiveIndex .sheath / setup.refractiveIndex .core := by
    rw [laws.normalAndAxisAnglesComplementary, Real.cos_pi_div_two_sub]
    apply (eq_div_iff hn₁).2
    simpa [Real.sin_pi_div_two, mul_comm] using laws.snellLawAtCriticalAngle
  have hproj := laws.criticalRouteAxialProjection UnitChoices.SI
  change lengthInMeters (setup.routePathLength .criticalReflections) *
      Real.cos setup.criticalRayAngleToAxisRadians =
    lengthInMeters setup.fiberLength at hproj
  rw [hcos] at hproj
  field_simp [hn₁] at hproj
  have hp : lengthInMeters (setup.routePathLength .criticalReflections) =
      setup.refractiveIndex .core * lengthInMeters setup.fiberLength /
        setup.refractiveIndex .sheath :=
    (eq_div_iff hn₂).2 hproj
  have htcrit :=
    laws.constantSpeedTravel FiberRoute.criticalReflections UnitChoices.SI
  change timeInSeconds (setup.routeTravelTime .criticalReflections) *
      speedInMetersPerSecond setup.lightSpeedInCore =
    lengthInMeters (setup.routePathLength .criticalReflections) at htcrit
  have htcrit' : timeInSeconds (setup.routeTravelTime .criticalReflections) =
      lengthInMeters (setup.routePathLength .criticalReflections) /
        speedInMetersPerSecond setup.lightSpeedInCore :=
    (eq_div_iff hv).2 htcrit
  have htaxis := laws.constantSpeedTravel FiberRoute.centralAxis UnitChoices.SI
  change timeInSeconds (setup.routeTravelTime .centralAxis) *
      speedInMetersPerSecond setup.lightSpeedInCore =
    lengthInMeters (setup.routePathLength .centralAxis) at htaxis
  rw [figure.centralAxisPath] at htaxis
  have htaxis' : timeInSeconds (setup.routeTravelTime .centralAxis) =
      lengthInMeters setup.fiberLength /
        speedInMetersPerSecond setup.lightSpeedInCore :=
    (eq_div_iff hv).2 htaxis
  have hspeed := laws.lightSpeedRefractiveIndexLaw UnitChoices.SI
  change speedInMetersPerSecond setup.lightSpeedInCore *
      setup.refractiveIndex .core =
    speedInMetersPerSecond DimSpeed.speedOfLight at hspeed
  have hv' : speedInMetersPerSecond setup.lightSpeedInCore =
      speedInMetersPerSecond DimSpeed.speedOfLight /
        setup.refractiveIndex .core :=
    (eq_div_iff hn₁).2 hspeed
  have hc : speedInMetersPerSecond DimSpeed.speedOfLight ≠ 0 := by
    simp [speedInMetersPerSecond]
  unfold travelTimeDifferenceSeconds
  rw [htcrit', htaxis', hp, hv']
  field_simp [hc, hn₁, hn₂]

/--
For the `300 m` plastic fiber with `n₁ = 1.58` and `n₂ = 1.53`, the
critical reflected route takes longer than the axial route by the exact
formula below. Its nanosecond readout is closest to `51.6 ns`, answer C.

The closest-choice statement accommodates the rounding convention in the
recorded multiple-choice answer while retaining Physlib's exact value
`299792458 m/s` for the vacuum speed of light.

Blueprint: `thm:physics:phyx_mini_0086:target`.
-/
theorem optical_fiber_travel_time_difference
    (setup : OpticalFiberPulseSetup)
    (figure : MatchesOpticalFiberFigure setup)
    (laws : SatisfiesOpticalFiberLaws setup) :
    travelTimeDifferenceSeconds setup =
        lengthInMeters setup.fiberLength * setup.refractiveIndex .core *
          (setup.refractiveIndex .core - setup.refractiveIndex .sheath) /
          (speedInMetersPerSecond DimSpeed.speedOfLight *
            setup.refractiveIndex .sheath) ∧
      IsClosestAnswerChoice (travelTimeDifferenceNanoseconds setup) .C := by
  constructor
  · exact critical_reflection_delay_formula setup figure laws
  · have time_nanoseconds_eq (time : DimTime) :
        timeInNanoseconds time = 1000000000 * timeInSeconds time := by
      have h := congrArg WithDim.val
        (time.property UnitChoices.SI nanosecondUnitChoices)
      norm_num [timeInNanoseconds, timeInSeconds, nanosecondUnitChoices,
        UnitChoices.dimScale, TimeUnit.nanoseconds, TimeUnit.scale,
        TimeUnit.div_eq_val, TimeUnit.seconds, smul_eq_mul] at h ⊢
      exact h
    have hdelay_units :
        travelTimeDifferenceNanoseconds setup =
          1000000000 * travelTimeDifferenceSeconds setup := by
      rw [travelTimeDifferenceNanoseconds, travelTimeDifferenceSeconds,
        time_nanoseconds_eq, time_nanoseconds_eq]
      ring
    have hseconds := critical_reflection_delay_formula setup figure laws
    unfold IsClosestAnswerChoice
    intro other hother
    rw [hdelay_units, hseconds, figure.fiberLengthReadout,
      figure.coreIndexReadout, figure.sheathIndexReadout]
    cases other with
    | A => norm_num [answerChoiceNanoseconds, speedInMetersPerSecond]
    | B => norm_num [answerChoiceNanoseconds, speedInMetersPerSecond]
    | C => exact (hother rfl).elim
    | D => norm_num [answerChoiceNanoseconds, speedInMetersPerSecond]

end

end PhyXMiniProblems.ProblemPhyXMini0086
