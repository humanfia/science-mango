import Mathlib.Analysis.SpecialFunctions.Trigonometric.Angle
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Arctan
import Physlib.SpaceAndTime.Space.LengthUnit
import Physlib.Units.WithDim.Speed

noncomputable section

namespace PhyXMiniProblems.ProblemPhyXMini0220

/-!
# Shock-cone angle from a delayed sonic boom

An aircraft is first seen directly overhead at an altitude of `1.45 km`.  It
flies horizontally at a supersonic speed, and the observer hears the sonic
boom after the aircraft has advanced `2.0 km`.  At that event the observer
lies on a boundary generator of the Mach cone.  The generator, the horizontal
flight path, and the vertical altitude form the right-triangle cross-section
used to determine the cone's labelled half-angle `θ`.

Lengths and speeds below are unit-independent Physlib quantities.  Real
numbers occur only as readouts in explicitly selected coherent units and as
dimensionless trigonometric or degree values.
-/

/-! ## Dimensionful quantities and unit readouts -/

/-- A nonnegative physical length, represented coherently in every unit system. -/
abbrev LengthQuantity : Type :=
  Dimensionful (WithDim Dimension.L𝓭 NNReal)

/-- Read a physical length as a real number in the selected length unit. -/
def lengthReadout (unit : LengthUnit) (length : LengthQuantity) : ℝ :=
  ((length {UnitChoices.SI with length := unit}).val : ℝ)

/-- Read a nonnegative physical speed in SI metres per second. -/
def speedInMetersPerSecond (speed : DimSpeed) : ℝ :=
  ((speed UnitChoices.SI).val : ℝ)

/-! ## Physical and primary-figure labels -/

/-- The two perpendicular directions used in the observer--aircraft cross-section. -/
inductive SpatialOrientation where
  | horizontal
  | vertical
  deriving DecidableEq, Repr

/-- The two rays bounding the angle `θ` in the supplied Mach-cone image. -/
inductive MachConeRay where
  | flightPathAxis
  | shockConeBoundary
  deriving DecidableEq, Repr

/-- The only mathematical label printed in the supplied image. -/
inductive FigureLabel where
  | theta
  deriving DecidableEq, Repr

/--
Qualitative evidence read from the primary image.  It depicts the aircraft,
the horizontal flight-path ray, a trailing shock-cone boundary below that ray,
and `θ` between those two rays.
-/
structure MachConeFigure where
  showsAircraft : Bool
  showsRay : MachConeRay → Bool
  displayedAngleLabel : FigureLabel
  firstSideOfTheta : MachConeRay
  secondSideOfTheta : MachConeRay
  coneBoundaryTrailsAircraft : Bool
  coneBoundaryBelowFlightPath : Bool

/-!
The independent physical quantities in the problem.  In particular,
`shockConeHalfAngleTheta` is an unknown angle and is not defined to equal an
answer formula.
-/
structure SonicBoomSetup where
  aircraftAltitude : LengthQuantity
  horizontalTravelWhenBoomHeard : LengthQuantity
  aircraftSpeed : DimSpeed
  soundSpeed : DimSpeed
  initialLineOfSight : SpatialOrientation
  flightPathOrientation : SpatialOrientation
  shockConeHalfAngleTheta : Real.Angle
  figure : MachConeFigure

/-!
## Assumptions

The following predicate records only problem-text measurements and qualitative
facts from the supplied image.  It gives no numerical value for `θ`.
-/
structure MatchesProblemAndSuppliedFigure (setup : SonicBoomSetup) : Prop where
  altitude_in_kilometers :
    lengthReadout LengthUnit.kilometers setup.aircraftAltitude = 1.45
  horizontal_travel_in_kilometers :
    lengthReadout LengthUnit.kilometers
      setup.horizontalTravelWhenBoomHeard = 2.0
  aircraft_was_seen_directly_overhead :
    setup.initialLineOfSight = .vertical
  aircraft_flight_is_horizontal :
    setup.flightPathOrientation = .horizontal
  figure_shows_aircraft : setup.figure.showsAircraft = true
  figure_shows_both_rays : ∀ ray, setup.figure.showsRay ray = true
  figure_angle_label_is_theta :
    setup.figure.displayedAngleLabel = .theta
  theta_first_side_is_flight_path :
    setup.figure.firstSideOfTheta = .flightPathAxis
  theta_second_side_is_cone_boundary :
    setup.figure.secondSideOfTheta = .shockConeBoundary
  figure_cone_trails_aircraft :
    setup.figure.coneBoundaryTrailsAircraft = true
  figure_cone_is_below_flight_path :
    setup.figure.coneBoundaryBelowFlightPath = true

/--
Positivity, supersonic motion, and the acute physical branch for the Mach
half-angle.  Comparing the dimensionful speeds through a common SI readout is
dimensionally meaningful.
-/
structure HasPhysicalSupersonicParameters (setup : SonicBoomSetup) : Prop where
  altitude_positive :
    0 < lengthReadout LengthUnit.kilometers setup.aircraftAltitude
  horizontal_travel_positive :
    0 < lengthReadout LengthUnit.kilometers
      setup.horizontalTravelWhenBoomHeard
  sound_speed_positive : 0 < speedInMetersPerSecond setup.soundSpeed
  aircraft_is_supersonic :
    speedInMetersPerSecond setup.soundSpeed <
      speedInMetersPerSecond setup.aircraftSpeed
  mach_half_angle_positive : 0 < setup.shockConeHalfAngleTheta.toReal
  mach_half_angle_acute :
    setup.shockConeHalfAngleTheta.toReal < Real.pi / 2

/--
The sonic-boom arrival law specialized to the vertical cross-section shown by
the problem: when the observer hears the boom, the observer lies on the shock
boundary.  Thus the altitude is the side opposite `θ` and the aircraft's
horizontal travel since passing overhead is the adjacent side.

This is a general governing relation among the independent quantities; it
does not state the requested angle or any answer choice.
-/
structure SatisfiesSonicBoomMachConeGeometry (setup : SonicBoomSetup) : Prop where
  observer_lies_on_cone_boundary_when_boom_heard :
    Real.Angle.tan setup.shockConeHalfAngleTheta *
        lengthReadout LengthUnit.kilometers
          setup.horizontalTravelWhenBoomHeard =
      lengthReadout LengthUnit.kilometers setup.aircraftAltitude

/-! ## Displayed degree answers -/

/-- Convert a real-valued degree readout into Mathlib's physical angle type. -/
noncomputable def angleOfDegrees (value : ℝ) : Real.Angle :=
  ((value * Real.pi / 180 : ℝ) : Real.Angle)

/-- Read the principal representative of a physical angle in degrees. -/
noncomputable def degreeReadout (angle : Real.Angle) : ℝ :=
  angle.toReal * 180 / Real.pi

/-- Labels of the four answers printed with the problem. -/
inductive AnswerChoice where
  | A
  | B
  | C
  | D
  deriving DecidableEq, Repr

/-- Degree values printed beside the four answer choices. -/
def AnswerChoice.degreeValue : AnswerChoice → ℝ
  | .A => 30
  | .B => 60
  | .C => 45
  | .D => 36

/-- A displayed whole-degree choice agrees with the angle to the nearest degree. -/
def MatchesAnswerToNearestDegree
    (angle : Real.Angle) (choice : AnswerChoice) : Prop :=
  |degreeReadout angle - choice.degreeValue| ≤ (1 : ℝ) / 2

/-!
The dimensionless leg ratio is `1.45 / 2.0 = 29 / 40`, so the acute Mach
half-angle is exactly `arctan (29 / 40)`.  Its degree readout rounds to `36°`,
which is answer D.

This formalizes `thm:physics:phyx_mini_0220:target`.
-/
theorem problem_phyx_mini_0220
    (setup : SonicBoomSetup)
    (_problemAndFigure : MatchesProblemAndSuppliedFigure setup)
    (_physical : HasPhysicalSupersonicParameters setup)
    (_machConeGeometry : SatisfiesSonicBoomMachConeGeometry setup) :
    setup.shockConeHalfAngleTheta =
        ((Real.arctan ((29 : ℝ) / 40) : ℝ) : Real.Angle) ∧
      MatchesAnswerToNearestDegree setup.shockConeHalfAngleTheta .D := by
  have htanAngle :
      Real.Angle.tan setup.shockConeHalfAngleTheta = (29 : ℝ) / 40 := by
    have hgeometry :=
      _machConeGeometry.observer_lies_on_cone_boundary_when_boom_heard
    rw [_problemAndFigure.horizontal_travel_in_kilometers,
      _problemAndFigure.altitude_in_kilometers] at hgeometry
    norm_num at hgeometry ⊢
    linarith
  have htanReal :
      Real.tan setup.shockConeHalfAngleTheta.toReal = (29 : ℝ) / 40 := by
    rw [Real.Angle.tan_toReal]
    exact htanAngle
  have hthetaReal :
      setup.shockConeHalfAngleTheta.toReal = Real.arctan ((29 : ℝ) / 40) := by
    symm
    apply Real.arctan_eq_of_tan_eq htanReal
    exact ⟨by linarith [Real.pi_pos, _physical.mach_half_angle_positive],
      _physical.mach_half_angle_acute⟩
  have htheta :
      setup.shockConeHalfAngleTheta =
        ((Real.arctan ((29 : ℝ) / 40) : ℝ) : Real.Angle) := by
    rw [← hthetaReal]
    exact (Real.Angle.coe_toReal setup.shockConeHalfAngleTheta).symm
  have r_lt_arctan_of_poly {r q : ℝ} (hr0 : 0 < r) (hr1 : r < 1)
      (hq0 : 0 ≤ q)
      (hpoly :
        r - r ^ 3 / 6 + r ^ 4 * (5 / 96) <
          q * (1 - r ^ 2 / 2 - r ^ 4 * (5 / 96))) :
      r < Real.arctan q := by
    have habs : |r| ≤ 1 := by
      rw [abs_of_pos hr0]
      exact hr1.le
    have hs := Real.sin_bound habs
    have hc := Real.cos_bound habs
    rw [abs_of_pos hr0] at hs hc
    have hsinUpper :
        Real.sin r ≤ r - r ^ 3 / 6 + r ^ 4 * (5 / 96) := by
      linarith [abs_le.mp hs |>.2]
    have hcosLower :
        1 - r ^ 2 / 2 - r ^ 4 * (5 / 96) ≤ Real.cos r := by
      linarith [abs_le.mp hc |>.1]
    have hrpi : r < Real.pi / 2 :=
      hr1.trans_le Real.one_le_pi_div_two
    have hcosPositive : 0 < Real.cos r :=
      Real.cos_pos_of_mem_Ioo
        ⟨by linarith [Real.pi_pos], hrpi⟩
    have htan : Real.tan r < q := by
      rw [Real.tan_eq_sin_div_cos, div_lt_iff₀ hcosPositive]
      calc
        Real.sin r ≤ r - r ^ 3 / 6 + r ^ 4 * (5 / 96) := hsinUpper
        _ < q * (1 - r ^ 2 / 2 - r ^ 4 * (5 / 96)) := hpoly
        _ ≤ q * Real.cos r :=
          mul_le_mul_of_nonneg_left hcosLower hq0
    rw [← Real.arctan_tan (by linarith [Real.pi_pos]) hrpi]
    exact Real.arctan_strictMono htan
  have arctan_lt_r_of_poly {q r : ℝ} (hr0 : 0 < r) (hr1 : r < 1)
      (hq0 : 0 ≤ q)
      (hpoly :
        q * (1 - r ^ 2 / 2 + r ^ 4 * (5 / 96)) <
          r - r ^ 3 / 6 - r ^ 4 * (5 / 96)) :
      Real.arctan q < r := by
    have habs : |r| ≤ 1 := by
      rw [abs_of_pos hr0]
      exact hr1.le
    have hs := Real.sin_bound habs
    have hc := Real.cos_bound habs
    rw [abs_of_pos hr0] at hs hc
    have hsinLower :
        r - r ^ 3 / 6 - r ^ 4 * (5 / 96) ≤ Real.sin r := by
      linarith [abs_le.mp hs |>.1]
    have hcosUpper :
        Real.cos r ≤ 1 - r ^ 2 / 2 + r ^ 4 * (5 / 96) := by
      linarith [abs_le.mp hc |>.2]
    have hrpi : r < Real.pi / 2 :=
      hr1.trans_le Real.one_le_pi_div_two
    have hcosPositive : 0 < Real.cos r :=
      Real.cos_pos_of_mem_Ioo
        ⟨by linarith [Real.pi_pos], hrpi⟩
    have htan : q < Real.tan r := by
      rw [Real.tan_eq_sin_div_cos, lt_div_iff₀ hcosPositive]
      calc
        q * Real.cos r ≤ q * (1 - r ^ 2 / 2 + r ^ 4 * (5 / 96)) :=
          mul_le_mul_of_nonneg_left hcosUpper hq0
        _ < r - r ^ 3 / 6 - r ^ 4 * (5 / 96) := hpoly
        _ ≤ Real.sin r := hsinLower
    rw [← Real.arctan_tan (by linarith [Real.pi_pos]) hrpi]
    exact Real.arctan_strictMono htan
  have hsmallLower :
      (31 / 200 : ℝ) < Real.arctan (11 / 69 : ℝ) := by
    apply r_lt_arctan_of_poly <;> norm_num
  have hsmallUpper :
      Real.arctan (11 / 69 : ℝ) < (4 / 25 : ℝ) := by
    apply arctan_lt_r_of_poly <;> norm_num
  have harctanFifthLower :
      (39 / 200 : ℝ) < Real.arctan (1 / 5 : ℝ) := by
    apply r_lt_arctan_of_poly <;> norm_num
  have harctanFifthUpper :
      Real.arctan (1 / 5 : ℝ) < (1 / 5 : ℝ) := by
    apply arctan_lt_r_of_poly <;> norm_num
  have harctan239Upper :
      Real.arctan (1 / 239 : ℝ) < (1 / 200 : ℝ) := by
    apply arctan_lt_r_of_poly <;> norm_num
  have harctan239Positive : 0 < Real.arctan (1 / 239 : ℝ) :=
    Real.arctan_pos.mpr (by norm_num)
  have hMachin := Real.four_mul_arctan_inv_5_sub_arctan_inv_239
  norm_num [inv_eq_one_div] at hMachin
  have hpiLower : (31 / 10 : ℝ) < Real.pi := by
    linarith
  have hpiUpper : Real.pi < (16 / 5 : ℝ) := by
    linarith
  have hsum :
      Real.arctan ((29 : ℝ) / 40) + Real.arctan (11 / 69 : ℝ) =
        Real.pi / 4 := by
    rw [Real.arctan_add]
    · norm_num [Real.arctan_one]
    · norm_num
  have hsmallLowerDegree :
      17 * Real.pi / 360 < Real.arctan (11 / 69 : ℝ) := by
    nlinarith
  have hsmallUpperDegree :
      Real.arctan (11 / 69 : ℝ) < 19 * Real.pi / 360 := by
    nlinarith
  have hdegreeLower :
      (71 / 2 : ℝ) ≤
        Real.arctan ((29 : ℝ) / 40) * 180 / Real.pi := by
    rw [le_div_iff₀ Real.pi_pos]
    nlinarith
  have hdegreeUpper :
      Real.arctan ((29 : ℝ) / 40) * 180 / Real.pi ≤
        (73 / 2 : ℝ) := by
    rw [div_le_iff₀ Real.pi_pos]
    nlinarith
  constructor
  · exact htheta
  · rw [htheta]
    unfold MatchesAnswerToNearestDegree degreeReadout
    rw [Real.Angle.toReal_coe_eq_self_iff.mpr
      ⟨by linarith [Real.neg_pi_div_two_lt_arctan ((29 : ℝ) / 40),
          Real.pi_pos],
        (Real.arctan_lt_pi_div_two ((29 : ℝ) / 40)).le.trans
          (by linarith [Real.pi_pos])⟩]
    simp only [AnswerChoice.degreeValue]
    rw [abs_le]
    constructor <;> linarith

end PhyXMiniProblems.ProblemPhyXMini0220
