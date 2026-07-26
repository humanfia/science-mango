import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Physlib.SpaceAndTime.Space.LengthUnit
import Physlib.Units.WithDim.Basic

noncomputable section

namespace PhyXMiniProblems.ProblemPhyXMini0071

/-!
# Mark seen through a water-filled tank

The tank height, tank width, scale spacing, eye height, and sightline depth are
physical lengths. Their numerical readouts are expressed in centimeters.
Refractive indices are dimensionless, while optical angles are real-valued
radian readouts measured from the vertical normal to the water surface.

The source question says "if the tank is empty", but that conflicts with both
the water-filled scenario/figure and the recorded `60 cm` answer, which relies
on water--air refraction. The declarations below formalize the water-filled
configuration supported by the figure and recorded answer; the wording
conflict is also recorded in the task result as a redraft request.
-/

open Dimension

/-! ## Dimensionful lengths and figure labels -/

/-- A physical length, represented independently of the unit used to read it. -/
abbrev DimLength : Type := Dimensionful (WithDim L𝓭 ℝ)

/-- Unit choices in which length readouts are expressed in centimeters. -/
def centimeterUnitChoices : UnitChoices :=
  { UnitChoices.SI with length := LengthUnit.centimeters }

/-- The scalar centimeter readout of a physical length. -/
def lengthInCentimeters (quantity : DimLength) : ℝ :=
  (quantity centimeterUnitChoices).val

/-- The two opposite vertical walls in the cross-sectional ray diagram. -/
inductive TankWall where
  | observationSide
  | scaleSide
  deriving DecidableEq, Repr

/-- The physical filling states mentioned by the source wording and figure. -/
inductive TankContents where
  | empty
  | completelyFilledWithWater
  deriving DecidableEq, Repr

/-- The filling state named literally by the final sentence of the question. -/
def sourceQuestionContents : TankContents := .empty

/-- The filling state shown in the diagram and stated in the scenario. -/
def picturedScenarioContents : TankContents := .completelyFilledWithWater

/-- The homogeneous optical media separated by the horizontal water surface. -/
inductive OpticalMedium where
  | water
  | air
  deriving DecidableEq, Repr

/-- Labels of all 10 cm depth marks drawn from the top to the tank bottom. -/
inductive DepthMark where
  | zero
  | ten
  | twenty
  | thirty
  | forty
  | fifty
  | sixty
  | seventy
  | eighty
  deriving DecidableEq, Repr

/-- The centimeter depth printed beside each mark in the figure. -/
def depthMarkCentimeters : DepthMark → ℝ
  | .zero => 0
  | .ten => 10
  | .twenty => 20
  | .thirty => 30
  | .forty => 40
  | .fifty => 50
  | .sixty => 60
  | .seventy => 70
  | .eighty => 80

/-- The depth scale fixed to one wall of the tank. -/
structure TankDepthScale where
  /-- Physical separation between consecutive marked depths. -/
  markSpacing : DimLength
  /-- Depth of the `0 cm` mark below the water surface. -/
  zeroMarkDepthBelowSurface : DimLength
  /-- Wall carrying the scale. -/
  wall : TankWall

/-- The observer location shown at the upper rim of the opposite wall. -/
structure ObservationPoint where
  /-- Wall beside which the observer stands. -/
  wall : TankWall
  /-- Vertical eye height above the water surface. -/
  heightAboveWaterSurface : DimLength

/-!
The unknown sightline depth is kept as a physical length. In particular, this
structure contains no field fixing it to the requested `60 cm` mark.
-/
structure TankViewingSetup where
  tankHeight : DimLength
  tankInteriorWidth : DimLength
  contents : TankContents
  scale : TankDepthScale
  observer : ObservationPoint
  /-- Depth where the limiting sightline meets the opposite-wall scale. -/
  limitingSightlineDepthBelowSurface : DimLength
  /-- Dimensionless refractive-index readout for each optical medium. -/
  refractiveIndexDimensionless : OpticalMedium → ℝ
  /-- Incidence angle in water, measured from the surface normal. -/
  waterIncidenceAngleRadians : ℝ
  /-- Transmitted angle in air, measured from the same normal. -/
  airTransmissionAngleRadians : ℝ

/-! ## Problem data, geometry, and governing optics -/

/--
Numerical and qualitative data read from the problem and figure: an `80 cm`
deep, `65 cm` wide tank filled to the top, a depth scale every `10 cm`, and an
eye at water level on the opposite wall. No limiting-ray depth is assigned.
-/
structure MatchesTankProblemAndFigure (setup : TankViewingSetup) : Prop where
  tankHeightReadout :
    lengthInCentimeters setup.tankHeight = 80
  tankWidthReadout :
    lengthInCentimeters setup.tankInteriorWidth = 65
  contentsReadout :
    setup.contents = picturedScenarioContents
  scaleSpacingReadout :
    lengthInCentimeters setup.scale.markSpacing = 10
  zeroMarkBarelySubmerged :
    lengthInCentimeters setup.scale.zeroMarkDepthBelowSurface = 0
  scaleOnMarkedWall :
    setup.scale.wall = .scaleSide
  observerOnOppositeWall :
    setup.observer.wall = .observationSide
  wallsAreOpposite :
    setup.observer.wall ≠ setup.scale.wall
  eyeLevelWithWaterTop :
    lengthInCentimeters setup.observer.heightAboveWaterSurface = 0
  scaleBottomAtTankBottom :
    lengthInCentimeters setup.tankHeight = depthMarkCentimeters .eighty

/-- Standard refractive-index readouts used for ordinary water and air. -/
structure ModelsOrdinaryWaterAndAir (setup : TankViewingSetup) : Prop where
  waterIndexReadout :
    setup.refractiveIndexDimensionless .water = 1.33
  airIndexReadout :
    setup.refractiveIndexDimensionless .air = 1.00

/--
Snell's law for the limiting ray. Because the eye is level with the water
surface, the transmitted limiting ray is horizontal and hence makes angle
`π / 2` with the vertical normal.
-/
structure SatisfiesGrazingWaterAirRefraction
    (setup : TankViewingSetup) : Prop where
  refractiveIndicesPositive :
    ∀ medium, 0 < setup.refractiveIndexDimensionless medium
  waterIndexGreaterThanAir :
    setup.refractiveIndexDimensionless .air <
      setup.refractiveIndexDimensionless .water
  waterIncidenceAnglePositive :
    0 < setup.waterIncidenceAngleRadians
  waterIncidenceAngleAcute :
    setup.waterIncidenceAngleRadians < Real.pi / 2
  transmittedRayIsGrazing :
    setup.airTransmissionAngleRadians = Real.pi / 2
  snellLawAtSurface :
    setup.refractiveIndexDimensionless .water *
        Real.sin setup.waterIncidenceAngleRadians =
      setup.refractiveIndexDimensionless .air *
        Real.sin setup.airTransmissionAngleRadians

/--
Right-triangle geometry of the limiting ray across the tank. The angle is
measured from the vertical normal, so horizontal run equals vertical drop
times its tangent. The depth is additionally constrained to the scale's
physical range, without assigning the requested numerical mark.
-/
structure SatisfiesLimitingSightlineGeometry
    (setup : TankViewingSetup) : Prop where
  widthFromDepthAndAngle :
    lengthInCentimeters setup.tankInteriorWidth =
      lengthInCentimeters setup.limitingSightlineDepthBelowSurface *
        Real.tan setup.waterIncidenceAngleRadians
  sightlineMeetsScaleWithinTank :
    0 ≤ lengthInCentimeters setup.limitingSightlineDepthBelowSurface ∧
      lengthInCentimeters setup.limitingSightlineDepthBelowSurface ≤
        lengthInCentimeters setup.tankHeight

/-! ## Mark selection and target conclusions -/

/-- Labels of the four multiple-choice answers. -/
inductive AnswerChoice where
  | A
  | B
  | C
  | D
  deriving DecidableEq, Repr

/-- The depth mark printed beside each answer choice. -/
def answerMark : AnswerChoice → DepthMark
  | .A => .twenty
  | .B => .fifty
  | .C => .sixty
  | .D => .eighty

/--
A limiting sightline selects a displayed mark when its intersection depth is
within half of the `10 cm` scale spacing of that mark.
-/
def IsNearestDisplayedMark
    (setup : TankViewingSetup) (mark : DepthMark) : Prop :=
  |lengthInCentimeters setup.limitingSightlineDepthBelowSurface -
      depthMarkCentimeters mark| ≤
    lengthInCentimeters setup.scale.markSpacing / 2

/-- A multiple-choice answer names the marked depth selected by the sightline. -/
def IsCorrectAnswer
    (setup : TankViewingSetup) (choice : AnswerChoice) : Prop :=
  IsNearestDisplayedMark setup (answerMark choice)

/-- Dataset metadata: the recorded answer label. It is not a theorem premise. -/
def recordedAnswerChoice : AnswerChoice := .C

/--
The right-triangle relation and physical acute-angle branch give the limiting
depth as tank width divided by the tangent of the underwater incidence angle.
-/
lemma limitingSightlineDepth_formula
    (setup : TankViewingSetup)
    (optics : SatisfiesGrazingWaterAirRefraction setup)
    (geometry : SatisfiesLimitingSightlineGeometry setup) :
    lengthInCentimeters setup.limitingSightlineDepthBelowSurface =
      lengthInCentimeters setup.tankInteriorWidth /
        Real.tan setup.waterIncidenceAngleRadians := by
  have htan : Real.tan setup.waterIncidenceAngleRadians ≠ 0 :=
    ne_of_gt (Real.tan_pos_of_pos_of_lt_pi_div_two
      optics.waterIncidenceAnglePositive optics.waterIncidenceAngleAcute)
  exact (eq_div_iff htan).2 geometry.widthFromDepthAndAngle.symm

/--
The `65 cm` width, ordinary water/air indices, grazing Snell law, and scale
spacing make the limiting depth closest to the `60 cm` mark.
-/
lemma limitingSightline_selects_sixty_centimeter_mark
    (setup : TankViewingSetup)
    (figure : MatchesTankProblemAndFigure setup)
    (media : ModelsOrdinaryWaterAndAir setup)
    (optics : SatisfiesGrazingWaterAirRefraction setup)
    (geometry : SatisfiesLimitingSightlineGeometry setup) :
    IsNearestDisplayedMark setup .sixty := by
  let angle := setup.waterIncidenceAngleRadians
  let depth :=
    lengthInCentimeters setup.limitingSightlineDepthBelowSurface
  have hsin : Real.sin angle = 100 / 133 := by
    have hsnell := optics.snellLawAtSurface
    rw [media.waterIndexReadout, media.airIndexReadout,
      optics.transmittedRayIsGrazing, Real.sin_pi_div_two] at hsnell
    norm_num at hsnell ⊢
    linarith
  have hcos_pos : 0 < Real.cos angle := by
    apply Real.cos_pos_of_mem_Ioo
    constructor
    · have hpi : 0 < Real.pi := Real.pi_pos
      dsimp [angle]
      nlinarith [optics.waterIncidenceAnglePositive]
    · exact optics.waterIncidenceAngleAcute
  have hcos_lower : 85 / 133 ≤ Real.cos angle := by
    have htrig := Real.sin_sq_add_cos_sq angle
    rw [hsin] at htrig
    norm_num at htrig ⊢
    nlinarith
  have htan_lower : 1 ≤ Real.tan angle := by
    rw [Real.tan_eq_sin_div_cos]
    apply (le_div_iff₀ hcos_pos).2
    have htrig := Real.sin_sq_add_cos_sq angle
    rw [hsin] at htrig
    norm_num at htrig ⊢
    nlinarith
  have htan_upper : Real.tan angle ≤ 13 / 11 := by
    rw [Real.tan_eq_sin_div_cos]
    apply (div_le_iff₀ hcos_pos).2
    rw [hsin]
    norm_num at hcos_lower ⊢
    nlinarith
  have hdepth_nonneg : 0 ≤ depth :=
    geometry.sightlineMeetsScaleWithinTank.1
  have hwidth : 65 = depth * Real.tan angle := by
    calc
      65 = lengthInCentimeters setup.tankInteriorWidth :=
        figure.tankWidthReadout.symm
      _ = depth * Real.tan angle := by
        simpa [depth, angle] using geometry.widthFromDepthAndAngle
  have hdepth_upper : depth ≤ 65 := by
    have hmul := mul_le_mul_of_nonneg_left htan_lower hdepth_nonneg
    nlinarith
  have hdepth_lower : 55 ≤ depth := by
    have hmul := mul_le_mul_of_nonneg_left htan_upper hdepth_nonneg
    nlinarith
  unfold IsNearestDisplayedMark
  simp only [depthMarkCentimeters]
  rw [figure.scaleSpacingReadout]
  change |depth - 60| ≤ 10 / 2
  rw [abs_le]
  constructor <;> nlinarith

/--
For the water-filled tank shown in the figure, the limiting sightline has the
critical-angle depth formula and selects answer C, the `60 cm` mark.

Blueprint: `thm:physics:phyx_mini_0071:target`.
-/
theorem problem_phyx_mini_0071
    (setup : TankViewingSetup)
    (figure : MatchesTankProblemAndFigure setup)
    (media : ModelsOrdinaryWaterAndAir setup)
    (optics : SatisfiesGrazingWaterAirRefraction setup)
    (geometry : SatisfiesLimitingSightlineGeometry setup) :
    lengthInCentimeters setup.limitingSightlineDepthBelowSurface =
        lengthInCentimeters setup.tankInteriorWidth /
          Real.tan setup.waterIncidenceAngleRadians ∧
      IsCorrectAnswer setup .C := by
  constructor
  · exact limitingSightlineDepth_formula setup optics geometry
  · simpa [IsCorrectAnswer, answerMark] using
      limitingSightline_selects_sixty_centimeter_mark
        setup figure media optics geometry

end PhyXMiniProblems.ProblemPhyXMini0071
