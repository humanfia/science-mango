import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Physlib.Units.WithDim.Speed

/-!
# Critical-angle setback for a trout fisherman

This file models sound traveling from air into faster water.  The primary
figure labels the incident sound ray, the surface normal, its angle `theta_i`,
and the horizontal distance `x` from the fisherman to the point where the ray
meets the water.  At the limiting ray the refracted sound travels along the
surface; for a larger incidence angle total internal reflection keeps sound
from entering the water interior.

Lengths and sound speeds are genuine dimensionful Physlib quantities.  Real
numbers occur only as named SI readouts, radian angle measures, dimensionless
trigonometric values, and displayed answer values.

Assumption/target split:

* `MatchesProblemData` contains the height and sound-speed calibrations;
* `MatchesPrimaryFigure` contains only labels and qualitative figure roles;
* `HasPhysicalParameters` selects the physically relevant angle branch;
* `SatisfiesCriticalAcousticRefractionPhysics` states Snell's law, the
  right-triangle geometry, and transmission/reflection criteria;
* `critical_bank_setback_is_recorded_choice_D` concludes both minimal safety
  and agreement, to the displayed precision, with `0.44 m` (choice D).
-/

noncomputable section

namespace PhyXMiniProblems.ProblemPhyXMini0209

open Dimension

/-! ## Dimensionful acoustic quantities and named SI readouts -/

/-- A nonnegative physical length, independent of the unit used to read it. -/
abbrev LengthMagnitude : Type := Dimensionful (WithDim L𝓭 NNReal)

/-- Read a physical length in metres. -/
def lengthInMeters (length : LengthMagnitude) : ℝ :=
  ((length UnitChoices.SI).val : ℝ)

/-- Read Physlib's nonnegative physical speed in metres per second. -/
def speedInMetersPerSecond (speed : DimSpeed) : ℝ :=
  ((speed UnitChoices.SI).val : ℝ)

/-- The two propagation media separated by the horizontal water surface. -/
inductive AcousticMedium where
  | air
  | water
  deriving DecidableEq, Repr

/-! ## Objects and annotations from the primary figure -/

/-- Physical objects visible in the fisherman-and-trout figure. -/
inductive FigureObject where
  | fishermanVoice
  | waterSurface
  | trout
  deriving DecidableEq, Repr

/-- Physical role assigned to each depicted object. -/
inductive FigureObjectRole where
  | elevatedSoundSource
  | airWaterBoundary
  | underwaterReceiver
  deriving DecidableEq, Repr

/-- The four distinguished lines or segments in the supplied image. -/
inductive FigureLine where
  | incidentSoundWave
  | refractedSoundWave
  | dashedSurfaceNormal
  | horizontalDistance
  deriving DecidableEq, Repr

/-- Geometric or acoustic role of a distinguished figure line. -/
inductive FigureLineRole where
  | incidentAcousticRay
  | grazingRefractedRay
  | normalToWaterSurface
  | setbackX
  deriving DecidableEq, Repr

/-- The incidence-angle symbol printed beside the dashed normal. -/
inductive FigureAngleLabel where
  | theta_i
  deriving DecidableEq, Repr

/-- The horizontal-distance symbol printed below the figure. -/
inductive FigureDistanceLabel where
  | x
  deriving DecidableEq, Repr

/-- Qualitative labels and roles read directly from the primary raster. -/
structure TroutFisherFigure where
  objectRole : FigureObject → FigureObjectRole
  lineRole : FigureLine → FigureLineRole
  angleLabel : FigureAngleLabel
  distanceLabel : FigureDistanceLabel

/-!
The acoustic setup and its unknown observables.

`bankSetbackX` is the unknown dimensionful distance labeled `x`, not a
preassigned answer value.  Likewise, the angle fields and the predicates
describing entry into the water and total reflection are independent until
the governing-law premise relates them.
-/
structure TroutFisherSoundSetup where
  voiceHeightAboveGround : LengthMagnitude
  soundSpeed : AcousticMedium → DimSpeed
  criticalIncidentAngle : ℝ
  criticalRefractedAngle : ℝ
  incidentAngleAtSetback : LengthMagnitude → ℝ
  bankSetbackX : LengthMagnitude
  soundReachesWaterInteriorAt : LengthMagnitude → Prop
  allSoundReflectedAt : LengthMagnitude → Prop
  figure : TroutFisherFigure

/-! ## Problem data, figure readouts, and governing physics -/

/-!
The numerical data stated in the prose: the voice is `1.8 m` above the
ground, and the sound speeds in air and water are respectively `343 m/s` and
`1440 m/s`.  No setback distance or answer choice occurs here.
-/
structure MatchesProblemData (setup : TroutFisherSoundSetup) : Prop where
  voiceHeight_meters :
    lengthInMeters setup.voiceHeightAboveGround = 18 / 10
  soundSpeedInAir_metersPerSecond :
    speedInMetersPerSecond (setup.soundSpeed .air) = 343
  soundSpeedInWater_metersPerSecond :
    speedInMetersPerSecond (setup.soundSpeed .water) = 1440

/-!
Primary-image evidence.  The pink incident ray and its grazing refracted
continuation are distinct from the dashed surface normal and the horizontal
bracket `x`.  These fields contain no numerical distance conclusion.
-/
structure MatchesPrimaryFigure (setup : TroutFisherSoundSetup) : Prop where
  voiceRole :
    setup.figure.objectRole .fishermanVoice = .elevatedSoundSource
  waterSurfaceRole :
    setup.figure.objectRole .waterSurface = .airWaterBoundary
  troutRole :
    setup.figure.objectRole .trout = .underwaterReceiver
  incidentWaveRole :
    setup.figure.lineRole .incidentSoundWave = .incidentAcousticRay
  grazingRefractedWaveRole :
    setup.figure.lineRole .refractedSoundWave = .grazingRefractedRay
  normalRole :
    setup.figure.lineRole .dashedSurfaceNormal = .normalToWaterSurface
  horizontalDistanceRole :
    setup.figure.lineRole .horizontalDistance = .setbackX
  angleIsThetaI : setup.figure.angleLabel = .theta_i
  distanceIsX : setup.figure.distanceLabel = .x

/-!
Positivity, the increase of wave speed at the boundary, and principal-angle
ranges.  Restricting incidence angles to `[0, pi/2)` selects the geometric
branch shown in the diagram and makes the tangent geometry unambiguous.
-/
structure HasPhysicalParameters (setup : TroutFisherSoundSetup) : Prop where
  voiceHeightPositive : 0 < lengthInMeters setup.voiceHeightAboveGround
  soundSpeedsPositive :
    ∀ medium, 0 < speedInMetersPerSecond (setup.soundSpeed medium)
  speedIncreasesAcrossBoundary :
    speedInMetersPerSecond (setup.soundSpeed .air) <
      speedInMetersPerSecond (setup.soundSpeed .water)
  bankSetbackPositive : 0 < lengthInMeters setup.bankSetbackX
  criticalIncidentAngleRange :
    0 ≤ setup.criticalIncidentAngle ∧
      setup.criticalIncidentAngle < Real.pi / 2
  incidentAngleRange :
    ∀ setback,
      0 ≤ setup.incidentAngleAtSetback setback ∧
        setup.incidentAngleAtSetback setback < Real.pi / 2

/-!
The governing physical model.

For waves, Snell's law can be written `sin theta_i / v_air =
sin theta_r / v_water`.  At the critical ray, `theta_r = pi/2`.  Since
`theta_i` is measured from the vertical normal, the right triangle in the
figure has `tan theta_i = x / h`.  Rays below the critical incidence angle
enter the water interior; rays strictly above it undergo total internal
reflection.  None of these relations assigns a numerical value to `x`.
-/
structure SatisfiesCriticalAcousticRefractionPhysics
    (setup : TroutFisherSoundSetup) : Prop where
  grazingRefraction :
    setup.criticalRefractedAngle = Real.pi / 2
  snellWaveSpeedLawAtCriticalRay :
    Real.sin setup.criticalIncidentAngle /
        speedInMetersPerSecond (setup.soundSpeed .air) =
      Real.sin setup.criticalRefractedAngle /
        speedInMetersPerSecond (setup.soundSpeed .water)
  displayedRayIsCritical :
    setup.incidentAngleAtSetback setup.bankSetbackX =
      setup.criticalIncidentAngle
  rightTriangleGeometry :
    ∀ setback,
      Real.tan (setup.incidentAngleAtSetback setback) =
        lengthInMeters setback /
          lengthInMeters setup.voiceHeightAboveGround
  waterInteriorTransmissionCriterion :
    ∀ setback,
      setup.soundReachesWaterInteriorAt setback ↔
        setup.incidentAngleAtSetback setback <
          setup.criticalIncidentAngle
  totalInternalReflectionCriterion :
    ∀ setback,
      setup.allSoundReflectedAt setback ↔
        setup.criticalIncidentAngle <
          setup.incidentAngleAtSetback setback

/-! ## Safety threshold and displayed answers -/

/-- Sound at this setback does not propagate into the water interior. -/
def KeepsTroutUnfrightened
    (setup : TroutFisherSoundSetup) (setback : LengthMagnitude) : Prop :=
  ¬ setup.soundReachesWaterInteriorAt setback

/-!
The setback is the safe threshold: it itself sends no sound into the water
interior, every shorter setback does, and every strictly larger setback puts
the modeled ray into total internal reflection.
-/
def IsMinimumSafeSetback
    (setup : TroutFisherSoundSetup) (setback : LengthMagnitude) : Prop :=
  KeepsTroutUnfrightened setup setback ∧
    (∀ shorterSetback,
      lengthInMeters shorterSetback < lengthInMeters setback →
        ¬ KeepsTroutUnfrightened setup shorterSetback) ∧
    ∀ fartherSetback,
      lengthInMeters setback < lengthInMeters fartherSetback →
        setup.allSoundReflectedAt fartherSetback

/-- Labels of the four distances printed beside the problem. -/
inductive AnswerChoice where
  | A
  | B
  | C
  | D
  deriving DecidableEq, Repr

/-- Metre value printed beside each answer label. -/
def AnswerChoice.meters : AnswerChoice → ℝ
  | .A => 56 / 100
  | .B => 52 / 100
  | .C => 48 / 100
  | .D => 44 / 100

/-- The answer label recorded in the dataset metadata. -/
def recordedAnswerChoice : AnswerChoice := .D

/-!
Agreement to the nearest displayed centimetre.  A half-centimetre tolerance
is appropriate because the two sound speeds are explicitly stated only as
approximate values and the answer table displays two decimal places in metres.
-/
def MatchesDisplayedCentimeter
    (setback : LengthMagnitude) (answer : AnswerChoice) : Prop :=
  |lengthInMeters setback - answer.meters| < 1 / 200

/--
The horizontal critical-angle setback is the minimum safe setback and rounds
to the recorded answer D, `0.44 m`.

This is the Lean declaration corresponding to blueprint label
`thm:physics:phyx_mini_0209:target`.
-/
theorem critical_bank_setback_is_recorded_choice_D
    (setup : TroutFisherSoundSetup)
    (h_data : MatchesProblemData setup)
    (h_figure : MatchesPrimaryFigure setup)
    (h_parameters : HasPhysicalParameters setup)
    (h_physics : SatisfiesCriticalAcousticRefractionPhysics setup) :
    IsMinimumSafeSetback setup setup.bankSetbackX ∧
      MatchesDisplayedCentimeter setup.bankSetbackX recordedAnswerChoice := by
  classical
  have incidentAngle_lt_of_setback_lt
      (setback₁ setback₂ : LengthMagnitude)
      (h_setback :
        lengthInMeters setback₁ < lengthInMeters setback₂) :
      setup.incidentAngleAtSetback setback₁ <
        setup.incidentAngleAtSetback setback₂ := by
    have h_angle₁ := h_parameters.incidentAngleRange setback₁
    have h_angle₂ := h_parameters.incidentAngleRange setback₂
    apply
      (Real.strictMonoOn_tan.lt_iff_lt
        ⟨by linarith [Real.pi_pos], h_angle₁.2⟩
        ⟨by linarith [Real.pi_pos], h_angle₂.2⟩).mp
    rw [h_physics.rightTriangleGeometry,
      h_physics.rightTriangleGeometry]
    exact
      (div_lt_div_iff_of_pos_right
        h_parameters.voiceHeightPositive).2 h_setback
  constructor
  · refine ⟨?_, ?_, ?_⟩
    · unfold KeepsTroutUnfrightened
      rw [h_physics.waterInteriorTransmissionCriterion,
        h_physics.displayedRayIsCritical]
      exact lt_irrefl _
    · intro shorterSetback h_shorter
      have h_angle :=
        incidentAngle_lt_of_setback_lt shorterSetback setup.bankSetbackX
          h_shorter
      rw [h_physics.displayedRayIsCritical] at h_angle
      simpa only [KeepsTroutUnfrightened, not_not,
        h_physics.waterInteriorTransmissionCriterion] using h_angle
    · intro fartherSetback h_farther
      rw [h_physics.totalInternalReflectionCriterion]
      have h_angle :=
        incidentAngle_lt_of_setback_lt setup.bankSetbackX fartherSetback
          h_farther
      rwa [h_physics.displayedRayIsCritical] at h_angle
  · change
      |lengthInMeters setup.bankSetbackX - 44 / 100| < 1 / 200
    have h_sin :
        Real.sin setup.criticalIncidentAngle = 343 / 1440 := by
      have h_snell := h_physics.snellWaveSpeedLawAtCriticalRay
      rw [h_data.soundSpeedInAir_metersPerSecond,
        h_data.soundSpeedInWater_metersPerSecond,
        h_physics.grazingRefraction, Real.sin_pi_div_two] at h_snell
      norm_num at h_snell ⊢
      linarith
    have h_cos_pos : 0 < Real.cos setup.criticalIncidentAngle :=
      Real.cos_pos_of_mem_Ioo
        ⟨by
          linarith [Real.pi_pos,
            h_parameters.criticalIncidentAngleRange.1],
          h_parameters.criticalIncidentAngleRange.2⟩
    have h_tan_nonneg : 0 ≤ Real.tan setup.criticalIncidentAngle :=
      Real.tan_nonneg_of_nonneg_of_le_pi_div_two
        h_parameters.criticalIncidentAngleRange.1
        h_parameters.criticalIncidentAngleRange.2.le
    have h_tan_cos :=
      Real.tan_mul_cos h_cos_pos.ne'
    have h_tan_sq :=
      congrArg (fun z : ℝ => z ^ 2) h_tan_cos
    have h_trig :=
      Real.sin_sq_add_cos_sq setup.criticalIncidentAngle
    have h_geometry :=
      h_physics.rightTriangleGeometry setup.bankSetbackX
    rw [h_sin] at h_tan_sq h_trig
    rw [h_physics.displayedRayIsCritical,
      h_data.voiceHeight_meters] at h_geometry
    norm_num at h_tan_sq h_trig h_geometry ⊢
    rw [abs_lt]
    constructor <;>
      nlinarith
        [sq_nonneg
          (lengthInMeters setup.bankSetbackX - 87 / 200),
        sq_nonneg
          (lengthInMeters setup.bankSetbackX - 89 / 200)]

end PhyXMiniProblems.ProblemPhyXMini0209
