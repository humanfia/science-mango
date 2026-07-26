import Mathlib.Analysis.SpecialFunctions.Trigonometric.Angle
import Physlib.Electromagnetism.Basic
import Physlib.Units.WithDim.Basic

/-!
# PhyX mini problem 0104: eccentricity after Brewster-angle transmission

A circularly polarized plane wave in air meets a material of refractive index
`1.62` at the polarizing (Brewster) angle.  Its equal incident polarization
components acquire different Fresnel transmission coefficients, so the
transmitted field traces the ellipse in the source figure.

The primary image labels the longer horizontal semiaxis `E₁` and the shorter
vertical semiaxis `E₂`.  Consequently the real geometric eccentricity is
`sqrt (1 - (E₂ / E₁)^2)`.  The reciprocal ratio printed in the prose is
incompatible with both that image and a real eccentricity; the formalization
therefore follows the instruction to use the image as primary evidence.

Electric fields use Physlib's spacetime-dependent `ElectricField`.  Intensity,
wave number, angular frequency, and peak electric-field amplitudes are genuine
dimensionful quantities.  Refractive indices, Fresnel coefficients,
eccentricity, and the displayed answer values are dimensionless real readouts.
-/

noncomputable section

namespace PhyXMiniProblems.ProblemPhyXMini0104

open Dimension

/-! ## Dimensionful optical quantities and readouts -/

/-- Optical intensity, with SI readout in watts per square metre. -/
abbrev OpticalIntensity : Type :=
  Dimensionful (WithDim (M𝓭 * T𝓭⁻¹ * T𝓭⁻¹ * T𝓭⁻¹) ℝ)

/-- Peak electric-field strength, with SI readout in volts per metre. -/
abbrev ElectricFieldAmplitude : Type :=
  Dimensionful
    (WithDim (M𝓭 * L𝓭 * T𝓭⁻¹ * T𝓭⁻¹ * C𝓭⁻¹) ℝ)

/-- Wave number, with SI readout in inverse metres. -/
abbrev OpticalWaveNumber : Type :=
  Dimensionful (WithDim L𝓭⁻¹ ℝ)

/-- Angular frequency, with SI readout in radians per second. -/
abbrev OpticalAngularFrequency : Type :=
  Dimensionful (WithDim T𝓭⁻¹ ℝ)

/-- Read an intensity as a number of watts per square metre. -/
def intensityInWattsPerSquareMeter (intensity : OpticalIntensity) : ℝ :=
  (intensity UnitChoices.SI).val

/-- Read an electric-field amplitude as a number of volts per metre. -/
def amplitudeInVoltsPerMeter (amplitude : ElectricFieldAmplitude) : ℝ :=
  (amplitude UnitChoices.SI).val

/-- Read a wave number as a number of inverse metres. -/
def waveNumberInInverseMeters (waveNumber : OpticalWaveNumber) : ℝ :=
  (waveNumber UnitChoices.SI).val

/-- Read an angular frequency as a number of radians per second. -/
def angularFrequencyInRadiansPerSecond
    (angularFrequency : OpticalAngularFrequency) : ℝ :=
  (angularFrequency UnitChoices.SI).val

/-! ## Physical and figure labels -/

/-- The homogeneous media on the two sides of the interface. -/
inductive OpticalMedium where
  | air
  | material
  deriving DecidableEq, Repr

/-- The three waves associated with the interface. -/
inductive WaveKind where
  | incident
  | reflected
  | refracted
  deriving DecidableEq, Repr

/-- Medium occupied by each wave in the idealized interface model. -/
def WaveKind.medium : WaveKind → OpticalMedium
  | .incident => .air
  | .reflected => .air
  | .refracted => .material

/-- The usual p and s components relative to the plane of incidence. -/
inductive PolarizationComponent where
  /-- p polarization, parallel to the plane of incidence. -/
  | parallel
  /-- s polarization, perpendicular to the plane of incidence. -/
  | perpendicular
  deriving DecidableEq, Repr

/-- Cartesian axes named in the incident-wave formula and ellipse figure. -/
inductive CartesianAxis where
  | x
  | y
  | z
  deriving DecidableEq, Repr

/-- Coordinate planes used to record the source's interface orientation. -/
inductive CoordinatePlane where
  | xy
  | xz
  | yz
  deriving DecidableEq, Repr

/-- The two semiaxis labels printed in the primary ellipse image. -/
inductive FigureAmplitudeLabel where
  | E1
  | E2
  deriving DecidableEq, Repr

/-- The image places `E₁` on the horizontal axis and `E₂` on the vertical axis. -/
def FigureAmplitudeLabel.axis : FigureAmplitudeLabel → CartesianAxis
  | .E1 => .x
  | .E2 => .y

/-- Polarization component represented by each principal ellipse axis. -/
def FigureAmplitudeLabel.component :
    FigureAmplitudeLabel → PolarizationComponent
  | .E1 => .parallel
  | .E2 => .perpendicular

/-! ## Interface setup and polarization descriptions -/

/--
Physical quantities in the Brewster-angle interface experiment.

For each wave, `electricField` is expressed in a local orthonormal frame whose
first two coordinates are the parallel and perpendicular transverse
polarization directions and whose third coordinate is the propagation
direction.  The scalar component values are SI electric-field readouts.
-/
structure BrewsterInterfaceSetup where
  /-- Spacetime-dependent electric vector field of each wave. -/
  electricField : WaveKind → Electromagnetism.ElectricField 3
  /-- Dimensionless phase of each wave at a spacetime point. -/
  phaseReadout : WaveKind → Time → Space 3 → ℝ
  /-- Nonnegative peak magnitude of each transverse field component. -/
  componentPeakAmplitude :
    WaveKind → PolarizationComponent → ElectricFieldAmplitude
  /-- Incident-wave intensity. -/
  incidentIntensity : OpticalIntensity
  /-- Incident wave number `k`. -/
  waveNumber : OpticalWaveNumber
  /-- Incident angular frequency `ω`. -/
  angularFrequency : OpticalAngularFrequency
  /-- Dimensionless refractive index of each medium. -/
  refractiveIndex : OpticalMedium → ℝ
  /-- Incident angle from the interface normal. -/
  incidenceAngle : Real.Angle
  /-- Refracted angle from the interface normal. -/
  refractionAngle : Real.Angle
  /-- Plane to which the flat interface is described as perpendicular. -/
  interfacePerpendicularTo : CoordinatePlane

/-- The physical amplitude represented by a label in the ellipse image. -/
def figureSemiAxisAmplitude
    (setup : BrewsterInterfaceSetup)
    (label : FigureAmplitudeLabel) : ElectricFieldAmplitude :=
  setup.componentPeakAmplitude .refracted label.component

/--
At every spacetime point, the two transverse components are in quadrature and
the longitudinal electric-field component vanishes.
-/
def HasQuadraturePolarization
    (setup : BrewsterInterfaceSetup) (wave : WaveKind) : Prop :=
  ∀ (t : Time) (position : Space 3),
    (setup.electricField wave t position) 0 =
        amplitudeInVoltsPerMeter
            (setup.componentPeakAmplitude wave .parallel) *
          Real.cos (setup.phaseReadout wave t position) ∧
      (setup.electricField wave t position) 1 =
        amplitudeInVoltsPerMeter
            (setup.componentPeakAmplitude wave .perpendicular) *
          Real.sin (setup.phaseReadout wave t position) ∧
      (setup.electricField wave t position) 2 = 0

/--
Problem-text and primary-image readouts.  This records the `150 W/m²`
intensity, index `1.62`, incident phase `kz - ωt`, equal incident components,
the stated `xz` orientation, and the image's ordering of the two semiaxes.
It does not record an eccentricity or an answer choice.
-/
structure MatchesProblemAndFigure (setup : BrewsterInterfaceSetup) : Prop where
  interfaceOrientation : setup.interfacePerpendicularTo = .xz
  incidentIntensityReadout :
    intensityInWattsPerSquareMeter setup.incidentIntensity = 150
  airIndexReadout : setup.refractiveIndex .air = 1
  materialIndexReadout : setup.refractiveIndex .material = 1.62
  incidentPhaseFormula : ∀ (t : Time) (position : Space 3),
    setup.phaseReadout .incident t position =
      waveNumberInInverseMeters setup.waveNumber * position.val 2 -
        angularFrequencyInRadiansPerSecond setup.angularFrequency * t.val
  incidentFieldIsCircular : HasQuadraturePolarization setup .incident
  equalIncidentComponentAmplitudes :
    setup.componentPeakAmplitude .incident .parallel =
      setup.componentPeakAmplitude .incident .perpendicular
  figureE2IsMinorAxis :
    0 < amplitudeInVoltsPerMeter (figureSemiAxisAmplitude setup .E2) ∧
      amplitudeInVoltsPerMeter (figureSemiAxisAmplitude setup .E2) ≤
        amplitudeInVoltsPerMeter (figureSemiAxisAmplitude setup .E1)

/-- An angle is on the acute branch used by the physical interface diagram. -/
def IsAcuteOpticalAngle (angle : Real.Angle) : Prop :=
  0 < angle.toReal ∧ angle.toReal < Real.pi / 2

/-- Positivity and branch conditions for the optical model. -/
structure HasPhysicalParameters (setup : BrewsterInterfaceSetup) : Prop where
  positiveRefractiveIndices :
    ∀ medium, 0 < setup.refractiveIndex medium
  materialOpticallyDenser :
    setup.refractiveIndex .air < setup.refractiveIndex .material
  positiveIncidentIntensity :
    0 < intensityInWattsPerSquareMeter setup.incidentIntensity
  positiveWaveNumber :
    0 < waveNumberInInverseMeters setup.waveNumber
  positiveAngularFrequency :
    0 < angularFrequencyInRadiansPerSecond setup.angularFrequency
  positiveIncidentComponents : ∀ component,
    0 < amplitudeInVoltsPerMeter
      (setup.componentPeakAmplitude .incident component)
  positiveRefractedComponents : ∀ component,
    0 < amplitudeInVoltsPerMeter
      (setup.componentPeakAmplitude .refracted component)
  nonnegativeReflectedComponents : ∀ component,
    0 ≤ amplitudeInVoltsPerMeter
      (setup.componentPeakAmplitude .reflected component)
  incidenceAngleAcute : IsAcuteOpticalAngle setup.incidenceAngle
  refractionAngleAcute : IsAcuteOpticalAngle setup.refractionAngle

/-- The reflected wave is s-polarized: its p component vanishes. -/
structure HasLinearlyPolarizedReflection
    (setup : BrewsterInterfaceSetup) : Prop where
  parallelComponentVanishes :
    amplitudeInVoltsPerMeter
        (setup.componentPeakAmplitude .reflected .parallel) = 0
  perpendicularComponentNonzero :
    amplitudeInVoltsPerMeter
        (setup.componentPeakAmplitude .reflected .perpendicular) ≠ 0

/-- The refracted wave follows the ellipse and has unequal principal axes. -/
structure HasEllipticallyPolarizedTransmission
    (setup : BrewsterInterfaceSetup) : Prop where
  quadratureField : HasQuadraturePolarization setup .refracted
  distinctSemiAxes :
    figureSemiAxisAmplitude setup .E1 ≠
      figureSemiAxisAmplitude setup .E2

/-! ## Governing interface laws -/

/-- Convert a numerical degree readout to Mathlib's physical angle type. -/
def angleFromDegrees (angleDegrees : ℝ) : Real.Angle :=
  ((angleDegrees * Real.pi / 180 : ℝ) : Real.Angle)

/--
Characterization of incidence at the polarizing angle: the two ray angles are
complementary and the tangent of the incident angle is the index ratio.
-/
structure IsAtPolarizingAngle (setup : BrewsterInterfaceSetup) : Prop where
  complementaryAngles :
    setup.incidenceAngle + setup.refractionAngle = angleFromDegrees 90
  tangentIndexRatio :
    Real.Angle.tan setup.incidenceAngle =
      setup.refractiveIndex .material / setup.refractiveIndex .air

/-- Snell's law at the air-material interface. -/
structure ObeysSnellsLaw (setup : BrewsterInterfaceSetup) : Prop where
  atInterface :
    setup.refractiveIndex .air *
        Real.Angle.sin setup.incidenceAngle =
      setup.refractiveIndex .material *
        Real.Angle.sin setup.refractionAngle

/--
Electric-field Fresnel transmission coefficient for a nonmagnetic dielectric
interface, separately for p and s polarization.
-/
def fresnelTransmissionCoefficient
    (setup : BrewsterInterfaceSetup) : PolarizationComponent → ℝ
  | .parallel =>
      (2 * setup.refractiveIndex .air *
          Real.Angle.cos setup.incidenceAngle) /
        (setup.refractiveIndex .material *
            Real.Angle.cos setup.incidenceAngle +
          setup.refractiveIndex .air *
            Real.Angle.cos setup.refractionAngle)
  | .perpendicular =>
      (2 * setup.refractiveIndex .air *
          Real.Angle.cos setup.incidenceAngle) /
        (setup.refractiveIndex .air *
            Real.Angle.cos setup.incidenceAngle +
          setup.refractiveIndex .material *
            Real.Angle.cos setup.refractionAngle)

/-- Fresnel transmission scales each incident component independently. -/
structure ObeysFresnelTransmission
    (setup : BrewsterInterfaceSetup) : Prop where
  transmittedComponent : ∀ component,
    amplitudeInVoltsPerMeter
        (setup.componentPeakAmplitude .refracted component) =
      fresnelTransmissionCoefficient setup component *
        amplitudeInVoltsPerMeter
          (setup.componentPeakAmplitude .incident component)

/-! ## Ellipse and answer target -/

/-- The rotating field-vector coordinates depicted at phase `ωt`. -/
def ellipseCoordinatesInVoltsPerMeter
    (setup : BrewsterInterfaceSetup) (phase : ℝ) : ℝ × ℝ :=
  (amplitudeInVoltsPerMeter (figureSemiAxisAmplitude setup .E1) *
      Real.cos phase,
    amplitudeInVoltsPerMeter (figureSemiAxisAmplitude setup .E2) *
      Real.sin phase)

/-- Standard eccentricity of the figure's `E₁`-major, `E₂`-minor ellipse. -/
def ellipseEccentricity (setup : BrewsterInterfaceSetup) : ℝ :=
  Real.sqrt
    (1 -
      (amplitudeInVoltsPerMeter (figureSemiAxisAmplitude setup .E2) /
        amplitudeInVoltsPerMeter (figureSemiAxisAmplitude setup .E1)) ^ 2)

/-- Labels of the four displayed answer choices. -/
inductive AnswerChoice where
  | A
  | B
  | C
  | D
  deriving DecidableEq, Repr

/-- Dimensionless eccentricity printed beside each answer label. -/
def AnswerChoice.eccentricityReadout : AnswerChoice → ℝ
  | .A => 0.449
  | .B => 0.439
  | .C => 0.412
  | .D => 0.521

/-- Dataset metadata: the recorded answer is A; this is not a theorem premise. -/
def recordedAnswerChoice : AnswerChoice := .A

/-- A displayed choice is strictly nearest to the physical eccentricity. -/
def IsNearestAnswerChoice
    (actualEccentricity : ℝ) (choice : AnswerChoice) : Prop :=
  ∀ otherChoice : AnswerChoice,
    otherChoice ≠ choice →
      |actualEccentricity - choice.eccentricityReadout| <
        |actualEccentricity - otherChoice.eccentricityReadout|

/--
At Brewster incidence the Fresnel laws make the minor-to-major semiaxis ratio
`2 n₁ n₂ / (n₁² + n₂²)`.
-/
lemma transmittedAxisRatioAtPolarizingAngle
    (setup : BrewsterInterfaceSetup)
    (hData : MatchesProblemAndFigure setup)
    (hParameters : HasPhysicalParameters setup)
    (hPolarizing : IsAtPolarizingAngle setup)
    (hSnell : ObeysSnellsLaw setup)
    (hFresnel : ObeysFresnelTransmission setup) :
    amplitudeInVoltsPerMeter (figureSemiAxisAmplitude setup .E2) /
        amplitudeInVoltsPerMeter (figureSemiAxisAmplitude setup .E1) =
      2 * setup.refractiveIndex .air * setup.refractiveIndex .material /
        (setup.refractiveIndex .air ^ 2 +
          setup.refractiveIndex .material ^ 2) := by
  have h90 : angleFromDegrees 90 =
      ((Real.pi / 2 : ℝ) : Real.Angle) := by
    dsimp [angleFromDegrees]
    congr 1
    ring
  have hRefractionAngle : setup.refractionAngle =
      -setup.incidenceAngle + ((Real.pi / 2 : ℝ) : Real.Angle) := by
    calc
      setup.refractionAngle =
          -setup.incidenceAngle +
            (setup.incidenceAngle + setup.refractionAngle) := by abel
      _ = -setup.incidenceAngle + angleFromDegrees 90 := by
        rw [hPolarizing.complementaryAngles]
      _ = -setup.incidenceAngle +
          ((Real.pi / 2 : ℝ) : Real.Angle) := by rw [h90]
  have hCosRefraction :
      Real.Angle.cos setup.refractionAngle =
        Real.Angle.sin setup.incidenceAngle := by
    rw [hRefractionAngle, Real.Angle.cos_add]
    simp
  have hSinRefraction :
      Real.Angle.sin setup.refractionAngle =
        Real.Angle.cos setup.incidenceAngle := by
    rw [hRefractionAngle, Real.Angle.sin_add]
    simp
  have hSnell' := hSnell.atInterface
  rw [hSinRefraction] at hSnell'
  have hCosIncidence : 0 < Real.Angle.cos setup.incidenceAngle := by
    rw [← Real.Angle.coe_toReal setup.incidenceAngle]
    rw [Real.Angle.cos_coe]
    apply Real.cos_pos_of_mem_Ioo
    constructor <;>
      linarith [hParameters.incidenceAngleAcute.1,
        hParameters.incidenceAngleAcute.2, Real.pi_pos]
  have hSinIncidence : 0 < Real.Angle.sin setup.incidenceAngle := by
    rw [← Real.Angle.coe_toReal setup.incidenceAngle]
    rw [Real.Angle.sin_coe]
    apply Real.sin_pos_of_pos_of_lt_pi hParameters.incidenceAngleAcute.1
    linarith [hParameters.incidenceAngleAcute.2, Real.pi_pos]
  have hAirIndex : 0 < setup.refractiveIndex .air :=
    hParameters.positiveRefractiveIndices .air
  have hMaterialIndex : 0 < setup.refractiveIndex .material :=
    hParameters.positiveRefractiveIndices .material
  have hIncidentAmplitude :
      0 < amplitudeInVoltsPerMeter
        (setup.componentPeakAmplitude .incident .parallel) :=
    hParameters.positiveIncidentComponents .parallel
  have hIncidentReadout :
      amplitudeInVoltsPerMeter
          (setup.componentPeakAmplitude .incident .perpendicular) =
        amplitudeInVoltsPerMeter
          (setup.componentPeakAmplitude .incident .parallel) := by
    exact congrArg amplitudeInVoltsPerMeter
      hData.equalIncidentComponentAmplitudes.symm
  change
    amplitudeInVoltsPerMeter
          (setup.componentPeakAmplitude .refracted .perpendicular) /
        amplitudeInVoltsPerMeter
          (setup.componentPeakAmplitude .refracted .parallel) = _
  rw [hFresnel.transmittedComponent .perpendicular,
    hFresnel.transmittedComponent .parallel, hIncidentReadout]
  simp only [fresnelTransmissionCoefficient]
  rw [hCosRefraction]
  field_simp
  nlinarith

/-- The corresponding exact Fresnel expression for the ellipse eccentricity. -/
lemma eccentricityFromFresnelTransmission
    (setup : BrewsterInterfaceSetup)
    (hData : MatchesProblemAndFigure setup)
    (hParameters : HasPhysicalParameters setup)
    (hPolarizing : IsAtPolarizingAngle setup)
    (hSnell : ObeysSnellsLaw setup)
    (hFresnel : ObeysFresnelTransmission setup) :
    ellipseEccentricity setup =
      Real.sqrt
        (1 -
          (2 * setup.refractiveIndex .air *
              setup.refractiveIndex .material /
            (setup.refractiveIndex .air ^ 2 +
              setup.refractiveIndex .material ^ 2)) ^ 2) := by
  unfold ellipseEccentricity
  rw [transmittedAxisRatioAtPolarizingAngle setup hData hParameters
    hPolarizing hSnell hFresnel]

/-!
For `n_air = 1` and `n_material = 1.62 = 81/50`, the exact eccentricity is
`4061/9061 ≈ 0.44818`.  Thus the source's displayed `0.449` is not an exact
three-decimal rounding, but it is uniquely the nearest of the four available
choices.

This formalizes `thm:physics:phyx_mini_0104:target`.
-/
theorem ellipticalEccentricityIsAnswerA
    (setup : BrewsterInterfaceSetup)
    (hData : MatchesProblemAndFigure setup)
    (hParameters : HasPhysicalParameters setup)
    (hReflected : HasLinearlyPolarizedReflection setup)
    (hRefracted : HasEllipticallyPolarizedTransmission setup)
    (hPolarizing : IsAtPolarizingAngle setup)
    (hSnell : ObeysSnellsLaw setup)
    (hFresnel : ObeysFresnelTransmission setup) :
    ellipseEccentricity setup = (4061 : ℝ) / 9061 ∧
      IsNearestAnswerChoice (ellipseEccentricity setup) .A := by
  have hEccentricity :
      ellipseEccentricity setup = (4061 : ℝ) / 9061 := by
    calc
      ellipseEccentricity setup =
          Real.sqrt
            (1 -
              (2 * setup.refractiveIndex .air *
                  setup.refractiveIndex .material /
                (setup.refractiveIndex .air ^ 2 +
                  setup.refractiveIndex .material ^ 2)) ^ 2) :=
        eccentricityFromFresnelTransmission setup hData hParameters
          hPolarizing hSnell hFresnel
      _ = (4061 : ℝ) / 9061 := by
        rw [hData.airIndexReadout, hData.materialIndexReadout]
        rw [show
          1 -
              (2 * (1 : ℝ) * 1.62 /
                ((1 : ℝ) ^ 2 + (1.62 : ℝ) ^ 2)) ^ 2 =
            ((4061 : ℝ) / 9061) ^ 2 by norm_num]
        rw [Real.sqrt_sq_eq_abs, abs_of_pos]
        norm_num
  constructor
  · exact hEccentricity
  · unfold IsNearestAnswerChoice
    rw [hEccentricity]
    intro otherChoice hOtherChoice
    cases otherChoice with
    | A => exact (hOtherChoice rfl).elim
    | B =>
        norm_num [AnswerChoice.eccentricityReadout, abs_of_nonneg,
          abs_of_nonpos]
    | C =>
        norm_num [AnswerChoice.eccentricityReadout, abs_of_nonneg,
          abs_of_nonpos]
    | D =>
        norm_num [AnswerChoice.eccentricityReadout, abs_of_nonneg,
          abs_of_nonpos]

end PhyXMiniProblems.ProblemPhyXMini0104
