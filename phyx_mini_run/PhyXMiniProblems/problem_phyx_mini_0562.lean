import Mathlib
import Physlib.Units.WithDim.Area

noncomputable section

namespace PhyXMiniProblems.ProblemPhyXMini0562

open Dimension

/-!
# Scattering of a pointlike shot by a smooth hard sphere

A pointlike shot in a uniform incident beam strikes a stationary smooth hard
sphere.  The supplied figure labels the sphere radius by `R`, the impact
parameter by `b`, the equal incidence and reflection angles by `β`, and the
scattering angle by `θ`.

Lengths, areas, incident particle intensity, and particle rates are represented
by Physlib dimensionful quantities.  Real numbers below are used only for
named-unit readouts, angles measured in radians, qualitative drawing data, and
the displayed answer expressions.
-/

/-! ## Dimensionful physical quantities and named-unit readouts -/

/-- A nonnegative physical length, independent of the chosen length unit. -/
abbrev LengthMagnitude : Type :=
  Dimensionful (WithDim L𝓭 NNReal)

/-- A physical area, such as an effective scattering cross-section. -/
abbrev AreaMagnitude : Type := DimArea

/--
Incident particle intensity, with dimension particles per unit area per unit
time.  Particle number is dimensionless, so the physical dimension is
`(length² · time)⁻¹`.
-/
abbrev ParticleIntensity : Type :=
  Dimensionful (WithDim ((L𝓭 * L𝓭 * T𝓭)⁻¹) NNReal)

/-- A number of particles per unit time. -/
abbrev ParticleRate : Type :=
  Dimensionful (WithDim T𝓭⁻¹ NNReal)

/-!
There are two normalization conventions relevant to the source.  An ordinary
three-dimensional beam counts the full impact disk and therefore carries a
factor of `π`.  Every displayed answer omits that factor, so the source can
only be read literally after adopting its reduced (azimuth-normalized)
convention.  Keeping this choice as data prevents the ambiguity from being
silently folded into the physical laws or the final answer.
-/
inductive CrossSectionNormalization where
  | fullImpactDisk
  | sourceAzimuthReduced
  deriving DecidableEq, Fintype, Repr

/-- Dimensionless area factor belonging to a cross-section convention. -/
def crossSectionNormalizationFactor : CrossSectionNormalization → ℝ
  | .fullImpactDisk => Real.pi
  | .sourceAzimuthReduced => 1

/-- Read a physical length in a selected length unit. -/
def lengthReadout (unit : LengthUnit) (length : LengthMagnitude) : ℝ :=
  ((length {UnitChoices.SI with length := unit}).val : ℝ)

/-- Read a physical area in the square of a selected length unit. -/
def areaReadout (unit : LengthUnit) (area : AreaMagnitude) : ℝ :=
  ((area {UnitChoices.SI with length := unit}).val : ℝ)

/--
Read incident intensity in particles per selected square-length per selected
time unit.
-/
def particleIntensityReadout
    (lengthUnit : LengthUnit) (timeUnit : TimeUnit)
    (intensity : ParticleIntensity) : ℝ :=
  ((intensity {UnitChoices.SI with
    length := lengthUnit, time := timeUnit}).val : ℝ)

/-- Read a particle rate in particles per selected time unit. -/
def particleRateReadout (unit : TimeUnit) (rate : ParticleRate) : ℝ :=
  ((rate {UnitChoices.SI with time := unit}).val : ℝ)

/-- Meter readout used for the figure lengths `R` and `b`. -/
def lengthInMeters (length : LengthMagnitude) : ℝ :=
  lengthReadout LengthUnit.meters length

/-- Square-meter readout of an effective scattering cross-section. -/
def areaInSquareMeters (area : AreaMagnitude) : ℝ :=
  areaReadout LengthUnit.meters area

/-- The scalar readout of the stated incoming intensity `I₀`. -/
def intensityInParticlesPerSecondSquareMeter
    (intensity : ParticleIntensity) : ℝ :=
  particleIntensityReadout LengthUnit.meters TimeUnit.seconds intensity

/-- The requested number of scattered particles per second. -/
def rateInParticlesPerSecond (rate : ParticleRate) : ℝ :=
  particleRateReadout TimeUnit.seconds rate

/-! ## Physical setup and primary-figure labels -/

/-- The three directed lines drawn at the collision point. -/
inductive FigureRay where
  | incident
  | reflected
  | contactNormal
  deriving DecidableEq, Fintype, Repr

/-- The two physical lengths labeled in the supplied image. -/
inductive FigureLengthLabel where
  | radiusR
  | impactParameterB
  deriving DecidableEq, Fintype, Repr

/-- The two copies of `β` and the scattering angle `θ` in the image. -/
inductive FigureAngleLabel where
  | incidenceBeta
  | reflectionBeta
  | scatteringTheta
  deriving DecidableEq, Fintype, Repr

/-!
Typed data carried by the primary bitmap.  The image is schematic and has no
quantitative scale; its length and angle maps state what each printed symbol
denotes in the physical setup.
-/
structure HardSphereScatteringFigure where
  sphereCircleShown : Bool
  sphereInteriorShaded : Bool
  centerLineShown : Bool
  rayShown : FigureRay → Bool
  lengthSymbol : FigureLengthLabel → String
  angleSymbol : FigureAngleLabel → String
  representedLength : FigureLengthLabel → LengthMagnitude
  representedAngleRadians : FigureAngleLabel → ℝ
  incidentRayHorizontal : Bool
  impactParameterPerpendicularToCenterLine : Bool
  normalSegmentEndsAtSphereCenter : Bool
  hasQuantitativeScale : Bool

/-!
All independent physical quantities in the scattering experiment.  In
particular, `scatteredRateAboveTheta` is an unknown observable: it is not
defined from an answer choice or from the desired closed form.
-/
structure HardSphereScatteringSetup where
  sphereRadiusR : LengthMagnitude
  shotRadius : LengthMagnitude
  impactParameterB : LengthMagnitude
  incomingIntensityI0 : ParticleIntensity
  effectiveCrossSectionAboveTheta : AreaMagnitude
  scatteredRateAboveTheta : ParticleRate
  incidenceAngleBeta : ℝ
  reflectionAngleBeta : ℝ
  scatteringThresholdTheta : ℝ
  crossSectionNormalization : CrossSectionNormalization
  usesPointParticleApproximation : Bool
  sphereIsStationary : Bool
  sphereSurfaceIsSmooth : Bool
  sphereIsHard : Bool
  shotHitsSphere : Bool
  figure : HardSphereScatteringFigure

/-!
The qualitative physical scenario from the prose.  "Negligible radius" is
recorded as use of the point-particle approximation rather than as an exact
claim that a physical radius equals zero.
-/
structure MatchesHardSphereScatteringScenario
    (setup : HardSphereScatteringSetup) : Prop where
  pointParticleApproximation :
    setup.usesPointParticleApproximation = true
  stationarySphere : setup.sphereIsStationary = true
  smoothSurface : setup.sphereSurfaceIsSmooth = true
  hardSphere : setup.sphereIsHard = true
  collisionOccurs : setup.shotHitsSphere = true

/-! Exact symbolic and geometric evidence read from image 562. -/
structure MatchesPrimaryFigure
    (setup : HardSphereScatteringSetup) : Prop where
  sphereCircleShown : setup.figure.sphereCircleShown = true
  sphereInteriorShaded : setup.figure.sphereInteriorShaded = true
  centerLineShown : setup.figure.centerLineShown = true
  everyRayShown : ∀ ray, setup.figure.rayShown ray = true
  radiusSymbol : setup.figure.lengthSymbol .radiusR = "R"
  impactParameterSymbol :
    setup.figure.lengthSymbol .impactParameterB = "b"
  incidenceAngleSymbol :
    setup.figure.angleSymbol .incidenceBeta = "β"
  reflectionAngleSymbol :
    setup.figure.angleSymbol .reflectionBeta = "β"
  scatteringAngleSymbol :
    setup.figure.angleSymbol .scatteringTheta = "θ"
  radiusMeaning :
    setup.figure.representedLength .radiusR = setup.sphereRadiusR
  impactParameterMeaning :
    setup.figure.representedLength .impactParameterB = setup.impactParameterB
  incidenceAngleMeaning :
    setup.figure.representedAngleRadians .incidenceBeta =
      setup.incidenceAngleBeta
  reflectionAngleMeaning :
    setup.figure.representedAngleRadians .reflectionBeta =
      setup.reflectionAngleBeta
  scatteringAngleMeaning :
    setup.figure.representedAngleRadians .scatteringTheta =
      setup.scatteringThresholdTheta
  incidentRayIsHorizontal : setup.figure.incidentRayHorizontal = true
  impactParameterIsPerpendicularOffset :
    setup.figure.impactParameterPerpendicularToCenterLine = true
  normalRunsToCenter :
    setup.figure.normalSegmentEndsAtSphereCenter = true
  imageIsSchematic : setup.figure.hasQuantitativeScale = false

/-! ## Domain conditions and governing laws -/

/-!
Physical angle and magnitude ranges.  Angles are measured in radians: `β`
lies between zero and a right angle and `θ` between zero and `π`.
-/
structure HasPhysicalHardSphereParameters
    (setup : HardSphereScatteringSetup) : Prop where
  radiusPositive : 0 < lengthInMeters setup.sphereRadiusR
  impactParameterNonnegative : 0 ≤ lengthInMeters setup.impactParameterB
  impactParameterAtMostRadius :
    lengthInMeters setup.impactParameterB ≤
      lengthInMeters setup.sphereRadiusR
  incomingIntensityNonnegative :
    0 ≤ intensityInParticlesPerSecondSquareMeter setup.incomingIntensityI0
  incidenceAngleNonnegative : 0 ≤ setup.incidenceAngleBeta
  incidenceAngleAtMostRightAngle :
    setup.incidenceAngleBeta ≤ Real.pi / 2
  reflectionAngleNonnegative : 0 ≤ setup.reflectionAngleBeta
  reflectionAngleAtMostRightAngle :
    setup.reflectionAngleBeta ≤ Real.pi / 2
  scatteringAngleNonnegative : 0 ≤ setup.scatteringThresholdTheta
  scatteringAngleAtMostPi : setup.scatteringThresholdTheta ≤ Real.pi

/-!
Specular reflection at a smooth hard surface.  The first field is the equal
angle law.  The second expresses the deflection between the incoming and
outgoing rays before substituting that equality; it does not contain the
requested particle rate.
-/
structure SatisfiesSpecularReflectionLaw
    (setup : HardSphereScatteringSetup) : Prop where
  equalAnglesToNormal :
    setup.reflectionAngleBeta = setup.incidenceAngleBeta
  scatteringAngleFromRayDeflection :
    setup.scatteringThresholdTheta =
      Real.pi - setup.incidenceAngleBeta - setup.reflectionAngleBeta

/-!
Right-triangle contact geometry from the figure.  The perpendicular impact
parameter is the radius times the sine of the incidence angle.
-/
structure SatisfiesHardSphereContactGeometry
    (setup : HardSphereScatteringSetup) : Prop where
  impactParameterRelation :
    lengthInMeters setup.impactParameterB =
      lengthInMeters setup.sphereRadiusR * Real.sin setup.incidenceAngleBeta

/-!
Uniform-beam counting: scattered rate equals incoming intensity times the
effective cross-section for the selected angular range.  This is a generic
flux-times-area law and contains no answer-choice expression.
-/
structure SatisfiesUniformBeamCountingLaw
    (setup : HardSphereScatteringSetup) : Prop where
  rateEqualsIntensityTimesCrossSection :
    rateInParticlesPerSecond setup.scatteredRateAboveTheta =
      intensityInParticlesPerSecondSquareMeter setup.incomingIntensityI0 *
        areaInSquareMeters setup.effectiveCrossSectionAboveTheta

/-!
Hard-sphere impact-disk law for the angular region above the threshold.  The
law is stated before eliminating `b`: its area is `π b²` for an ordinary
three-dimensional beam and `b²` under the convention implicit in the displayed
choices.  Thus this premise does not contain any final rate formula or any
answer-choice angular expression.
-/
structure SatisfiesHardSphereCrossSectionLaw
    (setup : HardSphereScatteringSetup) : Prop where
  effectiveCrossSectionFromImpactParameter :
    areaInSquareMeters setup.effectiveCrossSectionAboveTheta =
      crossSectionNormalizationFactor setup.crossSectionNormalization *
        (lengthInMeters setup.impactParameterB) ^ 2

/-! ## Displayed choices and current conclusions -/

/-- Labels of the four answer choices in the source problem. -/
inductive AnswerChoice where
  | A
  | B
  | C
  | D
  deriving DecidableEq, Fintype, Repr

/-- The dimensionless angular factor printed in each answer choice. -/
def displayedAngularFactor (choice : AnswerChoice) (theta : ℝ) : ℝ :=
  match choice with
  | .A => (Real.sin (theta / 2)) ^ 2
  | .B => (Real.tan (theta / 2)) ^ 2
  | .C => (1 / Real.tan (theta / 2)) ^ 2
  | .D => (Real.cos (theta / 2)) ^ 2

/-- The particle-rate readout printed beside a selected answer label. -/
def displayedRateExpression
    (setup : HardSphereScatteringSetup) (choice : AnswerChoice) : ℝ :=
  intensityInParticlesPerSecondSquareMeter setup.incomingIntensityI0 *
    (lengthInMeters setup.sphereRadiusR) ^ 2 *
      displayedAngularFactor choice setup.scatteringThresholdTheta

/-- The answer label recorded by the dataset; it is not a theorem premise. -/
def recordedDatasetAnswer : AnswerChoice := .D

/-- A displayed answer agrees with the modeled scattered particle rate. -/
def MatchesAnswerChoice
    (setup : HardSphereScatteringSetup) (choice : AnswerChoice) : Prop :=
  rateInParticlesPerSecond setup.scatteredRateAboveTheta =
    displayedRateExpression setup choice

/-!
The specular-reflection law gives the angle relation stated in the problem,
`θ = π - 2β`.  This is a derived geometric relation, not a rate formula.
-/
lemma scattering_angle_eq_pi_sub_two_beta
    (setup : HardSphereScatteringSetup)
    (hReflection : SatisfiesSpecularReflectionLaw setup) :
    setup.scatteringThresholdTheta =
      Real.pi - 2 * setup.incidenceAngleBeta := by
  linarith [hReflection.equalAnglesToNormal,
    hReflection.scatteringAngleFromRayDeflection]

/-!
Combining the scattering-angle relation with the contact triangle gives
`b = R cos(θ/2)`.  The result still does not determine a particle rate.
-/
lemma impact_parameter_eq_radius_mul_cos_half_scattering_angle
    (setup : HardSphereScatteringSetup)
    (hReflection : SatisfiesSpecularReflectionLaw setup)
    (hGeometry : SatisfiesHardSphereContactGeometry setup) :
    lengthInMeters setup.impactParameterB =
      lengthInMeters setup.sphereRadiusR *
        Real.cos (setup.scatteringThresholdTheta / 2) := by
  rw [hGeometry.impactParameterRelation,
    scattering_angle_eq_pi_sub_two_beta setup hReflection]
  congr 1
  rw [show (Real.pi - 2 * setup.incidenceAngleBeta) / 2 =
    Real.pi / 2 - setup.incidenceAngleBeta by ring,
    Real.cos_pi_div_two_sub]

/-!
Eliminating the impact parameter gives the convention-independent shape of the
effective cross-section.  Its normalization remains explicit: `π` for a full
impact disk and `1` for the source convention.
-/
lemma effective_cross_section_above_theta
    (setup : HardSphereScatteringSetup)
    (hReflection : SatisfiesSpecularReflectionLaw setup)
    (hGeometry : SatisfiesHardSphereContactGeometry setup)
    (hCrossSection : SatisfiesHardSphereCrossSectionLaw setup) :
    areaInSquareMeters setup.effectiveCrossSectionAboveTheta =
      crossSectionNormalizationFactor setup.crossSectionNormalization *
        (lengthInMeters setup.sphereRadiusR) ^ 2 *
          (Real.cos (setup.scatteringThresholdTheta / 2)) ^ 2 := by
  rw [hCrossSection.effectiveCrossSectionFromImpactParameter,
    impact_parameter_eq_radius_mul_cos_half_scattering_angle setup hReflection hGeometry]
  ring

/-!
For either normalization, the scattered rate is the incoming intensity times
the corresponding normalized impact-disk area.  This theorem exposes the
source ambiguity instead of assuming one of its two resolutions.

This is the normalization-independent substantive target.  Its right-hand
side is absent from all scenario, figure, domain, geometry, reflection, and
counting premises.
This formalizes `thm:physics:phyx_mini_0562:target`.
-/
theorem number_scattered_per_second_above_theta
    (setup : HardSphereScatteringSetup)
    (hScenario : MatchesHardSphereScatteringScenario setup)
    (hFigure : MatchesPrimaryFigure setup)
    (hPhysical : HasPhysicalHardSphereParameters setup)
    (hReflection : SatisfiesSpecularReflectionLaw setup)
    (hGeometry : SatisfiesHardSphereContactGeometry setup)
    (hCounting : SatisfiesUniformBeamCountingLaw setup)
    (hCrossSection : SatisfiesHardSphereCrossSectionLaw setup) :
    rateInParticlesPerSecond setup.scatteredRateAboveTheta =
      intensityInParticlesPerSecondSquareMeter setup.incomingIntensityI0 *
        crossSectionNormalizationFactor setup.crossSectionNormalization *
          (lengthInMeters setup.sphereRadiusR) ^ 2 *
            (Real.cos (setup.scatteringThresholdTheta / 2)) ^ 2 := by
  rw [hCounting.rateEqualsIntensityTimesCrossSection,
    effective_cross_section_above_theta setup hReflection hGeometry hCrossSection]
  ring

/-!
With ordinary particles-per-second-per-square-metre intensity and the full
three-dimensional impact disk, the rate contains the geometrically required
factor `π`.
-/
theorem number_scattered_per_second_above_theta_full_impact_disk
    (setup : HardSphereScatteringSetup)
    (hScenario : MatchesHardSphereScatteringScenario setup)
    (hFigure : MatchesPrimaryFigure setup)
    (hPhysical : HasPhysicalHardSphereParameters setup)
    (hReflection : SatisfiesSpecularReflectionLaw setup)
    (hGeometry : SatisfiesHardSphereContactGeometry setup)
    (hCounting : SatisfiesUniformBeamCountingLaw setup)
    (hCrossSection : SatisfiesHardSphereCrossSectionLaw setup)
    (hNormalization :
      setup.crossSectionNormalization = .fullImpactDisk) :
    rateInParticlesPerSecond setup.scatteredRateAboveTheta =
      Real.pi *
        intensityInParticlesPerSecondSquareMeter setup.incomingIntensityI0 *
          (lengthInMeters setup.sphereRadiusR) ^ 2 *
            (Real.cos (setup.scatteringThresholdTheta / 2)) ^ 2 := by
  rw [number_scattered_per_second_above_theta setup hScenario hFigure hPhysical
    hReflection hGeometry hCounting hCrossSection, hNormalization]
  simp only [crossSectionNormalizationFactor]
  ring

/-!
Under the reduced convention used by all four displayed options, the same
model gives the source's recorded expression without `π`.
-/
theorem number_scattered_per_second_above_theta_source_reduced
    (setup : HardSphereScatteringSetup)
    (hScenario : MatchesHardSphereScatteringScenario setup)
    (hFigure : MatchesPrimaryFigure setup)
    (hPhysical : HasPhysicalHardSphereParameters setup)
    (hReflection : SatisfiesSpecularReflectionLaw setup)
    (hGeometry : SatisfiesHardSphereContactGeometry setup)
    (hCounting : SatisfiesUniformBeamCountingLaw setup)
    (hCrossSection : SatisfiesHardSphereCrossSectionLaw setup)
    (hNormalization :
      setup.crossSectionNormalization = .sourceAzimuthReduced) :
    rateInParticlesPerSecond setup.scatteredRateAboveTheta =
      intensityInParticlesPerSecondSquareMeter setup.incomingIntensityI0 *
        (lengthInMeters setup.sphereRadiusR) ^ 2 *
          (Real.cos (setup.scatteringThresholdTheta / 2)) ^ 2 := by
  rw [number_scattered_per_second_above_theta setup hScenario hFigure hPhysical
    hReflection hGeometry hCounting hCrossSection, hNormalization]
  simp [crossSectionNormalizationFactor]

/-!
Consequently, the modeled source-reduced rate agrees with displayed choice D.
The normalization hypothesis is convention data, not the desired rate
equality.
-/
theorem answer_choice_D_matches_under_source_normalization
    (setup : HardSphereScatteringSetup)
    (hScenario : MatchesHardSphereScatteringScenario setup)
    (hFigure : MatchesPrimaryFigure setup)
    (hPhysical : HasPhysicalHardSphereParameters setup)
    (hReflection : SatisfiesSpecularReflectionLaw setup)
    (hGeometry : SatisfiesHardSphereContactGeometry setup)
    (hCounting : SatisfiesUniformBeamCountingLaw setup)
    (hCrossSection : SatisfiesHardSphereCrossSectionLaw setup)
    (hNormalization :
      setup.crossSectionNormalization = .sourceAzimuthReduced) :
    MatchesAnswerChoice setup .D := by
  simpa [MatchesAnswerChoice, displayedRateExpression, displayedAngularFactor] using
    number_scattered_per_second_above_theta_source_reduced setup hScenario hFigure
      hPhysical hReflection hGeometry hCounting hCrossSection hNormalization

end PhyXMiniProblems.ProblemPhyXMini0562
