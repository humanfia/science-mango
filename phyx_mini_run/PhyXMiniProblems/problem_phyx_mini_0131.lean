import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Physlib.Units.WithDim.Basic

noncomputable section

namespace PhyXMiniProblems.ProblemPhyXMini0131

open Dimension

/-!
# Resolution improvement of the Hubble Space Telescope

The Hubble Space Telescope is modeled as a reflecting telescope in orbit above
the atmosphere.  Its visible-light resolution is diffraction-limited, whereas
the comparison Earth-bound telescope is limited by atmospheric turbulence.

Lengths are genuine dimensionful Physlib quantities.  Real numbers are used
only for explicit unit readouts, dimensionless radian-angle readouts, and the
dimensionless improvement factor printed by the answer choices.
-/

/-- A nonnegative physical length, independent of the unit used to read it. -/
abbrev LengthQuantity : Type := Dimensionful (WithDim L𝓭 NNReal)

/-- Scalar readout of a physical length in a selected length unit. -/
def lengthReadout (unit : LengthUnit) (length : LengthQuantity) : ℝ :=
  ((length {UnitChoices.SI with length := unit}).val : ℝ)

/-- Meter readout used for the Hubble objective diameter. -/
def lengthInMeters (length : LengthQuantity) : ℝ :=
  lengthReadout LengthUnit.meters length

/-- Nanometer readout used for the visible wavelength. -/
def lengthInNanometers (length : LengthQuantity) : ℝ :=
  lengthReadout LengthUnit.nanometers length

/-- The stated number of arcseconds in one degree (`60 * 60`). -/
def arcsecondsPerDegree : ℝ := 3600

/-- Convert a scalar angular readout in arcseconds to radians. -/
def arcsecondsToRadians (angleArcseconds : ℝ) : ℝ :=
  angleArcseconds * Real.pi / (180 * arcsecondsPerDegree)

/-- Optical design explicitly assigned to Hubble in the problem. -/
inductive TelescopeOpticalDesign where
  | reflecting
  deriving DecidableEq, Repr

/-- Locations distinguished by whether atmospheric turbulence affects viewing. -/
inductive ObservatoryLocation where
  | orbitAboveEarthAtmosphere
  | earthSurfaceWithinAtmosphere
  deriving DecidableEq, Repr

/-- Dominant angular-resolution mechanisms used by the physical model. -/
inductive ResolutionLimitation where
  | circularApertureDiffraction
  | atmosphericTurbulence
  deriving DecidableEq, Repr

/-- Distinct qualitative objects and details visible in the supplied image. -/
inductive FigureFeature where
  | hubbleTelescope
  | metallicCylindricalBody
  | largeOrangeSolarPanels
  | partialEarth
  | earthCloudsAndOcean
  | darkSpaceBackdrop
  deriving DecidableEq, Repr

/-- Coarse locations of features in the supplied image. -/
inductive FigureLocation where
  | foreground
  | background
  deriving DecidableEq, Repr

/-!
All physical quantities and qualitative labels in the problem.

`resolutionImprovementFactor` is an unknown dimensionless result.  No field
assigns it a displayed value or selects an answer choice.
-/
structure TelescopeResolutionSetup where
  hubbleOpticalDesign : TelescopeOpticalDesign
  hubbleLocation : ObservatoryLocation
  earthTelescopeLocation : ObservatoryLocation
  hubbleDominantLimitation : ResolutionLimitation
  earthDominantLimitation : ResolutionLimitation
  figureShows : FigureFeature → Prop
  featureLocation : FigureFeature → FigureLocation
  figureContainsText : Prop
  hubbleObjectiveDiameter : LengthQuantity
  visibleWavelength : LengthQuantity
  hubbleAngularResolutionRad : ℝ
  earthAngularResolutionRad : ℝ
  resolutionImprovementFactor : ℝ

/-!
Qualitative scenario and primary-image readouts.  The image identifies the
orbiting Hubble hardware and Earth but contains no numerical labels or text.
-/
def MatchesScenarioAndFigure (setup : TelescopeResolutionSetup) : Prop :=
  setup.hubbleOpticalDesign = .reflecting ∧
    setup.hubbleLocation = .orbitAboveEarthAtmosphere ∧
    setup.earthTelescopeLocation = .earthSurfaceWithinAtmosphere ∧
    setup.hubbleDominantLimitation = .circularApertureDiffraction ∧
    setup.earthDominantLimitation = .atmosphericTurbulence ∧
    setup.figureShows .hubbleTelescope ∧
    setup.figureShows .metallicCylindricalBody ∧
    setup.figureShows .largeOrangeSolarPanels ∧
    setup.figureShows .partialEarth ∧
    setup.figureShows .earthCloudsAndOcean ∧
    setup.figureShows .darkSpaceBackdrop ∧
    setup.featureLocation .hubbleTelescope = .foreground ∧
    setup.featureLocation .partialEarth = .background ∧
    ¬ setup.figureContainsText

/-!
Numerical data stated in the problem: a `2.4 m` Hubble objective, visible light
of wavelength `550 nm`, and an atmospheric limit of one-half arcsecond for an
Earth-bound telescope.
-/
def MatchesProblemReadouts (setup : TelescopeResolutionSetup) : Prop :=
  lengthInMeters setup.hubbleObjectiveDiameter = (12 / 5 : ℝ) ∧
    lengthInNanometers setup.visibleWavelength = 550 ∧
    setup.earthAngularResolutionRad = arcsecondsToRadians (1 / 2)

/-- Positivity and small-angle conditions for the physical configuration. -/
def HasPhysicalResolutionParameters (setup : TelescopeResolutionSetup) : Prop :=
  0 < lengthInMeters setup.hubbleObjectiveDiameter ∧
    0 < lengthInMeters setup.visibleWavelength ∧
    0 < setup.hubbleAngularResolutionRad ∧
    setup.hubbleAngularResolutionRad < 1 ∧
    0 < setup.earthAngularResolutionRad ∧
    setup.earthAngularResolutionRad < 1 ∧
    0 < setup.resolutionImprovementFactor

/-!
Rayleigh's circular-aperture criterion `θ = 1.22 λ / D`, with the radian
angle dimensionless.  The factor `1.22` is represented exactly by `61 / 50`.
This governing law determines Hubble's angular resolution but does not assign
the requested numerical improvement factor.
-/
structure SatisfiesRayleighCriterion (setup : TelescopeResolutionSetup) : Prop where
  hubbleAngularResolutionLaw :
    ∀ unit : LengthUnit,
      setup.hubbleAngularResolutionRad =
        (61 / 50 : ℝ) * lengthReadout unit setup.visibleWavelength /
          lengthReadout unit setup.hubbleObjectiveDiameter

/-!
The improvement factor compares the worse Earth-based angular limit with the
smaller Hubble angular limit.  This is the definition of the physical ratio,
not a hypothesis that it equals any displayed answer.
-/
structure SatisfiesResolutionImprovementLaw
    (setup : TelescopeResolutionSetup) : Prop where
  improvementIsAngularResolutionRatio :
    setup.resolutionImprovementFactor =
      setup.earthAngularResolutionRad / setup.hubbleAngularResolutionRad

/-- Labels of the four dimensionless improvement factors printed in the problem. -/
inductive AnswerChoice where
  | A
  | B
  | C
  | D
  deriving DecidableEq, Repr

/-- Improvement factor displayed beside each answer choice. -/
def displayedImprovementFactor : AnswerChoice → ℝ
  | .A => 7
  | .B => 12
  | .C => 14
  | .D => 9

/-- The answer label recorded in the source dataset. -/
def recordedDatasetAnswer : AnswerChoice := .C

/-!
A choice is the best estimate when its displayed factor is at least as close
to the physically derived factor as every other displayed option.
-/
def IsNearestDisplayedImprovementChoice
    (setup : TelescopeResolutionSetup) (choice : AnswerChoice) : Prop :=
  ∀ alternative : AnswerChoice,
    |setup.resolutionImprovementFactor - displayedImprovementFactor choice| ≤
      |setup.resolutionImprovementFactor - displayedImprovementFactor alternative|

/-!
Under the stated telescope data, atmospheric angular limit, circular-aperture
law, and comparison law, `9×` (choice D) is the best displayed estimate of
Hubble's improvement over an Earth-bound telescope.  The conflicting recorded
choice C remains available separately as dataset metadata.

This formalizes `thm:physics:phyx_mini_0131:target`.
-/
theorem problem_phyx_mini_0131
    (setup : TelescopeResolutionSetup)
    (h_scenario : MatchesScenarioAndFigure setup)
    (h_data : MatchesProblemReadouts setup)
    (h_physical : HasPhysicalResolutionParameters setup)
    (h_rayleigh : SatisfiesRayleighCriterion setup)
    (h_comparison : SatisfiesResolutionImprovementLaw setup) :
    IsNearestDisplayedImprovementChoice setup .D := by
  rcases h_data with ⟨h_diameter, h_wavelength_nm, h_earth⟩
  let nmUnits : UnitChoices :=
    {UnitChoices.SI with length := LengthUnit.nanometers}
  have hSI : ({UnitChoices.SI with length := LengthUnit.meters} : UnitChoices) =
      UnitChoices.SI := by
    ext <;> rfl
  have h_unit_relation :
      lengthInMeters setup.visibleWavelength =
        (((nmUnits.dimScale UnitChoices.SI L𝓭 : NNReal) : ℝ) *
          lengthInNanometers setup.visibleWavelength) := by
    have h := congrArg (fun q => ((q.val : NNReal) : ℝ))
      (setup.visibleWavelength.property nmUnits UnitChoices.SI)
    simpa only [lengthInMeters, lengthInNanometers, lengthReadout, nmUnits,
      WithDim.smul_val, smul_eq_mul, NNReal.coe_mul, WithDim.dim_apply, hSI] using h
  have h_scale : (((nmUnits.dimScale UnitChoices.SI L𝓭 : NNReal) : ℝ)) =
      (1 / 1000000000 : ℝ) := by
    norm_num [nmUnits, UnitChoices.dimScale, LengthUnit.nanometers,
      LengthUnit.meters, LengthUnit.scale, LengthUnit.div_eq_val]
    rfl
  have h_wavelength_m :
      lengthInMeters setup.visibleWavelength = (11 / 20000000 : ℝ) := by
    calc
      lengthInMeters setup.visibleWavelength =
          (((nmUnits.dimScale UnitChoices.SI L𝓭 : NNReal) : ℝ) *
            lengthInNanometers setup.visibleWavelength) := h_unit_relation
      _ = 11 / 20000000 := by
        rw [h_scale, h_wavelength_nm]
        norm_num
  have h_hubble := h_rayleigh.hubbleAngularResolutionLaw LengthUnit.meters
  change setup.hubbleAngularResolutionRad =
    (61 / 50 : ℝ) * lengthInMeters setup.visibleWavelength /
      lengthInMeters setup.hubbleObjectiveDiameter at h_hubble
  rw [h_wavelength_m, h_diameter] at h_hubble
  norm_num at h_hubble
  have h_earth' : setup.earthAngularResolutionRad = Real.pi / 1296000 := by
    rw [h_earth]
    unfold arcsecondsToRadians arcsecondsPerDegree
    ring
  have h_factor :
      setup.resolutionImprovementFactor = 50000 * Real.pi / 18117 := by
    calc
      setup.resolutionImprovementFactor =
          setup.earthAngularResolutionRad /
            setup.hubbleAngularResolutionRad :=
        h_comparison.improvementIsAngularResolutionRatio
      _ = 50000 * Real.pi / 18117 := by
        rw [h_earth', h_hubble]
        ring
  have h_pi_lower : (3 : ℝ) < Real.pi := by
    have hbound := Real.cos_bound (x := (1 / 2 : ℝ)) (by norm_num)
    have hpos := Real.cos_pos_of_le_one (x := (1 / 2 : ℝ)) (by norm_num)
    have hcos : (1 / 2 : ℝ) < Real.cos 1 := by
      rw [show (1 : ℝ) = 2 * (1 / 2) by norm_num, Real.cos_two_mul]
      rw [abs_le] at hbound
      nlinarith
    by_contra h
    have hpi : Real.pi / 3 ≤ (1 : ℝ) := by
      have := le_of_not_gt h
      linarith
    have hcosle : Real.cos 1 ≤ Real.cos (Real.pi / 3) :=
      Real.cos_le_cos_of_nonneg_of_le_pi
        (by positivity) (by linarith [Real.two_le_pi]) hpi
    rw [Real.cos_pi_div_three] at hcosle
    linarith
  have h_pi_upper : Real.pi < (19 / 5 : ℝ) := by
    have hbound := Real.cos_bound (x := (19 / 20 : ℝ))
      (by norm_num [abs_of_nonneg])
    have hpos := Real.cos_pos_of_le_one (x := (19 / 20 : ℝ))
      (by norm_num [abs_of_nonneg])
    have hcos : Real.cos (19 / 10 : ℝ) < 0 := by
      rw [show (19 / 10 : ℝ) = 2 * (19 / 20) by norm_num, Real.cos_two_mul]
      rw [abs_le] at hbound
      have hupper : Real.cos (19 / 20 : ℝ) < 3 / 5 := by
        nlinarith
      have hprod : 0 ≤ ((3 / 5 : ℝ) - Real.cos (19 / 20)) *
          ((3 / 5 : ℝ) + Real.cos (19 / 20)) := by
        positivity
      nlinarith
    have hhalf : Real.pi / 2 < (19 / 10 : ℝ) := by
      by_contra h
      have hnonneg := Real.cos_nonneg_of_neg_pi_div_two_le_of_le
        (x := (19 / 10 : ℝ)) (by linarith [Real.pi_pos]) (by linarith)
      linarith
    linarith
  have h_factor_lower : (8 : ℝ) < setup.resolutionImprovementFactor := by
    rw [h_factor]
    nlinarith
  have h_factor_upper : setup.resolutionImprovementFactor < (21 / 2 : ℝ) := by
    rw [h_factor]
    nlinarith
  intro alternative
  cases alternative with
  | A =>
      simp only [displayedImprovementFactor]
      rw [← sq_le_sq]
      nlinarith
  | B =>
      simp only [displayedImprovementFactor]
      rw [← sq_le_sq]
      nlinarith
  | C =>
      simp only [displayedImprovementFactor]
      rw [← sq_le_sq]
      nlinarith
  | D =>
      exact le_rfl

end PhyXMiniProblems.ProblemPhyXMini0131
