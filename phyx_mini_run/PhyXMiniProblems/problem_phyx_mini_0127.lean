import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Physlib.Units.WithDim.Basic

/-!
# Minimum thickness of a green soap-bubble film

This file formalizes the air--film--air geometry shown in problem
`phyx_mini_0127`.  Wavelength and film thickness are unit-aware physical
lengths.  Refractive indices, radian phase shifts, incidence angles in radians,
and numerical nanometer readouts are dimensionless real scalars.
-/

noncomputable section

namespace PhyXMiniProblems.ProblemPhyXMini0127

open CarriesDimension Dimension

/-- A physical length with a real scalar carrier. -/
abbrev DimLength := Dimensionful (WithDim L𝓭 ℝ)

/-- Unit choices whose length unit is the nanometer used by the problem. -/
def nanometerUnitChoices : UnitChoices :=
  { UnitChoices.SI with length := LengthUnit.nanometers }

/-- The scalar nanometer readout of a physical length. -/
def nanometersValue (length : DimLength) : ℝ :=
  (length nanometerUnitChoices).val

/-- The Euclidean plane containing the thin-film diagram. -/
abbrev DiagramPlane := EuclideanSpace ℝ (Fin 2)

/-- The three physically distinct optical regions in the figure. -/
inductive OpticalRegion where
  | outsideAir
  | soapFilm
  | bubbleInterior
  deriving DecidableEq, Repr

/-- The two film interfaces met by the incident light. -/
inductive FilmInterface where
  | outsideToFilm
  | filmToInterior
  deriving DecidableEq, Repr

/-- Labels for the two reflected rays whose interference is observed. -/
inductive ReflectedRayLabel where
  | reflectedAtFrontSurface
  | reflectedAtInnerSurface
  deriving DecidableEq, Repr

/-- The incident region of each oriented film interface. -/
def incidentRegion : FilmInterface → OpticalRegion
  | .outsideToFilm => .outsideAir
  | .filmToInterior => .soapFilm

/-- The transmitted region of each oriented film interface. -/
def transmittedRegion : FilmInterface → OpticalRegion
  | .outsideToFilm => .soapFilm
  | .filmToInterior => .bubbleInterior

/-- A directed straight segment used to retain the ray labels in the figure. -/
structure RaySegment where
  sourcePoint : DiagramPlane
  targetPoint : DiagramPlane

/--
The ray reflected at the inner film surface: it enters the film at the front
surface, reflects at the film--interior interface, returns to the front
surface, and then travels back toward the viewer.
-/
structure InnerSurfaceReflectedRoute where
  frontEntryPoint : DiagramPlane
  innerReflectionPoint : DiagramPlane
  frontExitPoint : DiagramPlane
  outgoingEndpoint : DiagramPlane

/--
The physical quantities and labeled geometry of the depicted soap bubble.

`constructivelyReflectsGreenAtThicknessNm x` is the observable reflected-light
condition for a hypothetical film with nanometer thickness readout `x`.  Its
dependence on optical physics is supplied separately by
`ObeysThinFilmReflectionLaws`; it is not defined to make the target true.
-/
structure SoapBubbleThinFilm where
  /-- Vacuum/air wavelength of the green light seen by the viewer. -/
  greenWavelengthInAir : DimLength
  /-- Physical thickness labeled `t` between the two film interfaces. -/
  filmThickness : DimLength
  /-- Dimensionless refractive index of each homogeneous optical region. -/
  refractiveIndex : OpticalRegion → ℝ
  /-- Point on the front surface nearest the viewer. -/
  frontSurfacePointNearestViewer : DiagramPlane
  /-- Corresponding point on the inner surface along the local film normal. -/
  innerSurfacePoint : DiagramPlane
  /-- The incident ray drawn from the outside air to the nearest point. -/
  incidentRay : RaySegment
  /-- The ray reflected directly at the outside-air--film interface. -/
  frontSurfaceReflectedRay : RaySegment
  /-- The second reflected route, which makes a round trip through the film. -/
  innerSurfaceReflectedRoute : InnerSurfaceReflectedRoute
  /-- Incidence angle at the viewer-nearest point, measured from the normal. -/
  incidenceAngleRadians : ℝ
  /-- Boundary-induced phase shift of each reflected ray, in radians. -/
  reflectionPhaseShiftRadians : ReflectedRayLabel → ℝ
  /-- Constructive reflected interference for a positive nanometer thickness. -/
  constructivelyReflectsGreenAtThicknessNm : ℝ → Prop

/--
Figure and problem readouts: green light has wavelength `540 nm`, the soap
film has index `1.35`, and both adjacent regions are air with index `1.00`.
The viewer-nearest surface point gives normal incidence in this local model.
The route equalities retain the incident and two reflected rays shown in the
source image.  No numerical value of the unknown thickness occurs here.
-/
structure MatchesSoapBubbleFigure
    (setup : SoapBubbleThinFilm) : Prop where
  wavelengthReadout : nanometersValue setup.greenWavelengthInAir = 540
  outsideAirIndexReadout : setup.refractiveIndex .outsideAir = 1
  soapFilmIndexReadout : setup.refractiveIndex .soapFilm = 1.35
  interiorAirIndexReadout : setup.refractiveIndex .bubbleInterior = 1
  normalIncidenceAtNearestPoint : setup.incidenceAngleRadians = 0
  incidentReachesFrontSurface :
    setup.incidentRay.targetPoint = setup.frontSurfacePointNearestViewer
  frontReflectionStartsAtFrontSurface :
    setup.frontSurfaceReflectedRay.sourcePoint =
      setup.frontSurfacePointNearestViewer
  indirectRayEntersAtFrontSurface :
    setup.innerSurfaceReflectedRoute.frontEntryPoint =
      setup.frontSurfacePointNearestViewer
  indirectRayReflectsAtInnerSurface :
    setup.innerSurfaceReflectedRoute.innerReflectionPoint =
      setup.innerSurfacePoint
  indirectRayExitsAtFrontSurface :
    setup.innerSurfaceReflectedRoute.frontExitPoint =
      setup.frontSurfacePointNearestViewer

/--
Positivity and optical-density ordering for an ordinary soap film surrounded
by air.  These conditions contain no value for the requested minimum.
-/
structure HasPhysicalSoapFilmParameters
    (setup : SoapBubbleThinFilm) : Prop where
  wavelengthPositive : 0 < nanometersValue setup.greenWavelengthInAir
  actualThicknessPositive : 0 < nanometersValue setup.filmThickness
  refractiveIndexPositive : ∀ region, 0 < setup.refractiveIndex region
  frontReflectionIsLowToHigh :
    setup.refractiveIndex (incidentRegion .outsideToFilm) <
      setup.refractiveIndex (transmittedRegion .outsideToFilm)
  innerReflectionIsHighToLow :
    setup.refractiveIndex (transmittedRegion .filmToInterior) <
      setup.refractiveIndex (incidentRegion .filmToInterior)

/--
The governing normal-incidence reflected-light laws for an air--film--air
layer.  Reflection from outside air into the denser film contributes a
half-turn phase reversal, while reflection from film to interior air does not.
Consequently constructive reflection occurs exactly when the round-trip
optical thickness is an odd half-wavelength:
`4 n_film t = (2 m + 1) λ` for some nonnegative interference order `m`.

This is a general thin-film interference condition for candidate thicknesses,
not the requested minimum-thickness conclusion.
-/
structure ObeysThinFilmReflectionLaws
    (setup : SoapBubbleThinFilm) : Prop where
  frontSurfacePhaseReversal :
    setup.reflectionPhaseShiftRadians .reflectedAtFrontSurface = Real.pi
  innerSurfaceHasNoPhaseReversal :
    setup.reflectionPhaseShiftRadians .reflectedAtInnerSurface = 0
  constructiveReflectionIffOddQuarterWave :
    ∀ thicknessNm : ℝ, 0 < thicknessNm →
      setup.constructivelyReflectsGreenAtThicknessNm thicknessNm ↔
        ∃ order : ℕ,
          4 * setup.refractiveIndex .soapFilm * thicknessNm =
            (2 * (order : ℝ) + 1) *
              nanometersValue setup.greenWavelengthInAir

/-- The observed bubble thickness produces constructive green reflection. -/
def AppearsGreenAtNearestPoint (setup : SoapBubbleThinFilm) : Prop :=
  setup.constructivelyReflectsGreenAtThicknessNm
    (nanometersValue setup.filmThickness)

/-- Positive nanometer thicknesses that could produce the observed green color. -/
def possibleGreenThicknessesNm (setup : SoapBubbleThinFilm) : Set ℝ :=
  {thicknessNm |
    0 < thicknessNm ∧
      setup.constructivelyReflectsGreenAtThicknessNm thicknessNm}

/-- Labels of the four displayed multiple-choice answers. -/
inductive AnswerChoice where
  | A
  | B
  | C
  | D
  deriving DecidableEq, Repr

/-- Film-thickness readout in nanometers printed beside each answer choice. -/
def answerThicknessNanometers : AnswerChoice → ℝ
  | .A => 98
  | .B => 96
  | .C => 100
  | .D => 102

/-- The answer label recorded by the source dataset. -/
def recordedAnswerChoice : AnswerChoice := .C

/--
For `λ = 540 nm` and soap-film index `n = 1.35`, the least positive film
thickness that constructively reflects the observed green wavelength is the
recorded choice C, `100 nm`.  In particular, the actual positive thickness
of any depicted bubble that appears green at this point cannot be smaller.

Blueprint: `thm:physics:phyx_mini_0127:target`.
-/
theorem smallestGreenFilmThickness_isRecordedChoiceC
    (setup : SoapBubbleThinFilm)
    (hFigure : MatchesSoapBubbleFigure setup)
    (hPhysical : HasPhysicalSoapFilmParameters setup)
    (hLaws : ObeysThinFilmReflectionLaws setup)
    (hAppearance : AppearsGreenAtNearestPoint setup) :
    IsLeast (possibleGreenThicknessesNm setup)
        (answerThicknessNanometers recordedAnswerChoice) ∧
      answerThicknessNanometers recordedAnswerChoice ≤
        nanometersValue setup.filmThickness := by
  simp only [recordedAnswerChoice, answerThicknessNanometers]
  have hHundredConstructive :
      setup.constructivelyReflectsGreenAtThicknessNm 100 := by
    have hConstructiveIfPositive :
        0 < (100 : ℝ) →
          setup.constructivelyReflectsGreenAtThicknessNm 100 :=
      (hLaws.constructiveReflectionIffOddQuarterWave 100).2 (by
        refine ⟨0, ?_⟩
        rw [hFigure.soapFilmIndexReadout, hFigure.wavelengthReadout]
        norm_num)
    exact hConstructiveIfPositive (by norm_num)
  have hHundredPossible : 100 ∈ possibleGreenThicknessesNm setup := by
    exact ⟨by norm_num, hHundredConstructive⟩
  have hHundredLeast : IsLeast (possibleGreenThicknessesNm setup) 100 := by
    refine ⟨hHundredPossible, ?_⟩
    intro thicknessNm hThicknessPossible
    rcases hThicknessPossible with ⟨hThicknessPositive, hThicknessConstructive⟩
    have hOrderExists :=
      (hLaws.constructiveReflectionIffOddQuarterWave thicknessNm).1
        (fun _ => hThicknessConstructive)
    rcases hOrderExists with ⟨order, hOrder⟩
    rw [hFigure.soapFilmIndexReadout, hFigure.wavelengthReadout] at hOrder
    have hOrderNonnegative : (0 : ℝ) ≤ order := by positivity
    nlinarith
  refine ⟨hHundredLeast, hHundredLeast.2 ?_⟩
  exact ⟨hPhysical.actualThicknessPositive, hAppearance⟩

end PhyXMiniProblems.ProblemPhyXMini0127
