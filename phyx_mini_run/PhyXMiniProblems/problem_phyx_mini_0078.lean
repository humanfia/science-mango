import Mathlib
import Physlib.SpaceAndTime.Space.LengthUnit
import Physlib.Units.WithDim.Basic

noncomputable section

namespace PhyXMiniProblems.ProblemPhyXMini0078

open Dimension

/-!
# Zoom of a separated converging--diverging lens pair

The primary figure shows two thin lenses on a horizontal optical axis.  The
left lens is converging with signed focal length `+f`, the right lens is
diverging with signed focal length `-f`, and their center-to-center separation
is `d`.  The source only says that the incident object is *very distant*, so
the model below does not replace it by an exactly collimated finite state.
Instead, a positive dimensionless parameter tends to zero while the physical
object distance tends to infinity.

All focal lengths, separations, and signed object/image distances below are
genuine dimensionful lengths.  A negative object distance at the right lens
represents the virtual object formed when the first lens's focal image lies to
the right of that lens.  The zoom is a dimensionless ratio of effective focal
lengths, where each effective focal length is measured from the midpoint of
the lens pair to the final image.
-/

/-- A signed physical length, independent of the unit used to read it. -/
abbrev LengthQuantity : Type := Dimensionful (WithDim L𝓭 ℝ)

/-- The signed scalar readout of a physical length in a selected length unit. -/
def lengthReadout (unit : LengthUnit) (length : LengthQuantity) : ℝ :=
  (length { UnitChoices.SI with length := unit }).val

/-- The signed scalar readout of a physical length in meters. -/
def lengthInMeters (length : LengthQuantity) : ℝ :=
  lengthReadout LengthUnit.meters length

/-- The two thin lenses in their left-to-right propagation order. -/
inductive LensLabel where
  | left
  | right
  deriving DecidableEq, Repr

/-- Thin-lens type, distinguished by the sign of its focal length. -/
inductive ThinLensKind where
  | converging
  | diverging
  deriving DecidableEq, Repr

/-- The orientation of the principal optical axis in the source figure. -/
inductive PrincipalAxisOrientation where
  | horizontal
  deriving DecidableEq, Repr

/-- The incident-object regime stipulated by the problem. -/
inductive IncidentObjectRegime where
  | veryDistant
  deriving DecidableEq, Repr

/-- The reference point used to define the effective focal length. -/
inductive EffectiveFocalReference where
  | midpointBetweenLenses
  deriving DecidableEq, Repr

/-- The two endpoint adjustments whose effective focal lengths are compared. -/
inductive ZoomSetting where
  | separationHalfF
  | separationQuarterF
  deriving DecidableEq, Repr

/-!
Physical quantities for the two-stage paraxial ray trace.

Distances at the right lens use the signed Gaussian convention.  In
particular, `rightLensObjectDistance` is negative when the converging lens's
intermediate image is a virtual object for the diverging lens.  Object and
image distances that vary with the far-object parameter are functions of a
real scalar; this scalar is dimensionless, while their values remain genuine
physical lengths.
-/
structure SimpleZoomLensSetup where
  principalAxisOrientation : PrincipalAxisOrientation
  lensKind : LensLabel → ThinLensKind
  incidentObjectRegime : IncidentObjectRegime
  effectiveFocalReference : EffectiveFocalReference
  focalLengthMagnitude : LengthQuantity
  signedFocalLength : LensLabel → LengthQuantity
  lensSeparation : ZoomSetting → LengthQuantity
  incidentObjectDistance : ℝ → LengthQuantity
  firstImageDistanceFromLeftLens : ℝ → LengthQuantity
  rightLensObjectDistance : ℝ → ZoomSetting → LengthQuantity
  rightLensImageDistance : ℝ → ZoomSetting → LengthQuantity
  midpointToRightLensDistance : ZoomSetting → LengthQuantity
  effectiveFocalLength : ℝ → ZoomSetting → LengthQuantity

/-!
Categorical and focal-length labels read from the primary figure: the axis is
horizontal, the left lens is converging and labeled `f`, and the right lens is
diverging and labeled `-f`.  These relations hold in every length unit and do
not assign the requested zoom.
-/
def MatchesPrimaryFigure (setup : SimpleZoomLensSetup) : Prop :=
  setup.principalAxisOrientation = .horizontal ∧
    setup.lensKind .left = .converging ∧
    setup.lensKind .right = .diverging ∧
    (∀ unit : LengthUnit,
      lengthReadout unit (setup.signedFocalLength .left) =
        lengthReadout unit setup.focalLengthMagnitude) ∧
    ∀ unit : LengthUnit,
      lengthReadout unit (setup.signedFocalLength .right) =
        -lengthReadout unit setup.focalLengthMagnitude

/-!
The textual assumptions about the incident object and focal reference.  The
limit is taken as a positive dimensionless far-object parameter approaches
zero.  Requiring every unit readout of the object distance to tend to `+∞`
formalizes `s ≈ ∞` without identifying a finite object distance with infinity.
-/
def HasStatedObjectRegimeAndReference (setup : SimpleZoomLensSetup) : Prop :=
  setup.incidentObjectRegime = .veryDistant ∧
    setup.effectiveFocalReference = .midpointBetweenLenses ∧
    ∀ unit : LengthUnit,
      Filter.Tendsto
        (fun farObjectParameter : ℝ =>
          lengthReadout unit
            (setup.incidentObjectDistance farObjectParameter))
        (nhdsWithin (0 : ℝ) (Set.Ioi 0)) Filter.atTop

/-!
The two adjustment readouts in the question: `d = f/2` and `d = f/4`.
They constrain only the physical lens separation at each endpoint.
-/
def MatchesAdjustmentReadouts (setup : SimpleZoomLensSetup) : Prop :=
  (∀ unit : LengthUnit,
      lengthReadout unit (setup.lensSeparation .separationHalfF) =
        (1 / 2 : ℝ) * lengthReadout unit setup.focalLengthMagnitude) ∧
    ∀ unit : LengthUnit,
      lengthReadout unit (setup.lensSeparation .separationQuarterF) =
        (1 / 4 : ℝ) * lengthReadout unit setup.focalLengthMagnitude

/-!
The stated physical range `0 < d < f`, together with positivity of the common
focal-length magnitude.  The virtual-object sign is intentionally not assumed:
it is a consequence of this ordering and the transfer geometry below.
-/
def HasPhysicalSeparationRange (setup : SimpleZoomLensSetup) : Prop :=
  0 < lengthInMeters setup.focalLengthMagnitude ∧
    ∀ setting : ZoomSetting,
      0 < lengthInMeters (setup.lensSeparation setting) ∧
        lengthInMeters (setup.lensSeparation setting) <
          lengthInMeters setup.focalLengthMagnitude

/-!
The first converging lens obeys the signed Gaussian thin-lens equation for all
sufficiently distant finite objects.  This is a neighborhood law, not the
global exact assertion that the intermediate image is already at the focal
plane.  Together with `HasStatedObjectRegimeAndReference`, it makes that focal
plane the limit of the intermediate-image position.
-/
def ObeysCollimatedInputLaw (setup : SimpleZoomLensSetup) : Prop :=
  ∀ unit : LengthUnit,
    ∀ᶠ farObjectParameter in nhdsWithin (0 : ℝ) (Set.Ioi 0),
      lengthReadout unit setup.focalLengthMagnitude *
          (lengthReadout unit
              (setup.incidentObjectDistance farObjectParameter) +
            lengthReadout unit
              (setup.firstImageDistanceFromLeftLens farObjectParameter)) =
        lengthReadout unit
            (setup.incidentObjectDistance farObjectParameter) *
          lengthReadout unit
            (setup.firstImageDistanceFromLeftLens farObjectParameter)

/-!
Transfer of the first image to the second lens.  With positive object distance
on the incident side of the right lens, an intermediate image at axial
distance `x` from the left lens gives signed object distance `d - x`.  The
relation is required only in the same far-object neighborhood as the paraxial
model.
-/
def ObeysIntermediateImageTransfer (setup : SimpleZoomLensSetup) : Prop :=
  ∀ (setting : ZoomSetting) (unit : LengthUnit),
    ∀ᶠ farObjectParameter in nhdsWithin (0 : ℝ) (Set.Ioi 0),
      lengthReadout unit
          (setup.rightLensObjectDistance farObjectParameter setting) =
        lengthReadout unit (setup.lensSeparation setting) -
          lengthReadout unit
            (setup.firstImageDistanceFromLeftLens farObjectParameter)

/-!
The signed Gaussian thin-lens equation at the diverging lens,
`1/f₂ = 1/s₂ + 1/s₂'`, written in the division-free, dimensionally homogeneous
form `f₂ (s₂ + s₂') = s₂ s₂'` in every selected length unit and throughout a
sufficiently small positive neighborhood of the far-object limit.
-/
def ObeysDivergingThinLensEquation (setup : SimpleZoomLensSetup) : Prop :=
  ∀ (setting : ZoomSetting) (unit : LengthUnit),
    ∀ᶠ farObjectParameter in nhdsWithin (0 : ℝ) (Set.Ioi 0),
      lengthReadout unit (setup.signedFocalLength .right) *
          (lengthReadout unit
              (setup.rightLensObjectDistance farObjectParameter setting) +
            lengthReadout unit
              (setup.rightLensImageDistance farObjectParameter setting)) =
        lengthReadout unit
            (setup.rightLensObjectDistance farObjectParameter setting) *
          lengthReadout unit
            (setup.rightLensImageDistance farObjectParameter setting)

/-!
Geometry implementing the problem's definition of effective focal length.
The right lens is `d/2` to the right of the pair's midpoint, so the distance
from that midpoint to the final image is `d/2 + s₂'`.
-/
def ObeysMidpointEffectiveFocalDefinition
    (setup : SimpleZoomLensSetup) : Prop :=
  (∀ (setting : ZoomSetting) (unit : LengthUnit),
      lengthReadout unit (setup.midpointToRightLensDistance setting) =
        lengthReadout unit (setup.lensSeparation setting) / 2) ∧
    ∀ (setting : ZoomSetting) (unit : LengthUnit),
      ∀ᶠ farObjectParameter in nhdsWithin (0 : ℝ) (Set.Ioi 0),
        lengthReadout unit
            (setup.effectiveFocalLength farObjectParameter setting) =
          lengthReadout unit (setup.midpointToRightLensDistance setting) +
            lengthReadout unit
              (setup.rightLensImageDistance farObjectParameter setting)

/-!
The dimensionless zoom between the two stated endpoints at a finite member of
the far-object family.  The quarter-`f` separation is the numerator of the
standard longest-to-shortest ratio.  The source's requested zoom is the limit
of this function, rather than its value at an exactly collimated finite state.
-/
def zoomRatio
    (setup : SimpleZoomLensSetup) (farObjectParameter : ℝ) : ℝ :=
  lengthInMeters
      (setup.effectiveFocalLength farObjectParameter .separationQuarterF) /
    lengthInMeters
      (setup.effectiveFocalLength farObjectParameter .separationHalfF)

/-- Labels of the four displayed multiple-choice answers. -/
inductive AnswerChoice where
  | A
  | B
  | C
  | D
  deriving DecidableEq, Repr

/-- The dimensionless zoom printed beside each answer choice. -/
def AnswerChoice.displayedZoom : AnswerChoice → ℝ
  | .A => 7 / 5
  | .B => 13 / 5
  | .C => 5 / 2
  | .D => 39 / 20

/-!
A displayed choice is correct when its value is the limiting physical zoom as
the finite incident-object distance tends to infinity.
-/
def IsCorrectZoomChoice
    (setup : SimpleZoomLensSetup) (choice : AnswerChoice) : Prop :=
  Filter.Tendsto (zoomRatio setup)
    (nhdsWithin (0 : ℝ) (Set.Ioi 0)) (nhds choice.displayedZoom)

/-!
As the finite object distance tends to infinity, the first image tends to the
left lens's focal plane.  Because `d < f`, the first image therefore eventually
lies to the right of the diverging lens and supplies it with a negative signed
object distance.  Both the focal-plane limit and the virtual-object sign are
derived conclusions rather than premises.
-/
lemma firstImageFormsVirtualObject
    (setup : SimpleZoomLensSetup)
    (h_objectAndReference : HasStatedObjectRegimeAndReference setup)
    (h_physical : HasPhysicalSeparationRange setup)
    (h_collimated : ObeysCollimatedInputLaw setup)
    (h_transfer : ObeysIntermediateImageTransfer setup) :
    Filter.Tendsto
        (fun farObjectParameter : ℝ =>
          lengthInMeters
            (setup.firstImageDistanceFromLeftLens farObjectParameter))
        (nhdsWithin (0 : ℝ) (Set.Ioi 0))
        (nhds (lengthInMeters setup.focalLengthMagnitude)) ∧
      ∀ setting : ZoomSetting,
        ∀ᶠ farObjectParameter in nhdsWithin (0 : ℝ) (Set.Ioi 0),
          lengthInMeters (setup.lensSeparation setting) <
              lengthInMeters
                (setup.firstImageDistanceFromLeftLens farObjectParameter) ∧
            lengthInMeters
                (setup.rightLensObjectDistance farObjectParameter setting) < 0 := by
  sorry

/-!
For a finite far-object parameter, write `x` for the first image's distance
from the left lens.  The two signed thin-lens stages and midpoint geometry
give the division-free identity

`(d - x + f) * (F_eff - d/2) = f * (x - d)`.

As the object distance tends to infinity, `x → f`, and this identity yields
the limiting formula `F_eff(d) → f^2/d - f + d/2`.  Thus no finite object is
silently replaced by an exactly collimated one.
-/
lemma effectiveFocalLength_formula
    (setup : SimpleZoomLensSetup)
    (h_figure : MatchesPrimaryFigure setup)
    (h_objectAndReference : HasStatedObjectRegimeAndReference setup)
    (h_physical : HasPhysicalSeparationRange setup)
    (h_collimated : ObeysCollimatedInputLaw setup)
    (h_transfer : ObeysIntermediateImageTransfer setup)
    (h_thinLens : ObeysDivergingThinLensEquation setup)
    (h_effective : ObeysMidpointEffectiveFocalDefinition setup) :
    ∀ (setting : ZoomSetting) (unit : LengthUnit),
      (∀ᶠ farObjectParameter in nhdsWithin (0 : ℝ) (Set.Ioi 0),
          (lengthReadout unit (setup.lensSeparation setting) -
                lengthReadout unit
                  (setup.firstImageDistanceFromLeftLens farObjectParameter) +
              lengthReadout unit setup.focalLengthMagnitude) *
              (lengthReadout unit
                    (setup.effectiveFocalLength farObjectParameter setting) -
                lengthReadout unit (setup.lensSeparation setting) / 2) =
            lengthReadout unit setup.focalLengthMagnitude *
              (lengthReadout unit
                  (setup.firstImageDistanceFromLeftLens farObjectParameter) -
                lengthReadout unit (setup.lensSeparation setting))) ∧
        Filter.Tendsto
          (fun farObjectParameter : ℝ =>
            lengthReadout unit
              (setup.effectiveFocalLength farObjectParameter setting))
          (nhdsWithin (0 : ℝ) (Set.Ioi 0))
          (nhds
            (lengthReadout unit setup.focalLengthMagnitude ^ 2 /
                lengthReadout unit (setup.lensSeparation setting) -
              lengthReadout unit setup.focalLengthMagnitude +
              lengthReadout unit (setup.lensSeparation setting) / 2)) := by
  sorry

/-!
In the far-object limit, the midpoint-to-image effective focal length tends to
`5f/4` at `d = f/2` and to `25f/8` at `d = f/4`.  These are limit conclusions
derived from the governing laws and endpoint readouts, not exact finite-state
assumptions.
-/
lemma endpointEffectiveFocalLengths
    (setup : SimpleZoomLensSetup)
    (h_figure : MatchesPrimaryFigure setup)
    (h_objectAndReference : HasStatedObjectRegimeAndReference setup)
    (h_adjustments : MatchesAdjustmentReadouts setup)
    (h_physical : HasPhysicalSeparationRange setup)
    (h_collimated : ObeysCollimatedInputLaw setup)
    (h_transfer : ObeysIntermediateImageTransfer setup)
    (h_thinLens : ObeysDivergingThinLensEquation setup)
    (h_effective : ObeysMidpointEffectiveFocalDefinition setup) :
    Filter.Tendsto
        (fun farObjectParameter : ℝ =>
          lengthInMeters
            (setup.effectiveFocalLength farObjectParameter .separationHalfF))
        (nhdsWithin (0 : ℝ) (Set.Ioi 0))
        (nhds ((5 / 4 : ℝ) *
          lengthInMeters setup.focalLengthMagnitude)) ∧
      Filter.Tendsto
        (fun farObjectParameter : ℝ =>
          lengthInMeters
            (setup.effectiveFocalLength farObjectParameter .separationQuarterF))
        (nhdsWithin (0 : ℝ) (Set.Ioi 0))
        (nhds ((25 / 8 : ℝ) *
          lengthInMeters setup.focalLengthMagnitude)) := by
  sorry

/-!
The endpoint effective focal lengths tend to `5f/4` and `25f/8`; their ratio
therefore tends to `5/2 = 2.5`.  Thus choice C is the limiting zoom for the
source's `s ≈ ∞` regime.  The theorem deliberately makes no exact `5/2` claim
about any finite incident-object distance.

This formalizes `thm:physics:phyx_mini_0078:target`.
-/
theorem problem_phyx_mini_0078
    (setup : SimpleZoomLensSetup)
    (h_figure : MatchesPrimaryFigure setup)
    (h_objectAndReference : HasStatedObjectRegimeAndReference setup)
    (h_adjustments : MatchesAdjustmentReadouts setup)
    (h_physical : HasPhysicalSeparationRange setup)
    (h_collimated : ObeysCollimatedInputLaw setup)
    (h_transfer : ObeysIntermediateImageTransfer setup)
    (h_thinLens : ObeysDivergingThinLensEquation setup)
    (h_effective : ObeysMidpointEffectiveFocalDefinition setup) :
    Filter.Tendsto (zoomRatio setup)
        (nhdsWithin (0 : ℝ) (Set.Ioi 0)) (nhds (5 / 2 : ℝ)) ∧
      IsCorrectZoomChoice setup .C := by
  sorry

end PhyXMiniProblems.ProblemPhyXMini0078
