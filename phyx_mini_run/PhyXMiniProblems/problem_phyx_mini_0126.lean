import Mathlib.Analysis.SpecialFunctions.Trigonometric.Angle
import Physlib.Units.WithDim.Basic

noncomputable section

namespace PhyXMiniProblems.ProblemPhyXMini0126

open Dimension

/-!
# Angular width of a single-slit central diffraction maximum

Monochromatic light of wavelength `750 nm` illuminates a rectangular slit of
width `1.0 * 10⁻³ mm`. The source image shows a screen `20 cm` from the slit,
parallel incident wavefronts, two first-minimum boundary rays, and an `x` label
for each half of the central maximum. Each boundary angle is displayed as
`49°`, so the recorded multiple-choice angular width is `98°`.

Lengths and irradiances are unit-independent Physlib quantities. Boundary
directions use Mathlib's `Real.Angle`; real scalars occur only as unit readouts,
degree readouts, or other dimensionless quantities. The displayed whole-degree
angles are modeled by half-degree error intervals rather than exact equalities:
the ideal law gives `sin θ = 750 / 1000 = 3 / 4`, whose acute solution is close
to, but not exactly, `49°`.
-/

/-- A signed, unit-independent physical quantity carrying length dimension. -/
abbrev LengthQuantity : Type := Dimensionful (WithDim L𝓭 ℝ)

/-- Irradiance has SI dimension `mass / time³`, equivalently power per area. -/
abbrev IrradianceQuantity : Type :=
  Dimensionful (WithDim (M𝓭 * T𝓭⁻¹ * T𝓭⁻¹ * T𝓭⁻¹) NNReal)

/-- Read a physical length as a real scalar in the selected length unit. -/
def lengthReadout (unit : LengthUnit) (length : LengthQuantity) : ℝ :=
  (length { UnitChoices.SI with length := unit }).val

/-- The metre readout used for positivity conditions. -/
def lengthInMeters (length : LengthQuantity) : ℝ :=
  lengthReadout LengthUnit.meters length

/-- The centimetre readout used for the slit-to-screen distance. -/
def lengthInCentimeters (length : LengthQuantity) : ℝ :=
  lengthReadout LengthUnit.centimeters length

/-- The millimetre readout used for the slit width. -/
def lengthInMillimeters (length : LengthQuantity) : ℝ :=
  lengthReadout LengthUnit.millimeters length

/-- The nanometre readout used for the incident wavelength. -/
def lengthInNanometers (length : LengthQuantity) : ℝ :=
  lengthReadout LengthUnit.nanometers length

/-- Read a physical irradiance as a nonnegative SI scalar. -/
def irradianceInSI (irradiance : IrradianceQuantity) : ℝ :=
  ((irradiance UnitChoices.SI).val : ℝ)

/-- Interpret a numerical angle in degrees as a Mathlib physical angle. -/
def degrees (value : ℝ) : Real.Angle :=
  ((value * Real.pi / 180 : ℝ) : Real.Angle)

/-- Read the canonical representative of a physical angle in degrees. -/
def angleInDegrees (angle : Real.Angle) : ℝ :=
  angle.toReal * 180 / Real.pi

/-- A degree readout agrees with a displayed whole degree to half a degree. -/
def MatchesWholeDegreeReadout (degreeReadout displayed : ℝ) : Prop :=
  |degreeReadout - displayed| ≤ (1 / 2 : ℝ)

/-- The two symmetric sides of the central diffraction maximum. -/
inductive ScreenSide where
  | upper
  | lower
  deriving DecidableEq, Repr

/-- The three screen locations singled out by the diagram. -/
inductive ScreenPoint where
  | upperFirstMinimum
  | centralAxis
  | lowerFirstMinimum
  deriving DecidableEq, Repr

/-- The slit plane and observation screen shown in the figure. -/
inductive OpticalPlane where
  | slitPlane
  | screen
  deriving DecidableEq, Repr

/-- The incident wavefront geometry drawn to the left of the slit. -/
inductive IncidentWavefront where
  | parallel
  | nonparallel
  deriving DecidableEq, Repr

/-- The aperture model selected by the one finite vertical slit in the image. -/
inductive ApertureGeometry where
  | singleRectangularSlit
  | other
  deriving DecidableEq, Repr

/-- The far-field model used for the first-minimum law. -/
inductive DiffractionRegime where
  | fraunhoferSingleSlit
  | other
  deriving DecidableEq, Repr

/-- Monochromatic incident light together with its physical wavelength. -/
structure MonochromaticLight where
  wavelength : LengthQuantity

/-- The finite rectangular aperture through which the light passes. -/
structure SingleSlitAperture where
  width : LengthQuantity
  geometry : ApertureGeometry

/-!
All physical quantities and figure-derived labels in the diffraction setup.

`centralMaximumHalfWidthX side` denotes either of the two lengths labeled `x`
on the screen. `firstMinimumAngle side` is the unsigned angle from the central
axis to the corresponding dashed boundary ray. The full angular width is an
unknown degree readout: no field assigns it `98` or selects an answer.
-/
structure SingleSlitDiffractionSetup where
  light : MonochromaticLight
  aperture : SingleSlitAperture
  incidentWavefront : IncidentWavefront
  regime : DiffractionRegime
  axialCoordinate : OpticalPlane → LengthQuantity
  screenDistance : LengthQuantity
  screenTransverseCoordinate : ScreenPoint → LengthQuantity
  centralMaximumHalfWidthX : ScreenSide → LengthQuantity
  firstMinimumAngle : ScreenSide → Real.Angle
  irradianceAtScreenPoint : ScreenPoint → IrradianceQuantity
  centralMaximumAngularWidthDegrees : ℝ

/-- The first-minimum boundary point associated with either screen side. -/
def firstMinimumPoint : ScreenSide → ScreenPoint
  | .upper => .upperFirstMinimum
  | .lower => .lowerFirstMinimum

/-!
Positive physical inputs and the acute branch for both first-minimum angles.
These conditions neither fix the angular width numerically nor select an
answer label.
-/
def HasPhysicalParameters (setup : SingleSlitDiffractionSetup) : Prop :=
  0 < lengthInMeters setup.light.wavelength ∧
    0 < lengthInMeters setup.aperture.width ∧
    0 < lengthInMeters setup.screenDistance ∧
    (∀ side : ScreenSide,
      0 < lengthInMeters (setup.centralMaximumHalfWidthX side)) ∧
    (∀ side : ScreenSide,
      0 < (setup.firstMinimumAngle side).toReal ∧
        (setup.firstMinimumAngle side).toReal < Real.pi / 2) ∧
    0 < irradianceInSI
      (setup.irradianceAtScreenPoint .centralAxis) ∧
    0 < setup.centralMaximumAngularWidthDegrees

/-- Numerical quantities stated in the problem text. -/
def MatchesProblemReadouts (setup : SingleSlitDiffractionSetup) : Prop :=
  lengthInNanometers setup.light.wavelength = 750 ∧
    lengthInMillimeters setup.aperture.width = 1 / 1000 ∧
    lengthInCentimeters setup.screenDistance = 20

/-!
Qualitative and metric information read from the primary image.

The wavefronts are parallel, there is one rectangular slit, the screen is
`20 cm` beyond the slit plane, and each labeled `x` runs from the central axis
to a first-minimum boundary. The matching `x` labels also express symmetry.
The two printed `49°` values are recorded to whole-degree precision. Neither
the unknown full angular width nor an answer choice appears here.
-/
def MatchesSingleSlitFigure (setup : SingleSlitDiffractionSetup) : Prop :=
  setup.incidentWavefront = .parallel ∧
    setup.aperture.geometry = .singleRectangularSlit ∧
    (∀ unit : LengthUnit,
      lengthReadout unit (setup.axialCoordinate .screen) -
          lengthReadout unit (setup.axialCoordinate .slitPlane) =
        lengthReadout unit setup.screenDistance) ∧
    lengthInCentimeters setup.screenDistance = 20 ∧
    (∀ unit : LengthUnit,
      lengthReadout unit
        (setup.screenTransverseCoordinate .centralAxis) = 0) ∧
    (∀ unit : LengthUnit,
      lengthReadout unit
            (setup.screenTransverseCoordinate .upperFirstMinimum) -
          lengthReadout unit
            (setup.screenTransverseCoordinate .centralAxis) =
        lengthReadout unit (setup.centralMaximumHalfWidthX .upper)) ∧
    (∀ unit : LengthUnit,
      lengthReadout unit
            (setup.screenTransverseCoordinate .centralAxis) -
          lengthReadout unit
            (setup.screenTransverseCoordinate .lowerFirstMinimum) =
        lengthReadout unit (setup.centralMaximumHalfWidthX .lower)) ∧
    (∀ unit : LengthUnit,
      lengthReadout unit (setup.centralMaximumHalfWidthX .upper) =
        lengthReadout unit (setup.centralMaximumHalfWidthX .lower)) ∧
    (∀ side : ScreenSide,
      MatchesWholeDegreeReadout
        (angleInDegrees (setup.firstMinimumAngle side)) 49)

/-- The setup is interpreted using Fraunhofer diffraction by one finite slit. -/
def UsesFraunhoferSingleSlitModel
    (setup : SingleSlitDiffractionSetup) : Prop :=
  setup.regime = .fraunhoferSingleSlit

/-!
Governing laws for the ideal single-slit pattern and the pictured screen.

The first minima obey `a |sin θ₁| = λ`; exact ray geometry gives
`x = L |tan θ₁|`; the intensity vanishes at each first minimum and is maximal
at the central point; and the full angular width is the sum of the two unsigned
boundary-angle readouts. These general laws contain neither `98°` nor an
answer label.
-/
structure SatisfiesSingleSlitDiffractionLaws
    (setup : SingleSlitDiffractionSetup) : Prop where
  firstMinimumLaw : ∀ (side : ScreenSide) (unit : LengthUnit),
    lengthReadout unit setup.aperture.width *
        |Real.Angle.sin (setup.firstMinimumAngle side)| =
      lengthReadout unit setup.light.wavelength
  exactScreenProjection : ∀ (side : ScreenSide) (unit : LengthUnit),
    lengthReadout unit (setup.centralMaximumHalfWidthX side) =
      lengthReadout unit setup.screenDistance *
        |Real.Angle.tan (setup.firstMinimumAngle side)|
  firstMinimumIsDark : ∀ side : ScreenSide,
    irradianceInSI
      (setup.irradianceAtScreenPoint (firstMinimumPoint side)) = 0
  centralPointIsBrightest : ∀ point : ScreenPoint,
    irradianceInSI (setup.irradianceAtScreenPoint point) ≤
      irradianceInSI (setup.irradianceAtScreenPoint .centralAxis)
  centralMaximumAngularWidthLaw :
    setup.centralMaximumAngularWidthDegrees =
      angleInDegrees (setup.firstMinimumAngle .upper) +
        angleInDegrees (setup.firstMinimumAngle .lower)

/-- Labels of the four angular-width choices printed with the problem. -/
inductive AnswerChoice where
  | A
  | B
  | C
  | D
  deriving DecidableEq, Repr

/-- The central-maximum width in degrees printed beside each answer label. -/
def displayedAngularWidthDegrees : AnswerChoice → ℝ
  | .A => 108
  | .B => 88
  | .C => 98
  | .D => 93

/-- A choice is at least as close to the derived width as every choice. -/
def IsClosestDisplayedAngularWidth
    (setup : SingleSlitDiffractionSetup) (choice : AnswerChoice) : Prop :=
  ∀ other : AnswerChoice,
    |setup.centralMaximumAngularWidthDegrees -
        displayedAngularWidthDegrees choice| ≤
      |setup.centralMaximumAngularWidthDegrees -
        displayedAngularWidthDegrees other|

/-- The selected choice is the unique closest displayed angular width. -/
def IsUniqueClosestDisplayedAngularWidth
    (setup : SingleSlitDiffractionSetup) (choice : AnswerChoice) : Prop :=
  IsClosestDisplayedAngularWidth setup choice ∧
    ∀ other : AnswerChoice,
      IsClosestDisplayedAngularWidth setup other → other = choice

/-!
The two whole-degree figure readouts and the angular-width composition law
place the central maximum between `97°` and `99°`. This interval is a derived
conclusion, not a setup field, readout premise, or governing-law premise.
-/
lemma centralMaximumAngularWidth_bounds
    (setup : SingleSlitDiffractionSetup)
    (h_figure : MatchesSingleSlitFigure setup)
    (h_laws : SatisfiesSingleSlitDiffractionLaws setup) :
    97 ≤ setup.centralMaximumAngularWidthDegrees ∧
      setup.centralMaximumAngularWidthDegrees ≤ 99 := by
  rcases h_figure with ⟨_, _, _, _, _, _, _, _, h_angles⟩
  have h_upper := h_angles .upper
  have h_lower := h_angles .lower
  rw [h_laws.centralMaximumAngularWidthLaw]
  simp only [MatchesWholeDegreeReadout] at h_upper h_lower
  rcases abs_le.mp h_upper with ⟨h_upper_lower, h_upper_upper⟩
  rcases abs_le.mp h_lower with ⟨h_lower_lower, h_lower_upper⟩
  constructor <;> linarith

/-!
For `λ = 750 nm`, slit width `1.0 * 10⁻³ mm`, and a screen `20 cm` away,
the single-slit first-minimum law determines the acute boundary angles. The
figure reports each as `49°` to whole-degree precision, so the full width lies
between `97°` and `99°`. Of `108°`, `88°`, `98°`, and `93°`, the unique closest
displayed width is therefore choice C, `98°`.

This formalizes `thm:physics:phyx_mini_0126:target`.
-/
theorem problem_phyx_mini_0126
    (setup : SingleSlitDiffractionSetup)
    (h_physical : HasPhysicalParameters setup)
    (h_problem : MatchesProblemReadouts setup)
    (h_figure : MatchesSingleSlitFigure setup)
    (h_model : UsesFraunhoferSingleSlitModel setup)
    (h_laws : SatisfiesSingleSlitDiffractionLaws setup) :
    97 ≤ setup.centralMaximumAngularWidthDegrees ∧
      setup.centralMaximumAngularWidthDegrees ≤ 99 ∧
      IsUniqueClosestDisplayedAngularWidth setup .C ∧
      displayedAngularWidthDegrees .C = 98 := by
  have h_bounds := centralMaximumAngularWidth_bounds setup h_figure h_laws
  rcases h_bounds with ⟨h_width_lower, h_width_upper⟩
  let width := setup.centralMaximumAngularWidthDegrees
  have h_C : |width - 98| ≤ 1 := by
    apply abs_le.mpr
    constructor <;> dsimp [width] <;> linarith
  have h_A : 9 ≤ |width - 108| := by
    calc
      9 ≤ -(width - 108) := by dsimp [width]; linarith
      _ ≤ |width - 108| := neg_le_abs _
  have h_B : 9 ≤ |width - 88| := by
    calc
      9 ≤ width - 88 := by dsimp [width]; linarith
      _ ≤ |width - 88| := le_abs_self _
  have h_D : 4 ≤ |width - 93| := by
    calc
      4 ≤ width - 93 := by dsimp [width]; linarith
      _ ≤ |width - 93| := le_abs_self _
  constructor
  · exact h_width_lower
  constructor
  · exact h_width_upper
  constructor
  · constructor
    · intro other
      cases other with
      | A =>
          change |width - 98| ≤ |width - 108|
          linarith
      | B =>
          change |width - 98| ≤ |width - 88|
          linarith
      | C =>
          exact le_rfl
      | D =>
          change |width - 98| ≤ |width - 93|
          linarith
    · intro other h_other
      cases other with
      | A =>
          have h_AC := h_other .C
          change |width - 108| ≤ |width - 98| at h_AC
          exfalso
          linarith
      | B =>
          have h_BC := h_other .C
          change |width - 88| ≤ |width - 98| at h_BC
          exfalso
          linarith
      | C =>
          rfl
      | D =>
          have h_DC := h_other .C
          change |width - 93| ≤ |width - 98| at h_DC
          exfalso
          linarith
  · rfl

end PhyXMiniProblems.ProblemPhyXMini0126
