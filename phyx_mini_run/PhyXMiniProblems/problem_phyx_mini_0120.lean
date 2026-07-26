import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Physlib.Units.WithDim.Basic

noncomputable section

namespace PhyXMiniProblems.ProblemPhyXMini0120

open Dimension

/-!
# Nearest absolute maximum of a three-slit interference pattern

The three identical narrow slits are separated by the physical distance `d`
and illuminated by monochromatic light of wavelength `lambda`.  The screen is
a physical distance `R` from the slit plane.  At the labeled screen point `P`,
the middle-slit electric-field component is `E cos (omega t)`, while the upper
and lower components have phases `+phi` and `-phi`.

The source image supplies the labels `d`, `R`, `y`, `theta`, `d sin theta`, and
`P`, but no numerical values for `d`, `R`, or `lambda`.  Consequently the
physical laws below determine the symbolic distance `R * lambda / d`; the
recorded `3.25 mm` answer is retained as a separate conclusion of the main
target, without being inserted into any premise.
-/

/-- A unit-independent physical quantity carrying the dimension of length. -/
abbrev LengthQuantity : Type := Dimensionful (WithDim L𝓭 ℝ)

/-- A unit-independent physical time. -/
abbrev TimeQuantity : Type := Dimensionful (WithDim T𝓭 ℝ)

/-- Angular frequency has inverse-time dimension; radians are dimensionless. -/
abbrev AngularFrequencyQuantity : Type :=
  Dimensionful (WithDim T𝓭⁻¹ ℝ)

/--
A scalar electric-field component, with dimension
`mass * length / (time^2 * charge)`.
-/
abbrev ElectricFieldComponentQuantity : Type :=
  Dimensionful
    (WithDim (M𝓭 * L𝓭 * T𝓭⁻¹ * T𝓭⁻¹ * C𝓭⁻¹) ℝ)

/-- Irradiance has SI unit `W / m^2`, hence dimension `mass / time^3`. -/
abbrev IrradianceQuantity : Type :=
  Dimensionful (WithDim (M𝓭 * T𝓭⁻¹ * T𝓭⁻¹ * T𝓭⁻¹) NNReal)

/-- Scalar readout of a physical length in a selected length unit. -/
def lengthReadout (unit : LengthUnit) (length : LengthQuantity) : ℝ :=
  (length { UnitChoices.SI with length := unit }).val

/-- Scalar readout of a physical length in meters. -/
def lengthInMeters (length : LengthQuantity) : ℝ :=
  lengthReadout LengthUnit.meters length

/-- Scalar readout of a physical length in millimeters. -/
def lengthInMillimeters (length : LengthQuantity) : ℝ :=
  lengthReadout LengthUnit.millimeters length

/-- Scalar SI readout of a physical time, in seconds. -/
def timeInSeconds (time : TimeQuantity) : ℝ :=
  (time UnitChoices.SI).val

/-- Scalar SI readout of angular frequency, in radians per second. -/
def angularFrequencyInRadiansPerSecond
    (frequency : AngularFrequencyQuantity) : ℝ :=
  (frequency UnitChoices.SI).val

/-- Scalar SI readout of the electric-field component, in volts per meter. -/
def electricFieldComponentInSI
    (field : ElectricFieldComponentQuantity) : ℝ :=
  (field UnitChoices.SI).val

/-- Scalar SI irradiance readout, in watts per square meter. -/
def irradianceInSI (irradiance : IrradianceQuantity) : ℝ :=
  ((irradiance UnitChoices.SI).val : ℝ)

/-- The three apertures, ordered vertically as in the source image. -/
inductive SlitLabel where
  | upper
  | middle
  | lower
  deriving DecidableEq, Repr

/-- The two optical planes shown in the ray diagram. -/
inductive OpticalPlane where
  | slitPlane
  | screen
  deriving DecidableEq, Repr

/-- The central screen point and the explicitly labeled point `P`. -/
inductive ScreenPoint where
  | central
  | P
  deriving DecidableEq, Repr

/-- Coordinate axes implicit in the labels `R` (axial) and `y` (transverse). -/
inductive FigureAxis where
  | axial
  | transverse
  deriving DecidableEq, Repr

/-- Whether an aperture is idealized as narrow or assigned a finite width. -/
inductive ApertureModel where
  | narrow
  | finiteWidth
  deriving DecidableEq, Repr

/-- The propagation model used to project a ray angle onto the screen. -/
inductive OpticalApproximation where
  | smallAngle
  | exactRayGeometry
  deriving DecidableEq, Repr

/--
Physical quantities, field readouts, and labeled geometry for the experiment.

`phaseAtOffsetY y` is the adjacent-slit phase at signed screen offset `y`.
The three individual fields at `P` and their coherent sum remain dimensionful
electric-field components.  The full screen pattern is a dimensionful
irradiance.
-/
structure ThreeSlitInterferenceSetup where
  axialCoordinate : OpticalPlane → LengthQuantity
  slitTransverseCoordinate : SlitLabel → LengthQuantity
  screenPointOffsetY : ScreenPoint → LengthQuantity
  apertureModel : SlitLabel → ApertureModel
  arrivalPoint : SlitLabel → ScreenPoint
  axialAxisLabel : FigureAxis
  transverseAxisLabel : FigureAxis
  approximation : OpticalApproximation
  slitSeparationD : LengthQuantity
  screenDistanceR : LengthQuantity
  wavelengthLambda : LengthQuantity
  fieldAmplitudeE : ElectricFieldComponentQuantity
  angularFrequencyOmega : AngularFrequencyQuantity
  pointPTheta : ℝ
  pointPPhasePhi : ℝ
  pathDifferenceFromMiddleAtP : SlitLabel → LengthQuantity
  electricFieldComponentAtP :
    SlitLabel → TimeQuantity → ElectricFieldComponentQuantity
  totalElectricFieldComponentAtP :
    TimeQuantity → ElectricFieldComponentQuantity
  screenRayAngle : LengthQuantity → ℝ
  phaseAtOffsetY : LengthQuantity → ℝ
  irradianceAtOffsetY : LengthQuantity → IrradianceQuantity
  centralIrradiance : IrradianceQuantity

/-- The phase assigned to each slit in the field formulas stated at `P`. -/
def slitPhaseAtP
    (setup : ThreeSlitInterferenceSetup) : SlitLabel → ℝ
  | .upper => setup.pointPPhasePhi
  | .middle => 0
  | .lower => -setup.pointPPhasePhi

/-- Signed transverse separation from the central screen point, in a unit. -/
def signedOffsetFromCentral
    (unit : LengthUnit) (setup : ThreeSlitInterferenceSetup)
    (offsetY : LengthQuantity) : ℝ :=
  lengthReadout unit offsetY -
    lengthReadout unit (setup.screenPointOffsetY .central)

/-- Positive distance from the central point, read in millimeters. -/
def distanceFromCentralInMillimeters
    (setup : ThreeSlitInterferenceSetup) (offsetY : LengthQuantity) : ℝ :=
  |signedOffsetFromCentral LengthUnit.millimeters setup offsetY|

/--
Qualitative and metric information read from the primary image.

The upper-to-middle and middle-to-lower separations are both `d`; every ray
arrives at `P`; the screen is `R` beyond the slit plane; the central point has
zero transverse offset; and the signed adjacent path differences at `P` are
`d sin theta`, `0`, and `-d sin theta`.  No requested fringe distance occurs
in this figure predicate.
-/
def MatchesThreeSlitFigure (setup : ThreeSlitInterferenceSetup) : Prop :=
  setup.axialAxisLabel = .axial ∧
    setup.transverseAxisLabel = .transverse ∧
    (∀ slit : SlitLabel, setup.apertureModel slit = .narrow) ∧
    (∀ slit : SlitLabel, setup.arrivalPoint slit = .P) ∧
    (∀ unit : LengthUnit,
      lengthReadout unit (setup.axialCoordinate .screen) -
          lengthReadout unit (setup.axialCoordinate .slitPlane) =
        lengthReadout unit setup.screenDistanceR) ∧
    (∀ unit : LengthUnit,
      lengthReadout unit (setup.slitTransverseCoordinate .upper) -
          lengthReadout unit (setup.slitTransverseCoordinate .middle) =
        lengthReadout unit setup.slitSeparationD) ∧
    (∀ unit : LengthUnit,
      lengthReadout unit (setup.slitTransverseCoordinate .middle) -
          lengthReadout unit (setup.slitTransverseCoordinate .lower) =
        lengthReadout unit setup.slitSeparationD) ∧
    lengthInMeters (setup.screenPointOffsetY .central) = 0 ∧
    setup.screenRayAngle (setup.screenPointOffsetY .P) = setup.pointPTheta ∧
    setup.phaseAtOffsetY (setup.screenPointOffsetY .P) =
      setup.pointPPhasePhi ∧
    (∀ unit : LengthUnit,
      lengthReadout unit (setup.pathDifferenceFromMiddleAtP .upper) =
        lengthReadout unit setup.slitSeparationD *
          Real.sin setup.pointPTheta) ∧
    (∀ unit : LengthUnit,
      lengthReadout unit (setup.pathDifferenceFromMiddleAtP .middle) = 0) ∧
    (∀ unit : LengthUnit,
      lengthReadout unit (setup.pathDifferenceFromMiddleAtP .lower) =
        -(lengthReadout unit setup.slitSeparationD *
          Real.sin setup.pointPTheta))

/-- Positivity conditions for the physical inputs and central illumination. -/
def HasPhysicalParameters (setup : ThreeSlitInterferenceSetup) : Prop :=
  0 < lengthInMeters setup.slitSeparationD ∧
    0 < lengthInMeters setup.screenDistanceR ∧
    0 < lengthInMeters setup.wavelengthLambda ∧
    0 < electricFieldComponentInSI setup.fieldAmplitudeE ∧
    0 < angularFrequencyInRadiansPerSecond setup.angularFrequencyOmega ∧
    0 < irradianceInSI setup.centralIrradiance

/--
The three monochromatic field formulas stated in the problem, together with
linear coherent superposition.  The phase convention is upper `+phi`, middle
`0`, and lower `-phi`.
-/
structure SatisfiesMonochromaticFieldsAtP
    (setup : ThreeSlitInterferenceSetup) : Prop where
  phaseFromPathDifference :
    setup.pointPPhasePhi =
      2 * Real.pi * lengthInMeters setup.slitSeparationD *
          Real.sin setup.pointPTheta /
        lengthInMeters setup.wavelengthLambda
  harmonicComponentLaw :
    ∀ (slit : SlitLabel) (time : TimeQuantity),
      electricFieldComponentInSI
          (setup.electricFieldComponentAtP slit time) =
        electricFieldComponentInSI setup.fieldAmplitudeE *
          Real.cos
            (angularFrequencyInRadiansPerSecond
                  setup.angularFrequencyOmega *
                timeInSeconds time +
              slitPhaseAtP setup slit)
  coherentSuperpositionLaw :
    ∀ time : TimeQuantity,
      electricFieldComponentInSI
          (setup.totalElectricFieldComponentAtP time) =
        electricFieldComponentInSI
            (setup.electricFieldComponentAtP .upper time) +
          electricFieldComponentInSI
            (setup.electricFieldComponentAtP .middle time) +
          electricFieldComponentInSI
            (setup.electricFieldComponentAtP .lower time)

/--
Governing small-angle geometry and ideal equal-amplitude three-slit
interference across the screen.

The laws are `y = R sin theta`, `phi = 2 pi d sin(theta) / lambda`, and the
normalized intensity `I = I_central ((1 + 2 cos phi) / 3)^2`.  They contain
neither the requested `3.25 mm` value nor an answer-choice label.
-/
structure SatisfiesParaxialThreeSlitInterferenceLaws
    (setup : ThreeSlitInterferenceSetup) : Prop where
  usesSmallAngleApproximation : setup.approximation = .smallAngle
  screenProjectionLaw :
    ∀ offsetY : LengthQuantity,
      signedOffsetFromCentral LengthUnit.meters setup offsetY =
        lengthInMeters setup.screenDistanceR *
          Real.sin (setup.screenRayAngle offsetY)
  phaseDifferenceLaw :
    ∀ offsetY : LengthQuantity,
      setup.phaseAtOffsetY offsetY =
        2 * Real.pi * lengthInMeters setup.slitSeparationD *
            Real.sin (setup.screenRayAngle offsetY) /
          lengthInMeters setup.wavelengthLambda
  equalAmplitudeIntensityLaw :
    ∀ offsetY : LengthQuantity,
      irradianceInSI (setup.irradianceAtOffsetY offsetY) =
        irradianceInSI setup.centralIrradiance *
          ((1 + 2 * Real.cos (setup.phaseAtOffsetY offsetY)) / 3) ^ 2

/-- A screen offset realizes the global (absolute) maximum irradiance. -/
def IsAbsoluteIntensityMaximum
    (setup : ThreeSlitInterferenceSetup) (offsetY : LengthQuantity) : Prop :=
  ∀ otherOffsetY : LengthQuantity,
    irradianceInSI (setup.irradianceAtOffsetY otherOffsetY) ≤
      irradianceInSI (setup.irradianceAtOffsetY offsetY)

/--
The closest absolute maximum on the positive-`y` side of the central maximum.
This identifies the requested point without assigning its distance.
-/
def IsClosestPositiveAbsoluteMaximum
    (setup : ThreeSlitInterferenceSetup) (offsetY : LengthQuantity) : Prop :=
  0 < signedOffsetFromCentral LengthUnit.millimeters setup offsetY ∧
    IsAbsoluteIntensityMaximum setup offsetY ∧
    ∀ otherOffsetY : LengthQuantity,
      0 < signedOffsetFromCentral LengthUnit.millimeters setup otherOffsetY →
        IsAbsoluteIntensityMaximum setup otherOffsetY →
          signedOffsetFromCentral LengthUnit.millimeters setup offsetY ≤
            signedOffsetFromCentral LengthUnit.millimeters setup otherOffsetY

/-- The four answer labels printed with the problem. -/
inductive AnswerChoice where
  | A
  | B
  | C
  | D
  deriving DecidableEq, Repr

/--
Displayed distance readouts, in millimeters.  The degree sign appended to D in
the source is dimensionally inconsistent and is not part of its readout.
-/
def displayedDistanceMillimeters : AnswerChoice → ℝ
  | .A => 13 / 4
  | .B => 83 / 25
  | .C => 78 / 25
  | .D => 167 / 50

/-- The answer label recorded in the source dataset. -/
def recordedDatasetAnswer : AnswerChoice := .A

/-- A displayed choice equals the requested central-to-maximum distance. -/
def MatchesDisplayedDistanceChoice
    (setup : ThreeSlitInterferenceSetup) (offsetY : LengthQuantity)
    (choice : AnswerChoice) : Prop :=
  distanceFromCentralInMillimeters setup offsetY =
    displayedDistanceMillimeters choice

/-- A choice is the unique displayed distance matching the requested point. -/
def IsUniqueMatchingDisplayedChoice
    (setup : ThreeSlitInterferenceSetup) (offsetY : LengthQuantity)
    (choice : AnswerChoice) : Prop :=
  MatchesDisplayedDistanceChoice setup offsetY choice ∧
    ∀ other : AnswerChoice,
      MatchesDisplayedDistanceChoice setup offsetY other → other = choice

/--
The stated harmonic components coherently add to
`E (1 + 2 cos phi) cos(omega t)` at `P`.
-/
lemma resultantElectricFieldAtP
    (setup : ThreeSlitInterferenceSetup)
    (h_fields : SatisfiesMonochromaticFieldsAtP setup)
    (time : TimeQuantity) :
    electricFieldComponentInSI
        (setup.totalElectricFieldComponentAtP time) =
      electricFieldComponentInSI setup.fieldAmplitudeE *
        (1 + 2 * Real.cos setup.pointPPhasePhi) *
        Real.cos
          (angularFrequencyInRadiansPerSecond setup.angularFrequencyOmega *
            timeInSeconds time) := by
  simp only [h_fields.coherentSuperpositionLaw,
    h_fields.harmonicComponentLaw]
  simp [slitPhaseAtP, Real.cos_add]
  ring

/--
In the paraxial model the first positive absolute maximum has adjacent-slit
phase `2 pi`, the first recurrence of the central phasor alignment.
-/
lemma closestAbsoluteMaximum_phase_eq_two_pi
    (setup : ThreeSlitInterferenceSetup)
    (closestOffsetY : LengthQuantity)
    (h_physical : HasPhysicalParameters setup)
    (h_figure : MatchesThreeSlitFigure setup)
    (h_laws : SatisfiesParaxialThreeSlitInterferenceLaws setup)
    (h_closest :
      IsClosestPositiveAbsoluteMaximum setup closestOffsetY) :
    setup.phaseAtOffsetY closestOffsetY = 2 * Real.pi := by
  have hd : 0 < lengthInMeters setup.slitSeparationD := h_physical.1
  have hR : 0 < lengthInMeters setup.screenDistanceR := h_physical.2.1
  have hl : 0 < lengthInMeters setup.wavelengthLambda :=
    h_physical.2.2.1
  have hI : 0 < irradianceInSI setup.centralIrradiance :=
    h_physical.2.2.2.2.2
  have h_meters_choice :
      {UnitChoices.SI with length := LengthUnit.meters} =
        UnitChoices.SI := by
    rfl
  have h_meters_eq (length : LengthQuantity) :
      lengthInMeters length = (length UnitChoices.SI).val := by
    unfold lengthInMeters lengthReadout
    rw [h_meters_choice]
  have h_millimeters_eq (length : LengthQuantity) :
      lengthInMillimeters length = 1000 * lengthInMeters length := by
    unfold lengthInMillimeters lengthInMeters lengthReadout
    change
      (length
          {UnitChoices.SI with length := LengthUnit.millimeters}).val =
        1000 * (length UnitChoices.SI).val
    rw [length.property UnitChoices.SI
      {UnitChoices.SI with length := LengthUnit.millimeters}]
    norm_num [UnitChoices.dimScale, LengthUnit.millimeters,
      LengthUnit.meters, LengthUnit.scale, LengthUnit.div_eq_val]
    rfl
  have h_signed_millimeters_eq (offsetY : LengthQuantity) :
      signedOffsetFromCentral LengthUnit.millimeters setup offsetY =
        1000 *
          signedOffsetFromCentral LengthUnit.meters setup offsetY := by
    change
      lengthInMillimeters offsetY -
          lengthInMillimeters (setup.screenPointOffsetY .central) =
        1000 *
          (lengthInMeters offsetY -
            lengthInMeters (setup.screenPointOffsetY .central))
    rw [h_millimeters_eq, h_millimeters_eq]
    ring
  have h_signed_closest_pos :
      0 <
        signedOffsetFromCentral LengthUnit.meters setup closestOffsetY := by
    have hpos := h_closest.1
    rw [h_signed_millimeters_eq] at hpos
    nlinarith
  have h_sin_closest_pos :
      0 < Real.sin (setup.screenRayAngle closestOffsetY) := by
    have h_projection := h_laws.screenProjectionLaw closestOffsetY
    have h_product_pos :
        0 <
          lengthInMeters setup.screenDistanceR *
            Real.sin (setup.screenRayAngle closestOffsetY) := by
      rw [← h_projection]
      exact h_signed_closest_pos
    exact pos_of_mul_pos_right h_product_pos hR.le
  have h_phase_pos : 0 < setup.phaseAtOffsetY closestOffsetY := by
    rw [h_laws.phaseDifferenceLaw]
    positivity
  have h_signed_central :
      signedOffsetFromCentral LengthUnit.meters setup
          (setup.screenPointOffsetY .central) =
        0 := by
    simp [signedOffsetFromCentral]
  have h_sin_central :
      Real.sin
          (setup.screenRayAngle (setup.screenPointOffsetY .central)) =
        0 := by
    have h_projection :=
      h_laws.screenProjectionLaw (setup.screenPointOffsetY .central)
    rw [h_signed_central] at h_projection
    exact
      (mul_eq_zero.mp h_projection.symm).resolve_left (ne_of_gt hR)
  have h_phase_central :
      setup.phaseAtOffsetY (setup.screenPointOffsetY .central) = 0 := by
    rw [h_laws.phaseDifferenceLaw, h_sin_central]
    simp
  have h_central_value :
      irradianceInSI
          (setup.irradianceAtOffsetY
            (setup.screenPointOffsetY .central)) =
        irradianceInSI setup.centralIrradiance := by
    rw [h_laws.equalAmplitudeIntensityLaw, h_phase_central]
    norm_num
  have h_at_least_central :=
    h_closest.2.1 (setup.screenPointOffsetY .central)
  rw [h_central_value, h_laws.equalAmplitudeIntensityLaw] at h_at_least_central
  have h_factor_ge :
      1 ≤
        ((1 + 2 * Real.cos (setup.phaseAtOffsetY closestOffsetY)) /
            3) ^
          2 :=
    (le_mul_iff_one_le_right hI).mp h_at_least_central
  rcases Real.cos_mem_Icc (setup.phaseAtOffsetY closestOffsetY) with
    ⟨h_cos_lower, h_cos_upper⟩
  have h_cos_eq_one :
      Real.cos (setup.phaseAtOffsetY closestOffsetY) = 1 := by
    nlinarith
  have h_closest_value :
      irradianceInSI (setup.irradianceAtOffsetY closestOffsetY) =
        irradianceInSI setup.centralIrradiance := by
    rw [h_laws.equalAmplitudeIntensityLaw, h_cos_eq_one]
    norm_num
  let firstOffsetY : LengthQuantity :=
    CarriesDimension.toDimensionful UnitChoices.SI
      ⟨lengthInMeters (setup.screenPointOffsetY .central) +
        lengthInMeters setup.screenDistanceR *
            lengthInMeters setup.wavelengthLambda /
          lengthInMeters setup.slitSeparationD⟩
  have h_first_meters :
      lengthInMeters firstOffsetY =
        lengthInMeters (setup.screenPointOffsetY .central) +
            lengthInMeters setup.screenDistanceR *
              lengthInMeters setup.wavelengthLambda /
          lengthInMeters setup.slitSeparationD := by
    rw [h_meters_eq]
    simp [firstOffsetY, CarriesDimension.toDimensionful_apply_apply]
  have h_first_signed :
      signedOffsetFromCentral LengthUnit.meters setup firstOffsetY =
        lengthInMeters setup.screenDistanceR *
            lengthInMeters setup.wavelengthLambda /
          lengthInMeters setup.slitSeparationD := by
    change
      lengthInMeters firstOffsetY -
          lengthInMeters (setup.screenPointOffsetY .central) =
        _
    rw [h_first_meters]
    ring
  have h_sin_first :
      Real.sin (setup.screenRayAngle firstOffsetY) =
        lengthInMeters setup.wavelengthLambda /
          lengthInMeters setup.slitSeparationD := by
    have h_projection := h_laws.screenProjectionLaw firstOffsetY
    rw [h_first_signed] at h_projection
    have h_cleared :
        lengthInMeters setup.screenDistanceR *
            lengthInMeters setup.wavelengthLambda =
          lengthInMeters setup.screenDistanceR *
            (Real.sin (setup.screenRayAngle firstOffsetY) *
              lengthInMeters setup.slitSeparationD) := by
      calc
        _ =
            (lengthInMeters setup.screenDistanceR *
                  lengthInMeters setup.wavelengthLambda /
                lengthInMeters setup.slitSeparationD) *
              lengthInMeters setup.slitSeparationD := by
                field_simp
        _ =
            (lengthInMeters setup.screenDistanceR *
                Real.sin (setup.screenRayAngle firstOffsetY)) *
              lengthInMeters setup.slitSeparationD := by
                rw [h_projection]
        _ = _ := by ring
    have h_product := mul_left_cancel₀ (ne_of_gt hR) h_cleared
    exact (eq_div_iff (ne_of_gt hd)).2 h_product.symm
  have h_phase_first :
      setup.phaseAtOffsetY firstOffsetY = 2 * Real.pi := by
    rw [h_laws.phaseDifferenceLaw, h_sin_first]
    field_simp
  have h_first_positive :
      0 <
        signedOffsetFromCentral LengthUnit.millimeters setup
          firstOffsetY := by
    rw [h_signed_millimeters_eq, h_first_signed]
    positivity
  have h_first_value :
      irradianceInSI (setup.irradianceAtOffsetY firstOffsetY) =
        irradianceInSI setup.centralIrradiance := by
    rw [h_laws.equalAmplitudeIntensityLaw, h_phase_first]
    norm_num
  have h_first_maximum :
      IsAbsoluteIntensityMaximum setup firstOffsetY := by
    intro otherOffsetY
    calc
      irradianceInSI (setup.irradianceAtOffsetY otherOffsetY) ≤
          irradianceInSI
            (setup.irradianceAtOffsetY closestOffsetY) :=
        h_closest.2.1 otherOffsetY
      _ = irradianceInSI setup.centralIrradiance := h_closest_value
      _ = irradianceInSI (setup.irradianceAtOffsetY firstOffsetY) :=
        h_first_value.symm
  have h_signed_le_millimeters :=
    h_closest.2.2 firstOffsetY h_first_positive h_first_maximum
  have h_signed_le :
      signedOffsetFromCentral LengthUnit.meters setup closestOffsetY ≤
        signedOffsetFromCentral LengthUnit.meters setup firstOffsetY := by
    rw [h_signed_millimeters_eq, h_signed_millimeters_eq] at h_signed_le_millimeters
    nlinarith
  have h_phase_linear (offsetY : LengthQuantity) :
      setup.phaseAtOffsetY offsetY =
        (2 * Real.pi * lengthInMeters setup.slitSeparationD /
            (lengthInMeters setup.screenDistanceR *
              lengthInMeters setup.wavelengthLambda)) *
          signedOffsetFromCentral LengthUnit.meters setup offsetY := by
    have h_projection := h_laws.screenProjectionLaw offsetY
    have h_sin :
        Real.sin (setup.screenRayAngle offsetY) =
          signedOffsetFromCentral LengthUnit.meters setup offsetY /
            lengthInMeters setup.screenDistanceR := by
      apply (eq_div_iff (ne_of_gt hR)).2
      rw [mul_comm]
      exact h_projection.symm
    rw [h_laws.phaseDifferenceLaw, h_sin]
    field_simp
  have h_phase_le :
      setup.phaseAtOffsetY closestOffsetY ≤
        setup.phaseAtOffsetY firstOffsetY := by
    rw [h_phase_linear, h_phase_linear]
    exact mul_le_mul_of_nonneg_left h_signed_le (by positivity)
  rcases (Real.cos_eq_one_iff _).1 h_cos_eq_one with ⟨n, hn⟩
  have h_two_pi_pos : 0 < 2 * Real.pi := by positivity
  have hn_real_pos : 0 < (n : ℝ) := by
    apply pos_of_mul_pos_left
    · rw [hn]
      exact h_phase_pos
    · exact h_two_pi_pos.le
  have hn_pos : 0 < n := by exact_mod_cast hn_real_pos
  have hn_ge_one : (1 : ℤ) ≤ n := by omega
  have hn_real_le_one : (n : ℝ) ≤ 1 := by
    rw [h_phase_first] at h_phase_le
    nlinarith
  have hn_le_one : n ≤ (1 : ℤ) := by exact_mod_cast hn_real_le_one
  have hn_eq_one : n = 1 := le_antisymm hn_le_one hn_ge_one
  calc
    setup.phaseAtOffsetY closestOffsetY =
        (n : ℝ) * (2 * Real.pi) :=
      hn.symm
    _ = 2 * Real.pi := by rw [hn_eq_one]; norm_num

/--
The symbolic distance to the closest positive absolute maximum is
`R lambda / d`, expressed using millimeter readouts throughout.
-/
lemma closestAbsoluteMaximumDistance_formula
    (setup : ThreeSlitInterferenceSetup)
    (closestOffsetY : LengthQuantity)
    (h_physical : HasPhysicalParameters setup)
    (h_figure : MatchesThreeSlitFigure setup)
    (h_laws : SatisfiesParaxialThreeSlitInterferenceLaws setup)
    (h_closest :
      IsClosestPositiveAbsoluteMaximum setup closestOffsetY) :
    distanceFromCentralInMillimeters setup closestOffsetY =
      lengthInMillimeters setup.screenDistanceR *
        lengthInMillimeters setup.wavelengthLambda /
          lengthInMillimeters setup.slitSeparationD := by
  have hd : 0 < lengthInMeters setup.slitSeparationD := h_physical.1
  have h_phase :=
    closestAbsoluteMaximum_phase_eq_two_pi setup closestOffsetY
      h_physical h_figure h_laws h_closest
  have h_phase_law := h_laws.phaseDifferenceLaw closestOffsetY
  rw [h_phase] at h_phase_law
  have hl : 0 < lengthInMeters setup.wavelengthLambda :=
    h_physical.2.2.1
  have h_two_pi_ne : 2 * Real.pi ≠ 0 := by positivity
  have h_scaled := (eq_div_iff (ne_of_gt hl)).mp h_phase_law
  have h_cancelled :
      lengthInMeters setup.wavelengthLambda =
        lengthInMeters setup.slitSeparationD *
          Real.sin (setup.screenRayAngle closestOffsetY) := by
    apply mul_left_cancel₀ h_two_pi_ne
    calc
      (2 * Real.pi) * lengthInMeters setup.wavelengthLambda =
          2 * Real.pi * lengthInMeters setup.slitSeparationD *
            Real.sin (setup.screenRayAngle closestOffsetY) :=
        h_scaled
      _ =
          (2 * Real.pi) *
            (lengthInMeters setup.slitSeparationD *
              Real.sin (setup.screenRayAngle closestOffsetY)) := by
        ring
  have h_sin :
      Real.sin (setup.screenRayAngle closestOffsetY) =
        lengthInMeters setup.wavelengthLambda /
          lengthInMeters setup.slitSeparationD := by
    apply (eq_div_iff (ne_of_gt hd)).2
    calc
      Real.sin (setup.screenRayAngle closestOffsetY) *
          lengthInMeters setup.slitSeparationD =
        lengthInMeters setup.slitSeparationD *
          Real.sin (setup.screenRayAngle closestOffsetY) :=
        mul_comm _ _
      _ = lengthInMeters setup.wavelengthLambda := h_cancelled.symm
  have h_signed_meters :
      signedOffsetFromCentral LengthUnit.meters setup closestOffsetY =
        lengthInMeters setup.screenDistanceR *
            lengthInMeters setup.wavelengthLambda /
          lengthInMeters setup.slitSeparationD := by
    rw [h_laws.screenProjectionLaw, h_sin]
    ring
  have h_millimeters_eq (length : LengthQuantity) :
      lengthInMillimeters length = 1000 * lengthInMeters length := by
    unfold lengthInMillimeters lengthInMeters lengthReadout
    change
      (length
          {UnitChoices.SI with length := LengthUnit.millimeters}).val =
        1000 * (length UnitChoices.SI).val
    rw [length.property UnitChoices.SI
      {UnitChoices.SI with length := LengthUnit.millimeters}]
    norm_num [UnitChoices.dimScale, LengthUnit.millimeters,
      LengthUnit.meters, LengthUnit.scale, LengthUnit.div_eq_val]
    rfl
  have h_signed_millimeters :
      signedOffsetFromCentral LengthUnit.millimeters setup closestOffsetY =
        1000 *
          signedOffsetFromCentral LengthUnit.meters setup closestOffsetY := by
    change
      lengthInMillimeters closestOffsetY -
          lengthInMillimeters (setup.screenPointOffsetY .central) =
        1000 *
          (lengthInMeters closestOffsetY -
            lengthInMeters (setup.screenPointOffsetY .central))
    rw [h_millimeters_eq, h_millimeters_eq]
    ring
  rw [distanceFromCentralInMillimeters, abs_of_pos h_closest.1,
    h_signed_millimeters, h_signed_meters, h_millimeters_eq,
    h_millimeters_eq, h_millimeters_eq]
  field_simp

/--
The physical result is the symbolic distance `R lambda / d`.  The source
dataset additionally records that distance as `3.25 mm`, uniquely selecting
choice A.  This formalizes `thm:physics:phyx_mini_0120:target`.

The numerical conjunct is deliberately a conclusion, not a premise.  Since
the supplied source has no numerical readouts for `R`, `lambda`, or `d`, that
conjunct is underdetermined by the available data and remains a later proof or
source-redraft obligation.
-/
theorem problem_phyx_mini_0120
    (setup : ThreeSlitInterferenceSetup)
    (closestOffsetY : LengthQuantity)
    (h_physical : HasPhysicalParameters setup)
    (h_figure : MatchesThreeSlitFigure setup)
    (h_fields : SatisfiesMonochromaticFieldsAtP setup)
    (h_laws : SatisfiesParaxialThreeSlitInterferenceLaws setup)
    (h_closest :
      IsClosestPositiveAbsoluteMaximum setup closestOffsetY) :
    distanceFromCentralInMillimeters setup closestOffsetY =
        lengthInMillimeters setup.screenDistanceR *
          lengthInMillimeters setup.wavelengthLambda /
            lengthInMillimeters setup.slitSeparationD ∧
      distanceFromCentralInMillimeters setup closestOffsetY = 13 / 4 ∧
      IsUniqueMatchingDisplayedChoice setup closestOffsetY
        recordedDatasetAnswer := by
  refine
    ⟨closestAbsoluteMaximumDistance_formula setup closestOffsetY
        h_physical h_figure h_laws h_closest,
      ?_⟩
  have h_numeric :
      distanceFromCentralInMillimeters setup closestOffsetY = 13 / 4 := by
    calc
      distanceFromCentralInMillimeters setup closestOffsetY =
          lengthInMillimeters setup.screenDistanceR *
            lengthInMillimeters setup.wavelengthLambda /
              lengthInMillimeters setup.slitSeparationD :=
        closestAbsoluteMaximumDistance_formula setup closestOffsetY
          h_physical h_figure h_laws h_closest
      _ = 13 / 4 := by
        -- No premise supplies this numerical calibration of `R * lambda / d`.
        sorry
  refine ⟨h_numeric, ?_⟩
  unfold IsUniqueMatchingDisplayedChoice MatchesDisplayedDistanceChoice
  constructor
  · simpa [recordedDatasetAnswer, displayedDistanceMillimeters] using
      h_numeric
  · intro other h_other
    have h_value : displayedDistanceMillimeters other = 13 / 4 :=
      h_other.symm.trans h_numeric
    cases other with
    | A => rfl
    | B => norm_num [displayedDistanceMillimeters] at h_value
    | C => norm_num [displayedDistanceMillimeters] at h_value
    | D => norm_num [displayedDistanceMillimeters] at h_value

end PhyXMiniProblems.ProblemPhyXMini0120
