import Mathlib.Analysis.SpecialFunctions.Trigonometric.Angle
import Physlib.SpaceAndTime.Space.LengthUnit
import Physlib.Units.WithDim.Basic

noncomputable section

namespace PhyXMiniProblems.ProblemPhyXMini0750

open Dimension

/-!
# Airplane displacement from two radar observations

A radar dish observes an airplane first on the east side of the station and
later on the west side.  The two slant ranges are labelled `d₁` and `d₂`, and
the angle swept by the radar ray is labelled `Δθ`.  The airplane's
displacement is the third side of the resulting triangle.

Distances are unit-independent Physlib quantities.  Real numbers occur only
as coherent unit readouts, dimensionless trigonometric values, and displayed
answer values.  Angles use Mathlib's `Real.Angle`.

Assumption/target boundary:

* scenario and figure predicates identify the vertical east-west tracking
  plane, the two airplane positions, the radar dish, and the labels `d₁`,
  `d₂`, `θ₁`, and `Δθ`;
* the supplied data predicate records only `360 m`, `790 m`, `40 degrees`,
  and `123 degrees`;
* the governing law is the generic cosine rule for the radar triangle in
  every length unit;
* the numerical displacement and answer choice C occur only in conclusions.
-/

/-! ## Dimensionful distances and angle conversion -/

/-- A nonnegative physical distance, represented coherently in every unit. -/
abbrev LengthQuantity : Type := Dimensionful (WithDim L𝓭 NNReal)

/-- Read a physical distance in a selected length unit. -/
def lengthReadout (unit : LengthUnit) (distance : LengthQuantity) : ℝ :=
  ((distance {UnitChoices.SI with length := unit}).val : ℝ)

/-- Metre readout of a physical distance. -/
def lengthInMeters (distance : LengthQuantity) : ℝ :=
  lengthReadout LengthUnit.meters distance

/-- Convert a numerical degree readout to Mathlib's angle type. -/
def angleFromDegrees (degreeValue : ℝ) : Real.Angle :=
  ((degreeValue * Real.pi / 180 : ℝ) : Real.Angle)

/-! ## Physical roles and primary-figure labels -/

/-- The vertical plane in which the radar tracks the airplane. -/
inductive TrackingPlaneKind where
  | verticalEastWest
  deriving DecidableEq, Repr

/-- Side of the radar station on which an observed airplane position lies. -/
inductive HorizonSide where
  | east
  | west
  deriving DecidableEq, Fintype, Repr

/-- Direction of the airplane's motion shown by the figure's arrow. -/
inductive AirplaneTravelDirection where
  | eastToWest
  deriving DecidableEq, Repr

/-- Physical objects and geometric features visible in the supplied image. -/
inductive FigureObject where
  | airplaneAtInitialObservation
  | airplaneAtFinalObservation
  | radarDish
  | horizontalEastWestReference
  | ground
  deriving DecidableEq, Fintype, Repr

/-- Literal symbolic and compass labels visible in the supplied image. -/
inductive FigureLabel where
  | distanceD1
  | distanceD2
  | initialAngleTheta1
  | angularChangeDeltaTheta
  | east
  | west
  | airplane
  | radarDish
  deriving DecidableEq, Fintype, Repr

/-!
Structured transcription of image 750.  It stores the quantities denoted by
the four geometric labels and qualitative incidence information.  The image
contains no displacement-magnitude label and no numerical answer choice.
-/
structure SuppliedRadarFigure where
  showsObject : FigureObject → Bool
  showsLabel : FigureLabel → Bool
  distanceLabelD1 : LengthQuantity
  distanceLabelD2 : LengthQuantity
  angleLabelTheta1 : Real.Angle
  angleLabelDeltaTheta : Real.Angle
  initialRayPointsToEastSide : Bool
  finalRayPointsToWestSide : Bool
  theta1IsBetweenInitialRayAndHorizon : Bool
  deltaThetaIsBetweenObservationRays : Bool
  motionArrowPointsFromInitialToFinal : Bool
  containsDisplacementMagnitudeLabel : Bool

/-!
Independent physical quantities in the radar-tracking model.  In particular,
`displacementMagnitude` is not defined from an answer choice; it is related to
the two radar ranges by the governing triangle law below.
-/
structure RadarTrackingSetup where
  trackingPlane : TrackingPlaneKind
  initialSide : HorizonSide
  finalSide : HorizonSide
  travelDirection : AirplaneTravelDirection
  initialRadarDistanceD1 : LengthQuantity
  finalRadarDistanceD2 : LengthQuantity
  displacementMagnitude : LengthQuantity
  initialElevationAngleTheta1 : Real.Angle
  trackedAngularChangeDeltaTheta : Real.Angle
  figure : SuppliedRadarFigure

/-! ## Scenario, data, figure, and governing-law assumptions -/

/-- Qualitative geometry and direction stated by the problem. -/
structure MatchesRadarTrackingScenario (setup : RadarTrackingSetup) : Prop where
  trackedInVerticalEastWestPlane :
    setup.trackingPlane = .verticalEastWest
  airplaneInitiallyEastOfStation : setup.initialSide = .east
  airplaneFinallyWestOfStation : setup.finalSide = .west
  airplaneApproachesFromEastAndTravelsWest :
    setup.travelDirection = .eastToWest

/-!
Numerical readouts supplied by the prose.  This contains neither a value for
the displacement nor an answer-choice label.
-/
structure MatchesSuppliedRadarReadouts (setup : RadarTrackingSetup) : Prop where
  initialDistanceMeters :
    lengthInMeters setup.initialRadarDistanceD1 = 360
  finalDistanceMeters :
    lengthInMeters setup.finalRadarDistanceD2 = 790
  initialElevationFortyDegrees :
    setup.initialElevationAngleTheta1 = angleFromDegrees 40
  trackedChangeOneHundredTwentyThreeDegrees :
    setup.trackedAngularChangeDeltaTheta = angleFromDegrees 123

/-!
Objects, labels, and incidence relations read from the primary bitmap.  The
fields connect the figure's `d₁`, `d₂`, `θ₁`, and `Δθ` labels to the physical
setup without assigning the requested third-side length.
-/
structure MatchesSuppliedRadarFigure (setup : RadarTrackingSetup) : Prop where
  everyObjectShown : ∀ object, setup.figure.showsObject object = true
  everyLabelShown : ∀ label, setup.figure.showsLabel label = true
  d1LabelDenotesInitialRange :
    setup.figure.distanceLabelD1 = setup.initialRadarDistanceD1
  d2LabelDenotesFinalRange :
    setup.figure.distanceLabelD2 = setup.finalRadarDistanceD2
  theta1LabelDenotesInitialElevation :
    setup.figure.angleLabelTheta1 = setup.initialElevationAngleTheta1
  deltaThetaLabelDenotesTrackedChange :
    setup.figure.angleLabelDeltaTheta = setup.trackedAngularChangeDeltaTheta
  initialRayIsOnEastSide : setup.figure.initialRayPointsToEastSide = true
  finalRayIsOnWestSide : setup.figure.finalRayPointsToWestSide = true
  theta1IsMeasuredAboveHorizon :
    setup.figure.theta1IsBetweenInitialRayAndHorizon = true
  deltaThetaSpansTheTwoRadarRays :
    setup.figure.deltaThetaIsBetweenObservationRays = true
  arrowShowsMotionFromInitialToFinal :
    setup.figure.motionArrowPointsFromInitialToFinal = true
  figureDoesNotLabelRequestedMagnitude :
    setup.figure.containsDisplacementMagnitudeLabel = false

/-!
Positivity and angle-branch conditions selecting the geometry shown in the
image.  These conditions provide no numerical displacement.
-/
structure HasPhysicalRadarParameters (setup : RadarTrackingSetup) : Prop where
  initialDistancePositive :
    0 < lengthInMeters setup.initialRadarDistanceD1
  finalDistancePositive :
    0 < lengthInMeters setup.finalRadarDistanceD2
  displacementMagnitudePositive :
    0 < lengthInMeters setup.displacementMagnitude
  initialElevationIsAcute :
    setup.initialElevationAngleTheta1.toReal ∈ Set.Ioo 0 (Real.pi / 2)
  trackedChangeIsInteriorAngle :
    setup.trackedAngularChangeDeltaTheta.toReal ∈ Set.Ioo 0 Real.pi

/-!
The governing law for the triangle whose vertices are the radar station and
the airplane's two observed positions.  It is stated in every length unit and
is the dimensionful readout form of the cosine rule.  It does not specialize
the supplied numerical data or identify an answer choice.
-/
structure SatisfiesRadarTriangleCosineLaw
    (setup : RadarTrackingSetup) : Prop where
  cosineRule : ∀ unit : LengthUnit,
    lengthReadout unit setup.displacementMagnitude ^ 2 =
      lengthReadout unit setup.initialRadarDistanceD1 ^ 2 +
        lengthReadout unit setup.finalRadarDistanceD2 ^ 2 -
          2 * lengthReadout unit setup.initialRadarDistanceD1 *
            lengthReadout unit setup.finalRadarDistanceD2 *
              Real.Angle.cos setup.trackedAngularChangeDeltaTheta

/-! ## Derived displacement and displayed choices -/

/-- Labels of the four displayed displacement choices. -/
inductive AnswerChoice where
  | A
  | B
  | C
  | D
  deriving DecidableEq, Fintype, Repr

/-- Metre value printed beside each answer label. -/
def displayedDisplacementMeters : AnswerChoice → ℝ
  | .A => 936
  | .B => 965
  | .C => 1031
  | .D => 1261

/-- The answer label recorded in the supplied dataset. -/
def recordedDatasetAnswer : AnswerChoice := .C

/-!
A displacement matches an integer-metre answer when its metre readout rounds
to that integer, expressed by an error strictly below half a metre.
-/
def RoundsToDisplayedMeter
    (distance : LengthQuantity) (choice : AnswerChoice) : Prop :=
  |lengthInMeters distance - displayedDisplacementMeters choice| < 1 / 2

/-- A choice is the unique displayed nearest-metre match. -/
def IsUniqueNearestMeterAnswer
    (distance : LengthQuantity) (choice : AnswerChoice) : Prop :=
  RoundsToDisplayedMeter distance choice ∧
    ∀ other : AnswerChoice,
      RoundsToDisplayedMeter distance other → other = choice

/-!
Specializing the unit-generic cosine rule to metres and the supplied radar
readouts gives the exact squared displacement relation.  This is a derived
intermediate result, not a premise of the model.
-/
lemma displacementSquaredInMeters_eq_cosineRule
    (setup : RadarTrackingSetup)
    (_readouts : MatchesSuppliedRadarReadouts setup)
    (_triangleLaw : SatisfiesRadarTriangleCosineLaw setup) :
    lengthInMeters setup.displacementMagnitude ^ 2 =
      (360 : ℝ) ^ 2 + (790 : ℝ) ^ 2 -
        2 * 360 * 790 * Real.Angle.cos (angleFromDegrees 123) := by
  have h := _triangleLaw.cosineRule LengthUnit.meters
  change lengthInMeters setup.displacementMagnitude ^ 2 =
    lengthInMeters setup.initialRadarDistanceD1 ^ 2 +
    lengthInMeters setup.finalRadarDistanceD2 ^ 2 -
    2 * lengthInMeters setup.initialRadarDistanceD1 *
    lengthInMeters setup.finalRadarDistanceD2 *
    Real.Angle.cos setup.trackedAngularChangeDeltaTheta at h
  rw [_readouts.initialDistanceMeters, _readouts.finalDistanceMeters,
    _readouts.trackedChangeOneHundredTwentyThreeDegrees] at h
  exact h

/-!
The cosine rule gives a displacement of approximately `1031.2568 m`, whose
unique nearest-metre answer is `1031 m`, choice C.  The exact squared relation
is included alongside the multiple-choice conclusion to retain the physical
calculation rather than only its rounded presentation.

This formalizes blueprint label `thm:physics:phyx_mini_0750:target`.
-/
theorem airplaneDisplacement_matches_recordedAnswerC
    (setup : RadarTrackingSetup)
    (_scenario : MatchesRadarTrackingScenario setup)
    (_readouts : MatchesSuppliedRadarReadouts setup)
    (_figure : MatchesSuppliedRadarFigure setup)
    (_physical : HasPhysicalRadarParameters setup)
    (_triangleLaw : SatisfiesRadarTriangleCosineLaw setup) :
    lengthInMeters setup.displacementMagnitude ^ 2 =
        (360 : ℝ) ^ 2 + (790 : ℝ) ^ 2 -
          2 * 360 * 790 * Real.Angle.cos (angleFromDegrees 123) ∧
      IsUniqueNearestMeterAnswer
        setup.displacementMagnitude recordedDatasetAnswer := by
  have hSquared := displacementSquaredInMeters_eq_cosineRule
    setup _readouts _triangleLaw
  have hPiLower : (3 : ℝ) < Real.pi := by
    have hbound := Real.sin_bound (x := (1 / 2 : ℝ)) (by norm_num)
    have hsinlt : Real.sin (1 / 2 : ℝ) < 1 / 2 := by
      have hu := le_of_abs_le hbound
      norm_num at hu ⊢
      linarith
    by_contra hpi
    have hpi' : Real.pi ≤ 3 := le_of_not_gt hpi
    have hxy : Real.pi / 6 ≤ (1 / 2 : ℝ) := by
      linarith
    have hmono := Real.sin_le_sin_of_le_of_le_pi_div_two
      (x := Real.pi / 6) (y := (1 / 2 : ℝ))
      (by linarith [Real.pi_pos])
      (by linarith [Real.one_le_pi_div_two]) hxy
    rw [Real.sin_pi_div_six] at hmono
    linarith
  have hPiUpper : Real.pi < (63 / 20 : ℝ) := by
    have hSinSmall :
        (2592 / 10000 : ℝ) < Real.sin (21 / 80 : ℝ) := by
      have hbound := Real.sin_bound (x := (21 / 80 : ℝ)) (by norm_num)
      have hl := neg_le_of_abs_le hbound
      norm_num at hl ⊢
      linarith
    have hCosSmall :
        (96529 / 100000 : ℝ) < Real.cos (21 / 80 : ℝ) := by
      have hbound := Real.cos_bound (x := (21 / 80 : ℝ)) (by norm_num)
      have hl := neg_le_of_abs_le hbound
      norm_num at hl ⊢
      linarith
    have hProduct : (1 / 4 : ℝ) <
        Real.sin (21 / 80 : ℝ) * Real.cos (21 / 80 : ℝ) := by
      have h₁ := mul_pos (sub_pos.mpr hSinSmall)
        (lt_trans (by norm_num) hCosSmall)
      have h₂ := mul_pos (by norm_num : (0 : ℝ) < 2592 / 10000)
        (sub_pos.mpr hCosSmall)
      nlinarith
    have hsinlt : (1 / 2 : ℝ) < Real.sin (21 / 40 : ℝ) := by
      rw [show (21 / 40 : ℝ) = 2 * (21 / 80 : ℝ) by norm_num,
        Real.sin_two_mul]
      nlinarith
    by_contra hpi
    have hpi' : (63 / 20 : ℝ) ≤ Real.pi := le_of_not_gt hpi
    have hxy : (21 / 40 : ℝ) ≤ Real.pi / 6 := by
      linarith
    have hmono := Real.sin_le_sin_of_le_of_le_pi_div_two
      (x := (21 / 40 : ℝ)) (y := Real.pi / 6)
      (by linarith [Real.one_le_pi_div_two])
      (by linarith [Real.pi_pos]) hxy
    rw [Real.sin_pi_div_six] at hmono
    linarith
  let δ : ℝ := Real.pi / 60
  have hδpos : 0 < δ := by
    dsimp [δ]
    positivity
  have hδLower : (1 / 20 : ℝ) < δ := by
    dsimp [δ]
    linarith
  have hδUpper : δ < (21 / 400 : ℝ) := by
    dsimp [δ]
    linarith
  have hδLe : δ ≤ (1 / 15 : ℝ) := by
    dsimp [δ]
    linarith [Real.pi_le_four]
  have hδnonneg : 0 ≤ δ := hδpos.le
  have hδsq : δ ^ 2 ≤ (1 / 15 : ℝ) ^ 2 :=
    pow_le_pow_left₀ hδnonneg hδLe 2
  have hδcube : δ ^ 3 ≤ (1 / 15 : ℝ) ^ 3 :=
    pow_le_pow_left₀ hδnonneg hδLe 3
  have hδfour : δ ^ 4 ≤ (1 / 15 : ℝ) ^ 4 :=
    pow_le_pow_left₀ hδnonneg hδLe 4
  have hδAbsLeOne : |δ| ≤ (1 : ℝ) := by
    rw [abs_of_pos hδpos]
    linarith
  have hSinBound := Real.sin_bound (x := δ) hδAbsLeOne
  have hSinLower : (499 / 10000 : ℝ) < Real.sin δ := by
    have hl := neg_le_of_abs_le hSinBound
    rw [abs_of_pos hδpos] at hl
    nlinarith
  have hSinUpper : Real.sin δ < (5251 / 100000 : ℝ) := by
    have hu := le_of_abs_le hSinBound
    rw [abs_of_pos hδpos] at hu
    nlinarith
  have hCosBound := Real.cos_bound (x := δ) hδAbsLeOne
  have hCosLower : (9977 / 10000 : ℝ) < Real.cos δ := by
    have hl := neg_le_of_abs_le hCosBound
    rw [abs_of_pos hδpos] at hl
    nlinarith
  have hCosUpper : Real.cos δ ≤ 1 := Real.cos_le_one δ
  have hSqrtSq : Real.sqrt 3 ^ 2 = (3 : ℝ) :=
    Real.sq_sqrt (by norm_num)
  have hSqrtPos : 0 < Real.sqrt 3 :=
    Real.sqrt_pos.2 (by norm_num)
  have hSqrtLower : (433 / 250 : ℝ) < Real.sqrt 3 := by
    nlinarith
  have hSqrtUpper : Real.sqrt 3 < (17321 / 10000 : ℝ) := by
    nlinarith
  have hSinPos : 0 < Real.sin δ :=
    lt_trans (by norm_num) hSinLower
  have hProductLower :
      (433 / 250 : ℝ) * (499 / 10000 : ℝ) <
        Real.sqrt 3 * Real.sin δ := by
    have h₁ := mul_pos (sub_pos.mpr hSqrtLower) hSinPos
    have h₂ := mul_pos (by norm_num : (0 : ℝ) < 433 / 250)
      (sub_pos.mpr hSinLower)
    nlinarith
  have hProductUpper :
      Real.sqrt 3 * Real.sin δ <
        (17321 / 10000 : ℝ) * (5251 / 100000 : ℝ) := by
    have h₁ := mul_pos (sub_pos.mpr hSqrtUpper) hSinPos
    have h₂ := mul_pos (by norm_num : (0 : ℝ) < 17321 / 10000)
      (sub_pos.mpr hSinUpper)
    nlinarith
  have hCosIdentity :
      Real.cos ((123 : ℝ) * Real.pi / 180) =
        -(1 / 2 : ℝ) * Real.cos δ -
          (Real.sqrt 3 / 2) * Real.sin δ := by
    rw [show (123 : ℝ) * Real.pi / 180 =
      (Real.pi - Real.pi / 3) + δ by
        dsimp [δ]
        ring,
      Real.cos_add, Real.cos_pi_sub, Real.sin_pi_sub,
      Real.cos_pi_div_three, Real.sin_pi_div_three]
  have hCosBounds :
      (-1091 / 2000 : ℝ) <
          Real.Angle.cos (angleFromDegrees 123) ∧
        Real.Angle.cos (angleFromDegrees 123) <
          (-542 / 1000 : ℝ) := by
    rw [angleFromDegrees, Real.Angle.cos_coe, hCosIdentity]
    constructor <;> nlinarith
  have hSqLower :
      (2061 / 2 : ℝ) ^ 2 <
        lengthInMeters setup.displacementMagnitude ^ 2 := by
    rw [hSquared]
    nlinarith only [hCosBounds.2]
  have hSqUpper :
      lengthInMeters setup.displacementMagnitude ^ 2 <
        (2063 / 2 : ℝ) ^ 2 := by
    rw [hSquared]
    nlinarith only [hCosBounds.1]
  have hDistanceLower :
      (2061 / 2 : ℝ) <
        lengthInMeters setup.displacementMagnitude := by
    exact (sq_lt_sq₀ (by norm_num)
      _physical.displacementMagnitudePositive.le).mp hSqLower
  have hDistanceUpper :
      lengthInMeters setup.displacementMagnitude <
        (2063 / 2 : ℝ) := by
    exact (sq_lt_sq₀ _physical.displacementMagnitudePositive.le
      (by norm_num)).mp hSqUpper
  constructor
  · exact hSquared
  · constructor
    · rw [RoundsToDisplayedMeter, recordedDatasetAnswer,
        displayedDisplacementMeters, abs_lt]
      constructor <;>
        linarith only [hDistanceLower, hDistanceUpper]
    · intro other hother
      cases other with
      | A =>
          exfalso
          change
            |lengthInMeters setup.displacementMagnitude - 936| < 1 / 2
            at hother
          rw [abs_lt] at hother
          linarith only [hDistanceLower, hother.2]
      | B =>
          exfalso
          change
            |lengthInMeters setup.displacementMagnitude - 965| < 1 / 2
            at hother
          rw [abs_lt] at hother
          linarith only [hDistanceLower, hother.2]
      | C => rfl
      | D =>
          exfalso
          change
            |lengthInMeters setup.displacementMagnitude - 1261| < 1 / 2
            at hother
          rw [abs_lt] at hother
          linarith only [hDistanceUpper, hother.1]

end PhyXMiniProblems.ProblemPhyXMini0750
