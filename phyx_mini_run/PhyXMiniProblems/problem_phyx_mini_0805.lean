import Mathlib
import Physlib.Units.WithDim.Basic

noncomputable section

namespace PhyXMiniProblems.ProblemPhyXMini0805

open Dimension

/-!
# Tension in an ideal air-track glider and hanging-mass system

The primary raster shows a glider labelled `m₁` on a horizontal air track.  A
single string runs horizontally from the glider, over a fixed pulley, and
vertically down to a hanging laboratory mass labelled `m₂`.  The prose states
that the track and pulley are frictionless and that the string is light,
flexible, and nonstretching.

Masses, acceleration magnitudes, and tension magnitudes are represented by
unit-independent Physlib quantities.  Real numbers occur only as coherent-unit
readouts and in the symbolic scalar formulas printed as answer choices.
-/

/-! ## Dimensionful physical quantities and coherent-unit readouts -/

/-- The physical dimension `L T⁻²` of an acceleration magnitude. -/
def accelerationDimension : Dimension :=
  L𝓭 * T𝓭⁻¹ * T𝓭⁻¹

/-- The physical dimension `M L T⁻²` of a force magnitude. -/
def forceDimension : Dimension :=
  M𝓭 * L𝓭 * T𝓭⁻¹ * T𝓭⁻¹

/-- A nonnegative, unit-independent physical mass. -/
abbrev MassQuantity : Type :=
  Dimensionful (WithDim M𝓭 NNReal)

/-- A nonnegative, unit-independent physical acceleration magnitude. -/
abbrev AccelerationQuantity : Type :=
  Dimensionful (WithDim accelerationDimension NNReal)

/-- A nonnegative, unit-independent force magnitude, used for string tension. -/
abbrev TensionQuantity : Type :=
  Dimensionful (WithDim forceDimension NNReal)

/-- Read a mass in the mass unit selected by a coherent unit system. -/
def massReadout (units : UnitChoices) (mass : MassQuantity) : ℝ :=
  ((mass units).val : ℝ)

/-- Read an acceleration in the coherent unit selected by a unit system. -/
def accelerationReadout
    (units : UnitChoices) (acceleration : AccelerationQuantity) : ℝ :=
  ((acceleration units).val : ℝ)

/-- Read a tension in the coherent force unit selected by a unit system. -/
def tensionReadout (units : UnitChoices) (tension : TensionQuantity) : ℝ :=
  ((tension units).val : ℝ)

/-- Kilogram readout of a physical mass. -/
def massInKilograms (mass : MassQuantity) : ℝ :=
  massReadout UnitChoices.SI mass

/-- Metres-per-second-squared readout of an acceleration magnitude. -/
def accelerationInMetersPerSecondSquared
    (acceleration : AccelerationQuantity) : ℝ :=
  accelerationReadout UnitChoices.SI acceleration

/-- Newton readout of a string-tension magnitude. -/
def tensionInNewtons (tension : TensionQuantity) : ℝ :=
  tensionReadout UnitChoices.SI tension

/-! ## Apparatus and primary-figure vocabulary -/

/-- The two bodies labelled in the problem and the supplied raster. -/
inductive BodyLabel where
  | m1Glider
  | m2HangingMass
  deriving DecidableEq, Fintype, Repr

/-- The two straight portions of the pictured string. -/
inductive StringSegment where
  | horizontal
  | vertical
  deriving DecidableEq, Fintype, Repr

/-- Individually recognizable objects visible in the primary raster. -/
inductive FigureObject where
  | airTrack
  | glider
  | horizontalString
  | fixedPulley
  | verticalString
  | hangingLabWeight
  deriving DecidableEq, Fintype, Repr

/-- Literal symbolic mass labels visible in the primary raster. -/
inductive FigureTextLabel where
  | m1
  | m2
  deriving DecidableEq, Fintype, Repr

/-- Locations of the two labelled bodies in the apparatus. -/
inductive BodyLocation where
  | onHorizontalTrack
  | hangingBelowPulley
  deriving DecidableEq, Repr

/-- Geometric orientation of a straight string segment. -/
inductive SegmentOrientation where
  | horizontal
  | vertical
  deriving DecidableEq, Repr

/-- The complete route of the single string shown in the figure. -/
inductive StringRoute where
  | fromGliderAcrossTrackOverFixedPulleyToHangingMass
  deriving DecidableEq, Repr

/-- Orientation of the air track stated in the problem. -/
inductive TrackOrientation where
  | level
  | inclined
  deriving DecidableEq, Repr

/-- Resistance model for glider motion along the track. -/
inductive TrackResistanceModel where
  | frictionless
  | resistive
  deriving DecidableEq, Repr

/-- Mass idealization for the connecting string. -/
inductive StringMassModel where
  | light
  | massive
  deriving DecidableEq, Repr

/-- Flexibility idealization for the connecting string. -/
inductive StringFlexibilityModel where
  | flexible
  | rigid
  deriving DecidableEq, Repr

/-- Extensibility idealization for the connecting string. -/
inductive StringExtensibilityModel where
  | nonstretching
  | extensible
  deriving DecidableEq, Repr

/-- Motion state of the pulley support. -/
inductive PulleyMotionModel where
  | stationary
  | moving
  deriving DecidableEq, Repr

/-- Axle/contact resistance model for the pulley. -/
inductive PulleyResistanceModel where
  | frictionless
  | resistive
  deriving DecidableEq, Repr

/-- Positive coordinate direction used in each body's scalar force equation. -/
inductive PositiveAxisDirection where
  | alongTrackTowardPulley
  | verticallyDownward
  deriving DecidableEq, Repr

/-!
Typed transcription of image `805.png`.  It records the horizontal air-track
geometry actually visible in the raster; the auxiliary generated caption's
claim that the track is inclined is deliberately not encoded.
-/
structure SuppliedAirTrackFigure where
  showsObject : FigureObject → Bool
  showsTextLabel : FigureTextLabel → Bool
  bodyLocation : BodyLabel → BodyLocation
  segmentOrientation : StringSegment → SegmentOrientation
  stringRoute : StringRoute
  trackDrawnLevel : Bool
  pulleyAttachedToTrackFrame : Bool

/-!
Independent physical quantities and apparatus properties.  The tension and
accelerations are fields, rather than definitions manufactured from the
recorded answer formula.
-/
structure AirTrackPulleySetup where
  bodyMass : BodyLabel → MassQuantity
  bodyAccelerationMagnitude : BodyLabel → AccelerationQuantity
  segmentTension : StringSegment → TensionQuantity
  gravitationalAcceleration : AccelerationQuantity
  trackOrientation : TrackOrientation
  trackResistance : TrackResistanceModel
  stringMassModel : StringMassModel
  stringFlexibility : StringFlexibilityModel
  stringExtensibility : StringExtensibilityModel
  pulleyMotion : PulleyMotionModel
  pulleyResistance : PulleyResistanceModel
  positiveAxis : BodyLabel → PositiveAxisDirection
  gliderIsMoving : Prop
  figure : SuppliedAirTrackFigure

/-! ## Scenario assumptions, image facts, and governing laws -/

/-- Qualitative idealizations stated in the problem prose. -/
structure MatchesWrittenScenario (setup : AirTrackPulleySetup) : Prop where
  gliderMoves : setup.gliderIsMoving
  trackIsLevel : setup.trackOrientation = .level
  trackIsFrictionless : setup.trackResistance = .frictionless
  stringIsLight : setup.stringMassModel = .light
  stringIsFlexible : setup.stringFlexibility = .flexible
  stringIsNonstretching : setup.stringExtensibility = .nonstretching
  pulleyIsStationary : setup.pulleyMotion = .stationary
  pulleyIsFrictionless : setup.pulleyResistance = .frictionless
  gliderPositiveAxis :
    setup.positiveAxis .m1Glider = .alongTrackTowardPulley
  hangingMassPositiveAxis :
    setup.positiveAxis .m2HangingMass = .verticallyDownward

/-- Geometry and symbolic labels read directly from the primary raster. -/
structure MatchesSuppliedFigure (setup : AirTrackPulleySetup) : Prop where
  everyObjectShown : ∀ object, setup.figure.showsObject object = true
  everyMassLabelShown : ∀ label, setup.figure.showsTextLabel label = true
  gliderLocation :
    setup.figure.bodyLocation .m1Glider = .onHorizontalTrack
  hangingMassLocation :
    setup.figure.bodyLocation .m2HangingMass = .hangingBelowPulley
  horizontalSegmentOrientation :
    setup.figure.segmentOrientation .horizontal = .horizontal
  verticalSegmentOrientation :
    setup.figure.segmentOrientation .vertical = .vertical
  routeReadout :
    setup.figure.stringRoute =
      .fromGliderAcrossTrackOverFixedPulleyToHangingMass
  trackIsDrawnLevel : setup.figure.trackDrawnLevel = true
  pulleyIsFrameMounted : setup.figure.pulleyAttachedToTrackFrame = true

/-- Positivity assumptions selecting the nondegenerate physical regime. -/
structure HasPositivePhysicalParameters (setup : AirTrackPulleySetup) : Prop where
  everyBodyMassPositive :
    ∀ body, 0 < massInKilograms (setup.bodyMass body)
  gravityPositive :
    0 < accelerationInMetersPerSecondSquared
      setup.gravitationalAcceleration

/-!
The governing ideal-string, ideal-pulley, and Newton-law relations.  The first
two laws express the constraints supplied by a single light nonstretching
string over a frictionless fixed pulley.  The final two equations are Newton's
second law along the chosen positive axes: `T = m₁ a₁` for the frictionless
glider and `m₂ g - T = m₂ a₂` for the descending hanging mass.

These are generic relations in every coherent unit system.  None contains the
solved tension formula asked for in the current question.
-/
structure SatisfiesIdealAirTrackPulleyLaws
    (setup : AirTrackPulleySetup) : Prop where
  nonstretchingStringAccelerationConstraint :
    ∀ units,
      accelerationReadout units
          (setup.bodyAccelerationMagnitude .m1Glider) =
        accelerationReadout units
          (setup.bodyAccelerationMagnitude .m2HangingMass)
  lightStringAndIdealPulleyTransmitTension :
    ∀ units,
      tensionReadout units (setup.segmentTension .horizontal) =
        tensionReadout units (setup.segmentTension .vertical)
  gliderNewtonSecondLaw :
    ∀ units,
      tensionReadout units (setup.segmentTension .horizontal) =
        massReadout units (setup.bodyMass .m1Glider) *
          accelerationReadout units
            (setup.bodyAccelerationMagnitude .m1Glider)
  hangingMassNewtonSecondLaw :
    ∀ units,
      massReadout units (setup.bodyMass .m2HangingMass) *
            accelerationReadout units setup.gravitationalAcceleration -
          tensionReadout units (setup.segmentTension .vertical) =
        massReadout units (setup.bodyMass .m2HangingMass) *
          accelerationReadout units
            (setup.bodyAccelerationMagnitude .m2HangingMass)

/-! ## Printed answer choices and current target -/

/-- Labels of the four symbolic alternatives printed with the problem. -/
inductive AnswerChoice where
  | A
  | B
  | C
  | D
  deriving DecidableEq, Fintype, Repr

/--
Scalar tension formula printed beside an answer label, evaluated from coherent
readouts `m₁`, `m₂`, and `g`.
-/
def AnswerChoice.displayedTension
    (choice : AnswerChoice) (m1 m2 g : ℝ) : ℝ :=
  match choice with
  | .A => (2 * m1 * m2) / (m1 + m2) * g
  | .B => (m1 * m2) / (m1 + m2) * g
  | .C => (m1 * m2) / (2 * m1 + m2) * g
  | .D => (m1 * m2) / (m1 + 2 * m2) * g

/-- Dataset answer metadata, deliberately not used as a theorem premise. -/
def recordedDatasetAnswer : AnswerChoice := .B

/-- Every segment tension agrees with the formula printed for a choice. -/
def MatchesAnswerChoice
    (setup : AirTrackPulleySetup) (choice : AnswerChoice) : Prop :=
  ∀ segment,
    tensionInNewtons (setup.segmentTension segment) =
      choice.displayedTension
        (massInKilograms (setup.bodyMass .m1Glider))
        (massInKilograms (setup.bodyMass .m2HangingMass))
        (accelerationInMetersPerSecondSquared
          setup.gravitationalAcceleration)

/-- A choice is the unique printed formula agreeing with the string tension. -/
def IsUniqueMatchingAnswer
    (setup : AirTrackPulleySetup) (choice : AnswerChoice) : Prop :=
  MatchesAnswerChoice setup choice ∧
    ∀ other : AnswerChoice,
      MatchesAnswerChoice setup other → other = choice

/-!
Solving the two Newton-law equations using the common acceleration and common
tension constraints gives

`T = (m₁ m₂ / (m₁ + m₂)) g`

on both string segments.  Among the displayed alternatives this is uniquely
choice B.

This formalizes `thm:physics:phyx_mini_0805:target`.
-/
theorem problem_phyx_mini_0805
    (setup : AirTrackPulleySetup)
    (hScenario : MatchesWrittenScenario setup)
    (hFigure : MatchesSuppliedFigure setup)
    (hPhysical : HasPositivePhysicalParameters setup)
    (hLaws : SatisfiesIdealAirTrackPulleyLaws setup) :
    (∀ segment,
      tensionInNewtons (setup.segmentTension segment) =
        (massInKilograms (setup.bodyMass .m1Glider) *
            massInKilograms (setup.bodyMass .m2HangingMass)) /
          (massInKilograms (setup.bodyMass .m1Glider) +
            massInKilograms (setup.bodyMass .m2HangingMass)) *
          accelerationInMetersPerSecondSquared
            setup.gravitationalAcceleration) ∧
      IsUniqueMatchingAnswer setup recordedDatasetAnswer := by
  let m1 : ℝ := massInKilograms (setup.bodyMass .m1Glider)
  let m2 : ℝ := massInKilograms (setup.bodyMass .m2HangingMass)
  let g : ℝ :=
    accelerationInMetersPerSecondSquared setup.gravitationalAcceleration
  let tH : ℝ := tensionInNewtons (setup.segmentTension .horizontal)
  let tV : ℝ := tensionInNewtons (setup.segmentTension .vertical)
  let a1 : ℝ :=
    accelerationInMetersPerSecondSquared
      (setup.bodyAccelerationMagnitude .m1Glider)
  let a2 : ℝ :=
    accelerationInMetersPerSecondSquared
      (setup.bodyAccelerationMagnitude .m2HangingMass)
  have hm1 : 0 < m1 := by
    simpa [m1] using hPhysical.everyBodyMassPositive .m1Glider
  have hm2 : 0 < m2 := by
    simpa [m2] using hPhysical.everyBodyMassPositive .m2HangingMass
  have hg : 0 < g := by
    simpa [g] using hPhysical.gravityPositive
  have ha : a1 = a2 := by
    simpa [a1, a2, accelerationInMetersPerSecondSquared] using
      hLaws.nonstretchingStringAccelerationConstraint UnitChoices.SI
  have ht : tH = tV := by
    simpa [tH, tV, tensionInNewtons] using
      hLaws.lightStringAndIdealPulleyTransmitTension UnitChoices.SI
  have hglider : tH = m1 * a1 := by
    simpa [tH, m1, a1, tensionInNewtons, massInKilograms,
      accelerationInMetersPerSecondSquared] using
        hLaws.gliderNewtonSecondLaw UnitChoices.SI
  have hhanging : m2 * g - tV = m2 * a2 := by
    simpa [m2, g, tV, a2, massInKilograms,
      accelerationInMetersPerSecondSquared, tensionInNewtons] using
        hLaws.hangingMassNewtonSecondLaw UnitChoices.SI
  rw [← ht, ← ha] at hhanging
  have hsum_pos : 0 < m1 + m2 := add_pos hm1 hm2
  have hsum_ne : m1 + m2 ≠ 0 := ne_of_gt hsum_pos
  have hbalance : (m1 + m2) * tH = m1 * m2 * g := by
    linear_combination -m1 * hhanging + m2 * hglider
  have htH : tH = (m1 * m2) / (m1 + m2) * g := by
    field_simp [hsum_ne]
    nlinarith [hbalance]
  have hFormula : ∀ segment,
      tensionInNewtons (setup.segmentTension segment) =
        (massInKilograms (setup.bodyMass .m1Glider) *
            massInKilograms (setup.bodyMass .m2HangingMass)) /
          (massInKilograms (setup.bodyMass .m1Glider) +
            massInKilograms (setup.bodyMass .m2HangingMass)) *
          accelerationInMetersPerSecondSquared
            setup.gravitationalAcceleration := by
    intro segment
    cases segment with
    | horizontal => simpa [tH, m1, m2, g] using htH
    | vertical =>
        have htV : tV = (m1 * m2) / (m1 + m2) * g :=
          ht.symm.trans htH
        simpa [tV, m1, m2, g] using htV
  refine ⟨hFormula, ?_⟩
  unfold IsUniqueMatchingAnswer
  constructor
  · simpa [MatchesAnswerChoice, recordedDatasetAnswer,
      AnswerChoice.displayedTension] using hFormula
  · change ∀ other, MatchesAnswerChoice setup other → other = .B
    intro other hOther
    cases other with
    | A =>
        exfalso
        have hA := hOther .horizontal
        have hB := hFormula .horizontal
        simp only [AnswerChoice.displayedTension] at hA
        change tensionInNewtons (setup.segmentTension .horizontal) =
          (2 * m1 * m2) / (m1 + m2) * g at hA
        change tensionInNewtons (setup.segmentTension .horizontal) =
          (m1 * m2) / (m1 + m2) * g at hB
        have hEq : (m1 * m2) / (m1 + m2) * g =
            (2 * m1 * m2) / (m1 + m2) * g :=
          hB.symm.trans hA
        field_simp [hsum_ne] at hEq
        have hprod : 0 < m1 * m2 * g := by positivity
        nlinarith [hEq, hprod]
    | B => rfl
    | C =>
        exfalso
        have hC := hOther .horizontal
        have hB := hFormula .horizontal
        simp only [AnswerChoice.displayedTension] at hC
        change tensionInNewtons (setup.segmentTension .horizontal) =
          (m1 * m2) / (2 * m1 + m2) * g at hC
        change tensionInNewtons (setup.segmentTension .horizontal) =
          (m1 * m2) / (m1 + m2) * g at hB
        have hEq : (m1 * m2) / (m1 + m2) * g =
            (m1 * m2) / (2 * m1 + m2) * g :=
          hB.symm.trans hC
        have hdenomC : 2 * m1 + m2 ≠ 0 :=
          ne_of_gt (by positivity)
        field_simp [hsum_ne, hdenomC] at hEq
        have hprod : 0 < m1 * m1 * m2 * g := by positivity
        nlinarith [hEq, hprod]
    | D =>
        exfalso
        have hD := hOther .horizontal
        have hB := hFormula .horizontal
        simp only [AnswerChoice.displayedTension] at hD
        change tensionInNewtons (setup.segmentTension .horizontal) =
          (m1 * m2) / (m1 + 2 * m2) * g at hD
        change tensionInNewtons (setup.segmentTension .horizontal) =
          (m1 * m2) / (m1 + m2) * g at hB
        have hEq : (m1 * m2) / (m1 + m2) * g =
            (m1 * m2) / (m1 + 2 * m2) * g :=
          hB.symm.trans hD
        have hdenomD : m1 + 2 * m2 ≠ 0 :=
          ne_of_gt (by positivity)
        field_simp [hsum_ne, hdenomD] at hEq
        have hprod : 0 < m1 * m2 * m2 * g := by positivity
        nlinarith [hEq, hprod]

end PhyXMiniProblems.ProblemPhyXMini0805
