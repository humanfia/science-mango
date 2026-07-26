import Mathlib
import Physlib.Units.WithDim.Basic

/- USER: The assigned source file did not exist when this autoformalization task began. -/

noncomputable section

namespace PhyXMiniProblems.ProblemPhyXMini0799

open Dimension

/-!
# Normal force on a car secured to a trailer ramp

A car of weight `w` rests on a trailer ramp inclined by `alpha` above the
horizontal. Its brakes are off and its transmission is in neutral. A cable
parallel to the ramp supplies the only tangential restraint. The primary
figure shows the weight `w` vertically downward, the cable tension `T` uphill
along the ramp, and the tire contact force `n` perpendicular to the ramp.

The three forces are independent, unit-independent Physlib quantities in the
vertical cross-section. Real scalars occur only as coherent-unit vector and
magnitude readouts, the dimensionless angle in radians, and the symbolic
multiple-choice expressions.

Assumption/target split:

* governing laws: each force has the direction shown in the free-body diagram,
  and the three external force vectors sum to zero in static equilibrium;
* previous-part results: none;
* figure/data readouts: the car and ramp geometry, the labels `w`, `T`, `n`,
  and `alpha`, the cable parallel to the ramp, and the normal and vertical
  arrow directions transcribed from image `799.png`;
* current target conclusion: the ramp-normal magnitude is
  `w * cos alpha`, which is displayed answer B.
-/

/-! ## Dimensionful force vectors and coherent-unit readouts -/

/-- The physical dimension `M L T^-2` of force. -/
def forceDimension : Dimension :=
  M𝓭 * L𝓭 * T𝓭⁻¹ * T𝓭⁻¹

/-- The oriented vertical cross-section: `x` points right and `y` points up. -/
abbrev PlanarVector : Type := EuclideanSpace ℝ (Fin 2)

/-- A unit-independent physical force vector in the ramp cross-section. -/
abbrev PlanarForceQuantity : Type :=
  Dimensionful (WithDim forceDimension PlanarVector)

/-- Read a planar force vector in a chosen coherent system of units. -/
def forceVectorReadout
    (units : UnitChoices) (force : PlanarForceQuantity) : PlanarVector :=
  (force units).val

/-- Read the magnitude of a planar force in a chosen coherent unit system. -/
def forceMagnitudeReadout
    (units : UnitChoices) (force : PlanarForceQuantity) : ℝ :=
  ‖forceVectorReadout units force‖

/-- SI force-vector readout, whose components are numerical newton values. -/
def forceVectorInNewtons (force : PlanarForceQuantity) : PlanarVector :=
  forceVectorReadout UnitChoices.SI force

/-- SI magnitude readout of a physical force, numerically in newtons. -/
def forceMagnitudeInNewtons (force : PlanarForceQuantity) : ℝ :=
  forceMagnitudeReadout UnitChoices.SI force

/-! ## Ramp geometry, physical roles, and primary-figure vocabulary -/

/-- Unit direction of vertical downward weight in the page coordinates. -/
def verticalDownUnitDirection : PlanarVector :=
  !₂[0, -1]

/-- Uphill ramp-tangent unit direction for an angle measured from horizontal. -/
def uphillRampUnitDirection (angleRadians : ℝ) : PlanarVector :=
  !₂[Real.cos angleRadians, Real.sin angleRadians]

/-- Outward ramp-normal unit direction for an angle measured from horizontal. -/
def outwardRampNormalUnitDirection (angleRadians : ℝ) : PlanarVector :=
  !₂[-Real.sin angleRadians, Real.cos angleRadians]

/-- The three force arrows named in the supplied free-body diagram. -/
inductive ForceLabel where
  | weightW
  | cableTensionT
  | rampNormalN
  deriving DecidableEq, Fintype, Repr

/-- Motion state of the car relative to the trailer ramp. -/
inductive CarMotionState where
  | atRestOnRamp
  | movingAlongRamp
  deriving DecidableEq, Repr

/-- State of the car's service and parking brakes. -/
inductive BrakeState where
  | off
  | engaged
  deriving DecidableEq, Repr

/-- Transmission state relevant to drivetrain restraint. -/
inductive TransmissionState where
  | neutral
  | engaged
  deriving DecidableEq, Repr

/-- Idealization of the resultant force at the tire--ramp contact. -/
inductive TireRampContactModel where
  | normalReactionOnly
  | includesTangentialContactForce
  deriving DecidableEq, Repr

/-- How the cable participates in preventing downhill rolling. -/
inductive TangentialRestraint where
  | cableOnly
  | cableAndOtherRestraints
  deriving DecidableEq, Repr

/-- Physical objects visibly distinguished in image `799.png`. -/
inductive FigureObject where
  | car
  | inclinedRamp
  | trailer
  | cable
  | tires
  deriving DecidableEq, Fintype, Repr

/-- Literal symbolic labels visible in the primary image. -/
inductive FigureLabel where
  | weightW
  | cableTensionT
  | rampNormalN
  | inclineAngleAlpha
  deriving DecidableEq, Fintype, Repr

/-- Qualitative arrow directions shown in the supplied figure. -/
inductive FigureArrowDirection where
  | verticalDown
  | uphillParallelToRamp
  | normalAwayFromRamp
  deriving DecidableEq, Repr

/-!
Typed evidence transcribed from the supplied raster. The picture displays
all three symbolic force arrows and the angle `alpha`, but no numerical force
magnitude and no solved expression for `n`.
-/
structure SuppliedCarRampFigure where
  showsObject : FigureObject → Bool
  showsLabel : FigureLabel → Bool
  showsForceArrow : ForceLabel → Bool
  arrowDirection : ForceLabel → FigureArrowDirection
  rampRisesToRight : Bool
  carTiresContactRamp : Bool
  cableConnectsTrailerToCar : Bool
  alphaIsAngleBetweenRampAndHorizontal : Bool
  containsNumericalForceMagnitude : Bool
  containsSolvedNormalForceFormula : Bool

/-!
Independent physical state and observables. In particular,
`force .rampNormalN` is not defined from the weight, angle, or answer choice;
its value is constrained only through force directions and static equilibrium.
-/
structure CarOnTrailerRampSetup where
  motionState : CarMotionState
  brakeState : BrakeState
  transmissionState : TransmissionState
  contactModel : TireRampContactModel
  tangentialRestraint : TangentialRestraint
  rampAngleRadians : ℝ
  force : ForceLabel → PlanarForceQuantity
  figure : SuppliedCarRampFigure

/-! ## Scenario assumptions, figure evidence, and physical admissibility -/

/-- Qualitative assignments stated in the prose. -/
structure MatchesCarOnTrailerRampScenario
    (setup : CarOnTrailerRampSetup) : Prop where
  carIsAtRest : setup.motionState = .atRestOnRamp
  brakesAreOff : setup.brakeState = .off
  transmissionIsNeutral : setup.transmissionState = .neutral
  cableIsOnlyTangentialRestraint :
    setup.tangentialRestraint = .cableOnly
  tireContactIsNormalReactionOnly :
    setup.contactModel = .normalReactionOnly

/-- Objects, labels, incidences, and arrow directions read from the image. -/
structure MatchesSuppliedCarRampFigure
    (setup : CarOnTrailerRampSetup) : Prop where
  everyObjectShown :
    ∀ object : FigureObject, setup.figure.showsObject object = true
  everyLabelShown :
    ∀ label : FigureLabel, setup.figure.showsLabel label = true
  everyForceArrowShown :
    ∀ force : ForceLabel, setup.figure.showsForceArrow force = true
  weightArrowVerticalDown :
    setup.figure.arrowDirection .weightW = .verticalDown
  tensionArrowUphillAlongRamp :
    setup.figure.arrowDirection .cableTensionT = .uphillParallelToRamp
  normalArrowPerpendicularToRamp :
    setup.figure.arrowDirection .rampNormalN = .normalAwayFromRamp
  rampAscendingRight : setup.figure.rampRisesToRight = true
  carSupportedAtTires : setup.figure.carTiresContactRamp = true
  cableRunsFromTrailerToCar :
    setup.figure.cableConnectsTrailerToCar = true
  alphaMeasuresInclineFromHorizontal :
    setup.figure.alphaIsAngleBetweenRampAndHorizontal = true
  noNumericalForceMagnitude :
    setup.figure.containsNumericalForceMagnitude = false
  noSolvedNormalFormula :
    setup.figure.containsSolvedNormalForceFormula = false

/-- Positivity and the acute branch depicted for the ramp. -/
structure HasPhysicalCarRampParameters
    (setup : CarOnTrailerRampSetup) : Prop where
  inclineAngleAcute :
    setup.rampAngleRadians ∈ Set.Ioo 0 (Real.pi / 2)
  weightPositive :
    0 < forceMagnitudeInNewtons (setup.force .weightW)
  cableTensionPositive :
    0 < forceMagnitudeInNewtons (setup.force .cableTensionT)
  rampNormalPositive :
    0 < forceMagnitudeInNewtons (setup.force .rampNormalN)

/-! ## Governing geometry and statics laws -/

/-!
The three force vectors follow the orientations displayed in the figure.
Each equality is required in every coherent unit system. These direction laws
relate each vector only to its own magnitude; they do not relate `n` to `w`
or contain the requested `w * cos alpha` formula.
-/
structure ObeysCarRampForceDirections
    (setup : CarOnTrailerRampSetup) : Prop where
  weightDirection :
    ∀ units : UnitChoices,
      forceVectorReadout units (setup.force .weightW) =
        forceMagnitudeReadout units (setup.force .weightW) •
          verticalDownUnitDirection
  cableTensionDirection :
    ∀ units : UnitChoices,
      forceVectorReadout units (setup.force .cableTensionT) =
        forceMagnitudeReadout units (setup.force .cableTensionT) •
          uphillRampUnitDirection setup.rampAngleRadians
  rampNormalDirection :
    ∀ units : UnitChoices,
      forceVectorReadout units (setup.force .rampNormalN) =
        forceMagnitudeReadout units (setup.force .rampNormalN) •
          outwardRampNormalUnitDirection setup.rampAngleRadians

/-!
Static equilibrium for the car: the only three modeled external forces sum
to zero. This is a vector governing law, not the requested resolved normal
component.
-/
structure SatisfiesCarStaticEquilibrium
    (setup : CarOnTrailerRampSetup) : Prop where
  forceBalance :
    ∀ units : UnitChoices,
      forceVectorReadout units (setup.force .weightW) +
          forceVectorReadout units (setup.force .cableTensionT) +
          forceVectorReadout units (setup.force .rampNormalN) =
        0

/-! ## Displayed symbolic answers and current target -/

/-- Labels of the four alternatives printed with the problem. -/
inductive AnswerChoice where
  | A
  | B
  | C
  | D
  deriving DecidableEq, Fintype, Repr

/-- The four displayed force expressions, read in any coherent force unit. -/
def displayedAnswerForceReadout
    (setup : CarOnTrailerRampSetup) (units : UnitChoices) :
    AnswerChoice → ℝ
  | .A =>
      forceMagnitudeReadout units (setup.force .weightW) *
        Real.sin setup.rampAngleRadians
  | .B =>
      forceMagnitudeReadout units (setup.force .weightW) *
        Real.cos setup.rampAngleRadians
  | .C =>
      2 * forceMagnitudeReadout units (setup.force .weightW) *
        Real.cos setup.rampAngleRadians
  | .D =>
      2 * forceMagnitudeReadout units (setup.force .weightW) *
        Real.sin setup.rampAngleRadians

/-- Dataset answer metadata, deliberately not used as a theorem premise. -/
def recordedDatasetAnswer : AnswerChoice := .B

/-!
Resolving static equilibrium perpendicular to the ramp eliminates the
ramp-parallel cable tension and gives `n = w * cos alpha` in every coherent
unit system. Consequently the requested force is the expression displayed
in choice B.

No premise above contains this normal-force relation or selects an answer.
This declaration formalizes `thm:physics:phyx_mini_0799:target`.
-/
theorem problem_phyx_mini_0799
    (setup : CarOnTrailerRampSetup)
    (_hScenario : MatchesCarOnTrailerRampScenario setup)
    (_hFigure : MatchesSuppliedCarRampFigure setup)
    (_hPhysical : HasPhysicalCarRampParameters setup)
    (_hDirections : ObeysCarRampForceDirections setup)
    (_hEquilibrium : SatisfiesCarStaticEquilibrium setup) :
    ∀ units : UnitChoices,
      forceMagnitudeReadout units (setup.force .rampNormalN) =
          forceMagnitudeReadout units (setup.force .weightW) *
            Real.cos setup.rampAngleRadians ∧
        forceMagnitudeReadout units (setup.force .rampNormalN) =
          displayedAnswerForceReadout setup units .B := by
  intro units
  have hBalance := _hEquilibrium.forceBalance units
  rw [_hDirections.weightDirection units,
      _hDirections.cableTensionDirection units,
      _hDirections.rampNormalDirection units] at hBalance
  have hx :
      forceMagnitudeReadout units (setup.force .cableTensionT) *
            Real.cos setup.rampAngleRadians +
          -(forceMagnitudeReadout units (setup.force .rampNormalN) *
            Real.sin setup.rampAngleRadians) = 0 := by
    simpa [verticalDownUnitDirection, uphillRampUnitDirection,
      outwardRampNormalUnitDirection] using
        congrArg (fun v : PlanarVector => v 0) hBalance
  have hy :
      -forceMagnitudeReadout units (setup.force .weightW) +
            forceMagnitudeReadout units (setup.force .cableTensionT) *
              Real.sin setup.rampAngleRadians +
          forceMagnitudeReadout units (setup.force .rampNormalN) *
            Real.cos setup.rampAngleRadians = 0 := by
    simpa [verticalDownUnitDirection, uphillRampUnitDirection,
      outwardRampNormalUnitDirection] using
        congrArg (fun v : PlanarVector => v 1) hBalance
  have hNormalBalance :
      -(forceMagnitudeReadout units (setup.force .weightW) *
          Real.cos setup.rampAngleRadians) +
          forceMagnitudeReadout units (setup.force .rampNormalN) *
            (Real.sin setup.rampAngleRadians ^ 2 +
              Real.cos setup.rampAngleRadians ^ 2) = 0 := by
    linear_combination
      Real.cos setup.rampAngleRadians * hy -
        Real.sin setup.rampAngleRadians * hx
  have hnormal :
      forceMagnitudeReadout units (setup.force .rampNormalN) =
        forceMagnitudeReadout units (setup.force .weightW) *
          Real.cos setup.rampAngleRadians := by
    rw [Real.sin_sq_add_cos_sq] at hNormalBalance
    linarith
  exact ⟨hnormal, by simpa [displayedAnswerForceReadout] using hnormal⟩

end PhyXMiniProblems.ProblemPhyXMini0799
