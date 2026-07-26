import Mathlib
import Physlib.Units.WithDim.Area
import Physlib.Units.WithDim.Pressure

/- USER: The assigned source file did not exist when this autoformalization task began. -/

/-!
# Maximum load supported by a ceiling-mounted suction cup

A circular suction cup of diameter `10.0 cm` is pressed against a smooth
ceiling.  The supplied force diagram shows the air-pressure force `F_air`
upward, the ceiling normal force `n` and gravitational force `F_G` downward,
and `F_net = 0`.  At the largest sustainable load the normal force has fallen
to zero; under the ideal maximum-suction model, the pressure beneath the cup
is vacuum and the full atmospheric pressure acts over the circular seal.

Lengths, areas, pressures, masses, accelerations, and force magnitudes retain
their physical dimensions.  Real numbers are used only for named SI readouts,
figure text, and displayed multiple-choice values.
-/

noncomputable section

namespace PhyXMiniProblems.ProblemPhyXMini0720

open Dimension

/-! ## Dimensionful quantities and named-unit readouts -/

/-- The physical dimension of an acceleration magnitude, `L T⁻²`. -/
def accelerationDimension : Dimension := L𝓭 * T𝓭⁻¹ * T𝓭⁻¹

/-- The physical dimension of a force magnitude, `M L T⁻²`. -/
def forceDimension : Dimension := M𝓭 * accelerationDimension

/-- A nonnegative unit-independent physical length. -/
abbrev LengthQuantity : Type := Dimensionful (WithDim L𝓭 NNReal)

/-- A nonnegative unit-independent physical mass. -/
abbrev MassQuantity : Type := Dimensionful (WithDim M𝓭 NNReal)

/-- A nonnegative unit-independent acceleration magnitude. -/
abbrev AccelerationQuantity : Type :=
  Dimensionful (WithDim accelerationDimension NNReal)

/-- A nonnegative unit-independent force magnitude. -/
abbrev ForceMagnitude : Type :=
  Dimensionful (WithDim forceDimension NNReal)

/-- Coherent-SI metre readout of a physical length. -/
def lengthInMeters (length : LengthQuantity) : ℝ :=
  ((length UnitChoices.SI).val : ℝ)

/-- Centimetre readout used for the stated cup diameter. -/
def lengthInCentimeters (length : LengthQuantity) : ℝ :=
  100 * lengthInMeters length

/-- Coherent-SI square-metre readout of a physical area. -/
def areaInSquareMeters (area : DimArea) : ℝ :=
  ((area UnitChoices.SI).val : ℝ)

/-- Coherent-SI pascal readout of a physical pressure. -/
def pressureInPascals (pressure : DimPressure) : ℝ :=
  (pressure UnitChoices.SI).val

/-- Coherent-SI kilogram readout of a physical mass. -/
def massInKilograms (mass : MassQuantity) : ℝ :=
  ((mass UnitChoices.SI).val : ℝ)

/-- Metre-per-second-squared readout of an acceleration magnitude. -/
def accelerationInMetersPerSecondSquared
    (acceleration : AccelerationQuantity) : ℝ :=
  ((acceleration UnitChoices.SI).val : ℝ)

/-- Coherent-SI newton readout of a force magnitude. -/
def forceInNewtons (force : ForceMagnitude) : ℝ :=
  ((force UnitChoices.SI).val : ℝ)

/--
The upward force in newtons supplied by a uniform pressure difference across
the sealed circular area.
-/
def pressureDifferenceForceInNewtons
    (outsidePressure insidePressure : DimPressure) (area : DimArea) : ℝ :=
  (pressureInPascals outsidePressure - pressureInPascals insidePressure) *
    areaInSquareMeters area

/-- The weight magnitude in newtons of a physical mass. -/
def weightInNewtons
    (mass : MassQuantity) (gravity : AccelerationQuantity) : ℝ :=
  massInKilograms mass * accelerationInMetersPerSecondSquared gravity

/-! ## Apparatus and primary-figure vocabulary -/

/-- Vertical directions of the three nonzero arrows in the supplied diagram. -/
inductive VerticalDirection where
  | upward
  | downward
  deriving DecidableEq, Fintype, Repr

/-- Force labels printed in the supplied raster. -/
inductive FigureForceLabel where
  | airPressureForce
  | gravitationalForce
  | ceilingNormalForce
  deriving DecidableEq, Fintype, Repr

/--
Qualitative and textual evidence from the two-part supplied figure.  This
record contains no pressure, mass, or force magnitude.
-/
structure SuctionCupFigure where
  printedSymbol : FigureForceLabel → String
  arrowDirection : FigureForceLabel → VerticalDirection
  netForceText : String
  showsSmoothHorizontalCeiling : Bool
  showsCupPressedAgainstCeiling : Bool
  showsObjectHangingBelowCup : Bool
  showsVerticalConnectingRodOrString : Bool
  showsXAxis : Bool
  showsYAxis : Bool

/-- Mechanical state of the suction cup and its suspended load. -/
inductive AttachmentState where
  | attachedEquilibrium
  | incipientDetachment
  deriving DecidableEq, Repr

/-!
Independent physical quantities of the setup.  The suspended mass and the
three force magnitudes are observables constrained only by the hypotheses
below; they are not defined from the recorded answer.
-/
structure SuctionCupSetup where
  cupDiameter : LengthQuantity
  sealedCircularArea : DimArea
  outsideAtmosphericPressure : DimPressure
  pressureBeneathCup : DimPressure
  suspendedObjectMass : MassQuantity
  suctionCupMass : MassQuantity
  gravitationalAcceleration : AccelerationQuantity
  upwardAirPressureForce : ForceMagnitude
  ceilingNormalForce : ForceMagnitude
  downwardGravitationalForce : ForceMagnitude
  attachmentState : AttachmentState
  cupPressedAgainstSmoothCeiling : Bool
  sealIsAirtight : Bool
  figure : SuctionCupFigure

/-! ## Scenario, figure evidence, calibrations, and governing laws -/

/-- The qualitative apparatus assumptions stated in the problem. -/
structure MatchesSuctionCupScenario (setup : SuctionCupSetup) : Prop where
  pressedAgainstSmoothCeiling : setup.cupPressedAgainstSmoothCeiling = true
  airtightAtLimitingLoad : setup.sealIsAirtight = true
  cupAtIncipientDetachment : setup.attachmentState = .incipientDetachment

/-!
Primary-image evidence: `F_air` points upward, `F_G` and `n` point downward,
the net force is shown as zero, and the object hangs beneath the ceiling cup.
-/
structure MatchesSuppliedFigure (setup : SuctionCupSetup) : Prop where
  airForceSymbol :
    setup.figure.printedSymbol .airPressureForce = "F_air"
  gravityForceSymbol :
    setup.figure.printedSymbol .gravitationalForce = "F_G"
  normalForceSymbol :
    setup.figure.printedSymbol .ceilingNormalForce = "n"
  airForcePointsUp :
    setup.figure.arrowDirection .airPressureForce = .upward
  gravityForcePointsDown :
    setup.figure.arrowDirection .gravitationalForce = .downward
  normalForcePointsDown :
    setup.figure.arrowDirection .ceilingNormalForce = .downward
  netForceShownZero : setup.figure.netForceText = "F_net = 0"
  ceilingShown : setup.figure.showsSmoothHorizontalCeiling = true
  cupShownAtCeiling : setup.figure.showsCupPressedAgainstCeiling = true
  objectShownHanging : setup.figure.showsObjectHangingBelowCup = true
  connectorShown : setup.figure.showsVerticalConnectingRodOrString = true
  xAxisShown : setup.figure.showsXAxis = true
  yAxisShown : setup.figure.showsYAxis = true

/-!
Numerical and idealizing data stated or implied by the problem.  The suction
cup diameter is `10.0 cm`, and its negligible mass is modeled as zero.  This
record contains no suspended-object mass or answer-choice selection.
-/
structure MatchesProblemReadouts (setup : SuctionCupSetup) : Prop where
  cupDiameterCentimeters : lengthInCentimeters setup.cupDiameter = 10
  suctionCupMassNegligible : massInKilograms setup.suctionCupMass = 0

/-!
Standard environmental calibration used by the recorded numerical answer:
one standard atmosphere is `101325 Pa` and near-Earth gravity is `9.8 m/s²`.
-/
structure UsesStandardEnvironment (setup : SuctionCupSetup) : Prop where
  atmosphericPressurePascals :
    pressureInPascals setup.outsideAtmosphericPressure = 101325
  gravitationalAccelerationSI :
    accelerationInMetersPerSecondSquared setup.gravitationalAcceleration =
      49 / 5

/-!
The maximum ideal suction is attained when the pressure beneath the sealed
cup is vacuum.  This is a pressure calibration, not a mass conclusion.
-/
structure UsesIdealVacuumLimit (setup : SuctionCupSetup) : Prop where
  pressureBeneathCupPascals : pressureInPascals setup.pressureBeneathCup = 0

/-- The sealed face is the disk determined by the stated cup diameter. -/
structure SatisfiesCircularCupGeometry (setup : SuctionCupSetup) : Prop where
  circularAreaLaw :
    areaInSquareMeters setup.sealedCircularArea =
      Real.pi * (lengthInMeters setup.cupDiameter / 2) ^ 2

/-!
Governing pressure-force and weight laws, together with vertical static
equilibrium.  The diagram's upward air force balances the downward ceiling
normal and gravitational forces.  No numerical mass occurs in these laws.
-/
structure SatisfiesSuctionCupStatics (setup : SuctionCupSetup) : Prop where
  pressureDifferenceTimesArea :
    forceInNewtons setup.upwardAirPressureForce =
      pressureDifferenceForceInNewtons
        setup.outsideAtmosphericPressure setup.pressureBeneathCup
        setup.sealedCircularArea
  gravitationalForceIsTotalWeight :
    forceInNewtons setup.downwardGravitationalForce =
      weightInNewtons setup.suspendedObjectMass
          setup.gravitationalAcceleration +
        weightInNewtons setup.suctionCupMass setup.gravitationalAcceleration
  verticalEquilibrium :
    forceInNewtons setup.upwardAirPressureForce =
      forceInNewtons setup.ceilingNormalForce +
        forceInNewtons setup.downwardGravitationalForce

/-!
At incipient detachment the ceiling can no longer exert a downward normal
force on the cup, so that force has fallen to zero.
-/
structure AtDetachmentThreshold (setup : SuctionCupSetup) : Prop where
  ceilingNormalForceVanishes :
    forceInNewtons setup.ceilingNormalForce = 0

/-! ## Sustainable loads, displayed choices, and current target -/

/--
A candidate object mass is sustainable when its weight plus the negligible
cup weight does not exceed the available pressure-difference force.
-/
def CanBeSuspended (setup : SuctionCupSetup) (candidate : MassQuantity) : Prop :=
  weightInNewtons candidate setup.gravitationalAcceleration +
      weightInNewtons setup.suctionCupMass setup.gravitationalAcceleration ≤
    pressureDifferenceForceInNewtons
      setup.outsideAtmosphericPressure setup.pressureBeneathCup
      setup.sealedCircularArea

/-- A mass is maximal among all object masses sustainable by this setup. -/
def IsMaximumSustainableObjectMass
    (setup : SuctionCupSetup) (mass : MassQuantity) : Prop :=
  CanBeSuspended setup mass ∧
    ∀ candidate : MassQuantity,
      CanBeSuspended setup candidate →
        massInKilograms candidate ≤ massInKilograms mass

/-- Labels of the four mass choices printed with the problem. -/
inductive AnswerChoice where
  | A
  | B
  | C
  | D
  deriving DecidableEq, Fintype, Repr

/-- Kilogram values printed beside the answer labels. -/
def displayedMassInKilograms : AnswerChoice → ℝ
  | .A => 77
  | .B => 79
  | .C => 81
  | .D => 83

/-- A displayed choice is uniquely closest to the derived limiting mass. -/
def IsUniqueClosestAnswer (setup : SuctionCupSetup) (choice : AnswerChoice) : Prop :=
  ∀ otherChoice : AnswerChoice,
    otherChoice ≠ choice →
      |massInKilograms setup.suspendedObjectMass -
          displayedMassInKilograms choice| <
        |massInKilograms setup.suspendedObjectMass -
          displayedMassInKilograms otherChoice|

/-!
With a `0.10 m` diameter, disk area `π / 400 m²`, standard atmospheric
pressure, ideal vacuum beneath the cup, and `g = 9.8 m/s²`, the limiting mass
is exactly `20265π / 784 kg`, approximately `81.2 kg`.  It is the maximum
sustainable object mass, and `81 kg` (choice C) is uniquely closest.

This formalizes `thm:physics:phyx_mini_0720:target`.
-/
theorem problem_phyx_mini_0720
    (setup : SuctionCupSetup)
    (hScenario : MatchesSuctionCupScenario setup)
    (hFigure : MatchesSuppliedFigure setup)
    (hReadouts : MatchesProblemReadouts setup)
    (hEnvironment : UsesStandardEnvironment setup)
    (hVacuum : UsesIdealVacuumLimit setup)
    (hGeometry : SatisfiesCircularCupGeometry setup)
    (hStatics : SatisfiesSuctionCupStatics setup)
    (hThreshold : AtDetachmentThreshold setup) :
    massInKilograms setup.suspendedObjectMass =
        20265 * Real.pi / 784 ∧
      IsMaximumSustainableObjectMass setup setup.suspendedObjectMass ∧
      IsUniqueClosestAnswer setup .C := by
  have hDiameterMeters : lengthInMeters setup.cupDiameter = 1 / 10 := by
    have h := hReadouts.cupDiameterCentimeters
    rw [lengthInCentimeters] at h
    norm_num at h ⊢
    linarith
  have hArea :
      areaInSquareMeters setup.sealedCircularArea = Real.pi / 400 := by
    rw [hGeometry.circularAreaLaw, hDiameterMeters]
    ring
  have hPressureForce :
      pressureDifferenceForceInNewtons setup.outsideAtmosphericPressure
          setup.pressureBeneathCup setup.sealedCircularArea =
        101325 * Real.pi / 400 := by
    rw [pressureDifferenceForceInNewtons,
      hEnvironment.atmosphericPressurePascals,
      hVacuum.pressureBeneathCupPascals, hArea]
    ring
  have hCupWeight :
      weightInNewtons setup.suctionCupMass setup.gravitationalAcceleration = 0 := by
    rw [weightInNewtons, hReadouts.suctionCupMassNegligible]
    ring
  have hForceBalance :
      pressureDifferenceForceInNewtons setup.outsideAtmosphericPressure
          setup.pressureBeneathCup setup.sealedCircularArea =
        weightInNewtons setup.suspendedObjectMass setup.gravitationalAcceleration +
          weightInNewtons setup.suctionCupMass setup.gravitationalAcceleration := by
    calc
      _ = forceInNewtons setup.upwardAirPressureForce :=
        hStatics.pressureDifferenceTimesArea.symm
      _ = forceInNewtons setup.ceilingNormalForce +
            forceInNewtons setup.downwardGravitationalForce :=
        hStatics.verticalEquilibrium
      _ = forceInNewtons setup.downwardGravitationalForce := by
        rw [hThreshold.ceilingNormalForceVanishes, zero_add]
      _ = _ := hStatics.gravitationalForceIsTotalWeight
  have hMass :
      massInKilograms setup.suspendedObjectMass =
        20265 * Real.pi / 784 := by
    rw [hPressureForce, hCupWeight, weightInNewtons,
      hEnvironment.gravitationalAccelerationSI] at hForceBalance
    nlinarith [hForceBalance]
  refine ⟨hMass, ?_, ?_⟩
  · constructor
    · unfold CanBeSuspended
      exact hForceBalance.symm.le
    · intro candidate hCandidate
      unfold CanBeSuspended at hCandidate
      rw [hCupWeight, hPressureForce, weightInNewtons,
        hEnvironment.gravitationalAccelerationSI] at hCandidate
      rw [hMass]
      nlinarith
  · have hMassLower : 81 < massInKilograms setup.suspendedObjectMass := by
      rw [hMass]
      nlinarith [Real.pi_gt_d2]
    have hMassUpper : massInKilograms setup.suspendedObjectMass < 82 := by
      rw [hMass]
      nlinarith [Real.pi_lt_d2]
    unfold IsUniqueClosestAnswer
    intro otherChoice hOther
    fin_cases otherChoice
    · simp only [displayedMassInKilograms]
      rw [abs_of_pos (by linarith), abs_of_pos (by linarith)]
      linarith
    · simp only [displayedMassInKilograms]
      rw [abs_of_pos (by linarith), abs_of_pos (by linarith)]
      linarith
    · exact (hOther rfl).elim
    · simp only [displayedMassInKilograms]
      rw [abs_of_pos (by linarith), abs_of_neg (by linarith)]
      linarith

end PhyXMiniProblems.ProblemPhyXMini0720
