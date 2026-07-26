import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Physlib.Units.WithDim.Area
import Physlib.Units.WithDim.Pressure

/- USER: The assigned source file did not exist when this autoformalization task began. -/

/-!
# Pressure after admitting air beneath a spring-loaded piston

This file formalizes problem `phyx_mini_0396`.  A five-kilogram piston moves
vertically in a circular cylinder.  Gas pressure below the piston supports the
piston against atmospheric pressure, gravity, and a linear spring mounted
between the piston and the top of the cylinder.  The spring is unloaded when
the piston is at the cylinder bottom.  Opening the shown valve admits air and
raises the piston by two centimetres.

Mass, length, area, volume, pressure, acceleration, force, and spring
stiffness carry physical dimensions through Physlib.  Real numbers occur only
as explicitly named unit readouts and as the numerical values printed in the
problem and its answer choices.

Assumption/target split:

* `MatchesProblemAndPrimaryFigure` records the prose data and the labels and
  connections visible in image `396.png`;
* `UsesTextbookTerrestrialGravity` supplies the standard gravitational
  calibration needed for the numerical answer;
* `HasPhysicalParameters` selects the positive physical branch;
* `SatisfiesCylinderAndPistonKinematics` states the circular-cylinder volume
  law, the unloaded-spring reference geometry, and the two-centimetre rise;
* `SatisfiesLinearSpringAndStaticEquilibrium` states Hooke's law and the
  quasistatic vertical force balance; and
* `newPressure_matches_recordedAnswerB` concludes, rather than assumes, that
  the final pressure agrees with `515.3 kPa` to the displayed precision and
  uniquely selects answer B at that precision.
-/

noncomputable section

namespace PhyXMiniProblems.ProblemPhyXMini0396

open Dimension

/-! ## Dimensionful physical quantities and named readouts -/

/-- A physical mass, independent of the unit used to read it. -/
abbrev MassQuantity : Type := Dimensionful (WithDim M𝓭 ℝ)

/-- A signed physical length or vertical displacement. -/
abbrev LengthQuantity : Type := Dimensionful (WithDim L𝓭 ℝ)

/-- The nonnegative cross-sectional area supplied by Physlib. -/
abbrev AreaQuantity : Type := DimArea

/-- A physical volume carrying dimension `L³`. -/
abbrev VolumeQuantity : Type :=
  Dimensionful (WithDim (L𝓭 * L𝓭 * L𝓭) ℝ)

/-- A physical pressure carrying dimension `M L⁻¹ T⁻²`. -/
abbrev PressureQuantity : Type := DimPressure

/-- A physical acceleration, used for the downward gravitational field. -/
abbrev AccelerationQuantity : Type :=
  Dimensionful (WithDim (L𝓭 * T𝓭⁻¹ * T𝓭⁻¹) ℝ)

/-- A force magnitude carrying dimension `M L T⁻²`. -/
abbrev ForceQuantity : Type :=
  Dimensionful (WithDim (M𝓭 * L𝓭 * T𝓭⁻¹ * T𝓭⁻¹) ℝ)

/-- A linear spring stiffness, with dimension force per length, `M T⁻²`. -/
abbrev SpringStiffnessQuantity : Type :=
  Dimensionful (WithDim (M𝓭 * T𝓭⁻¹ * T𝓭⁻¹) ℝ)

/-- Kilogram readout of a physical mass. -/
def massInKilograms (mass : MassQuantity) : ℝ :=
  (mass UnitChoices.SI).val

/-- Metre readout of a physical length. -/
def lengthInMeters (length : LengthQuantity) : ℝ :=
  (length UnitChoices.SI).val

/-- Millimetre readout used for the stated cylinder diameter. -/
def lengthInMillimeters (length : LengthQuantity) : ℝ :=
  1000 * lengthInMeters length

/-- Centimetre readout used for the stated piston rise. -/
def lengthInCentimeters (length : LengthQuantity) : ℝ :=
  100 * lengthInMeters length

/-- Square-metre readout of a physical area. -/
def areaInSquareMeters (area : AreaQuantity) : ℝ :=
  ((area UnitChoices.SI).val : ℝ)

/-- Cubic-metre readout of a physical volume. -/
def volumeInCubicMeters (volume : VolumeQuantity) : ℝ :=
  (volume UnitChoices.SI).val

/-- Litre readout used for the initial gas volume. -/
def volumeInLiters (volume : VolumeQuantity) : ℝ :=
  1000 * volumeInCubicMeters volume

/-- Pascal readout of a physical pressure. -/
def pressureInPascals (pressure : PressureQuantity) : ℝ :=
  (pressure UnitChoices.SI).val

/-- Kilopascal readout used in the problem statement and answer choices. -/
def pressureInKilopascals (pressure : PressureQuantity) : ℝ :=
  pressureInPascals pressure / 1000

/-- Metres-per-second-squared readout of physical acceleration. -/
def accelerationInMetersPerSecondSquared
    (acceleration : AccelerationQuantity) : ℝ :=
  (acceleration UnitChoices.SI).val

/-- Newton readout of a physical force magnitude. -/
def forceInNewtons (force : ForceQuantity) : ℝ :=
  (force UnitChoices.SI).val

/-- Newton-per-metre readout of a linear spring stiffness. -/
def springStiffnessInNewtonsPerMeter
    (stiffness : SpringStiffnessQuantity) : ℝ :=
  (stiffness UnitChoices.SI).val

/-! ## Apparatus, process states, and primary-figure vocabulary -/

/-- Gas states before and after the valve admits additional air. -/
inductive GasState where
  | shownInitial
  | afterAirAdmission
  deriving DecidableEq, Repr

/-- Piston locations needed to express the unloaded-spring reference. -/
inductive PistonPosition where
  | cylinderBottom
  | shownInitial
  | raisedFinal
  deriving DecidableEq, Repr

/-- Vertical directions appearing in the prose or primary figure. -/
inductive VerticalDirection where
  | upward
  | downward
  deriving DecidableEq, Repr

/-- The circular shape stated for the cylinder bore. -/
inductive CylinderCrossSection where
  | circular
  deriving DecidableEq, Repr

/-- Constraint on the piston's motion in the cylinder. -/
inductive PistonGuide where
  | verticalTranslation
  deriving DecidableEq, Repr

/-- Constitutive model stated for the spring. -/
inductive SpringModel where
  | linear
  deriving DecidableEq, Repr

/-- Direction of air transfer when the depicted valve is opened. -/
inductive AirTransferDirection where
  | fromSupplyLineIntoCylinder
  deriving DecidableEq, Repr

/-- Operation performed on the valve during the transition. -/
inductive ValveOperation where
  | openedToAdmitAir
  deriving DecidableEq, Repr

/-- Physical components distinguished in image `396.png`. -/
inductive FigureComponent where
  | cylinderTop
  | piston
  | gasBelowPiston
  | atmosphereAbovePiston
  | supplyLine
  | valve
  deriving DecidableEq, Repr

/-- Text or symbols printed in the primary image. -/
inductive FigureLabel where
  | air
  | outsidePressureP0
  | gravityG
  | airSupplyLine
  deriving DecidableEq, Repr

/-- Which component or region a visible figure label denotes. -/
inductive FigureLabelTarget where
  | gasRegion
  | outsideAtmosphere
  | gravitationalField
  | supplyPipe
  deriving DecidableEq, Repr

/-- Structured transcription of the geometry and labels in image `396.png`. -/
structure SpringLoadedPistonFigure where
  componentShown : FigureComponent → Bool
  labelShown : FigureLabel → Bool
  labelTarget : FigureLabel → FigureLabelTarget
  gravityArrowDirection : VerticalDirection
  springUpperAttachment : FigureComponent
  springLowerAttachment : FigureComponent
  airRegionIsBelowPiston : Bool
  supplyLineConnectsToGasRegion : Bool
  valveLiesOnSupplyLine : Bool

/-!
Independent physical quantities for the cylinder, piston, spring, gas, and
air-admission process.  In particular, the final gas pressure and the spring
stiffness are independent fields; neither is defined from the recorded answer.
-/
structure SpringLoadedPistonSetup where
  cylinderCrossSection : CylinderCrossSection
  pistonGuide : PistonGuide
  springModel : SpringModel
  airTransferDirection : AirTransferDirection
  valveOperation : ValveOperation
  pistonMass : MassQuantity
  cylinderDiameter : LengthQuantity
  pistonArea : AreaQuantity
  outsideAtmosphericPressure : PressureQuantity
  gravitationalAcceleration : AccelerationQuantity
  springStiffness : SpringStiffnessQuantity
  pistonHeightAboveBottom : PistonPosition → LengthQuantity
  springCompression : PistonPosition → LengthQuantity
  springForceMagnitude : PistonPosition → ForceQuantity
  gasStatePosition : GasState → PistonPosition
  gasPressure : GasState → PressureQuantity
  gasVolume : GasState → VolumeQuantity
  pistonRiseDuringAirAdmission : LengthQuantity
  figure : SpringLoadedPistonFigure

/-! ## Stated data and governing physical laws -/

/-!
Numerical data from the prose and qualitative data from the primary image.
The final pressure, the recorded value `515.3 kPa`, and every answer-choice
value are deliberately absent from this structure.
-/
structure MatchesProblemAndPrimaryFigure
    (setup : SpringLoadedPistonSetup) : Prop where
  circularCylinder : setup.cylinderCrossSection = .circular
  pistonMovesVertically : setup.pistonGuide = .verticalTranslation
  springIsLinear : setup.springModel = .linear
  airFlowsIntoCylinder :
    setup.airTransferDirection = .fromSupplyLineIntoCylinder
  valveIsOpenedToAdmitAir : setup.valveOperation = .openedToAdmitAir
  pistonMassIsFiveKilograms : massInKilograms setup.pistonMass = 5
  cylinderDiameterIsOneHundredMillimeters :
    lengthInMillimeters setup.cylinderDiameter = 100
  atmosphericPressureIsOneHundredKilopascals :
    pressureInKilopascals setup.outsideAtmosphericPressure = 100
  shownPressureIsFourHundredKilopascals :
    pressureInKilopascals (setup.gasPressure .shownInitial) = 400
  shownVolumeIsFourTenthsLiter :
    volumeInLiters (setup.gasVolume .shownInitial) = 4 / 10
  pistonRiseIsTwoCentimeters :
    lengthInCentimeters setup.pistonRiseDuringAirAdmission = 2
  shownStateUsesShownPosition :
    setup.gasStatePosition .shownInitial = .shownInitial
  finalStateUsesRaisedPosition :
    setup.gasStatePosition .afterAirAdmission = .raisedFinal
  springExertsNoForceAtCylinderBottom :
    forceInNewtons (setup.springForceMagnitude .cylinderBottom) = 0
  everyComponentIsShown :
    ∀ component, setup.figure.componentShown component = true
  everyLabelIsShown :
    ∀ label, setup.figure.labelShown label = true
  airLabelTargetsGasRegion :
    setup.figure.labelTarget .air = .gasRegion
  outsidePressureLabelTargetsAtmosphere :
    setup.figure.labelTarget .outsidePressureP0 = .outsideAtmosphere
  gravityLabelTargetsField :
    setup.figure.labelTarget .gravityG = .gravitationalField
  supplyLabelTargetsPipe :
    setup.figure.labelTarget .airSupplyLine = .supplyPipe
  gravityArrowPointsDownward :
    setup.figure.gravityArrowDirection = .downward
  springMountedBetweenTopAndPiston :
    setup.figure.springUpperAttachment = .cylinderTop ∧
      setup.figure.springLowerAttachment = .piston
  airIsDrawnBelowPiston : setup.figure.airRegionIsBelowPiston = true
  supplyLineReachesGas : setup.figure.supplyLineConnectsToGasRegion = true
  valveIsDrawnOnSupplyLine : setup.figure.valveLiesOnSupplyLine = true

/-!
Standard textbook calibration for the downward gravitational acceleration.
This is a physical input needed to turn the stated mass into a weight; it does
not mention or determine the requested final pressure by itself.
-/
structure UsesTextbookTerrestrialGravity
    (setup : SpringLoadedPistonSetup) : Prop where
  gravityInSI :
    accelerationInMetersPerSecondSquared setup.gravitationalAcceleration =
      98 / 10

/-- Positivity and nonnegativity conditions selecting the physical branch. -/
structure HasPhysicalParameters
    (setup : SpringLoadedPistonSetup) : Prop where
  massPositive : 0 < massInKilograms setup.pistonMass
  diameterPositive : 0 < lengthInMeters setup.cylinderDiameter
  areaPositive : 0 < areaInSquareMeters setup.pistonArea
  atmosphericPressurePositive :
    0 < pressureInPascals setup.outsideAtmosphericPressure
  gravityPositive :
    0 < accelerationInMetersPerSecondSquared setup.gravitationalAcceleration
  stiffnessPositive :
    0 < springStiffnessInNewtonsPerMeter setup.springStiffness
  stateHeightPositive :
    ∀ state,
      0 < lengthInMeters
        (setup.pistonHeightAboveBottom (setup.gasStatePosition state))
  stateVolumePositive :
    ∀ state, 0 < volumeInCubicMeters (setup.gasVolume state)
  statePressurePositive :
    ∀ state, 0 < pressureInPascals (setup.gasPressure state)
  compressionNonnegative :
    ∀ position, 0 ≤ lengthInMeters (setup.springCompression position)
  springForceNonnegative :
    ∀ position, 0 ≤ forceInNewtons (setup.springForceMagnitude position)

/-!
Circular-cylinder geometry and piston kinematics.  Because the spring is
unloaded at the bottom, upward piston travel is its compression.  The gas
volume equals cross-sectional area times piston height, and the final piston
height is obtained by adding the stated rise.  No pressure value occurs in
these laws.
-/
structure SatisfiesCylinderAndPistonKinematics
    (setup : SpringLoadedPistonSetup) : Prop where
  circularPistonArea :
    areaInSquareMeters setup.pistonArea =
      Real.pi * (lengthInMeters setup.cylinderDiameter / 2) ^ 2
  bottomHeightIsZero :
    lengthInMeters (setup.pistonHeightAboveBottom .cylinderBottom) = 0
  compressionMeasuredFromBottom :
    ∀ position,
      lengthInMeters (setup.springCompression position) =
        lengthInMeters (setup.pistonHeightAboveBottom position)
  cylindricalGasVolume :
    ∀ state,
      volumeInCubicMeters (setup.gasVolume state) =
        areaInSquareMeters setup.pistonArea *
          lengthInMeters
            (setup.pistonHeightAboveBottom (setup.gasStatePosition state))
  finalHeightAfterRise :
    lengthInMeters (setup.pistonHeightAboveBottom .raisedFinal) =
      lengthInMeters (setup.pistonHeightAboveBottom .shownInitial) +
        lengthInMeters setup.pistonRiseDuringAirAdmission

/-!
Hooke's law and quasistatic vertical force balance in coherent SI readouts.
For either gas state,

`P_gas A = P_atmosphere A + m g + F_spring`.

The law constrains the unknown final pressure but does not assume its numerical
value or any answer choice.
-/
structure SatisfiesLinearSpringAndStaticEquilibrium
    (setup : SpringLoadedPistonSetup) : Prop where
  hookeLaw :
    ∀ position,
      forceInNewtons (setup.springForceMagnitude position) =
        springStiffnessInNewtonsPerMeter setup.springStiffness *
          lengthInMeters (setup.springCompression position)
  quasistaticVerticalForceBalance :
    ∀ state,
      pressureInPascals (setup.gasPressure state) *
          areaInSquareMeters setup.pistonArea =
        pressureInPascals setup.outsideAtmosphericPressure *
            areaInSquareMeters setup.pistonArea +
          massInKilograms setup.pistonMass *
            accelerationInMetersPerSecondSquared
              setup.gravitationalAcceleration +
          forceInNewtons
            (setup.springForceMagnitude (setup.gasStatePosition state))

/-! ## Displayed choices and requested conclusion -/

/-- Labels of the four answers printed with the problem. -/
inductive AnswerChoice where
  | A
  | B
  | C
  | D
  deriving DecidableEq, Repr

/-- Kilopascal value printed beside each displayed answer label. -/
def answerPressureInKilopascals : AnswerChoice → ℝ
  | .A => 4000
  | .B => 5153 / 10
  | .C => 154
  | .D => 102 / 10

/-- The answer label recorded in the supplied dataset. -/
def recordedAnswerChoice : AnswerChoice := .B

/-!
The post-admission pressure agrees with `515.3 kPa` to within `0.1 kPa`,
the precision appropriate to the displayed choice, and no other displayed
choice lies within the same tolerance.

Blueprint label: `thm:physics:phyx_mini_0396:target`.
-/
theorem newPressure_matches_recordedAnswerB
    (setup : SpringLoadedPistonSetup)
    (_figure : MatchesProblemAndPrimaryFigure setup)
    (_gravity : UsesTextbookTerrestrialGravity setup)
    (_physical : HasPhysicalParameters setup)
    (_kinematics : SatisfiesCylinderAndPistonKinematics setup)
    (_laws : SatisfiesLinearSpringAndStaticEquilibrium setup) :
    abs
        (pressureInKilopascals
            (setup.gasPressure .afterAirAdmission) -
          answerPressureInKilopascals .B) <
      1 / 10 ∧
    ∀ choice,
      abs
          (pressureInKilopascals
              (setup.gasPressure .afterAirAdmission) -
            answerPressureInKilopascals choice) <
        1 / 10 →
      choice = .B := by
  let A : ℝ := areaInSquareMeters setup.pistonArea
  let d : ℝ := lengthInMeters setup.cylinderDiameter
  let p0 : ℝ := pressureInPascals setup.outsideAtmosphericPressure
  let p1 : ℝ := pressureInPascals (setup.gasPressure .shownInitial)
  let p2 : ℝ := pressureInPascals (setup.gasPressure .afterAirAdmission)
  let m : ℝ := massInKilograms setup.pistonMass
  let g : ℝ :=
    accelerationInMetersPerSecondSquared setup.gravitationalAcceleration
  let k : ℝ := springStiffnessInNewtonsPerMeter setup.springStiffness
  let h1 : ℝ :=
    lengthInMeters (setup.pistonHeightAboveBottom .shownInitial)
  let h2 : ℝ :=
    lengthInMeters (setup.pistonHeightAboveBottom .raisedFinal)
  let c1 : ℝ := lengthInMeters (setup.springCompression .shownInitial)
  let c2 : ℝ := lengthInMeters (setup.springCompression .raisedFinal)
  let F1 : ℝ := forceInNewtons (setup.springForceMagnitude .shownInitial)
  let F2 : ℝ := forceInNewtons (setup.springForceMagnitude .raisedFinal)
  let V1 : ℝ := volumeInCubicMeters (setup.gasVolume .shownInitial)
  let rise : ℝ := lengthInMeters setup.pistonRiseDuringAirAdmission
  have hApos : 0 < A := by
    simpa [A] using _physical.areaPositive
  have hd : d = 1 / 10 := by
    have h := _figure.cylinderDiameterIsOneHundredMillimeters
    change 1000 * d = 100 at h
    norm_num at h ⊢
    linarith
  have hA : A = Real.pi / 400 := by
    have h := _kinematics.circularPistonArea
    change A = Real.pi * (d / 2) ^ 2 at h
    rw [hd] at h
    calc
      A = Real.pi * ((1 / 10 : ℝ) / 2) ^ 2 := h
      _ = Real.pi / 400 := by ring
  have hp0 : p0 = 100000 := by
    have h := _figure.atmosphericPressureIsOneHundredKilopascals
    change p0 / 1000 = 100 at h
    linarith
  have hp1 : p1 = 400000 := by
    have h := _figure.shownPressureIsFourHundredKilopascals
    change p1 / 1000 = 400 at h
    linarith
  have hm : m = 5 := by
    exact _figure.pistonMassIsFiveKilograms
  have hg : g = 98 / 10 := by
    exact _gravity.gravityInSI
  have hV1 : V1 = 1 / 2500 := by
    have h := _figure.shownVolumeIsFourTenthsLiter
    change 1000 * V1 = 4 / 10 at h
    norm_num at h ⊢
    linarith
  have hrise : rise = 1 / 50 := by
    have h := _figure.pistonRiseIsTwoCentimeters
    change 100 * rise = 2 at h
    norm_num at h ⊢
    linarith
  have hvolume : V1 = A * h1 := by
    have h := _kinematics.cylindricalGasVolume .shownInitial
    rw [_figure.shownStateUsesShownPosition] at h
    exact h
  have hheight : h2 = h1 + rise := by
    exact _kinematics.finalHeightAfterRise
  have hcomp1 : c1 = h1 := by
    exact _kinematics.compressionMeasuredFromBottom .shownInitial
  have hcomp2 : c2 = h2 := by
    exact _kinematics.compressionMeasuredFromBottom .raisedFinal
  have hhooke1 : F1 = k * c1 := by
    exact _laws.hookeLaw .shownInitial
  have hhooke2 : F2 = k * c2 := by
    exact _laws.hookeLaw .raisedFinal
  have heq1 : p1 * A = p0 * A + m * g + F1 := by
    have h := _laws.quasistaticVerticalForceBalance .shownInitial
    rw [_figure.shownStateUsesShownPosition] at h
    exact h
  have heq2 : p2 * A = p0 * A + m * g + F2 := by
    have h := _laws.quasistaticVerticalForceBalance .afterAirAdmission
    rw [_figure.finalStateUsesRaisedPosition] at h
    exact h
  have hF1 : F1 = 300000 * A - 49 := by
    norm_num [hp0, hp1, hm, hg] at heq1
    linarith
  have hF2 : F2 = F1 + k / 50 := by
    rw [hhooke2, hcomp2, hheight, hrise, hhooke1, hcomp1]
    ring
  have hk_relation : k / 2500 = F1 * A := by
    calc
      k / 2500 = k * V1 := by rw [hV1]; ring
      _ = k * (A * h1) := by rw [← hvolume]
      _ = (k * c1) * A := by rw [hcomp1]; ring
      _ = F1 * A := by rw [← hhooke1]
  have hpressure_relation : (p2 - p1) * A = k / 50 := by
    rw [hF2] at heq2
    nlinarith [heq1]
  have hcancel : p2 - p1 = 50 * F1 := by
    have hscaled : k / 50 = (50 * F1) * A := by
      calc
        k / 50 = 50 * (k / 2500) := by ring
        _ = 50 * (F1 * A) := by rw [hk_relation]
        _ = (50 * F1) * A := by ring
    rw [hscaled] at hpressure_relation
    exact mul_right_cancel₀ hApos.ne' hpressure_relation
  have hp2 : p2 = 397550 + 37500 * Real.pi := by
    rw [hp1, hF1, hA] at hcancel
    nlinarith
  have hp2kPa :
      pressureInKilopascals (setup.gasPressure .afterAirAdmission) =
        7951 / 20 + 75 / 2 * Real.pi := by
    change p2 / 1000 = 7951 / 20 + 75 / 2 * Real.pi
    rw [hp2]
    ring
  /-
  `Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic` does not import the
  later decimal-bound theorems for `π`.  A sixth-order version of its
  exponential-series argument is sharp enough for the required bounds.
  -/
  have complexCosBoundSix {z : ℂ} (hz : ‖z‖ ≤ 1) :
      ‖Complex.cos z - (1 - z ^ 2 / 2 + z ^ 4 / 24)‖ ≤
        ‖z‖ ^ 6 * (7 / 4320) := by
    calc
      ‖Complex.cos z - (1 - z ^ 2 / 2 + z ^ 4 / 24)‖ =
          ‖(Complex.exp (-z * Complex.I) -
                ∑ n ∈ Finset.range 6,
                  (-z * Complex.I) ^ n / n.factorial) / 2 +
            (Complex.exp (z * Complex.I) -
                ∑ n ∈ Finset.range 6,
                  (z * Complex.I) ^ n / n.factorial) / 2‖ := by
        simp [Complex.cos, field, Finset.sum_range_succ, Nat.factorial]
        grind [Complex.I_sq, two_ne_zero]
      _ ≤ ‖Complex.exp (-z * Complex.I) -
                ∑ n ∈ Finset.range 6,
                  (-z * Complex.I) ^ n / n.factorial‖ / 2 +
            ‖Complex.exp (z * Complex.I) -
                ∑ n ∈ Finset.range 6,
                  (z * Complex.I) ^ n / n.factorial‖ / 2 := by
        grw [norm_add_le]
        simp
      _ ≤ ‖-z * Complex.I‖ ^ 6 *
                (Nat.succ 6 *
                  (Nat.factorial 6 * (6 : ℕ) : ℝ)⁻¹) / 2 +
            ‖z * Complex.I‖ ^ 6 *
                (Nat.succ 6 *
                  (Nat.factorial 6 * (6 : ℕ) : ℝ)⁻¹) / 2 := by
        grw [Complex.exp_bound (by simpa) (by simp),
          Complex.exp_bound (by simpa) (by simp)]
      _ ≤ ‖z‖ ^ 6 * (7 / 4320) := by norm_num
  have cosBoundSix {x : ℝ} (hx : |x| ≤ 1) :
      |Real.cos x - (1 - x ^ 2 / 2 + x ^ 4 / 24)| ≤
        |x| ^ 6 * (7 / 4320) := by
    simpa [← Complex.ofReal_cos, ← Real.norm_eq_abs,
      ← Complex.norm_real] using
      complexCosBoundSix (z := (x : ℂ)) (by simpa using hx)
  have hpi : (1569 / 500 : ℝ) < Real.pi ∧
      Real.pi < (1257 / 400 : ℝ) := by
    constructor
    · have hb := cosBoundSix (x := (523 / 1000 : ℝ))
          (by norm_num [abs_of_nonneg])
      have hc :
          (8661 / 10000 : ℝ) ≤ Real.cos (523 / 1000 : ℝ) := by
        have hbnds := abs_le.mp hb
        rw [abs_of_nonneg (by norm_num)] at hbnds
        norm_num at hbnds ⊢
        linarith only [hbnds.1, hbnds.2]
      have hcos : 0 < Real.cos (1569 / 1000 : ℝ) := by
        have hcpos : 0 < Real.cos (523 / 1000 : ℝ) := by
          nlinarith only [hc]
        have hsum :
            0 ≤ Real.cos (523 / 1000 : ℝ) + 8661 / 10000 := by
          nlinarith only [hc]
        have hsquare :=
          mul_nonneg (sub_nonneg.mpr hc) hsum
        have hfactor :
            0 < 4 * Real.cos (523 / 1000 : ℝ) ^ 2 - 3 := by
          norm_num at hsquare ⊢
          nlinarith only [hsquare]
        have hproduct :
            0 < Real.cos (523 / 1000 : ℝ) *
              (4 * Real.cos (523 / 1000 : ℝ) ^ 2 - 3) :=
          mul_pos hcpos hfactor
        rw [show (1569 / 1000 : ℝ) = 3 * (523 / 1000) by
          norm_num, Real.cos_three_mul]
        convert hproduct using 1
        all_goals ring
      by_contra hpiLower
      have horder : Real.pi / 2 ≤ (1569 / 1000 : ℝ) := by
        norm_num at hpiLower ⊢
        linarith only [hpiLower]
      have hnonpos : Real.cos (1569 / 1000 : ℝ) ≤ 0 := by
        have hle := Real.cos_le_cos_of_nonneg_of_le_pi
          (x := Real.pi / 2) (y := (1569 / 1000 : ℝ))
          (by linarith only [Real.pi_pos])
          (by linarith only [Real.two_le_pi])
          horder
        simpa using hle
      linarith only [hcos, hnonpos]
    · have hb := cosBoundSix (x := (419 / 800 : ℝ))
          (by norm_num [abs_of_nonneg])
      have hc :
          Real.cos (419 / 800 : ℝ) ≤ (86602 / 100000 : ℝ) := by
        have hbnds := abs_le.mp hb
        rw [abs_of_nonneg (by norm_num)] at hbnds
        norm_num at hbnds ⊢
        linarith only [hbnds.1, hbnds.2]
      have hcos : Real.cos (1257 / 800 : ℝ) < 0 := by
        have hcpos : 0 < Real.cos (419 / 800 : ℝ) :=
          Real.cos_pos_of_le_one (by norm_num [abs_of_nonneg])
        have hsum :
            0 ≤ 86602 / 100000 + Real.cos (419 / 800 : ℝ) := by
          nlinarith only [hcpos]
        have hsquare :=
          mul_nonneg (sub_nonneg.mpr hc) hsum
        have hfactor :
            4 * Real.cos (419 / 800 : ℝ) ^ 2 - 3 < 0 := by
          norm_num at hsquare ⊢
          nlinarith only [hsquare]
        have hproduct :
            Real.cos (419 / 800 : ℝ) *
              (4 * Real.cos (419 / 800 : ℝ) ^ 2 - 3) < 0 :=
          mul_neg_of_pos_of_neg hcpos hfactor
        rw [show (1257 / 800 : ℝ) = 3 * (419 / 800) by
          norm_num, Real.cos_three_mul]
        convert hproduct using 1
        all_goals ring
      by_contra hpiUpper
      have horder : (1257 / 800 : ℝ) ≤ Real.pi / 2 := by
        norm_num at hpiUpper ⊢
        linarith only [hpiUpper]
      have hnonneg : 0 ≤ Real.cos (1257 / 800 : ℝ) := by
        have hle := Real.cos_le_cos_of_nonneg_of_le_pi
          (x := (1257 / 800 : ℝ)) (y := Real.pi / 2)
          (by norm_num) (by linarith only [Real.pi_pos]) horder
        simpa using hle
      linarith only [hcos, hnonneg]
  have hmatch :
      abs
          (pressureInKilopascals
              (setup.gasPressure .afterAirAdmission) -
            answerPressureInKilopascals .B) <
        1 / 10 := by
    rw [hp2kPa]
    change
      abs
          ((7951 / 20 + 75 / 2 * Real.pi : ℝ) - 5153 / 10) <
        1 / 10
    rw [abs_lt]
    constructor
    · nlinarith only [hpi.1]
    · nlinarith only [hpi.2]
  refine ⟨hmatch, ?_⟩
  intro choice hchoice
  cases choice with
  | A =>
      have hb := abs_lt.mp hmatch
      have hc := abs_lt.mp hchoice
      norm_num [answerPressureInKilopascals] at hb hc
      linarith only [hb.1, hb.2, hc.1, hc.2]
  | B => rfl
  | C =>
      have hb := abs_lt.mp hmatch
      have hc := abs_lt.mp hchoice
      norm_num [answerPressureInKilopascals] at hb hc
      linarith only [hb.1, hb.2, hc.1, hc.2]
  | D =>
      have hb := abs_lt.mp hmatch
      have hc := abs_lt.mp hchoice
      norm_num [answerPressureInKilopascals] at hb hc
      linarith only [hb.1, hb.2, hc.1, hc.2]

end PhyXMiniProblems.ProblemPhyXMini0396
