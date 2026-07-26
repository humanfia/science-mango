import Mathlib
import Physlib.Units.WithDim.Speed

noncomputable section

namespace PhyXMiniProblems.ProblemPhyXMini0182

open Dimension

/-!
# Linear density from two coupled standing waves

The supplied figure shows two strings joined by a central stretched spring.
The outer endpoints are attached to walls.  Both strings have nodes at their
two endpoints; the left string contains two half-wavelength loops and the
right string contains three.  The problem states that the strings have equal
length and are driven at equal frequencies, and calls the left linear mass
density `μ₀`.

Lengths, linear mass densities, frequencies, speeds, and tensions below are
unit-aware physical quantities.  Real numbers occur only as readouts in a
chosen coherent system of units and as dimensionless harmonic counts.
-/

/-! ## Dimensionful physical quantities -/

/-- Physical length, used for both string length and standing wavelength. -/
abbrev LengthQuantity : Type := Dimensionful (WithDim L𝓭 ℝ)

/-- Linear mass density, with dimension mass per length. -/
abbrev LinearMassDensity : Type :=
  Dimensionful (WithDim (M𝓭 * L𝓭⁻¹) ℝ)

/-- Ordinary frequency, with dimension inverse time. -/
abbrev FrequencyQuantity : Type := Dimensionful (WithDim T𝓭⁻¹ ℝ)

/-- Transverse-wave propagation speed, using Physlib's unit-aware speed type. -/
abbrev SpeedQuantity : Type := DimSpeed

/-- String tension, with the physical dimension of force. -/
abbrev TensionQuantity : Type :=
  Dimensionful (WithDim (M𝓭 * L𝓭 * T𝓭⁻¹ * T𝓭⁻¹) ℝ)

/-- Scalar readout of a physical length in a coherent choice of units. -/
def lengthReadout (units : UnitChoices) (quantity : LengthQuantity) : ℝ :=
  (quantity units).val

/-- Scalar readout of a linear mass density in a coherent choice of units. -/
def linearDensityReadout
    (units : UnitChoices) (quantity : LinearMassDensity) : ℝ :=
  (quantity units).val

/-- Scalar readout of an ordinary frequency in a coherent choice of units. -/
def frequencyReadout
    (units : UnitChoices) (quantity : FrequencyQuantity) : ℝ :=
  (quantity units).val

/-- Scalar readout of a wave speed in a coherent choice of units. -/
def speedReadout (units : UnitChoices) (quantity : SpeedQuantity) : ℝ :=
  ((quantity units).val : ℝ)

/-- Scalar readout of a string tension in a coherent choice of units. -/
def tensionReadout (units : UnitChoices) (quantity : TensionQuantity) : ℝ :=
  (quantity units).val

/-! ## Figure labels and physical setup -/

/-- The two strings on opposite sides of the central spring. -/
inductive StringSide where
  | left
  | right
  deriving DecidableEq, Repr

/-- The end of a string nearest the wall or nearest the central connector. -/
inductive StringEnd where
  | outer
  | inner
  deriving DecidableEq, Repr

/-- Mechanical attachment shown at a string endpoint. -/
inductive EndpointAttachment where
  | fixedWall
  | centralSpring
  deriving DecidableEq, Repr

/-- Transverse-displacement condition visible at a standing-wave endpoint. -/
inductive TransverseBoundaryCondition where
  | node
  | antinode
  deriving DecidableEq, Repr

/-- The connector explicitly labeled in the center of the supplied figure. -/
inductive CentralConnectorKind where
  | stretchedSpring
  deriving DecidableEq, Repr

/--
All physical quantities and figure labels for the coupled-string system.

`halfWavelengthCount` is the number of loops (antinodes) visible along a
string.  The right linear density is an unconstrained physical quantity in
this structure; no answer value is built into the setup.
-/
structure CoupledStringDiagram where
  stringLength : StringSide → LengthQuantity
  linearDensity : StringSide → LinearMassDensity
  drivingFrequency : StringSide → FrequencyQuantity
  standingWavelength : StringSide → LengthQuantity
  waveSpeed : StringSide → SpeedQuantity
  tension : StringSide → TensionQuantity
  halfWavelengthCount : StringSide → ℕ
  endpointAttachment : StringSide → StringEnd → EndpointAttachment
  transverseBoundary : StringSide → StringEnd → TransverseBoundaryCondition
  centralConnector : CentralConnectorKind

/-! ## Stated data and figure-derived readouts -/

/--
The data stated in the prose: equal physical lengths, equal drive frequencies,
and left-string linear density `μ₀`.  No relation for the right density occurs
here.
-/
structure MatchesProblemStatement
    (diagram : CoupledStringDiagram) (μ₀ : LinearMassDensity) : Prop where
  equalStringLengths :
    diagram.stringLength .left = diagram.stringLength .right
  equalDrivingFrequencies :
    diagram.drivingFrequency .left = diagram.drivingFrequency .right
  leftLinearDensity : diagram.linearDensity .left = μ₀

/--
Primary-image readout: two loops appear on the left, three on the right, both
outer ends meet fixed walls, both inner ends meet the stretched spring, and
all four depicted standing-wave endpoints are displacement nodes.
-/
structure MatchesSuppliedFigure (diagram : CoupledStringDiagram) : Prop where
  connectorLabel : diagram.centralConnector = .stretchedSpring
  leftLoopCount : diagram.halfWavelengthCount .left = 2
  rightLoopCount : diagram.halfWavelengthCount .right = 3
  leftOuterAttachment :
    diagram.endpointAttachment .left .outer = .fixedWall
  leftInnerAttachment :
    diagram.endpointAttachment .left .inner = .centralSpring
  rightInnerAttachment :
    diagram.endpointAttachment .right .inner = .centralSpring
  rightOuterAttachment :
    diagram.endpointAttachment .right .outer = .fixedWall
  endpointsAreNodes :
    ∀ side endpoint, diagram.transverseBoundary side endpoint = .node

/-- Positivity conditions selecting the ordinary nondegenerate string regime. -/
structure HasPhysicalStringParameters (diagram : CoupledStringDiagram) : Prop where
  lengthPositive :
    ∀ side, 0 < lengthReadout UnitChoices.SI (diagram.stringLength side)
  densityPositive :
    ∀ side, 0 < linearDensityReadout UnitChoices.SI (diagram.linearDensity side)
  frequencyPositive :
    ∀ side, 0 < frequencyReadout UnitChoices.SI (diagram.drivingFrequency side)
  wavelengthPositive :
    ∀ side, 0 < lengthReadout UnitChoices.SI (diagram.standingWavelength side)
  speedPositive :
    ∀ side, 0 < speedReadout UnitChoices.SI (diagram.waveSpeed side)
  tensionPositive :
    ∀ side, 0 < tensionReadout UnitChoices.SI (diagram.tension side)
  harmonicNumberPositive : ∀ side, 0 < diagram.halfWavelengthCount side

/-! ## Governing standing-wave and stretched-string laws -/

/--
Standard laws used for the two strings, expressed in every coherent unit
choice:

* a node-to-node string containing `n` loops has `2 L = n λ`;
* wave kinematics gives `v = f λ`;
* a stretched string obeys `T = μ v²`;
* the same massless stretched spring transmits equal tension magnitudes to its
  two ends.

These are general physical laws.  None mentions the problem-specific density
factor `9/4` or any answer choice.
-/
structure SatisfiesCoupledStringStandingWaveLaws
    (diagram : CoupledStringDiagram) : Prop where
  fixedEndStandingWaveLaw :
    ∀ side units,
      (diagram.halfWavelengthCount side : ℝ) *
          lengthReadout units (diagram.standingWavelength side) =
        2 * lengthReadout units (diagram.stringLength side)
  waveKinematics :
    ∀ side units,
      speedReadout units (diagram.waveSpeed side) =
        frequencyReadout units (diagram.drivingFrequency side) *
          lengthReadout units (diagram.standingWavelength side)
  stretchedStringSpeedLaw :
    ∀ side units,
      linearDensityReadout units (diagram.linearDensity side) *
          speedReadout units (diagram.waveSpeed side) ^ 2 =
        tensionReadout units (diagram.tension side)
  stretchedSpringForceBalance :
    ∀ units,
      tensionReadout units (diagram.tension .left) =
        tensionReadout units (diagram.tension .right)

/-!
The generic consequence needed before substituting the figure's loop counts:
for equal length, frequency, and tension, density times the square of the
other string's relevant harmonic denominator gives the cross-multiplied ratio.
-/
lemma linearDensity_harmonic_ratio
    (diagram : CoupledStringDiagram)
    (μ₀ : LinearMassDensity)
    (hProblem : MatchesProblemStatement diagram μ₀)
    (hPhysical : HasPhysicalStringParameters diagram)
    (hLaws : SatisfiesCoupledStringStandingWaveLaws diagram)
    (units : UnitChoices) :
    linearDensityReadout units (diagram.linearDensity .right) *
          (diagram.halfWavelengthCount .left : ℝ) ^ 2 =
      linearDensityReadout units (diagram.linearDensity .left) *
        (diagram.halfWavelengthCount .right : ℝ) ^ 2 := by
  have hLength :
      lengthReadout UnitChoices.SI (diagram.stringLength .left) =
        lengthReadout UnitChoices.SI (diagram.stringLength .right) :=
    congrArg (lengthReadout UnitChoices.SI) hProblem.equalStringLengths
  have hFrequency :
      frequencyReadout UnitChoices.SI (diagram.drivingFrequency .left) =
        frequencyReadout UnitChoices.SI (diagram.drivingFrequency .right) :=
    congrArg (frequencyReadout UnitChoices.SI) hProblem.equalDrivingFrequencies
  have hWavelength :
      (diagram.halfWavelengthCount .left : ℝ) *
          lengthReadout UnitChoices.SI (diagram.standingWavelength .left) =
        (diagram.halfWavelengthCount .right : ℝ) *
          lengthReadout UnitChoices.SI (diagram.standingWavelength .right) := by
    calc
      (diagram.halfWavelengthCount .left : ℝ) *
            lengthReadout UnitChoices.SI (diagram.standingWavelength .left) =
          2 * lengthReadout UnitChoices.SI (diagram.stringLength .left) :=
        hLaws.fixedEndStandingWaveLaw .left UnitChoices.SI
      _ = 2 * lengthReadout UnitChoices.SI (diagram.stringLength .right) := by
        rw [hLength]
      _ = (diagram.halfWavelengthCount .right : ℝ) *
            lengthReadout UnitChoices.SI (diagram.standingWavelength .right) :=
        (hLaws.fixedEndStandingWaveLaw .right UnitChoices.SI).symm
  have hVelocity :
      (diagram.halfWavelengthCount .left : ℝ) *
          speedReadout UnitChoices.SI (diagram.waveSpeed .left) =
        (diagram.halfWavelengthCount .right : ℝ) *
          speedReadout UnitChoices.SI (diagram.waveSpeed .right) := by
    calc
      (diagram.halfWavelengthCount .left : ℝ) *
            speedReadout UnitChoices.SI (diagram.waveSpeed .left) =
          (diagram.halfWavelengthCount .left : ℝ) *
            (frequencyReadout UnitChoices.SI (diagram.drivingFrequency .left) *
              lengthReadout UnitChoices.SI (diagram.standingWavelength .left)) := by
        rw [hLaws.waveKinematics .left UnitChoices.SI]
      _ = frequencyReadout UnitChoices.SI (diagram.drivingFrequency .left) *
            ((diagram.halfWavelengthCount .left : ℝ) *
              lengthReadout UnitChoices.SI (diagram.standingWavelength .left)) := by
        ring
      _ = frequencyReadout UnitChoices.SI (diagram.drivingFrequency .left) *
            ((diagram.halfWavelengthCount .right : ℝ) *
              lengthReadout UnitChoices.SI (diagram.standingWavelength .right)) := by
        rw [hWavelength]
      _ = frequencyReadout UnitChoices.SI (diagram.drivingFrequency .right) *
            ((diagram.halfWavelengthCount .right : ℝ) *
              lengthReadout UnitChoices.SI (diagram.standingWavelength .right)) := by
        rw [hFrequency]
      _ = (diagram.halfWavelengthCount .right : ℝ) *
            (frequencyReadout UnitChoices.SI (diagram.drivingFrequency .right) *
              lengthReadout UnitChoices.SI (diagram.standingWavelength .right)) := by
        ring
      _ = (diagram.halfWavelengthCount .right : ℝ) *
            speedReadout UnitChoices.SI (diagram.waveSpeed .right) := by
        rw [hLaws.waveKinematics .right UnitChoices.SI]
  have hVelocitySq :
      (diagram.halfWavelengthCount .left : ℝ) ^ 2 *
          speedReadout UnitChoices.SI (diagram.waveSpeed .left) ^ 2 =
        (diagram.halfWavelengthCount .right : ℝ) ^ 2 *
          speedReadout UnitChoices.SI (diagram.waveSpeed .right) ^ 2 := by
    convert congrArg (fun x : ℝ => x ^ 2) hVelocity using 1 <;> ring
  have hTension :
      linearDensityReadout UnitChoices.SI (diagram.linearDensity .left) *
          speedReadout UnitChoices.SI (diagram.waveSpeed .left) ^ 2 =
        linearDensityReadout UnitChoices.SI (diagram.linearDensity .right) *
          speedReadout UnitChoices.SI (diagram.waveSpeed .right) ^ 2 := by
    calc
      linearDensityReadout UnitChoices.SI (diagram.linearDensity .left) *
            speedReadout UnitChoices.SI (diagram.waveSpeed .left) ^ 2 =
          tensionReadout UnitChoices.SI (diagram.tension .left) :=
        hLaws.stretchedStringSpeedLaw .left UnitChoices.SI
      _ = tensionReadout UnitChoices.SI (diagram.tension .right) :=
        hLaws.stretchedSpringForceBalance UnitChoices.SI
      _ = linearDensityReadout UnitChoices.SI (diagram.linearDensity .right) *
            speedReadout UnitChoices.SI (diagram.waveSpeed .right) ^ 2 :=
        (hLaws.stretchedStringSpeedLaw .right UnitChoices.SI).symm
  have hWithSpeed :
      speedReadout UnitChoices.SI (diagram.waveSpeed .left) ^ 2 *
          (linearDensityReadout UnitChoices.SI (diagram.linearDensity .right) *
            (diagram.halfWavelengthCount .left : ℝ) ^ 2) =
        speedReadout UnitChoices.SI (diagram.waveSpeed .left) ^ 2 *
          (linearDensityReadout UnitChoices.SI (diagram.linearDensity .left) *
            (diagram.halfWavelengthCount .right : ℝ) ^ 2) := by
    calc
      speedReadout UnitChoices.SI (diagram.waveSpeed .left) ^ 2 *
            (linearDensityReadout UnitChoices.SI (diagram.linearDensity .right) *
              (diagram.halfWavelengthCount .left : ℝ) ^ 2) =
          linearDensityReadout UnitChoices.SI (diagram.linearDensity .right) *
            ((diagram.halfWavelengthCount .left : ℝ) ^ 2 *
              speedReadout UnitChoices.SI (diagram.waveSpeed .left) ^ 2) := by
        ring
      _ = linearDensityReadout UnitChoices.SI (diagram.linearDensity .right) *
            ((diagram.halfWavelengthCount .right : ℝ) ^ 2 *
              speedReadout UnitChoices.SI (diagram.waveSpeed .right) ^ 2) := by
        rw [hVelocitySq]
      _ = (diagram.halfWavelengthCount .right : ℝ) ^ 2 *
            (linearDensityReadout UnitChoices.SI (diagram.linearDensity .right) *
              speedReadout UnitChoices.SI (diagram.waveSpeed .right) ^ 2) := by
        ring
      _ = (diagram.halfWavelengthCount .right : ℝ) ^ 2 *
            (linearDensityReadout UnitChoices.SI (diagram.linearDensity .left) *
              speedReadout UnitChoices.SI (diagram.waveSpeed .left) ^ 2) := by
        rw [← hTension]
      _ = speedReadout UnitChoices.SI (diagram.waveSpeed .left) ^ 2 *
            (linearDensityReadout UnitChoices.SI (diagram.linearDensity .left) *
              (diagram.halfWavelengthCount .right : ℝ) ^ 2) := by
        ring
  have hRatioSI :
      linearDensityReadout UnitChoices.SI (diagram.linearDensity .right) *
            (diagram.halfWavelengthCount .left : ℝ) ^ 2 =
        linearDensityReadout UnitChoices.SI (diagram.linearDensity .left) *
          (diagram.halfWavelengthCount .right : ℝ) ^ 2 :=
    mul_left_cancel₀
      (pow_ne_zero 2 (ne_of_gt (hPhysical.speedPositive .left))) hWithSpeed
  have hRightScale :
      linearDensityReadout units (diagram.linearDensity .right) =
        (UnitChoices.dimScale UnitChoices.SI units
            (M𝓭 * L𝓭⁻¹) : ℝ) *
          linearDensityReadout UnitChoices.SI (diagram.linearDensity .right) := by
    have h := congrArg WithDim.val
      ((diagram.linearDensity .right).2 UnitChoices.SI units)
    simpa [linearDensityReadout, NNReal.smul_def] using h
  have hLeftScale :
      linearDensityReadout units (diagram.linearDensity .left) =
        (UnitChoices.dimScale UnitChoices.SI units
            (M𝓭 * L𝓭⁻¹) : ℝ) *
          linearDensityReadout UnitChoices.SI (diagram.linearDensity .left) := by
    have h := congrArg WithDim.val
      ((diagram.linearDensity .left).2 UnitChoices.SI units)
    simpa [linearDensityReadout, NNReal.smul_def] using h
  rw [hRightScale, hLeftScale]
  calc
    ((UnitChoices.dimScale UnitChoices.SI units (M𝓭 * L𝓭⁻¹) : ℝ) *
          linearDensityReadout UnitChoices.SI (diagram.linearDensity .right)) *
        (diagram.halfWavelengthCount .left : ℝ) ^ 2 =
      (UnitChoices.dimScale UnitChoices.SI units (M𝓭 * L𝓭⁻¹) : ℝ) *
        (linearDensityReadout UnitChoices.SI (diagram.linearDensity .right) *
          (diagram.halfWavelengthCount .left : ℝ) ^ 2) := by
      ring
    _ = (UnitChoices.dimScale UnitChoices.SI units (M𝓭 * L𝓭⁻¹) : ℝ) *
        (linearDensityReadout UnitChoices.SI (diagram.linearDensity .left) *
          (diagram.halfWavelengthCount .right : ℝ) ^ 2) := by
      rw [hRatioSI]
    _ = ((UnitChoices.dimScale UnitChoices.SI units (M𝓭 * L𝓭⁻¹) : ℝ) *
          linearDensityReadout UnitChoices.SI (diagram.linearDensity .left)) *
        (diagram.halfWavelengthCount .right : ℝ) ^ 2 := by
      ring

/-! ## Displayed answer data -/

/-- Labels of the four answer choices printed in the problem. -/
inductive AnswerChoice where
  | A
  | B
  | C
  | D
  deriving DecidableEq, Repr

/-- Dimensionless multiplier of `μ₀` printed beside each answer choice. -/
def displayedDensityMultiplier : AnswerChoice → NNReal
  | .A => 4 / 9
  | .B => 3 / 2
  | .C => 2 / 3
  | .D => 9 / 4

/-- The physical density displayed by an answer choice. -/
def displayedLinearDensity
    (μ₀ : LinearMassDensity) (choice : AnswerChoice) : LinearMassDensity :=
  displayedDensityMultiplier choice • μ₀

/--
The three-loop right string has linear density `(9/4) μ₀`, which is answer D.
The equality is between unit-aware physical quantities, not merely one scalar
readout.

This formalizes blueprint label `thm:physics:phyx_mini_0182:target`.
-/
theorem problem_phyx_mini_0182
    (diagram : CoupledStringDiagram)
    (μ₀ : LinearMassDensity)
    (hProblem : MatchesProblemStatement diagram μ₀)
    (hFigure : MatchesSuppliedFigure diagram)
    (hPhysical : HasPhysicalStringParameters diagram)
    (hLaws : SatisfiesCoupledStringStandingWaveLaws diagram) :
    diagram.linearDensity .right = ((9 : NNReal) / 4) • μ₀ := by
  apply Dimensionful.ext
  funext units
  apply WithDim.ext
  have hRatio :=
    linearDensity_harmonic_ratio diagram μ₀ hProblem hPhysical hLaws units
  rw [hFigure.leftLoopCount, hFigure.rightLoopCount,
    hProblem.leftLinearDensity] at hRatio
  change linearDensityReadout units (diagram.linearDensity .right) =
    ((((9 : NNReal) / 4) • μ₀).1 units).val
  simp only [Dimensionful.smul_apply, WithDim.smul_val, NNReal.smul_def]
  norm_num at hRatio ⊢
  simp only [linearDensityReadout] at hRatio ⊢
  linarith

end PhyXMiniProblems.ProblemPhyXMini0182
