import Mathlib.Analysis.SpecialFunctions.Trigonometric.Arctan
import Physlib.Relativity.LorentzGroup.Boosts.Basic
import Physlib.Units.WithDim.Speed

/- USER: The assigned source file did not exist when this autoformalization task began. -/

/-!
# Proper-frame orientation of a relativistically moving rod

The primary figure shows a rod above a dashed direction-of-motion line.  The
rod is labelled `ℓ`, the acute angle from the motion line is labelled `θ`, and
the velocity arrow points to the right.  In the laboratory frame the rod has
length `2.00 m`, orientation `30.0°`, and speed `0.995 c`.

The physical lengths and speed below are unit-independent Physlib quantities.
Real numbers are used only for coherent-unit readouts, radian angles,
dimensionless speed fractions, and displayed answer values.  The proper-frame
angle is an independent field: it is constrained by projection geometry and
special-relativistic length contraction, not assigned an answer value.
-/

noncomputable section

namespace PhyXMiniProblems.ProblemPhyXMini0526

open Dimension

/-! ## Dimensionful quantities and scalar readouts -/

/-- A nonnegative physical rod length, independent of the chosen unit. -/
abbrev LengthQuantity : Type :=
  Dimensionful (WithDim L𝓭 NNReal)

/-- A real-valued physical speed carrying length-per-time dimension. -/
abbrev SpeedQuantity : Type :=
  Dimensionful (WithDim (L𝓭 * T𝓭⁻¹) ℝ)

/-- Scalar readout of a physical length in a selected length unit. -/
def lengthReadout (unit : LengthUnit) (length : LengthQuantity) : ℝ :=
  ((length {UnitChoices.SI with length := unit}).val : ℝ)

/-- Scalar readout of a physical speed in selected length and time units. -/
def speedReadout
    (lengthUnit : LengthUnit) (timeUnit : TimeUnit)
    (speed : SpeedQuantity) : ℝ :=
  (speed {UnitChoices.SI with
    length := lengthUnit, time := timeUnit}).val

/-- Physlib's exact vacuum speed of light in selected coherent units. -/
def vacuumSpeedOfLightReadout
    (lengthUnit : LengthUnit) (timeUnit : TimeUnit) : ℝ :=
  (DimSpeed.speedOfLight {UnitChoices.SI with
    length := lengthUnit, time := timeUnit}).val

/-- Convert a radian angle to the dimensionless numerical value in degrees. -/
def angleInDegrees (angleInRadians : ℝ) : ℝ :=
  angleInRadians * 180 / Real.pi

/-! ## Frames, rod components, and primary-figure vocabulary -/

/-- The laboratory frame and the rod's proper (rest) frame. -/
inductive InertialFrameLabel where
  | laboratory
  | rodProper
  deriving DecidableEq, Repr

/-- Components of the rod measured relative to the direction of motion. -/
inductive RodComponent where
  | parallelToMotion
  | transverseToMotion
  deriving DecidableEq, Repr

/-- Text or symbols printed in the supplied schematic. -/
inductive FigureLabel where
  | ell
  | theta
  | directionOfMotion
  deriving DecidableEq, Fintype, Repr

/-- Direction of the arrow drawn below the dashed motion axis. -/
inductive FigureArrowDirection where
  | rightward
  | leftward
  deriving DecidableEq, Repr

/-!
Qualitative transcription of `phyx_data/test_image/526.png`.  The bitmap has
no numerical scale; the numerical length, angle, and speed come from the prose.
-/
structure MovingRodFigure where
  labelVisible : FigureLabel → Bool
  motionAxisIsDashed : Bool
  motionArrowDirection : FigureArrowDirection
  rodLiesAboveMotionAxis : Bool
  rodRisesTowardArrowDirection : Bool
  ellLabelIsOnRod : Bool
  thetaIsAcuteAngleFromMotionAxis : Bool

/-! ## Independent physical setup -/

/-!
The moving rod and its independent measurements in two inertial frames.

`properOrientationRadians` is deliberately an independent observable.  It is
not defined by the requested formula or by an answer choice.  The component
lengths are also independent quantities until the geometric and relativistic
laws below are assumed.
-/
structure MovingRodSetup where
  figure : MovingRodFigure
  observedFrame : InertialFrameLabel
  properFrame : InertialFrameLabel
  observedLength : LengthQuantity
  properLength : LengthQuantity
  observedComponentLength : RodComponent → LengthQuantity
  properComponentLength : RodComponent → LengthQuantity
  observedOrientationRadians : ℝ
  properOrientationRadians : ℝ
  speedRelativeToLaboratory : SpeedQuantity

/-- The dimensionless special-relativistic speed parameter `β = v/c`. -/
def speedFractionOfLight (setup : MovingRodSetup) : ℝ :=
  speedReadout LengthUnit.meters TimeUnit.seconds
      setup.speedRelativeToLaboratory /
    vacuumSpeedOfLightReadout LengthUnit.meters TimeUnit.seconds

/-- Proper orientation read in degrees, for comparison with the choices. -/
def properOrientationDegrees (setup : MovingRodSetup) : ℝ :=
  angleInDegrees setup.properOrientationRadians

/-! ## Figure/data readouts and governing physics -/

/-- The inertial-frame roles and numerical data stated in the problem prose. -/
structure MatchesProblemStatement (setup : MovingRodSetup) : Prop where
  observationIsInLaboratoryFrame :
    setup.observedFrame = .laboratory
  properFrameIsRodRestFrame :
    setup.properFrame = .rodProper
  observedLengthMeters :
    lengthReadout LengthUnit.meters setup.observedLength = 2
  observedAngleThirtyDegrees :
    setup.observedOrientationRadians = Real.pi / 6
  speedIsPointNineNineFiveC :
    speedFractionOfLight setup = (199 / 200 : ℝ)

/-!
Primary-image evidence: `ℓ` lies on the rising rod, `θ` is measured from the
dashed direction-of-motion line, and the motion arrow points right.  These
qualitative fields contain no proper-frame angle or answer choice.
-/
structure MatchesSuppliedRodFigure (figure : MovingRodFigure) : Prop where
  everyPrintedLabelVisible : ∀ label, figure.labelVisible label = true
  dashedMotionAxisShown : figure.motionAxisIsDashed = true
  arrowPointsRight : figure.motionArrowDirection = .rightward
  rodAboveAxis : figure.rodLiesAboveMotionAxis = true
  rodRisesToRight : figure.rodRisesTowardArrowDirection = true
  ellPrintedOnRod : figure.ellLabelIsOnRod = true
  thetaMeasuredFromMotionAxis :
    figure.thetaIsAcuteAngleFromMotionAxis = true

/-!
Positivity, acute-angle, and subluminal conditions for the intended physical
configuration.  They select the physical branches of `tan` and `arctan` but do
not specify the requested numerical angle.
-/
structure HasPhysicalMovingRodParameters (setup : MovingRodSetup) : Prop where
  observedLengthPositive :
    0 < lengthReadout LengthUnit.meters setup.observedLength
  properLengthPositive :
    0 < lengthReadout LengthUnit.meters setup.properLength
  observedParallelPositive :
    0 < lengthReadout LengthUnit.meters
      (setup.observedComponentLength .parallelToMotion)
  observedTransversePositive :
    0 < lengthReadout LengthUnit.meters
      (setup.observedComponentLength .transverseToMotion)
  properParallelPositive :
    0 < lengthReadout LengthUnit.meters
      (setup.properComponentLength .parallelToMotion)
  properTransversePositive :
    0 < lengthReadout LengthUnit.meters
      (setup.properComponentLength .transverseToMotion)
  observedAngleAcute :
    0 < setup.observedOrientationRadians ∧
      setup.observedOrientationRadians < Real.pi / 2
  properAngleAcute :
    0 < setup.properOrientationRadians ∧
      setup.properOrientationRadians < Real.pi / 2
  speedNonnegative : 0 ≤ speedFractionOfLight setup
  speedSubluminal : speedFractionOfLight setup < 1

/-!
Euclidean component geometry in both frames.  The two projection equations are
stated in every length unit.  They are ordinary geometry, not the requested
proper-angle formula.
-/
structure SatisfiesRodProjectionGeometry (setup : MovingRodSetup) : Prop where
  observedParallelProjection :
    ∀ unit : LengthUnit,
      lengthReadout unit
          (setup.observedComponentLength .parallelToMotion) =
        lengthReadout unit setup.observedLength *
          Real.cos setup.observedOrientationRadians
  observedTransverseProjection :
    ∀ unit : LengthUnit,
      lengthReadout unit
          (setup.observedComponentLength .transverseToMotion) =
        lengthReadout unit setup.observedLength *
          Real.sin setup.observedOrientationRadians
  properParallelProjection :
    ∀ unit : LengthUnit,
      lengthReadout unit
          (setup.properComponentLength .parallelToMotion) =
        lengthReadout unit setup.properLength *
          Real.cos setup.properOrientationRadians
  properTransverseProjection :
    ∀ unit : LengthUnit,
      lengthReadout unit
          (setup.properComponentLength .transverseToMotion) =
        lengthReadout unit setup.properLength *
          Real.sin setup.properOrientationRadians

/-!
Special-relativistic length contraction for a boost parallel to the dashed
motion axis.  The longitudinal laboratory component is the proper component
divided by Physlib's `LorentzGroup.γ β`; the transverse component is invariant.
Neither law mentions the target angle or any displayed answer.
-/
structure ObeysSpecialRelativisticRodContraction
    (setup : MovingRodSetup) : Prop where
  longitudinalComponentLaw :
    ∀ unit : LengthUnit,
      lengthReadout unit
          (setup.observedComponentLength .parallelToMotion) =
        lengthReadout unit
            (setup.properComponentLength .parallelToMotion) /
          LorentzGroup.γ (speedFractionOfLight setup)
  transverseComponentInvariant :
    ∀ unit : LengthUnit,
      lengthReadout unit
          (setup.observedComponentLength .transverseToMotion) =
        lengthReadout unit
          (setup.properComponentLength .transverseToMotion)

/-! ## Multiple-choice readouts -/

/-- Labels of the four orientation choices printed in the problem. -/
inductive AnswerChoice where
  | A
  | B
  | C
  | D
  deriving DecidableEq, Fintype, Repr

/-- Degree value displayed beside each answer choice. -/
def displayedOrientationDegrees : AnswerChoice → ℝ
  | .A => 5 / 2
  | .B => 14 / 5
  | .C => 3
  | .D => 33 / 10

/-- The answer label recorded by the source dataset. -/
def recordedDatasetAnswer : AnswerChoice := .D

/-- A choice is at least as close to an angle as every displayed alternative. -/
def IsNearestAnswerChoice (angleDegrees : ℝ) (choice : AnswerChoice) : Prop :=
  ∀ other : AnswerChoice,
    abs (angleDegrees - displayedOrientationDegrees choice) ≤
      abs (angleDegrees - displayedOrientationDegrees other)

/-!
Agreement with a degree value displayed to two decimal places.  Half of one
unit in the final decimal place is `0.005 = 1 / 200` degrees.
-/
def AgreesWhenRoundedToTwoDecimals
    (angleDegrees : ℝ) (choice : AnswerChoice) : Prop :=
  abs (angleDegrees - displayedOrientationDegrees choice) < 1 / 200

/-!
For the `2.00 m`, `30.0°`, `0.995 c` observation, projection geometry and
relativistic contraction give

`θ₀ = arctan (tan θ / γ(β))`.

The exact value is approximately `3.30018°`, so it rounds to the displayed
`3.30°` and makes choice D the nearest option.  The observed total length is
part of the physical setup although it cancels from the angle ratio.

Blueprint: `thm:physics:phyx_mini_0526:target`.
-/
theorem properFrameOrientationOfMovingRod
    (setup : MovingRodSetup)
    (hData : MatchesProblemStatement setup)
    (hFigure : MatchesSuppliedRodFigure setup.figure)
    (hPhysical : HasPhysicalMovingRodParameters setup)
    (hGeometry : SatisfiesRodProjectionGeometry setup)
    (hContraction : ObeysSpecialRelativisticRodContraction setup) :
    setup.properOrientationRadians =
        Real.arctan
          (Real.tan setup.observedOrientationRadians /
            LorentzGroup.γ (speedFractionOfLight setup)) ∧
      AgreesWhenRoundedToTwoDecimals
        (properOrientationDegrees setup) .D ∧
      IsNearestAnswerChoice (properOrientationDegrees setup) .D := by
  -- Exact normalization of the 25-fold tangent uses large rational numerals.
  let op := lengthReadout LengthUnit.meters
    (setup.observedComponentLength .parallelToMotion)
  let ot := lengthReadout LengthUnit.meters
    (setup.observedComponentLength .transverseToMotion)
  let pp := lengthReadout LengthUnit.meters
    (setup.properComponentLength .parallelToMotion)
  let pt := lengthReadout LengthUnit.meters
    (setup.properComponentLength .transverseToMotion)
  let pL := lengthReadout LengthUnit.meters setup.properLength
  let β := speedFractionOfLight setup
  let γ := LorentzGroup.γ β
  have hop :
      op = lengthReadout LengthUnit.meters setup.observedLength *
        Real.cos setup.observedOrientationRadians :=
    hGeometry.observedParallelProjection _
  have hot :
      ot = lengthReadout LengthUnit.meters setup.observedLength *
        Real.sin setup.observedOrientationRadians :=
    hGeometry.observedTransverseProjection _
  have hpp :
      pp = pL * Real.cos setup.properOrientationRadians :=
    hGeometry.properParallelProjection _
  have hpt :
      pt = pL * Real.sin setup.properOrientationRadians :=
    hGeometry.properTransverseProjection _
  have hcpar : op = pp / γ :=
    hContraction.longitudinalComponentLaw _
  have hctrans : ot = pt :=
    hContraction.transverseComponentInvariant _
  have hop_pos : 0 < op := hPhysical.observedParallelPositive
  have hpp_pos : 0 < pp := hPhysical.properParallelPositive
  have hpL_pos : 0 < pL := hPhysical.properLengthPositive
  have hβ0 : 0 ≤ β := hPhysical.speedNonnegative
  have hβ1 : β < 1 := hPhysical.speedSubluminal
  have hroot : 0 < Real.sqrt (1 - β ^ 2) :=
    Real.sqrt_pos.2 (by nlinarith)
  have hγ_pos : 0 < γ := by
    dsimp [γ, LorentzGroup.γ]
    positivity
  have htanProper :
      Real.tan setup.properOrientationRadians = pt / pp := by
    rw [Real.tan_eq_sin_div_cos, hpp, hpt]
    field_simp
  have htanObserved :
      Real.tan setup.observedOrientationRadians = ot / op := by
    rw [Real.tan_eq_sin_div_cos, hop, hot]
    have hL :
        0 < lengthReadout LengthUnit.meters setup.observedLength :=
      hPhysical.observedLengthPositive
    field_simp
  have htan :
      Real.tan setup.properOrientationRadians =
        Real.tan setup.observedOrientationRadians / γ := by
    rw [htanProper, htanObserved, hctrans]
    rw [div_div]
    have hcpar' : op * γ = pp :=
      (eq_div_iff hγ_pos.ne').mp hcpar
    rw [hcpar']
  have hAngle :
      setup.properOrientationRadians =
        Real.arctan
          (Real.tan setup.observedOrientationRadians /
            LorentzGroup.γ (speedFractionOfLight setup)) := by
    symm
    apply Real.arctan_eq_of_tan_eq
      (by simpa [γ, β] using htan)
    exact ⟨(neg_nonpos.mpr (by positivity : 0 ≤ Real.pi / 2)).trans_lt
        hPhysical.properAngleAcute.1,
      hPhysical.properAngleAcute.2⟩
  let x :=
    Real.tan setup.observedOrientationRadians /
      LorentzGroup.γ (speedFractionOfLight setup)
  have hx_sq : x ^ 2 = (133 / 40000 : ℝ) := by
    dsimp [x]
    rw [hData.observedAngleThirtyDegrees,
      hData.speedIsPointNineNineFiveC, Real.tan_pi_div_six,
      LorentzGroup.γ]
    norm_num [div_pow]
  have hx_pos : 0 < x := by
    dsimp [x]
    rw [hData.observedAngleThirtyDegrees,
      hData.speedIsPointNineNineFiveC, Real.tan_pi_div_six,
      LorentzGroup.γ]
    positivity
  have hx_lt_one : x < 1 := by nlinarith [hx_sq]

  let x2 := 2 * x / (1 - x ^ 2)
  let x4 := 2 * x2 / (1 - x2 ^ 2)
  let x8 := 2 * x4 / (1 - x4 ^ 2)
  let x16 := 2 * x8 / (1 - x8 ^ 2)
  let z24 := (x16 + x8) / (1 - x16 * x8)
  let y := (z24 + x) / (1 - z24 * x)
  have hx_bounds :
      (57662 / 1000000 : ℝ) < x ∧
        x < 57663 / 1000000 := by
    have hlo : (57662 / 1000000 : ℝ) ^ 2 < x ^ 2 := by
      rw [hx_sq]
      norm_num
    have hhi : x ^ 2 < (57663 / 1000000 : ℝ) ^ 2 := by
      rw [hx_sq]
      norm_num
    constructor <;> nlinarith only [hlo, hhi, hx_pos]
  have hdbl_mono {l u : ℝ}
      (hl0 : 0 ≤ l) (hlu : l < u) (hu1 : u < 1) :
      2 * l / (1 - l ^ 2) < 2 * u / (1 - u ^ 2) := by
    have hu0 : 0 < u := by nlinarith only [hl0, hlu]
    have hdl : 0 < 1 - l ^ 2 := by nlinarith only [hl0, hlu, hu1]
    have hdu : 0 < 1 - u ^ 2 := by nlinarith only [hu0, hu1]
    rw [div_lt_div_iff₀ hdl hdu]
    have hprod : 0 < (u - l) * (1 + l * u) := by positivity
    nlinarith only [hprod]
  have hx2_bounds :
      (115708 / 1000000 : ℝ) < x2 ∧
        x2 < 115711 / 1000000 := by
    dsimp [x2]
    constructor
    · calc
        (115708 / 1000000 : ℝ) <
            2 * (57662 / 1000000) /
              (1 - (57662 / 1000000) ^ 2) := by norm_num
        _ < 2 * x / (1 - x ^ 2) :=
          hdbl_mono (by norm_num) hx_bounds.1 hx_lt_one
    · calc
        2 * x / (1 - x ^ 2) <
            2 * (57663 / 1000000) /
              (1 - (57663 / 1000000) ^ 2) :=
          hdbl_mono hx_pos.le hx_bounds.2 (by norm_num)
        _ < (115711 / 1000000 : ℝ) := by norm_num
  have hx2_pos : 0 < x2 := by linarith only [hx2_bounds.1]
  have hx2_lt_one : x2 < 1 := by linarith only [hx2_bounds.2]
  have hx4_bounds :
      (234556 / 1000000 : ℝ) < x4 ∧
        x4 < 234563 / 1000000 := by
    dsimp [x4]
    constructor
    · calc
        (234556 / 1000000 : ℝ) <
            2 * (115708 / 1000000) /
              (1 - (115708 / 1000000) ^ 2) := by norm_num
        _ < 2 * x2 / (1 - x2 ^ 2) :=
          hdbl_mono (by norm_num) hx2_bounds.1 hx2_lt_one
    · calc
        2 * x2 / (1 - x2 ^ 2) <
            2 * (115711 / 1000000) /
              (1 - (115711 / 1000000) ^ 2) :=
          hdbl_mono hx2_pos.le hx2_bounds.2 (by norm_num)
        _ < (234563 / 1000000 : ℝ) := by norm_num
  have hx4_pos : 0 < x4 := by linarith only [hx4_bounds.1]
  have hx4_lt_one : x4 < 1 := by linarith only [hx4_bounds.2]
  have hx8_bounds :
      (496423 / 1000000 : ℝ) < x8 ∧
        x8 < 496441 / 1000000 := by
    dsimp [x8]
    constructor
    · calc
        (496423 / 1000000 : ℝ) <
            2 * (234556 / 1000000) /
              (1 - (234556 / 1000000) ^ 2) := by norm_num
        _ < 2 * x4 / (1 - x4 ^ 2) :=
          hdbl_mono (by norm_num) hx4_bounds.1 hx4_lt_one
    · calc
        2 * x4 / (1 - x4 ^ 2) <
            2 * (234563 / 1000000) /
              (1 - (234563 / 1000000) ^ 2) :=
          hdbl_mono hx4_pos.le hx4_bounds.2 (by norm_num)
        _ < (496441 / 1000000 : ℝ) := by norm_num
  have hx8_pos : 0 < x8 := by linarith only [hx8_bounds.1]
  have hx8_lt_one : x8 < 1 := by linarith only [hx8_bounds.2]
  have hx16_bounds :
      (131753 / 100000 : ℝ) < x16 ∧
        x16 < 131762 / 100000 := by
    dsimp [x16]
    constructor
    · calc
        (131753 / 100000 : ℝ) <
            2 * (496423 / 1000000) /
              (1 - (496423 / 1000000) ^ 2) := by norm_num
        _ < 2 * x8 / (1 - x8 ^ 2) :=
          hdbl_mono (by norm_num) hx8_bounds.1 hx8_lt_one
    · calc
        2 * x8 / (1 - x8 ^ 2) <
            2 * (496441 / 1000000) /
              (1 - (496441 / 1000000) ^ 2) :=
          hdbl_mono hx8_pos.le hx8_bounds.2 (by norm_num)
        _ < (131762 / 100000 : ℝ) := by norm_num
  have hx16_pos : 0 < x16 := by linarith only [hx16_bounds.1]
  have hx16x8_lt_one : x16 * x8 < 1 := by
    calc
      x16 * x8 < (131762 / 100000 : ℝ) * x8 :=
        mul_lt_mul_of_pos_right hx16_bounds.2 hx8_pos
      _ < (131762 / 100000 : ℝ) * (496441 / 1000000) :=
        mul_lt_mul_of_pos_left hx8_bounds.2 (by norm_num)
      _ < 1 := by norm_num
  have hadd_mono_left {a b c : ℝ}
      (hab : a < b) (hc0 : 0 ≤ c) (hbc : b * c < 1) :
      (a + c) / (1 - a * c) <
        (b + c) / (1 - b * c) := by
    have hac : a * c < 1 :=
      lt_of_le_of_lt (mul_le_mul_of_nonneg_right hab.le hc0) hbc
    rw [div_lt_div_iff₀ (sub_pos.2 hac) (sub_pos.2 hbc)]
    have hprod : 0 < (b - a) * (1 + c ^ 2) := by positivity
    nlinarith only [hprod]
  have hadd_mono_right {a b c : ℝ}
      (hab : a < b) (hc0 : 0 ≤ c) (hcb : c * b < 1) :
      (c + a) / (1 - c * a) <
        (c + b) / (1 - c * b) := by
    have hca : c * a < 1 :=
      lt_of_le_of_lt (mul_le_mul_of_nonneg_left hab.le hc0) hcb
    rw [div_lt_div_iff₀ (sub_pos.2 hca) (sub_pos.2 hcb)]
    have hprod : 0 < (b - a) * (1 + c ^ 2) := by positivity
    nlinarith only [hprod]
  have hz24_bounds :
      (52434 / 10000 : ℝ) < z24 ∧ z24 < 52448 / 10000 := by
    dsimp [z24]
    constructor
    · calc
        (52434 / 10000 : ℝ) <
            ((131753 / 100000 : ℝ) + 496423 / 1000000) /
              (1 - (131753 / 100000 : ℝ) * (496423 / 1000000)) := by
          norm_num
        _ < (x16 + (496423 / 1000000 : ℝ)) /
              (1 - x16 * (496423 / 1000000)) :=
          hadd_mono_left hx16_bounds.1 (by norm_num)
            (by nlinarith only [hx16_bounds.2])
        _ < (x16 + x8) / (1 - x16 * x8) :=
          hadd_mono_right hx8_bounds.1 hx16_pos.le hx16x8_lt_one
    · calc
        (x16 + x8) / (1 - x16 * x8) <
            ((131762 / 100000 : ℝ) + x8) /
              (1 - (131762 / 100000 : ℝ) * x8) :=
          hadd_mono_left hx16_bounds.2 hx8_pos.le
            (by
              calc
                (131762 / 100000 : ℝ) * x8 <
                    (131762 / 100000) * (496441 / 1000000) :=
                  mul_lt_mul_of_pos_left hx8_bounds.2 (by norm_num)
                _ < 1 := by norm_num)
        _ < ((131762 / 100000 : ℝ) + 496441 / 1000000) /
              (1 - (131762 / 100000 : ℝ) * (496441 / 1000000)) :=
          hadd_mono_right hx8_bounds.2 (by norm_num)
            (by norm_num)
        _ < (52448 / 10000 : ℝ) := by norm_num
  have hz24_pos : 0 < z24 := by linarith only [hz24_bounds.1]
  have hz24x_lt_one : z24 * x < 1 := by
    calc
      z24 * x < (52448 / 10000 : ℝ) * x :=
        mul_lt_mul_of_pos_right hz24_bounds.2 hx_pos
      _ < (52448 / 10000 : ℝ) * (57663 / 1000000) :=
        mul_lt_mul_of_pos_left hx_bounds.2 (by norm_num)
      _ < 1 := by norm_num
  have hy_bounds :
      (759 / 100 : ℝ) < y ∧ y < 761 / 100 := by
    dsimp [y]
    constructor
    · calc
        (759 / 100 : ℝ) <
            ((52434 / 10000 : ℝ) + 57662 / 1000000) /
              (1 - (52434 / 10000 : ℝ) * (57662 / 1000000)) := by
          norm_num
        _ < (z24 + (57662 / 1000000 : ℝ)) /
              (1 - z24 * (57662 / 1000000)) :=
          hadd_mono_left hz24_bounds.1 (by norm_num)
            (by nlinarith only [hz24_bounds.2])
        _ < (z24 + x) / (1 - z24 * x) :=
          hadd_mono_right hx_bounds.1 hz24_pos.le hz24x_lt_one
    · calc
        (z24 + x) / (1 - z24 * x) <
            ((52448 / 10000 : ℝ) + x) /
              (1 - (52448 / 10000 : ℝ) * x) :=
          hadd_mono_left hz24_bounds.2 hx_pos.le
            (by
              calc
                (52448 / 10000 : ℝ) * x <
                    (52448 / 10000) * (57663 / 1000000) :=
                  mul_lt_mul_of_pos_left hx_bounds.2 (by norm_num)
                _ < 1 := by norm_num)
        _ < ((52448 / 10000 : ℝ) + 57663 / 1000000) /
              (1 - (52448 / 10000 : ℝ) * (57663 / 1000000)) :=
          hadd_mono_right hx_bounds.2 (by norm_num) (by norm_num)
        _ < (761 / 100 : ℝ) := by norm_num

  have hdouble2 :
      2 * Real.arctan x = Real.arctan x2 := by
    simpa [x2] using
      Real.two_mul_arctan (by linarith : -(1 : ℝ) < x) hx_lt_one
  have hdouble4 :
      2 * Real.arctan x2 = Real.arctan x4 := by
    simpa [x4] using
      Real.two_mul_arctan (by linarith : -(1 : ℝ) < x2) hx2_lt_one
  have hdouble8 :
      2 * Real.arctan x4 = Real.arctan x8 := by
    simpa [x8] using
      Real.two_mul_arctan (by linarith : -(1 : ℝ) < x4) hx4_lt_one
  have hdouble16 :
      2 * Real.arctan x8 = Real.arctan x16 := by
    simpa [x16] using
      Real.two_mul_arctan (by linarith : -(1 : ℝ) < x8) hx8_lt_one
  have hadd24 :
      Real.arctan x16 + Real.arctan x8 = Real.arctan z24 := by
    simpa [z24] using
      Real.arctan_add hx16x8_lt_one
  have hadd25 :
      Real.arctan z24 + Real.arctan x = Real.arctan y := by
    simpa [y] using Real.arctan_add hz24x_lt_one
  have htwentyfive :
      25 * setup.properOrientationRadians = Real.arctan y := by
    have hxAngle : setup.properOrientationRadians = Real.arctan x := by
      exact hAngle
    rw [hxAngle]
    linarith [hdouble2, hdouble4, hdouble8, hdouble16,
      hadd24, hadd25]

  let r2 := Real.sqrt 2
  let r3 := Real.sqrt 3
  let b := r2 - 1
  let a := (r3 + b) / (1 - r3 * b)
  have hr2_sq : r2 ^ 2 = 2 := by
    dsimp [r2]
    exact Real.sq_sqrt (by norm_num)
  have hr3_sq : r3 ^ 2 = 3 := by
    dsimp [r3]
    exact Real.sq_sqrt (by norm_num)
  have hr2_pos : 0 < r2 := by
    dsimp [r2]
    positivity
  have hr3_pos : 0 < r3 := by
    dsimp [r3]
    positivity
  have hr2_lo : (1414213 / 1000000 : ℝ) < r2 := by
    nlinarith only [hr2_sq, hr2_pos]
  have hr2_hi : r2 < (1414214 / 1000000 : ℝ) := by
    nlinarith only [hr2_sq, hr2_pos]
  have hr3_lo : (1732050 / 1000000 : ℝ) < r3 := by
    nlinarith only [hr3_sq, hr3_pos]
  have hr3_hi : r3 < (1732051 / 1000000 : ℝ) := by
    nlinarith only [hr3_sq, hr3_pos]
  have hb_pos : 0 < b := by
    dsimp [b]
    linarith only [hr2_lo]
  have hb_lt_one : b < 1 := by
    dsimp [b]
    linarith only [hr2_hi]
  have hb_atan : Real.arctan b = Real.pi / 8 := by
    have hd :=
      Real.two_mul_arctan
        (by linarith only [hb_pos] : -(1 : ℝ) < b) hb_lt_one
    have hfrac : 2 * b / (1 - b ^ 2) = (1 : ℝ) := by
      have hden : 1 - b ^ 2 ≠ 0 := by
        nlinarith only [hb_pos, hb_lt_one]
      dsimp [b] at hden ⊢
      field_simp
      nlinarith only [hr2_sq]
    rw [hfrac, Real.arctan_one] at hd
    linarith only [hd]
  have hr3b_lt_one : r3 * b < 1 := by
    dsimp [b]
    nlinarith only [hr2_sq, hr3_sq, hr2_pos, hr3_pos,
      sq_nonneg (r3 * (r2 - 1) - 3 / 4)]
  have hcentral :
      Real.pi / 3 + Real.pi / 8 = Real.arctan a := by
    dsimp [a]
    rw [← Real.arctan_sqrt_three, ← hb_atan]
    exact Real.arctan_add hr3b_lt_one
  have hr3b_lo :
      (1732050 / 1000000 : ℝ) * (414213 / 1000000) <
        r3 * b := by
    dsimp [b]
    exact mul_lt_mul hr3_lo (by linarith only [hr2_lo])
      (by norm_num) hr3_pos.le
  have hr3b_hi :
      r3 * b <
        (1732051 / 1000000 : ℝ) * (414214 / 1000000) := by
    dsimp [b]
    exact mul_lt_mul hr3_hi (by linarith only [hr2_hi])
      (by linarith only [hr2_lo]) (by norm_num)
  have ha_bounds :
      (7595 / 1000 : ℝ) < a ∧ a < 1899 / 250 := by
    have hden : 0 < 1 - r3 * b := by
      norm_num at hr3b_hi ⊢
      linarith only [hr3b_hi]
    constructor
    · dsimp [a]
      apply (lt_div_iff₀ hden).2
      nlinarith only [hr3_lo, hr2_lo, hr3b_lo, hr3b_hi]
    · dsimp [a]
      apply (div_lt_iff₀ hden).2
      nlinarith only [hr3_hi, hr2_hi, hr3b_lo, hr3b_hi]

  let δ := Real.pi / 2048
  let t := Real.tan δ
  have hδ_pos : 0 < δ := by
    dsimp [δ]
    positivity
  have hδ_le : δ ≤ (1 / 512 : ℝ) := by
    dsimp [δ]
    nlinarith only [Real.pi_le_four]
  have hδ_ge : (1 / 1024 : ℝ) ≤ δ := by
    dsimp [δ]
    nlinarith only [Real.two_le_pi]
  have hδ_abs : |δ| ≤ 1 := by
    rw [abs_of_pos hδ_pos]
    linarith only [hδ_le]
  have hsin_error := Real.sin_bound hδ_abs
  rw [abs_of_pos hδ_pos] at hsin_error
  have hsin_error_lo := (abs_le.mp hsin_error).1
  have hsin_error_hi := (abs_le.mp hsin_error).2
  have hδ_sq : δ ^ 2 ≤ (1 / 512 : ℝ) ^ 2 := by
    nlinarith only [hδ_pos, hδ_le]
  have hδ_cube : δ ^ 3 ≤ (1 / 512 : ℝ) ^ 3 := by
    calc
      δ ^ 3 = δ ^ 2 * δ := by ring
      _ ≤ (1 / 512 : ℝ) ^ 2 * δ :=
        mul_le_mul_of_nonneg_right hδ_sq hδ_pos.le
      _ ≤ (1 / 512 : ℝ) ^ 2 * (1 / 512) :=
        mul_le_mul_of_nonneg_left hδ_le (by positivity)
      _ = (1 / 512 : ℝ) ^ 3 := by ring
  have hδ_fourth : δ ^ 4 ≤ (1 / 512 : ℝ) ^ 4 := by
    calc
      δ ^ 4 = δ ^ 2 * δ ^ 2 := by ring
      _ ≤ (1 / 512 : ℝ) ^ 2 * δ ^ 2 :=
        mul_le_mul_of_nonneg_right hδ_sq (sq_nonneg δ)
      _ ≤ (1 / 512 : ℝ) ^ 2 * (1 / 512) ^ 2 :=
        mul_le_mul_of_nonneg_left hδ_sq (by positivity)
      _ = (1 / 512 : ℝ) ^ 4 := by ring
  have hsin_lo : (1 / 2000 : ℝ) < Real.sin δ := by
    nlinarith only [hδ_ge, hδ_cube, hδ_fourth, hsin_error_lo]
  have hsin_hi : Real.sin δ < (1 / 256 : ℝ) := by
    nlinarith only [hδ_le, hδ_fourth, hsin_error_hi,
      pow_nonneg hδ_pos.le 3]
  have hδ_lt_pi_div_three : δ < Real.pi / 3 := by
    dsimp [δ]
    nlinarith only [Real.pi_pos]
  have hcos_lo : (1 / 2 : ℝ) < Real.cos δ := by
    have h := Real.cos_lt_cos_of_nonneg_of_le_pi hδ_pos.le
      (by nlinarith only [Real.pi_pos] : Real.pi / 3 ≤ Real.pi)
      hδ_lt_pi_div_three
    simpa using h
  have hcos_le : Real.cos δ ≤ 1 := Real.cos_le_one δ
  have hsin_pos : 0 < Real.sin δ :=
    lt_trans (by norm_num) hsin_lo
  have ht_bounds :
      (1 / 2000 : ℝ) < t ∧ t < 1 / 100 := by
    dsimp [t]
    rw [Real.tan_eq_sin_div_cos]
    constructor
    · calc
        (1 / 2000 : ℝ) < Real.sin δ := hsin_lo
        _ ≤ Real.sin δ / Real.cos δ := by
          apply (le_div_iff₀ (by linarith only [hcos_lo])).2
          nlinarith only [hcos_le, hsin_pos]
    · apply (div_lt_iff₀ (by linarith only [hcos_lo])).2
      nlinarith only [hsin_hi, hcos_lo]
  have hδ_range :
      -(Real.pi / 2) < δ ∧ δ < Real.pi / 2 := by
    dsimp [δ]
    constructor <;> nlinarith only [Real.pi_pos]
  have ht_atan : Real.arctan t = δ := by
    dsimp [t]
    exact Real.arctan_tan hδ_range.1 hδ_range.2
  have ha_pos : 0 < a := by linarith only [ha_bounds.1]
  have ht_pos : 0 < t := by linarith [ht_bounds.1]
  have hat_lo :
      (7595 / 1000 : ℝ) * (1 / 2000) < a * t := by
    calc
      (7595 / 1000 : ℝ) * (1 / 2000) <
          (7595 / 1000) * t :=
        mul_lt_mul_of_pos_left ht_bounds.1 (by norm_num)
      _ < a * t := mul_lt_mul_of_pos_right ha_bounds.1 ht_pos
  have hat_lt_one : a * t < 1 := by
    calc
      a * t < a * (1 / 100 : ℝ) :=
        mul_lt_mul_of_pos_left ht_bounds.2 ha_pos
      _ < (1899 / 250 : ℝ) * (1 / 100) :=
        mul_lt_mul_of_pos_right ha_bounds.2 (by norm_num)
      _ < 1 := by norm_num
  have hden_plus : 0 < 1 + a * t := by positivity
  have hden_minus : 0 < 1 - a * t := sub_pos.2 hat_lt_one
  have hlower_arg :
      (a - t) / (1 + a * t) < (759 / 100 : ℝ) := by
    apply (div_lt_iff₀ hden_plus).2
    nlinarith only [ha_bounds.2, ht_bounds.1, hat_lo]
  have hupper_arg :
      (761 / 100 : ℝ) < (a + t) / (1 - a * t) := by
    apply (lt_div_iff₀ hden_minus).2
    nlinarith only [ha_bounds.1, ht_bounds.1, hat_lo]
  have hminus :=
    Real.arctan_add (x := a) (y := -t)
      (by nlinarith only [ha_pos, ht_pos] : a * (-t) < 1)
  have hplus := Real.arctan_add (x := a) (y := t) hat_lt_one
  rw [Real.arctan_neg] at hminus
  rw [← hcentral, ht_atan] at hminus hplus
  have hlower_angle :
      (Real.pi / 3 + Real.pi / 8) - δ <
        setup.properOrientationRadians * 25 := by
    have harg :
        (a - t) / (1 + a * t) < y :=
      hlower_arg.trans hy_bounds.1
    have hatan :
        Real.arctan ((a - t) / (1 + a * t)) <
          Real.arctan y :=
      Real.arctan_strictMono harg
    have hminus' :
        Real.arctan ((a - t) / (1 + a * t)) =
          (Real.pi / 3 + Real.pi / 8) - δ := by
      simpa [sub_eq_add_neg] using hminus.symm
    rw [hminus', ← htwentyfive] at hatan
    simpa [mul_comm] using hatan
  have hupper_angle :
      setup.properOrientationRadians * 25 <
        (Real.pi / 3 + Real.pi / 8) + δ := by
    have harg :
        y < (a + t) / (1 - a * t) :=
      hy_bounds.2.trans hupper_arg
    have hatan :
        Real.arctan y <
          Real.arctan ((a + t) / (1 - a * t)) :=
      Real.arctan_strictMono harg
    have hplus' :
        Real.arctan ((a + t) / (1 - a * t)) =
          (Real.pi / 3 + Real.pi / 8) + δ :=
      hplus.symm
    rw [hplus', ← htwentyfive] at hatan
    simpa [mul_comm] using hatan
  let d := properOrientationDegrees setup
  have hd_lower : (659 / 200 : ℝ) < d := by
    dsimp [d, properOrientationDegrees, angleInDegrees]
    apply (lt_div_iff₀ Real.pi_pos).2
    dsimp [δ] at hlower_angle
    nlinarith only [hlower_angle, Real.pi_pos]
  have hd_upper : d < (661 / 200 : ℝ) := by
    dsimp [d, properOrientationDegrees, angleInDegrees]
    apply (div_lt_iff₀ Real.pi_pos).2
    dsimp [δ] at hupper_angle
    nlinarith only [hupper_angle, Real.pi_pos]
  have hd_error : abs (d - 33 / 10) < 1 / 200 := by
    rw [abs_lt]
    constructor <;> linarith only [hd_lower, hd_upper]
  refine ⟨hAngle, ?_, ?_⟩
  dsimp [AgreesWhenRoundedToTwoDecimals]
  change abs (d - 33 / 10) < 1 / 200
  exact hd_error

  intro other
  fin_cases other
  · change abs (d - 33 / 10) ≤ abs (d - 5 / 2)
    refine (le_of_lt hd_error).trans ?_
    rw [abs_of_nonneg (by linarith only [hd_lower])]
    norm_num
    linarith only [hd_lower]
  · change abs (d - 33 / 10) ≤ abs (d - 14 / 5)
    refine (le_of_lt hd_error).trans ?_
    rw [abs_of_nonneg (by linarith only [hd_lower])]
    norm_num
    linarith only [hd_lower]
  · change abs (d - 33 / 10) ≤ abs (d - 3)
    refine (le_of_lt hd_error).trans ?_
    rw [abs_of_nonneg (by linarith only [hd_lower])]
    norm_num
    linarith only [hd_lower]
  · exact le_rfl

end PhyXMiniProblems.ProblemPhyXMini0526
