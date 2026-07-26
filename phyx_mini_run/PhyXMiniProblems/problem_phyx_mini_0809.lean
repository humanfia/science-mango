import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Physlib.Units.WithDim.Energy

/- USER: The assigned source file did not exist when this autoformalization task began. -/

/-!
# Quasistatic work done while pushing a swing

A rider of weight `w` hangs from chains of length `R`.  Starting at the lowest
point, a horizontal applied force slowly moves the rider to an angle `θ₀` from
the vertical.  The primary figure labels the circular arc by `s`, the forward
tangent element by `d⃗l`, and the applied horizontal force by `F⃗`.

Lengths, force magnitudes, and work retain their physical dimensions through
Physlib's unit-independent quantities.  Real numbers occur only as coherent
unit readouts and dimensionless radian angles.  The physical assumptions below
record circular-arc geometry, quasistatic tangential force balance, and the
line-integral definition of work; none assumes the requested final formula.
-/

noncomputable section

namespace PhyXMiniProblems.ProblemPhyXMini0809

open Dimension

/-! ## Dimensionful physical quantities and coherent-unit readouts -/

/-- The physical dimension of a force magnitude, `M L T⁻²`. -/
def forceDimension : Dimension :=
  M𝓭 * L𝓭 * T𝓭⁻¹ * T𝓭⁻¹

/-- A nonnegative, unit-independent physical length. -/
abbrev LengthQuantity : Type :=
  Dimensionful (WithDim L𝓭 NNReal)

/-- A nonnegative, unit-independent physical force magnitude. -/
abbrev ForceMagnitude : Type :=
  Dimensionful (WithDim forceDimension NNReal)

/-- Signed physical work, carrying Physlib's energy dimension. -/
abbrev WorkQuantity : Type := DimEnergy

/-- Scalar readout of a physical length in a coherent choice of base units. -/
def lengthReadout (units : UnitChoices) (length : LengthQuantity) : ℝ :=
  ((length units).val : ℝ)

/-- Scalar readout of a force magnitude in a coherent choice of base units. -/
def forceMagnitudeReadout
    (units : UnitChoices) (force : ForceMagnitude) : ℝ :=
  ((force units).val : ℝ)

/-- Signed scalar readout of work in a coherent choice of base units. -/
def workReadout (units : UnitChoices) (work : WorkQuantity) : ℝ :=
  (work units).val

/-- Metre readout of a physical length in coherent SI units. -/
def lengthInMeters (length : LengthQuantity) : ℝ :=
  lengthReadout UnitChoices.SI length

/-- Newton readout of a force magnitude in coherent SI units. -/
def forceMagnitudeInNewtons (force : ForceMagnitude) : ℝ :=
  forceMagnitudeReadout UnitChoices.SI force

/-- Joule readout of signed physical work. -/
def workInJoules (work : WorkQuantity) : ℝ :=
  workReadout UnitChoices.SI work /
    workReadout UnitChoices.SI DimEnergy.joule

/-! ## Process and primary-figure vocabulary -/

/-- Idealized weight models relevant to the problem's instruction. -/
inductive SwingWeightModel where
  | riderOnly
  | riderSeatAndChains
  deriving DecidableEq, Repr

/-- The slow process stipulated in the prose problem. -/
inductive SwingProcessRegime where
  | verySlowNearlyStaticEquilibrium
  | finiteSpeedDynamicalMotion
  deriving DecidableEq, Repr

/-- Named objects and curves visible in the supplied bitmap. -/
inductive FigureElement where
  | pivot
  | chains
  | riderAndSeat
  | dashedVerticalRadius
  | dashedCircularArc
  deriving DecidableEq, Fintype, Repr

/-- The two vector arrows explicitly labeled in the supplied bitmap. -/
inductive FigureVectorLabel where
  | appliedForceF
  | forwardPathElementDl
  deriving DecidableEq, Fintype, Repr

/-- Qualitative directions needed to transcribe the two pictured arrows. -/
inductive FigureVectorDirection where
  | horizontalRightward
  | tangentAlongIncreasingArc
  deriving DecidableEq, Repr

/-- Direct qualitative and textual evidence from the primary figure. -/
structure SwingFigure where
  showsElement : FigureElement → Bool
  vectorDirection : FigureVectorLabel → FigureVectorDirection
  appliedForceLabel : String
  pathElementLabel : String
  chainLengthLabel : String
  angleLabel : String
  arcLengthLabel : String
  showsAngleBetweenChainAndVertical : Bool
  showsSameAngleBetweenTangentAndHorizontal : Bool

/-! ## Physical setup, stated data, geometry, and governing laws -/

/-!
The independent physical quantities and path data.  The force magnitude is a
function of the current angular position because the push is varied during the
motion.  Neither `workDoneByPush` nor any field is defined from an answer
choice or from the requested closed formula.
-/
structure QuasistaticSwingSetup where
  figure : SwingFigure
  riderWeightMagnitude : ForceMagnitude
  chainLength : LengthQuantity
  initialAngleRadians : ℝ
  targetAngleRadians : ℝ
  appliedHorizontalForceMagnitude : ℝ → ForceMagnitude
  arcLengthFromInitial : ℝ → LengthQuantity
  pathTangentAngleAboveHorizontalRadians : ℝ → ℝ
  workDoneByPush : WorkQuantity
  weightModel : SwingWeightModel
  processRegime : SwingProcessRegime

/-!
Problem-statement and primary-image readouts.  The swing starts at the lowest
point (`θ = 0`), the horizontal push starts from zero, only the rider's weight
is retained, and all labels and directions are transcribed from the bitmap.
No value of the requested work occurs here.
-/
structure MatchesProblemAndPrimaryFigure
    (setup : QuasistaticSwingSetup) : Prop where
  riderWeightOnly : setup.weightModel = .riderOnly
  slowNearlyEquilibratedProcess :
    setup.processRegime = .verySlowNearlyStaticEquilibrium
  startsAtLowestPoint : setup.initialAngleRadians = 0
  appliedForceStartsAtZero :
    forceMagnitudeInNewtons
        (setup.appliedHorizontalForceMagnitude setup.initialAngleRadians) = 0
  allPicturedElementsShown :
    ∀ element : FigureElement, setup.figure.showsElement element = true
  forceArrowPointsHorizontallyRight :
    setup.figure.vectorDirection .appliedForceF = .horizontalRightward
  pathElementIsForwardArcTangent :
    setup.figure.vectorDirection .forwardPathElementDl =
      .tangentAlongIncreasingArc
  forceArrowText : setup.figure.appliedForceLabel = "F⃗"
  pathElementText : setup.figure.pathElementLabel = "d⃗l"
  chainLengthText : setup.figure.chainLengthLabel = "R"
  angleText : setup.figure.angleLabel = "θ"
  arcLengthText : setup.figure.arcLengthLabel = "s"
  angleIsMeasuredFromVertical :
    setup.figure.showsAngleBetweenChainAndVertical = true
  tangentCarriesSameAngleFromHorizontal :
    setup.figure.showsSameAngleBetweenTangentAndHorizontal = true

/-!
Positivity and the acute-angle branch depicted in the figure.  This is the
branch on which a finite horizontal force can maintain static equilibrium.
-/
structure HasPhysicalSwingParameters
    (setup : QuasistaticSwingSetup) : Prop where
  riderWeightPositive :
    0 < forceMagnitudeInNewtons setup.riderWeightMagnitude
  chainLengthPositive : 0 < lengthInMeters setup.chainLength
  targetAngleNonnegative : 0 ≤ setup.targetAngleRadians
  targetAngleAcute : setup.targetAngleRadians < Real.pi / 2

/-!
Circular-arc geometry from the primary figure: `s = R (θ - θᵢ)`, and the
forward tangent is inclined by `θ` above the horizontal when the chain is
inclined by `θ` from the vertical.  Both statements hold throughout the
depicted push.
-/
structure SatisfiesCircularSwingGeometry
    (setup : QuasistaticSwingSetup) : Prop where
  arcLengthLaw :
    ∀ (units : UnitChoices) (angleRadians : ℝ),
      setup.initialAngleRadians ≤ angleRadians →
      angleRadians ≤ setup.targetAngleRadians →
        lengthReadout units (setup.arcLengthFromInitial angleRadians) =
          lengthReadout units setup.chainLength *
            (angleRadians - setup.initialAngleRadians)
  tangentAngleLaw :
    ∀ angleRadians : ℝ,
      setup.initialAngleRadians ≤ angleRadians →
      angleRadians ≤ setup.targetAngleRadians →
        setup.pathTangentAngleAboveHorizontalRadians angleRadians =
          angleRadians

/-!
Tangential static equilibrium.  Chain tension has no tangential component, so
the component of the horizontal push along the forward tangent balances the
opposing tangential component of the rider's weight.  This local law contains
no integrated work or endpoint work formula.
-/
structure SatisfiesQuasistaticTangentialEquilibrium
    (setup : QuasistaticSwingSetup) : Prop where
  tangentialForceBalance :
    ∀ (units : UnitChoices) (angleRadians : ℝ),
      setup.initialAngleRadians ≤ angleRadians →
      angleRadians ≤ setup.targetAngleRadians →
        forceMagnitudeReadout units
              (setup.appliedHorizontalForceMagnitude angleRadians) *
            Real.cos
              (setup.pathTangentAngleAboveHorizontalRadians angleRadians) =
          forceMagnitudeReadout units setup.riderWeightMagnitude *
            Real.sin angleRadians

/-!
Work done by the applied force is its line integral along the circular path.
With `θ` as path parameter, `|d⃗l| = R dθ`; the cosine is the dot-product
projection of the horizontal force onto the forward tangent.  The law is
stated in every coherent unit system and does not evaluate the integral.
-/
structure SatisfiesAppliedForceWorkLaw
    (setup : QuasistaticSwingSetup) : Prop where
  workIntegrandIntervalIntegrable :
    ∀ units : UnitChoices,
      IntervalIntegrable
        (fun angleRadians : ℝ =>
          forceMagnitudeReadout units
                (setup.appliedHorizontalForceMagnitude angleRadians) *
              Real.cos
                (setup.pathTangentAngleAboveHorizontalRadians angleRadians) *
            lengthReadout units setup.chainLength)
        MeasureTheory.volume setup.initialAngleRadians setup.targetAngleRadians
  workIsAppliedForceLineIntegral :
    ∀ units : UnitChoices,
      workReadout units setup.workDoneByPush =
        ∫ angleRadians in
            setup.initialAngleRadians..setup.targetAngleRadians,
          forceMagnitudeReadout units
                (setup.appliedHorizontalForceMagnitude angleRadians) *
              Real.cos
                (setup.pathTangentAngleAboveHorizontalRadians angleRadians) *
            lengthReadout units setup.chainLength

/-! ## Displayed answers and current target -/

/-- Labels of the four answer choices printed with the problem. -/
inductive AnswerChoice where
  | A
  | B
  | C
  | D
  deriving DecidableEq, Fintype, Repr

/-!
The symbolic work expression printed beside each answer label, evaluated using
coherent-SI newton, metre, and joule readouts.
-/
def displayedWorkInJoules
    (setup : QuasistaticSwingSetup) : AnswerChoice → ℝ
  | .A =>
      2 * forceMagnitudeInNewtons setup.riderWeightMagnitude *
        lengthInMeters setup.chainLength *
          (1 - Real.cos setup.targetAngleRadians)
  | .B =>
      forceMagnitudeInNewtons setup.riderWeightMagnitude *
        lengthInMeters setup.chainLength *
          (1 - Real.cos setup.targetAngleRadians)
  | .C =>
      forceMagnitudeInNewtons setup.riderWeightMagnitude *
        lengthInMeters setup.chainLength *
          (1 - Real.sin setup.targetAngleRadians)
  | .D =>
      2 * forceMagnitudeInNewtons setup.riderWeightMagnitude *
        lengthInMeters setup.chainLength *
          (1 - Real.sin setup.targetAngleRadians)

/-- The physical work agrees with the symbolic expression of a displayed choice. -/
def MatchesDisplayedAnswer
    (setup : QuasistaticSwingSetup) (choice : AnswerChoice) : Prop :=
  workInJoules setup.workDoneByPush = displayedWorkInJoules setup choice

/-!
The quasistatic horizontal push does work equal to the rider's weight times
the vertical rise, `w R (1 - cos θ₀)`.  Hence the recorded answer is choice B.
The first conjunct states the dimensionally homogeneous relation in every
coherent unit system; the remaining conjuncts expose its SI/joule and answer-
choice forms.

This formalizes `thm:physics:phyx_mini_0809:target`.
-/
theorem problem_phyx_mini_0809
    (setup : QuasistaticSwingSetup)
    (hReadouts : MatchesProblemAndPrimaryFigure setup)
    (hPhysical : HasPhysicalSwingParameters setup)
    (hGeometry : SatisfiesCircularSwingGeometry setup)
    (hEquilibrium : SatisfiesQuasistaticTangentialEquilibrium setup)
    (hWork : SatisfiesAppliedForceWorkLaw setup) :
    (∀ units : UnitChoices,
      workReadout units setup.workDoneByPush =
        forceMagnitudeReadout units setup.riderWeightMagnitude *
          lengthReadout units setup.chainLength *
            (1 - Real.cos setup.targetAngleRadians)) ∧
      workInJoules setup.workDoneByPush =
        forceMagnitudeInNewtons setup.riderWeightMagnitude *
          lengthInMeters setup.chainLength *
            (1 - Real.cos setup.targetAngleRadians) ∧
      MatchesDisplayedAnswer setup .B := by
  have hInitialTarget :
      setup.initialAngleRadians ≤ setup.targetAngleRadians := by
    rw [hReadouts.startsAtLowestPoint]
    exact hPhysical.targetAngleNonnegative
  have hSinIntegral :
      (∫ angleRadians in
          setup.initialAngleRadians..setup.targetAngleRadians,
        Real.sin angleRadians) =
        1 - Real.cos setup.targetAngleRadians := by
    rw [integral_sin, hReadouts.startsAtLowestPoint]
    simp
  have hFormula :
      ∀ units : UnitChoices,
        workReadout units setup.workDoneByPush =
          forceMagnitudeReadout units setup.riderWeightMagnitude *
            lengthReadout units setup.chainLength *
              (1 - Real.cos setup.targetAngleRadians) := by
    intro units
    rw [hWork.workIsAppliedForceLineIntegral units]
    calc
      (∫ angleRadians in
          setup.initialAngleRadians..setup.targetAngleRadians,
        forceMagnitudeReadout units
              (setup.appliedHorizontalForceMagnitude angleRadians) *
            Real.cos
              (setup.pathTangentAngleAboveHorizontalRadians angleRadians) *
          lengthReadout units setup.chainLength) =
          ∫ angleRadians in
              setup.initialAngleRadians..setup.targetAngleRadians,
            (forceMagnitudeReadout units setup.riderWeightMagnitude *
              Real.sin angleRadians) *
                lengthReadout units setup.chainLength := by
        apply intervalIntegral.integral_congr
        intro angleRadians hAngle
        rw [Set.uIcc_of_le hInitialTarget] at hAngle
        dsimp
        have hBalance :=
          hEquilibrium.tangentialForceBalance
            units angleRadians hAngle.1 hAngle.2
        rw [hGeometry.tangentAngleLaw
          angleRadians hAngle.1 hAngle.2] at hBalance
        rw [hGeometry.tangentAngleLaw
          angleRadians hAngle.1 hAngle.2, hBalance]
      _ =
          forceMagnitudeReadout units setup.riderWeightMagnitude *
            lengthReadout units setup.chainLength *
              (1 - Real.cos setup.targetAngleRadians) := by
        rw [intervalIntegral.integral_mul_const,
          intervalIntegral.integral_const_mul, hSinIntegral]
        ring
  have hSI :
      workInJoules setup.workDoneByPush =
        forceMagnitudeInNewtons setup.riderWeightMagnitude *
          lengthInMeters setup.chainLength *
            (1 - Real.cos setup.targetAngleRadians) := by
    simpa [workInJoules, forceMagnitudeInNewtons, lengthInMeters,
      workReadout, DimEnergy.joule,
      CarriesDimension.toDimensionful_apply_apply] using
        hFormula UnitChoices.SI
  exact ⟨hFormula, hSI, by
    simpa [MatchesDisplayedAnswer, displayedWorkInJoules] using hSI⟩

end PhyXMiniProblems.ProblemPhyXMini0809
