import Mathlib
import Physlib.Units.WithDim.Speed

noncomputable section

namespace PhyXMiniProblems.ProblemPhyXMini0595

open Dimension

/-!
# Limiting transformed velocity as the moving frame approaches light speed

The supplied graph plots the signed one-dimensional velocity `u'` of a
particle measured in the inertial frame `S'` against the signed velocity `v`
of `S'` relative to `S`.  Both plotted coordinates are read as dimensionless
multiples of the vacuum speed of light.  The physical velocities themselves
retain length-per-time dimension through Physlib's unit-independent
`Dimensionful` type.
-/

/-! ## Dimensionful velocities and scalar graph readouts -/

/-- A signed one-dimensional physical velocity with dimension length/time. -/
abbrev SignedVelocityQuantity : Type :=
  Dimensionful (WithDim (L𝓭 * T𝓭⁻¹) ℝ)

/-- Read a signed velocity in the selected length and time units. -/
def signedVelocityReadout
    (lengthUnit : LengthUnit) (timeUnit : TimeUnit)
    (velocity : SignedVelocityQuantity) : ℝ :=
  (velocity {UnitChoices.SI with
    length := lengthUnit, time := timeUnit}).val

/-- The real SI readout of Physlib's dimensionful vacuum speed of light. -/
def vacuumSpeedOfLightInMetersPerSecond : ℝ :=
  signedVelocityReadout LengthUnit.meters TimeUnit.seconds
    DimSpeed.speedOfLight

/-- A signed physical velocity component as the dimensionless ratio `velocity / c`. -/
def velocityInLightSpeedUnits (velocity : SignedVelocityQuantity) : ℝ :=
  signedVelocityReadout LengthUnit.meters TimeUnit.seconds velocity /
    vacuumSpeedOfLightInMetersPerSecond

/-! ## Frame and graph labels -/

/-- The two inertial frames named in the problem. -/
inductive ReferenceFrameLabel where
  | S
  | SPrime
  deriving DecidableEq, Repr

/-- The velocity symbols printed on the two graph axes. -/
inductive VelocityAxisSymbol where
  | v
  | uPrime
  deriving DecidableEq, Repr

/-- Labeled ticks on the horizontal `v` axis. -/
inductive HorizontalTickLabel where
  | zero
  | pointTwoC
  | pointFourC
  deriving DecidableEq, Repr

/-- Labeled ticks on the vertical `u'` axis. -/
inductive VerticalTickLabel where
  | zero
  | uPrimeA
  deriving DecidableEq, Repr

/-- The qualitative rendering of the thick plotted trace. -/
inductive TraceStyle where
  | straightSegment
  deriving DecidableEq, Repr

/-- The qualitative direction in which the plotted trace changes. -/
inductive TraceTrend where
  | decreasing
  deriving DecidableEq, Repr

/--
The labels, calibrated ticks, and qualitative trace appearance visible in the
supplied graph.  Tick values are dimensionless multiples of `c`.
-/
structure VelocityTransformationFigure where
  horizontalAxisSymbol : VelocityAxisSymbol
  verticalAxisSymbol : VelocityAxisSymbol
  horizontalTickInLightSpeedUnits : HorizontalTickLabel → ℝ
  verticalTickInLightSpeedUnits : VerticalTickLabel → ℝ
  traceStyle : TraceStyle
  traceTrend : TraceTrend

/-!
The experiment consists of a fixed particle velocity in `S` and a scalar
graph readout `u'/c` for each scalar frame-velocity ratio `beta = v/c`.
The function field is an observable, not a definition of the requested limit.
-/
structure RelativisticVelocityGraphSetup where
  figure : VelocityTransformationFigure
  referenceFrame : ReferenceFrameLabel
  movingFrame : ReferenceFrameLabel
  particleVelocityInS : SignedVelocityQuantity
  uPrimeInLightSpeedUnitsAtFrameBeta : ℝ → ℝ

/-! ## Figure/data readouts and governing physics -/

/-!
Primary-image evidence and stated calibration.  The bottom vertical label is
`u'_a = -0.800 c`.  Four equal vertical grid intervals run from `0` at the top
to `u'_a` at the bottom, and the plotted trace begins on the first interval at
`v = 0`, giving the readout `u'(0) = -0.200 c`.  The last conjunct records only
the decreasing behavior on the displayed interval from `0` through `0.4 c`;
it does not constrain the requested limit at `c`.
-/
def MatchesSuppliedVelocityGraph
    (setup : RelativisticVelocityGraphSetup) : Prop :=
  setup.referenceFrame = .S ∧
    setup.movingFrame = .SPrime ∧
    setup.figure.horizontalAxisSymbol = .v ∧
    setup.figure.verticalAxisSymbol = .uPrime ∧
    setup.figure.horizontalTickInLightSpeedUnits .zero = 0 ∧
    setup.figure.horizontalTickInLightSpeedUnits .pointTwoC = (1 / 5 : ℝ) ∧
    setup.figure.horizontalTickInLightSpeedUnits .pointFourC = (2 / 5 : ℝ) ∧
    setup.figure.verticalTickInLightSpeedUnits .zero = 0 ∧
    setup.figure.verticalTickInLightSpeedUnits .uPrimeA = (-4 / 5 : ℝ) ∧
    setup.figure.traceStyle = .straightSegment ∧
    setup.figure.traceTrend = .decreasing ∧
    setup.uPrimeInLightSpeedUnitsAtFrameBeta 0 = (-1 / 5 : ℝ) ∧
    ∀ β₁ β₂ : ℝ,
      0 ≤ β₁ → β₁ < β₂ → β₂ ≤ (2 / 5 : ℝ) →
        setup.uPrimeInLightSpeedUnitsAtFrameBeta β₂ <
          setup.uPrimeInLightSpeedUnitsAtFrameBeta β₁

/-- Positivity of `c` and subluminality of the particle velocity in `S`. -/
def HasPhysicalRelativisticParameters
    (setup : RelativisticVelocityGraphSetup) : Prop :=
  0 < vacuumSpeedOfLightInMetersPerSecond ∧
    |velocityInLightSpeedUnits setup.particleVelocityInS| < 1

/-!
The governing collinear Einstein velocity transformation, written using
dimensionless signed components:

`u'/c = ((u/c) - (v/c)) / (1 - (u/c) * (v/c))`.

It applies at every subluminal frame velocity.  In particular, it is not an
assumption about the value or limit of `u'` at `v = c`.
-/
def ObeysCollinearEinsteinVelocityTransformation
    (setup : RelativisticVelocityGraphSetup) : Prop :=
  ∀ β : ℝ, |β| < 1 →
    setup.uPrimeInLightSpeedUnitsAtFrameBeta β =
      (velocityInLightSpeedUnits setup.particleVelocityInS - β) /
        (1 - velocityInLightSpeedUnits setup.particleVelocityInS * β)

/-! ## Multiple-choice target -/

/-- The four answer labels printed with the problem. -/
inductive AnswerChoice where
  | A
  | B
  | C
  | D
  deriving DecidableEq, Repr

/-- Candidate values of `u'/c`, including values outside the subluminal range. -/
def answerChoiceInLightSpeedUnits : AnswerChoice → ℝ
  | .A => -4 / 5
  | .B => 0
  | .C => -1
  | .D => -6 / 5

/-!
As the physical frame velocity `v` approaches `c` from below, the particle's
transformed signed velocity approaches `-c`.  Equivalently, the graph readout
`u'/c` tends to `-1`, which is answer choice C.

Blueprint label: `thm:physics:phyx_mini_0595:target`.
-/
theorem transformedVelocity_tendsto_negativeSpeedOfLight_choiceC
    (setup : RelativisticVelocityGraphSetup)
    (hFigure : MatchesSuppliedVelocityGraph setup)
    (hPhysical : HasPhysicalRelativisticParameters setup)
    (hEinstein : ObeysCollinearEinsteinVelocityTransformation setup) :
    Filter.Tendsto setup.uPrimeInLightSpeedUnitsAtFrameBeta
      (nhdsWithin 1 (Set.Iio 1))
      (nhds (answerChoiceInLightSpeedUnits .C)) := by
  rcases hFigure with ⟨_, _⟩
  rcases hPhysical with ⟨_, hParticleSubluminal⟩
  rw [abs_lt] at hParticleSubluminal
  let u : ℝ := velocityInLightSpeedUnits setup.particleVelocityInS
  have hu_lt_one : u < 1 := by
    exact hParticleSubluminal.2
  have hDenominatorNonzero : 1 - u * 1 ≠ 0 := by
    nlinarith
  have hIdentity :
      Filter.Tendsto (fun β : ℝ => β)
        (nhdsWithin 1 (Set.Iio 1)) (nhds 1) := by
    exact Filter.tendsto_id.mono_left nhdsWithin_le_nhds
  have hRational :
      Filter.Tendsto
        (fun β : ℝ => (u - β) / (1 - u * β))
        (nhdsWithin 1 (Set.Iio 1))
        (nhds ((u - 1) / (1 - u * 1))) := by
    exact (tendsto_const_nhds.sub hIdentity).div
      (tendsto_const_nhds.sub (tendsto_const_nhds.mul hIdentity))
      hDenominatorNonzero
  have hSubluminalEventually :
      ∀ᶠ β : ℝ in nhdsWithin 1 (Set.Iio 1), |β| < 1 := by
    rw [eventually_nhdsWithin_iff]
    filter_upwards [eventually_gt_nhds (show (-1 : ℝ) < 1 by norm_num)] with β hLower
    intro hUpper
    rw [abs_lt]
    exact ⟨hLower, hUpper⟩
  have hTransformation :
      setup.uPrimeInLightSpeedUnitsAtFrameBeta =ᶠ[
        nhdsWithin 1 (Set.Iio 1)]
        (fun β : ℝ => (u - β) / (1 - u * β)) := by
    filter_upwards [hSubluminalEventually] with β hβ
    exact hEinstein β hβ
  have hLimitValue : (u - 1) / (1 - u * 1) = (-1 : ℝ) := by
    rw [mul_one, div_eq_iff (by simpa using hDenominatorNonzero)]
    ring
  rw [show answerChoiceInLightSpeedUnits .C = (-1 : ℝ) by rfl,
    ← hLimitValue]
  exact hRational.congr' hTransformation.symm

end PhyXMiniProblems.ProblemPhyXMini0595
