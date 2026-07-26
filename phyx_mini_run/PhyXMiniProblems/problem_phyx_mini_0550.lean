import Mathlib.Data.Complex.Basic
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Physlib.QuantumMechanics.HilbertSpaces.OneDimension.Basic
import Physlib.Units.WithDim.Basic

/- USER: The assigned source file did not exist when this autoformalization task began. -/

/-!
# Position probability for a quadratic wavefunction in a one-dimensional box

The supplied figure places a particle between two hatched, impenetrable walls.
The left wall is the origin `O`, the right wall is a physical distance `l` away,
and the queried endpoint is the marked position `(1/3) l`.  Inside the box the
position-space wavefunction is `ψ(x) = c x (l - x)`.

Positions and the wall separation are unit-independent dimensionful quantities.
The wave amplitude has length dimension `L⁻¹ᐟ²`, while the coefficient `c` has
length dimension `L⁻⁵ᐟ²`.  Real and complex scalars below are named readouts in
a selected length unit; the requested probability is dimensionless.
-/

noncomputable section

namespace PhyXMiniProblems.ProblemPhyXMini0550

open CarriesDimension Dimension
open scoped Interval

/-! ## Dimensionful quantities and unit readouts -/

/-- A signed physical position on the horizontal axis. -/
abbrev PositionQuantity : Type :=
  Dimensionful (WithDim L𝓭 ℝ)

/-- A nonnegative physical length, used for the wall separation `l`. -/
abbrev LengthQuantity : Type :=
  Dimensionful (WithDim L𝓭 NNReal)

/-- A one-dimensional position-wavefunction amplitude, of dimension `L⁻¹ᐟ²`. -/
abbrev WaveAmplitudeQuantity : Type :=
  Dimensionful (WithDim (L𝓭 ^ ((-1 : ℚ) / 2)) ℂ)

/-- The coefficient in `ψ(x) = c x (l-x)`, of dimension `L⁻⁵ᐟ²`. -/
abbrev QuadraticCoefficientQuantity : Type :=
  Dimensionful (WithDim (L𝓭 ^ ((-5 : ℚ) / 2)) ℂ)

/-- Numerical position coordinate in a selected physical length unit. -/
def positionReadout (unit : LengthUnit) (position : PositionQuantity) : ℝ :=
  (position ({ UnitChoices.SI with length := unit } : UnitChoices)).val

/-- Numerical nonnegative length in a selected physical length unit. -/
def lengthReadout (unit : LengthUnit) (length : LengthQuantity) : ℝ :=
  ((length ({ UnitChoices.SI with length := unit } : UnitChoices)).val : ℝ)

/-- Construct a physical position from its coordinate in a selected unit. -/
def positionFromReadout (unit : LengthUnit) (value : ℝ) : PositionQuantity :=
  toDimensionful
    ({ UnitChoices.SI with length := unit } : UnitChoices)
    (show WithDim L𝓭 ℝ from ⟨value⟩)

/-- Numerical wave-amplitude readout in inverse square-root selected units. -/
def waveAmplitudeReadout
    (unit : LengthUnit) (amplitude : WaveAmplitudeQuantity) : ℂ :=
  (amplitude ({ UnitChoices.SI with length := unit } : UnitChoices)).val

/-- Numerical readout of `c` in inverse five-halves powers of the selected unit. -/
def coefficientReadout
    (unit : LengthUnit) (coefficient : QuadraticCoefficientQuantity) : ℂ :=
  (coefficient ({ UnitChoices.SI with length := unit } : UnitChoices)).val

/-! ## Quantum state, box geometry, and primary-figure vocabulary -/

/-- The visual style used for each vertical wall in the supplied diagram. -/
inductive WallRendering where
  | hatched
  | other
  deriving DecidableEq, Repr

/--
A pointwise one-dimensional quantum state together with its dimensionless
position-probability observable.  Born's rule is imposed separately, so the
observable is not defined using the requested numerical answer.
-/
structure OneDimensionalPositionState where
  waveAmplitudeAt : PositionQuantity → WaveAmplitudeQuantity
  positionProbabilityBetween : PositionQuantity → PositionQuantity → ℝ

/-- Geometry, labels, and landmarks shown in the supplied primary figure. -/
structure ParticleInBoxFigure where
  horizontalAxisLabel : String
  originLabel : String
  rightWallLabel : String
  oneThirdMarkLabel : String
  arrowPointsTowardIncreasingCoordinates : Bool
  leftWallRendering : WallRendering
  rightWallRendering : WallRendering
  origin : PositionQuantity
  rightWall : PositionQuantity
  oneThirdMark : PositionQuantity
  wallSeparation : LengthQuantity

/-- The particle state and the undetermined coefficient appearing in its profile. -/
structure ParticleInBoxSetup where
  figure : ParticleInBoxFigure
  state : OneDimensionalPositionState
  normalizationCoefficient : QuadraticCoefficientQuantity

/-! ## Figure/data readouts and governing physical laws -/

/--
Exact labels, wall styles, orientation, and relative positions read from the
primary image.  These are figure facts; no probability value occurs here.
-/
structure MatchesSuppliedParticleInBoxFigure
    (figure : ParticleInBoxFigure) : Prop where
  horizontalLabel : figure.horizontalAxisLabel = "x"
  originIsLabelledO : figure.originLabel = "O"
  rightWallIsLabelledL : figure.rightWallLabel = "l"
  queryMarkIsLabelledOneThirdL : figure.oneThirdMarkLabel = "1/3 l"
  positiveDirectionPointsRight :
    figure.arrowPointsTowardIncreasingCoordinates = true
  leftWallIsHatched : figure.leftWallRendering = .hatched
  rightWallIsHatched : figure.rightWallRendering = .hatched
  wallSeparationIsPositive :
    ∀ unit : LengthUnit, 0 < lengthReadout unit figure.wallSeparation
  originCoordinate :
    ∀ unit : LengthUnit, positionReadout unit figure.origin = 0
  rightWallCoordinate :
    ∀ unit : LengthUnit,
      positionReadout unit figure.rightWall =
        lengthReadout unit figure.wallSeparation
  oneThirdCoordinate :
    ∀ unit : LengthUnit,
      positionReadout unit figure.oneThirdMark =
        lengthReadout unit figure.wallSeparation / 3

/--
Inside the walls, the amplitude has the stated profile
`ψ(x) = c (x-O) (l-(x-O))`, equivalently `c (x-O) (x_right-x)`.
-/
def HasQuadraticWaveProfile (setup : ParticleInBoxSetup) : Prop :=
  ∀ (unit : LengthUnit) (x : ℝ),
    positionReadout unit setup.figure.origin ≤ x →
    x ≤ positionReadout unit setup.figure.rightWall →
      waveAmplitudeReadout unit
          (setup.state.waveAmplitudeAt (positionFromReadout unit x)) =
        coefficientReadout unit setup.normalizationCoefficient *
          ((x - positionReadout unit setup.figure.origin : ℝ) : ℂ) *
          ((positionReadout unit setup.figure.rightWall - x : ℝ) : ℂ)

/-- Impenetrable-wall confinement: the position amplitude vanishes outside the box. -/
def SatisfiesImpenetrableWallBoundaryCondition
    (setup : ParticleInBoxSetup) : Prop :=
  ∀ (unit : LengthUnit) (x : ℝ),
    (x < positionReadout unit setup.figure.origin ∨
      positionReadout unit setup.figure.rightWall < x) →
      waveAmplitudeReadout unit
          (setup.state.waveAmplitudeAt (positionFromReadout unit x)) = 0

/-- The pointwise representative of the state is square-integrable in every unit. -/
def IsSquareIntegrablePositionState (setup : ParticleInBoxSetup) : Prop :=
  ∀ unit : LengthUnit,
    QuantumMechanics.OneDimension.HilbertSpace.MemHS
      (fun x : ℝ ↦
        waveAmplitudeReadout unit
          (setup.state.waveAmplitudeAt (positionFromReadout unit x)))

/-- The confined wavefunction has total probability one inside the two walls. -/
def IsNormalizedInsideBox (setup : ParticleInBoxSetup) : Prop :=
  ∀ unit : LengthUnit,
    (∫ x in positionReadout unit setup.figure.origin..
        positionReadout unit setup.figure.rightWall,
      Complex.normSq
        (waveAmplitudeReadout unit
          (setup.state.waveAmplitudeAt (positionFromReadout unit x)))) = 1

/--
The position-space Born rule: probability between any ordered pair of physical
positions is the integral of the squared complex amplitude over that interval.
-/
def SatisfiesPositionBornRule (setup : ParticleInBoxSetup) : Prop :=
  ∀ (unit : LengthUnit) (lower upper : PositionQuantity),
    positionReadout unit lower ≤ positionReadout unit upper →
      setup.state.positionProbabilityBetween lower upper =
        ∫ x in positionReadout unit lower..positionReadout unit upper,
          Complex.normSq
            (waveAmplitudeReadout unit
              (setup.state.waveAmplitudeAt (positionFromReadout unit x)))

/-!
Blueprint label: `thm:physics:phyx_mini_0550:target`.

For the normalized quadratic profile in the box, Born's rule assigns probability
`17/81` to the interval from the origin through the marked one-third point.
-/
theorem probability_from_origin_to_one_third
    (setup : ParticleInBoxSetup)
    (h_figure : MatchesSuppliedParticleInBoxFigure setup.figure)
    (h_profile : HasQuadraticWaveProfile setup)
    (h_impenetrable : SatisfiesImpenetrableWallBoundaryCondition setup)
    (h_squareIntegrable : IsSquareIntegrablePositionState setup)
    (h_normalized : IsNormalizedInsideBox setup)
    (h_born : SatisfiesPositionBornRule setup) :
    setup.state.positionProbabilityBetween
        setup.figure.origin setup.figure.oneThirdMark = (17 : ℝ) / 81 := by
  have integral_recurrence (n : ℕ) (b : ℝ) :
      2 * (∫ x in (0 : ℝ)..b, x ^ n) =
        ∫ x in (0 : ℝ)..b, ((x / 2) ^ n + (b - x / 2) ^ n) := by
    have hpow : Continuous (fun x : ℝ => x ^ n) := by
      fun_prop
    have hsplit := intervalIntegral.integral_add_adjacent_intervals
      (hpow.intervalIntegrable (μ := MeasureTheory.volume) 0 (b / 2))
      (hpow.intervalIntegrable (μ := MeasureTheory.volume) (b / 2) b)
    have hfirst :
        (∫ x in (0 : ℝ)..b, (x / 2) ^ n) =
          2 * (∫ x in (0 : ℝ)..b / 2, x ^ n) := by
      simpa [smul_eq_mul] using
        (intervalIntegral.integral_comp_div
          (a := (0 : ℝ)) (b := b) (c := (2 : ℝ))
          (fun x : ℝ => x ^ n) (by norm_num))
    have hsecond :
        (∫ x in (0 : ℝ)..b, (b - x / 2) ^ n) =
          2 * (∫ x in b / 2..b, x ^ n) := by
      convert
        (intervalIntegral.integral_comp_sub_div
          (a := (0 : ℝ)) (b := b) (c := (2 : ℝ))
          (fun x : ℝ => x ^ n) (by norm_num) b) using 1 <;>
        simp only [smul_eq_mul] <;> ring
    rw [intervalIntegral.integral_add
      ((by
        fun_prop : Continuous (fun x : ℝ => (x / 2) ^ n)).intervalIntegrable 0 b)
      ((by
        fun_prop : Continuous (fun x : ℝ => (b - x / 2) ^ n)).intervalIntegrable 0 b),
      hfirst, hsecond]
    linarith

  have integrate_quartic (b c0 c1 c2 c3 c4 : ℝ) :
      (∫ x in (0 : ℝ)..b,
        c0 + (c1 * x + (c2 * x ^ 2 + (c3 * x ^ 3 + c4 * x ^ 4)))) =
        c0 * b + c1 * (∫ x in (0 : ℝ)..b, x) +
          c2 * (∫ x in (0 : ℝ)..b, x ^ 2) +
          c3 * (∫ x in (0 : ℝ)..b, x ^ 3) +
          c4 * (∫ x in (0 : ℝ)..b, x ^ 4) := by
    rw [intervalIntegral.integral_add
          (continuous_const.intervalIntegrable 0 b)
          ((by
            fun_prop : Continuous (fun x : ℝ =>
              c1 * x + (c2 * x ^ 2 + (c3 * x ^ 3 + c4 * x ^ 4)))).intervalIntegrable
                0 b),
        intervalIntegral.integral_add
          ((by
            fun_prop : Continuous (fun x : ℝ => c1 * x)).intervalIntegrable 0 b)
          ((by
            fun_prop : Continuous (fun x : ℝ =>
              c2 * x ^ 2 + (c3 * x ^ 3 + c4 * x ^ 4))).intervalIntegrable 0 b),
        intervalIntegral.integral_add
          ((by
            fun_prop : Continuous (fun x : ℝ => c2 * x ^ 2)).intervalIntegrable 0 b)
          ((by
            fun_prop : Continuous (fun x : ℝ =>
              c3 * x ^ 3 + c4 * x ^ 4)).intervalIntegrable 0 b),
        intervalIntegral.integral_add
          ((by
            fun_prop : Continuous (fun x : ℝ => c3 * x ^ 3)).intervalIntegrable 0 b)
          ((by
            fun_prop : Continuous (fun x : ℝ => c4 * x ^ 4)).intervalIntegrable 0 b),
        intervalIntegral.integral_const,
        intervalIntegral.integral_const_mul c1 (fun x : ℝ => x)]
    simp_rw [intervalIntegral.integral_const_mul]
    simp only [smul_eq_mul]
    ring

  have integral_first_power (b : ℝ) :
      (∫ x in (0 : ℝ)..b, x) = b ^ 2 / 2 := by
    have h := integral_recurrence 1 b
    have heval :
        (∫ x in (0 : ℝ)..b, ((x / 2) ^ 1 + (b - x / 2) ^ 1)) = b ^ 2 := by
      calc
        _ = ∫ x in (0 : ℝ)..b,
            b + ((0 : ℝ) * x + (0 * x ^ 2 + (0 * x ^ 3 + 0 * x ^ 4))) := by
              apply intervalIntegral.integral_congr
              intro x _
              ring
        _ = b ^ 2 := by
              rw [integrate_quartic]
              ring
    rw [heval] at h
    simp only [pow_one] at h
    linarith

  have integral_second_power (b : ℝ) :
      (∫ x in (0 : ℝ)..b, x ^ 2) = b ^ 3 / 3 := by
    have h := integral_recurrence 2 b
    have heval :
        (∫ x in (0 : ℝ)..b, ((x / 2) ^ 2 + (b - x / 2) ^ 2)) =
          b ^ 2 * b - b * (∫ x in (0 : ℝ)..b, x) +
            (1 / 2 : ℝ) * (∫ x in (0 : ℝ)..b, x ^ 2) := by
      calc
        _ = ∫ x in (0 : ℝ)..b,
            b ^ 2 + ((-b) * x + ((1 / 2 : ℝ) * x ^ 2 +
              (0 * x ^ 3 + 0 * x ^ 4))) := by
                apply intervalIntegral.integral_congr
                intro x _
                ring
        _ = _ := by
          rw [integrate_quartic]
          ring
    rw [heval, integral_first_power] at h
    linarith

  have integral_third_power (b : ℝ) :
      (∫ x in (0 : ℝ)..b, x ^ 3) = b ^ 4 / 4 := by
    have h := integral_recurrence 3 b
    have heval :
        (∫ x in (0 : ℝ)..b, ((x / 2) ^ 3 + (b - x / 2) ^ 3)) =
          b ^ 3 * b - (3 * b ^ 2 / 2) * (∫ x in (0 : ℝ)..b, x) +
            (3 * b / 4) * (∫ x in (0 : ℝ)..b, x ^ 2) := by
      calc
        _ = ∫ x in (0 : ℝ)..b,
            b ^ 3 + (-(3 * b ^ 2 / 2) * x +
              ((3 * b / 4) * x ^ 2 + (0 * x ^ 3 + 0 * x ^ 4))) := by
                apply intervalIntegral.integral_congr
                intro x _
                ring
        _ = _ := by
          rw [integrate_quartic]
          ring
    rw [heval, integral_first_power, integral_second_power] at h
    linarith

  have integral_fourth_power (b : ℝ) :
      (∫ x in (0 : ℝ)..b, x ^ 4) = b ^ 5 / 5 := by
    have h := integral_recurrence 4 b
    have heval :
        (∫ x in (0 : ℝ)..b, ((x / 2) ^ 4 + (b - x / 2) ^ 4)) =
          b ^ 4 * b - 2 * b ^ 3 * (∫ x in (0 : ℝ)..b, x) +
            (3 * b ^ 2 / 2) * (∫ x in (0 : ℝ)..b, x ^ 2) -
            (b / 2) * (∫ x in (0 : ℝ)..b, x ^ 3) +
            (1 / 8 : ℝ) * (∫ x in (0 : ℝ)..b, x ^ 4) := by
      calc
        _ = ∫ x in (0 : ℝ)..b,
            b ^ 4 + ((-2 * b ^ 3) * x +
              ((3 * b ^ 2 / 2) * x ^ 2 +
                ((-b / 2) * x ^ 3 + (1 / 8 : ℝ) * x ^ 4))) := by
                  apply intervalIntegral.integral_congr
                  intro x _
                  ring
        _ = _ := by
          rw [integrate_quartic]
          ring
    rw [heval, integral_first_power, integral_second_power,
      integral_third_power] at h
    linarith

  have quadratic_profile_integral (boxLength endpoint : ℝ) :
      (∫ x in (0 : ℝ)..endpoint, x ^ 2 * (boxLength - x) ^ 2) =
        boxLength ^ 2 * endpoint ^ 3 / 3 -
          boxLength * endpoint ^ 4 / 2 + endpoint ^ 5 / 5 := by
    calc
      (∫ x in (0 : ℝ)..endpoint, x ^ 2 * (boxLength - x) ^ 2) =
          ∫ x in (0 : ℝ)..endpoint,
            0 + (0 * x + (boxLength ^ 2 * x ^ 2 +
              ((-2 * boxLength) * x ^ 3 + 1 * x ^ 4))) := by
                apply intervalIntegral.integral_congr
                intro x _
                ring
      _ = _ := by
        rw [integrate_quartic, integral_second_power, integral_third_power,
          integral_fourth_power]
        ring

  let unit : LengthUnit := LengthUnit.meters
  let boxLength : ℝ := lengthReadout unit setup.figure.wallSeparation
  let coefficient : ℂ :=
    coefficientReadout unit setup.normalizationCoefficient
  have hboxLength : 0 < boxLength :=
    h_figure.wallSeparationIsPositive unit
  have horigin :
      positionReadout unit setup.figure.origin = 0 :=
    h_figure.originCoordinate unit
  have hright :
      positionReadout unit setup.figure.rightWall = boxLength :=
    h_figure.rightWallCoordinate unit
  have honeThird :
      positionReadout unit setup.figure.oneThirdMark = boxLength / 3 :=
    h_figure.oneThirdCoordinate unit

  have amplitude_normSq (x : ℝ) (hx0 : 0 ≤ x) (hxbox : x ≤ boxLength) :
      Complex.normSq
          (waveAmplitudeReadout unit
            (setup.state.waveAmplitudeAt (positionFromReadout unit x))) =
        Complex.normSq coefficient * (x ^ 2 * (boxLength - x) ^ 2) := by
    have hxorigin :
        positionReadout unit setup.figure.origin ≤ x := by
      rw [horigin]
      exact hx0
    have hxright :
        x ≤ positionReadout unit setup.figure.rightWall := by
      rw [hright]
      exact hxbox
    rw [h_profile unit x hxorigin hxright, Complex.normSq_mul,
      Complex.normSq_mul, Complex.normSq_ofReal, Complex.normSq_ofReal,
      horigin, hright]
    change
      Complex.normSq coefficient * ((x - 0) * (x - 0)) *
          ((boxLength - x) * (boxLength - x)) =
        Complex.normSq coefficient * (x ^ 2 * (boxLength - x) ^ 2)
    ring

  have normalized_polynomial :
      (∫ x in (0 : ℝ)..boxLength,
        Complex.normSq coefficient * (x ^ 2 * (boxLength - x) ^ 2)) = 1 := by
    calc
      _ = ∫ x in (0 : ℝ)..boxLength,
          Complex.normSq
            (waveAmplitudeReadout unit
              (setup.state.waveAmplitudeAt (positionFromReadout unit x))) := by
                apply intervalIntegral.integral_congr
                intro x hx
                rw [Set.uIcc_of_le hboxLength.le] at hx
                exact (amplitude_normSq x hx.1 hx.2).symm
      _ = ∫ x in positionReadout unit setup.figure.origin..
          positionReadout unit setup.figure.rightWall,
          Complex.normSq
            (waveAmplitudeReadout unit
              (setup.state.waveAmplitudeAt (positionFromReadout unit x))) := by
                rw [horigin, hright]
      _ = 1 := h_normalized unit

  have normalized_coefficient :
      Complex.normSq coefficient * (boxLength ^ 5 / 30) = 1 := by
    calc
      _ = Complex.normSq coefficient *
          (∫ x in (0 : ℝ)..boxLength, x ^ 2 * (boxLength - x) ^ 2) := by
            rw [quadratic_profile_integral]
            ring
      _ = ∫ x in (0 : ℝ)..boxLength,
          Complex.normSq coefficient * (x ^ 2 * (boxLength - x) ^ 2) := by
            rw [intervalIntegral.integral_const_mul]
      _ = 1 := normalized_polynomial

  have hordered :
      positionReadout unit setup.figure.origin ≤
        positionReadout unit setup.figure.oneThirdMark := by
    rw [horigin, honeThird]
    linarith
  calc
    setup.state.positionProbabilityBetween
        setup.figure.origin setup.figure.oneThirdMark =
        ∫ x in positionReadout unit setup.figure.origin..
            positionReadout unit setup.figure.oneThirdMark,
          Complex.normSq
            (waveAmplitudeReadout unit
              (setup.state.waveAmplitudeAt (positionFromReadout unit x))) :=
      h_born unit setup.figure.origin setup.figure.oneThirdMark hordered
    _ = ∫ x in (0 : ℝ)..boxLength / 3,
        Complex.normSq coefficient * (x ^ 2 * (boxLength - x) ^ 2) := by
          rw [horigin, honeThird]
          apply intervalIntegral.integral_congr
          intro x hx
          rw [Set.uIcc_of_le (by linarith : (0 : ℝ) ≤ boxLength / 3)] at hx
          apply amplitude_normSq x hx.1
          linarith [hx.2]
    _ = Complex.normSq coefficient *
        (boxLength ^ 2 * (boxLength / 3) ^ 3 / 3 -
          boxLength * (boxLength / 3) ^ 4 / 2 +
          (boxLength / 3) ^ 5 / 5) := by
            rw [intervalIntegral.integral_const_mul,
              quadratic_profile_integral]
    _ = (17 : ℝ) / 81 := by
      ring_nf at normalized_coefficient ⊢
      linarith

end PhyXMiniProblems.ProblemPhyXMini0550
