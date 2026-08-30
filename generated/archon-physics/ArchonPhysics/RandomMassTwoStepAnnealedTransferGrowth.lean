import ArchonPhysics.RandomMassWeakEnergyTransferGroundwork

/-!
# Two-step annealed transfer growth

For two independent masses with the frozen `Uniform[4/5, 6/5]` law, this
module computes the exact expectation of the invariant quadratic form after
two transfer steps.  In the range `0 < λ ≤ 1`, it gives a direction-uniform
lower bound with factor `1 + λ² / 150`.

The expectation is written as an explicit iterated integral, i.e. integration
against the two independent coordinate laws.  This is annealed second-moment
growth only; it is not quenched logarithmic growth, a Lyapunov-exponent
theorem, EFC, or localization.
-/

open scoped Matrix

namespace ArchonPhysics.RandomMassTwoStepAnnealedTransferGrowth

open ArchonPhysics
open ArchonPhysics.RandomMassAndersonTransferBridge
open ArchonPhysics.RandomMassWeakEnergyTransferGroundwork
open MeasureTheory

noncomputable section

/-- One transfer step acting on a two-component state. -/
def oneStepTransferState (lambda mass : Real) (state : Fin 2 → Real) :
    Fin 2 → Real :=
  Matrix.mulVec (andersonTransferMatrix lambda mass) state

/-- Two ordered steps, first with `mass0` and then with `mass1`. -/
def twoStepTransferState (lambda mass0 mass1 : Real)
    (state : Fin 2 → Real) : Fin 2 → Real :=
  oneStepTransferState lambda mass1
    (oneStepTransferState lambda mass0 state)

/-- Independent two-mass annealed expectation, written without hiding the
two coordinate integrations. -/
def independentTwoStepQuadraticExpectation
    (lambda : Real) (state : Fin 2 → Real) : Real :=
  ∫ mass0, ∫ mass1,
    meanInvariantQuadratic lambda
      (twoStepTransferState lambda mass0 mass1 state)
      ∂(RandomEnsemble.massCoordinateLaw)
    ∂(RandomEnsemble.massCoordinateLaw)

/-- A centered mass is uniformly bounded by `1/5` on the frozen support. -/
theorem abs_centeredMass_le_one_fifth_of_mem_massSupport
    {mass : Real} (hmass : mass ∈ RandomEnsemble.massSupport) :
    |centeredMass mass| ≤ (1 / 5 : Real) := by
  change RandomEnsemble.massLower ≤ mass ∧
    mass ≤ RandomEnsemble.massUpper at hmass
  rw [abs_le]
  constructor
  · norm_num [centeredMass, RandomEnsemble.massLower] at hmass ⊢
    linarith [hmass.1]
  · norm_num [centeredMass, RandomEnsemble.massUpper] at hmass ⊢
    linarith [hmass.2]

/-- Uniform bound for the sole centered random transfer coefficient. -/
theorem abs_centeredTransferCoefficient_le
    (lambda : Real) {mass : Real}
    (hmass : mass ∈ RandomEnsemble.massSupport) :
    |centeredTransferCoefficient lambda mass| ≤ |lambda| / 5 := by
  simp only [centeredTransferCoefficient, abs_mul, abs_neg]
  calc
    |lambda| * |centeredMass mass| ≤ |lambda| * (1 / 5 : Real) :=
      mul_le_mul_of_nonneg_left
        (abs_centeredMass_le_one_fifth_of_mem_massSupport hmass)
        (abs_nonneg lambda)
    _ = |lambda| / 5 := by ring

/-- The centered coefficient is integrable under the frozen mass law. -/
theorem integrable_centeredTransferCoefficient_massCoordinateLaw
    (lambda : Real) :
    Integrable (centeredTransferCoefficient lambda)
      RandomEnsemble.massCoordinateLaw := by
  apply Integrable.of_bound
    (measurable_centeredTransferCoefficient lambda).aestronglyMeasurable
    (|lambda| / 5)
  filter_upwards [RandomEnsemble.massCoordinate_mem_support_ae]
    with mass hmass
  simpa only [Real.norm_eq_abs] using
    abs_centeredTransferCoefficient_le lambda hmass

/-- Its square is integrable as well. -/
theorem integrable_centeredTransferCoefficient_sq_massCoordinateLaw
    (lambda : Real) :
    Integrable (fun mass => centeredTransferCoefficient lambda mass ^ 2)
      RandomEnsemble.massCoordinateLaw := by
  apply Integrable.of_bound
    (Measurable.aestronglyMeasurable
      ((measurable_centeredTransferCoefficient lambda).pow_const 2))
    ((|lambda| / 5) ^ 2)
  filter_upwards [RandomEnsemble.massCoordinate_mem_support_ae]
    with mass hmass
  have hbound := abs_centeredTransferCoefficient_le lambda hmass
  have hleft : 0 ≤ |centeredTransferCoefficient lambda mass| :=
    abs_nonneg _
  have hright : 0 ≤ |lambda| / 5 := by positivity
  rw [Real.norm_eq_abs, abs_pow]
  nlinarith

/-- The first component is the mean step plus the centered scalar entry. -/
theorem oneStepTransferState_apply_zero
    (lambda mass : Real) (state : Fin 2 → Real) :
    oneStepTransferState lambda mass state 0 =
      ((2 - lambda) * state 0 - state 1) +
        centeredTransferCoefficient lambda mass * state 0 := by
  simp [oneStepTransferState, andersonTransferMatrix,
    andersonDiagonalPotential, centeredTransferCoefficient, centeredMass,
    Matrix.mulVec, dotProduct, Fin.sum_univ_two]
  ring

/-- The second component after one step is the old first component. -/
theorem oneStepTransferState_apply_one
    (lambda mass : Real) (state : Fin 2 → Real) :
    oneStepTransferState lambda mass state 1 = state 0 := by
  simp [oneStepTransferState, andersonTransferMatrix,
    Matrix.mulVec, dotProduct, Fin.sum_univ_two]

/-- Exact pointwise expansion of the invariant form after one random step. -/
theorem meanInvariantQuadratic_oneStep_expansion
    (lambda mass : Real) (state : Fin 2 → Real) :
    meanInvariantQuadratic lambda
        (oneStepTransferState lambda mass state) =
      (meanInvariantQuadratic lambda state +
        (state 0 * ((2 - lambda) * state 0 - 2 * state 1)) *
          centeredTransferCoefficient lambda mass) +
        state 0 ^ 2 * centeredTransferCoefficient lambda mass ^ 2 := by
  rw [meanInvariantQuadratic, oneStepTransferState_apply_zero,
    oneStepTransferState_apply_one]
  simp only [meanInvariantQuadratic]
  ring

/-- Exact pointwise expansion of the squared outgoing first component. -/
theorem oneStepTransferState_apply_zero_sq_expansion
    (lambda mass : Real) (state : Fin 2 → Real) :
    oneStepTransferState lambda mass state 0 ^ 2 =
      (((2 - lambda) * state 0 - state 1) ^ 2 +
        (2 * ((2 - lambda) * state 0 - state 1) * state 0) *
          centeredTransferCoefficient lambda mass) +
        state 0 ^ 2 * centeredTransferCoefficient lambda mass ^ 2 := by
  rw [oneStepTransferState_apply_zero]
  ring

/-- Integrability companion for the one-step quadratic-form expansion. -/
theorem integrable_meanInvariantQuadratic_oneStep
    (lambda : Real) (state : Fin 2 → Real) :
    Integrable (fun mass => meanInvariantQuadratic lambda
      (oneStepTransferState lambda mass state))
      RandomEnsemble.massCoordinateLaw := by
  have hlinear :=
    (integrable_centeredTransferCoefficient_massCoordinateLaw lambda).const_mul
      (state 0 * ((2 - lambda) * state 0 - 2 * state 1))
  have hquadratic :=
    (integrable_centeredTransferCoefficient_sq_massCoordinateLaw lambda).const_mul
      (state 0 ^ 2)
  have hpoly := ((integrable_const
    (meanInvariantQuadratic lambda state)).add hlinear).add hquadratic
  exact hpoly.congr (Filter.Eventually.of_forall fun mass =>
    (meanInvariantQuadratic_oneStep_expansion lambda mass state).symm)

/-- Integrability companion for the squared first component. -/
theorem integrable_oneStepTransferState_apply_zero_sq
    (lambda : Real) (state : Fin 2 → Real) :
    Integrable (fun mass => oneStepTransferState lambda mass state 0 ^ 2)
      RandomEnsemble.massCoordinateLaw := by
  have hlinear :=
    (integrable_centeredTransferCoefficient_massCoordinateLaw lambda).const_mul
      (2 * ((2 - lambda) * state 0 - state 1) * state 0)
  have hquadratic :=
    (integrable_centeredTransferCoefficient_sq_massCoordinateLaw lambda).const_mul
      (state 0 ^ 2)
  have hpoly := ((integrable_const
    (((2 - lambda) * state 0 - state 1) ^ 2)).add hlinear).add
      hquadratic
  exact hpoly.congr (Filter.Eventually.of_forall fun mass =>
    (oneStepTransferState_apply_zero_sq_expansion lambda mass state).symm)

/-- Exact one-step annealed quadratic-form identity. -/
theorem integral_meanInvariantQuadratic_oneStep
    (lambda : Real) (state : Fin 2 → Real) :
    (∫ mass, meanInvariantQuadratic lambda
        (oneStepTransferState lambda mass state)
        ∂(RandomEnsemble.massCoordinateLaw)) =
      meanInvariantQuadratic lambda state + lambda ^ 2 / 75 * state 0 ^ 2 := by
  have hlinear :=
    (integrable_centeredTransferCoefficient_massCoordinateLaw lambda).const_mul
      (state 0 * ((2 - lambda) * state 0 - 2 * state 1))
  have hquadratic :=
    (integrable_centeredTransferCoefficient_sq_massCoordinateLaw lambda).const_mul
      (state 0 ^ 2)
  calc
    (∫ mass, meanInvariantQuadratic lambda
        (oneStepTransferState lambda mass state)
        ∂(RandomEnsemble.massCoordinateLaw)) =
      ∫ mass, (meanInvariantQuadratic lambda state +
        (state 0 * ((2 - lambda) * state 0 - 2 * state 1)) *
          centeredTransferCoefficient lambda mass) +
        state 0 ^ 2 * centeredTransferCoefficient lambda mass ^ 2
        ∂(RandomEnsemble.massCoordinateLaw) :=
      integral_congr_ae (Filter.Eventually.of_forall fun mass =>
        meanInvariantQuadratic_oneStep_expansion lambda mass state)
    _ = (∫ mass, meanInvariantQuadratic lambda state +
          (state 0 * ((2 - lambda) * state 0 - 2 * state 1)) *
            centeredTransferCoefficient lambda mass
          ∂(RandomEnsemble.massCoordinateLaw)) +
        ∫ mass, state 0 ^ 2 *
          centeredTransferCoefficient lambda mass ^ 2
          ∂(RandomEnsemble.massCoordinateLaw) :=
      integral_add
        ((integrable_const (meanInvariantQuadratic lambda state)).add hlinear)
        hquadratic
    _ = ((∫ mass, meanInvariantQuadratic lambda state
          ∂(RandomEnsemble.massCoordinateLaw)) +
        ∫ mass,
          (state 0 * ((2 - lambda) * state 0 - 2 * state 1)) *
            centeredTransferCoefficient lambda mass
          ∂(RandomEnsemble.massCoordinateLaw)) +
        ∫ mass, state 0 ^ 2 * centeredTransferCoefficient lambda mass ^ 2
          ∂(RandomEnsemble.massCoordinateLaw) := by
      rw [integral_add (integrable_const _) hlinear]
    _ = _ := by
      rw [integral_const_mul, integral_const_mul,
        integral_centeredTransferCoefficient_massCoordinateLaw,
        integral_centeredTransferCoefficient_sq_massCoordinateLaw]
      simp
      ring

/-- Exact one-step expectation of the squared outgoing first component. -/
theorem integral_oneStepTransferState_apply_zero_sq
    (lambda : Real) (state : Fin 2 → Real) :
    (∫ mass, oneStepTransferState lambda mass state 0 ^ 2
        ∂(RandomEnsemble.massCoordinateLaw)) =
      ((2 - lambda) * state 0 - state 1) ^ 2 +
        lambda ^ 2 / 75 * state 0 ^ 2 := by
  have hlinear :=
    (integrable_centeredTransferCoefficient_massCoordinateLaw lambda).const_mul
      (2 * ((2 - lambda) * state 0 - state 1) * state 0)
  have hquadratic :=
    (integrable_centeredTransferCoefficient_sq_massCoordinateLaw lambda).const_mul
      (state 0 ^ 2)
  calc
    (∫ mass, oneStepTransferState lambda mass state 0 ^ 2
        ∂(RandomEnsemble.massCoordinateLaw)) =
      ∫ mass, (((2 - lambda) * state 0 - state 1) ^ 2 +
        (2 * ((2 - lambda) * state 0 - state 1) * state 0) *
          centeredTransferCoefficient lambda mass) +
        state 0 ^ 2 * centeredTransferCoefficient lambda mass ^ 2
        ∂(RandomEnsemble.massCoordinateLaw) :=
      integral_congr_ae (Filter.Eventually.of_forall fun mass =>
        oneStepTransferState_apply_zero_sq_expansion lambda mass state)
    _ = (∫ mass, ((2 - lambda) * state 0 - state 1) ^ 2 +
          (2 * ((2 - lambda) * state 0 - state 1) * state 0) *
            centeredTransferCoefficient lambda mass
          ∂(RandomEnsemble.massCoordinateLaw)) +
        ∫ mass, state 0 ^ 2 * centeredTransferCoefficient lambda mass ^ 2
          ∂(RandomEnsemble.massCoordinateLaw) :=
      integral_add ((integrable_const _).add hlinear) hquadratic
    _ = ((∫ mass, ((2 - lambda) * state 0 - state 1) ^ 2
          ∂(RandomEnsemble.massCoordinateLaw)) +
        ∫ mass,
          (2 * ((2 - lambda) * state 0 - state 1) * state 0) *
            centeredTransferCoefficient lambda mass
          ∂(RandomEnsemble.massCoordinateLaw)) +
        ∫ mass, state 0 ^ 2 * centeredTransferCoefficient lambda mass ^ 2
          ∂(RandomEnsemble.massCoordinateLaw) := by
      rw [integral_add (integrable_const _) hlinear]
    _ = _ := by
      rw [integral_const_mul, integral_const_mul,
        integral_centeredTransferCoefficient_massCoordinateLaw,
        integral_centeredTransferCoefficient_sq_massCoordinateLaw]
      simp
      ring

/-- Exact two-step independent annealed expectation. -/
theorem independentTwoStepQuadraticExpectation_eq
    (lambda : Real) (state : Fin 2 → Real) :
    independentTwoStepQuadraticExpectation lambda state =
      meanInvariantQuadratic lambda state +
        (lambda ^ 2 / 75) *
          (state 0 ^ 2 + ((2 - lambda) * state 0 - state 1) ^ 2) +
        (lambda ^ 4 / 5625) * state 0 ^ 2 := by
  have hquadratic :=
    integrable_meanInvariantQuadratic_oneStep lambda state
  have hfirst :=
    integrable_oneStepTransferState_apply_zero_sq lambda state
  unfold independentTwoStepQuadraticExpectation twoStepTransferState
  calc
    (∫ mass0, ∫ mass1,
      meanInvariantQuadratic lambda
        (oneStepTransferState lambda mass1
          (oneStepTransferState lambda mass0 state))
        ∂(RandomEnsemble.massCoordinateLaw)
      ∂(RandomEnsemble.massCoordinateLaw)) =
      ∫ mass0, (meanInvariantQuadratic lambda
          (oneStepTransferState lambda mass0 state) +
        lambda ^ 2 / 75 *
          oneStepTransferState lambda mass0 state 0 ^ 2)
        ∂(RandomEnsemble.massCoordinateLaw) :=
      integral_congr_ae (Filter.Eventually.of_forall fun mass0 =>
        integral_meanInvariantQuadratic_oneStep lambda
          (oneStepTransferState lambda mass0 state))
    _ = (∫ mass0, meanInvariantQuadratic lambda
          (oneStepTransferState lambda mass0 state)
          ∂(RandomEnsemble.massCoordinateLaw)) +
        ∫ mass0, lambda ^ 2 / 75 *
          oneStepTransferState lambda mass0 state 0 ^ 2
          ∂(RandomEnsemble.massCoordinateLaw) :=
      integral_add hquadratic (hfirst.const_mul (lambda ^ 2 / 75))
    _ = _ := by
      rw [integral_const_mul,
        integral_meanInvariantQuadratic_oneStep,
        integral_oneStepTransferState_apply_zero_sq]
      ring

/-- The two Euclidean squares generated by the mean step dominate half of
the invariant quadratic form uniformly for `0 ≤ λ ≤ 1`. -/
theorem meanInvariantQuadratic_le_two_mul_stepSquares
    {lambda : Real} (hlambda_nonneg : 0 ≤ lambda) (hlambda_one : lambda ≤ 1)
    (state : Fin 2 → Real) :
    meanInvariantQuadratic lambda state ≤
      2 * (state 0 ^ 2 + ((2 - lambda) * state 0 - state 1) ^ 2) := by
  let a : Real := 2 - lambda
  let x : Real := state 0
  let u : Real := a * state 0 - state 1
  have hform : meanInvariantQuadratic lambda state =
      u ^ 2 - a * u * x + x ^ 2 := by
    dsimp [u, a, x, meanInvariantQuadratic]
    ring
  have ha_lower : 0 ≤ 2 - a := by
    dsimp [a]
    linarith
  have ha_upper : 0 ≤ 2 + a := by
    dsimp [a]
    linarith
  have hminus : 0 ≤ (2 - a) * (u - x) ^ 2 :=
    mul_nonneg ha_lower (sq_nonneg _)
  have hplus : 0 ≤ (2 + a) * (u + x) ^ 2 :=
    mul_nonneg ha_upper (sq_nonneg _)
  rw [hform]
  dsimp [u, x]
  nlinarith

/-- Direction-uniform two-step annealed second-moment growth for
`0 < λ ≤ 1`. -/
theorem independentTwoStepQuadraticExpectation_lower
    {lambda : Real} (hlambda_pos : 0 < lambda) (hlambda_one : lambda ≤ 1)
    (state : Fin 2 → Real) :
    (1 + lambda ^ 2 / 150) * meanInvariantQuadratic lambda state ≤
      independentTwoStepQuadraticExpectation lambda state := by
  rw [independentTwoStepQuadraticExpectation_eq]
  have hstep := meanInvariantQuadratic_le_two_mul_stepSquares
    hlambda_pos.le hlambda_one state
  have hscaled := mul_le_mul_of_nonneg_left hstep (sq_nonneg lambda)
  have hgrowth :
      lambda ^ 2 / 150 * meanInvariantQuadratic lambda state ≤
        lambda ^ 2 / 75 *
          (state 0 ^ 2 + ((2 - lambda) * state 0 - state 1) ^ 2) := by
    nlinarith
  have hextra : 0 ≤ lambda ^ 4 / 5625 * state 0 ^ 2 := by
    positivity
  linarith

end

end ArchonPhysics.RandomMassTwoStepAnnealedTransferGrowth
