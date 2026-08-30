import ArchonPhysics.RandomMassTwoStepAnnealedTransferGrowth

/-!
# Obstruction to uniform two-step logarithmic drift

The positive two-step expectation of the invariant quadratic form does not
imply positive expected logarithmic growth.  At `λ = 1/2` and the vertical
direction, reflection of the frozen uniform mass about its mean pairs the
two logarithms into the logarithm of a number at most one.  Consequently the
two-step expected log ratio is nonpositive in this direction.

This rules out a direction-uniform positive two-step log drift.  The final
section records the projective-stationary data that a genuine Furstenberg
argument must construct next; it does not assert that such data exist or
that a Lyapunov exponent, EFC, or localization has been proved.
-/

open scoped Matrix

namespace ArchonPhysics.RandomMassTwoStepQuenchedLogObstruction

open ArchonPhysics
open ArchonPhysics.FrozenUniformMassMoments
open ArchonPhysics.RandomMassAndersonTransferBridge
open ArchonPhysics.RandomMassTwoStepAnnealedTransferGrowth
open ArchonPhysics.RandomMassWeakEnergyTransferGroundwork
open MeasureTheory Set

noncomputable section

/-- General independent two-step logarithmic quadratic-form drift. -/
def independentTwoStepLogDrift
    (lambda : Real) (state : Fin 2 → Real) : Real :=
  ∫ mass0, ∫ mass1,
    Real.log
      (meanInvariantQuadratic lambda
          (twoStepTransferState lambda mass0 mass1 state) /
        meanInvariantQuadratic lambda state)
      ∂(RandomEnsemble.massCoordinateLaw)
    ∂(RandomEnsemble.massCoordinateLaw)

/-- The vertical unit direction used by the counterexample. -/
def verticalUnitState : Fin 2 → Real :=
  ![0, 1]

theorem verticalUnitState_ne_zero : verticalUnitState ≠ 0 := by
  intro hzero
  have h := congrFun hzero 1
  norm_num [verticalUnitState] at h

/-- At `λ = 1/2`, the two-step ratio in the vertical direction depends only
on the second centered mass. -/
def halfVerticalTwoStepRatio (mass : Real) : Real :=
  1 - (3 / 4 : Real) * centeredMass mass +
    (1 / 4 : Real) * centeredMass mass ^ 2

theorem half_vertical_twoStep_quadratic_ratio
    (mass0 mass1 : Real) :
    meanInvariantQuadratic (1 / 2 : Real)
        (twoStepTransferState (1 / 2 : Real) mass0 mass1
          verticalUnitState) /
      meanInvariantQuadratic (1 / 2 : Real) verticalUnitState =
        halfVerticalTwoStepRatio mass1 := by
  simp [twoStepTransferState, oneStepTransferState, verticalUnitState,
    meanInvariantQuadratic, andersonTransferMatrix,
    RandomMassAndersonTransferBridge.andersonDiagonalPotential,
    halfVerticalTwoStepRatio, centeredMass, Matrix.mulVec, dotProduct,
    Fin.sum_univ_two]
  ring

/-- The special ratio is globally positive, so its real logarithm is the
ordinary logarithm of a positive number. -/
theorem halfVerticalTwoStepRatio_pos (mass : Real) :
    0 < halfVerticalTwoStepRatio mass := by
  have hsquare : 0 ≤ (centeredMass mass - 3 / 2) ^ 2 := sq_nonneg _
  unfold halfVerticalTwoStepRatio
  nlinarith

/-- Exact reflection product for masses paired about their mean one. -/
theorem halfVerticalTwoStepRatio_mul_reflection (mass : Real) :
    halfVerticalTwoStepRatio mass * halfVerticalTwoStepRatio (2 - mass) =
      1 - centeredMass mass ^ 2 * (1 - centeredMass mass ^ 2) / 16 := by
  unfold halfVerticalTwoStepRatio centeredMass
  ring

/-- On the frozen support, the reflected product is at most one. -/
theorem halfVerticalTwoStepRatio_mul_reflection_le_one
    {mass : Real} (hmass : mass ∈ RandomEnsemble.massSupport) :
    halfVerticalTwoStepRatio mass * halfVerticalTwoStepRatio (2 - mass) ≤ 1 := by
  have habs :=
    abs_centeredMass_le_one_fifth_of_mem_massSupport hmass
  have hbounds := (abs_le.mp habs)
  have hfactorLeft : 0 ≤ (1 / 5 : Real) - centeredMass mass := by
    linarith
  have hfactorRight : 0 ≤ (1 / 5 : Real) + centeredMass mass := by
    linarith
  have hsquare : centeredMass mass ^ 2 ≤ (1 / 25 : Real) := by
    have hproduct := mul_nonneg hfactorLeft hfactorRight
    nlinarith
  have hone : 0 ≤ 1 - centeredMass mass ^ 2 := by
    linarith
  have hterm :
      0 ≤ centeredMass mass ^ 2 * (1 - centeredMass mass ^ 2) / 16 := by
    exact div_nonneg (mul_nonneg (sq_nonneg _) hone) (by norm_num)
  rw [halfVerticalTwoStepRatio_mul_reflection]
  linarith

/-- Each reflected logarithmic pair is nonpositive on the support. -/
theorem halfVerticalTwoStep_log_pair_nonpos
    {mass : Real} (hmass : mass ∈ RandomEnsemble.massSupport) :
    Real.log (halfVerticalTwoStepRatio mass) +
        Real.log (halfVerticalTwoStepRatio (2 - mass)) ≤ 0 := by
  have hleft := halfVerticalTwoStepRatio_pos mass
  have hright := halfVerticalTwoStepRatio_pos (2 - mass)
  rw [← Real.log_mul hleft.ne' hright.ne']
  exact Real.log_nonpos (mul_nonneg hleft.le hright.le)
    (halfVerticalTwoStepRatio_mul_reflection_le_one hmass)

theorem continuous_halfVerticalTwoStep_logRatio :
    Continuous (fun mass => Real.log (halfVerticalTwoStepRatio mass)) := by
  have hratio : Continuous halfVerticalTwoStepRatio := by
    unfold halfVerticalTwoStepRatio centeredMass
    fun_prop
  exact hratio.log fun mass => (halfVerticalTwoStepRatio_pos mass).ne'

/-- Reflection about one preserves the oriented frozen-support integral. -/
theorem intervalIntegral_halfVerticalTwoStep_logRatio_reflection :
    (∫ mass in RandomEnsemble.massLower..RandomEnsemble.massUpper,
      Real.log (halfVerticalTwoStepRatio (2 - mass))) =
    ∫ mass in RandomEnsemble.massLower..RandomEnsemble.massUpper,
      Real.log (halfVerticalTwoStepRatio mass) := by
  have h := intervalIntegral.integral_comp_sub_left
    (a := RandomEnsemble.massLower)
    (b := RandomEnsemble.massUpper)
    (fun mass => Real.log (halfVerticalTwoStepRatio mass)) 2
  convert h using 1;
    norm_num [RandomEnsemble.massLower, RandomEnsemble.massUpper]

/-- The reflected logarithmic pairing makes the frozen interval integral
nonpositive. -/
theorem intervalIntegral_halfVerticalTwoStep_logRatio_nonpos :
    (∫ mass in RandomEnsemble.massLower..RandomEnsemble.massUpper,
      Real.log (halfVerticalTwoStepRatio mass)) ≤ 0 := by
  have hbase : IntervalIntegrable
      (fun mass => Real.log (halfVerticalTwoStepRatio mass))
      volume RandomEnsemble.massLower RandomEnsemble.massUpper :=
    continuous_halfVerticalTwoStep_logRatio.intervalIntegrable _ _
  have hreflected : IntervalIntegrable
      (fun mass => Real.log (halfVerticalTwoStepRatio (2 - mass)))
      volume RandomEnsemble.massLower RandomEnsemble.massUpper :=
    (continuous_halfVerticalTwoStep_logRatio.comp
      (continuous_const.sub continuous_id)).intervalIntegrable _ _
  have hpair : IntervalIntegrable
      (fun mass => Real.log (halfVerticalTwoStepRatio mass) +
        Real.log (halfVerticalTwoStepRatio (2 - mass)))
      volume RandomEnsemble.massLower RandomEnsemble.massUpper :=
    hbase.add hreflected
  have hpair_nonpos :
      (∫ mass in RandomEnsemble.massLower..RandomEnsemble.massUpper,
        (Real.log (halfVerticalTwoStepRatio mass) +
          Real.log (halfVerticalTwoStepRatio (2 - mass)))) ≤ 0 := by
    have hmono := intervalIntegral.integral_mono_on
      RandomEnsemble.massLower_le_massUpper hpair intervalIntegrable_const
      (fun mass hmass =>
        halfVerticalTwoStep_log_pair_nonpos
          (show mass ∈ RandomEnsemble.massSupport from hmass))
    simpa using hmono
  rw [intervalIntegral.integral_add hbase hreflected,
    intervalIntegral_halfVerticalTwoStep_logRatio_reflection] at hpair_nonpos
  linarith

/-- The one-mass logarithmic expectation in the obstructing direction is
nonpositive under the actual normalized frozen law. -/
theorem integral_halfVerticalTwoStep_logRatio_nonpos :
    (∫ mass, Real.log (halfVerticalTwoStepRatio mass)
      ∂(RandomEnsemble.massCoordinateLaw)) ≤ 0 := by
  rw [integral_massCoordinateLaw_eq_normalized_setIntegral,
    integral_massSupport_eq_intervalIntegral]
  exact mul_nonpos_of_nonneg_of_nonpos (by norm_num)
    intervalIntegral_halfVerticalTwoStep_logRatio_nonpos

/-- The actual two-step logarithmic drift is nonpositive at `λ = 1/2` in
the vertical direction. -/
theorem independentTwoStepLogDrift_half_vertical_nonpos :
    independentTwoStepLogDrift (1 / 2 : Real) verticalUnitState ≤ 0 := by
  have heq : independentTwoStepLogDrift (1 / 2 : Real) verticalUnitState =
      ∫ mass, Real.log (halfVerticalTwoStepRatio mass)
        ∂(RandomEnsemble.massCoordinateLaw) := by
    unfold independentTwoStepLogDrift
    simp_rw [half_vertical_twoStep_quadratic_ratio]
    simp
  rw [heq]
  exact integral_halfVerticalTwoStep_logRatio_nonpos

/-- Therefore a positive two-step expected log drift cannot hold uniformly
over all nonzero directions throughout `0 < λ ≤ 1`. -/
theorem not_forall_independentTwoStepLogDrift_pos :
    ¬(∀ lambda : Real, 0 < lambda → lambda ≤ 1 →
      ∀ state : Fin 2 → Real, state ≠ 0 →
        0 < independentTwoStepLogDrift lambda state) := by
  intro huniform
  have hpositive := huniform (1 / 2 : Real) (by norm_num) (by norm_num)
    verticalUnitState verticalUnitState_ne_zero
  exact (not_lt_of_ge independentTwoStepLogDrift_half_vertical_nonpos)
    hpositive

/-! ## Honest next projective-stationary interface -/

/-- The actual one-step logarithmic cocycle evaluated on supplied direction
representatives. -/
def transferLogCocycle
    {Direction : Type*} (lambda : Real)
    (representative : Direction → Fin 2 → Real)
    (sample : Real × Direction) : Real :=
  Real.log
    (meanInvariantQuadratic lambda
        (oneStepTransferState lambda sample.1 (representative sample.2)) /
      meanInvariantQuadratic lambda (representative sample.2))

/-- Data that a projective-stationary Furstenberg route must genuinely
construct.  Positivity is deliberately not a field of this structure. -/
structure ProjectiveStationaryData
    (lambda : Real) (Direction : Type*) [MeasurableSpace Direction] where
  directionLaw : Measure Direction
  probability_univ : directionLaw Set.univ = 1
  representative : Direction → Fin 2 → Real
  representative_measurable : Measurable representative
  representative_unit :
    ∀ direction, meanInvariantQuadratic lambda (representative direction) = 1
  action : Real → Direction → Direction
  action_measurable : Measurable fun sample : Real × Direction =>
    action sample.1 sample.2
  action_represents : ∀ mass direction,
    ∃ scale : Real, scale ≠ 0 ∧
      representative (action mass direction) =
        scale • oneStepTransferState lambda mass (representative direction)
  stationary :
    Measure.map (fun sample : Real × Direction => action sample.1 sample.2)
        (RandomEnsemble.massCoordinateLaw.prod directionLaw) =
      directionLaw
  cocycle_integrable :
    Integrable (transferLogCocycle lambda representative)
      (RandomEnsemble.massCoordinateLaw.prod directionLaw)

/-- Furstenberg's remaining positivity target for supplied stationary
projective data. -/
def HasPositiveProjectiveLogDrift
    {lambda : Real} {Direction : Type*} [MeasurableSpace Direction]
    (data : ProjectiveStationaryData lambda Direction) : Prop :=
  0 < ∫ sample, transferLogCocycle lambda data.representative sample
    ∂(RandomEnsemble.massCoordinateLaw.prod data.directionLaw)

end

end ArchonPhysics.RandomMassTwoStepQuenchedLogObstruction
