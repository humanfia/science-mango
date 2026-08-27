import ArchonPhysics.ResonantThreeWaveKineticLInfinityPositivePicard

/-!
# Integrating-factor positivity for the unclipped L-infinity collision field

The canonical collision field is quasipositive, not everywhere positive on
the nonnegative cone.  On a norm ball of radius `R`, adding the scalar loss
rate `2 g^2 R` makes it positive.  The time-dependent integrating-factor
field below packages this observation in the form required by a forward
Picard construction.
-/

namespace ArchonPhysics.ResonantThreeWaveKineticLInfinityIntegratingFactor

open Filter Function MeasureTheory Metric Set
open ArchonPhysics.ResonantThreeWaveMeasure
open ArchonPhysics.ResonantThreeWaveKineticLInfinityLocalWellposedness
open ArchonPhysics.ResonantThreeWaveKineticLInfinityPositivePicard
open ArchonPhysics.ResonantThreeWaveKineticLInfinityPositiveContinuation
open scoped ENNReal NNReal MeasureTheory Topology

noncomputable section

variable {Mode : Type*} [MeasurableSpace Mode]

/-- Uniform loss rate on the canonical origin ball of radius `radius`. -/
def dampingRate (g radius : Real) : Real :=
  2 * g ^ 2 * radius

/-- The exponentially damped state used to conjugate the collision ODE. -/
def dampedState
    (collision : ResonantThreeWaveMeasure Mode)
    (g radius t : Real) (action : CanonicalLInfinity collision) :
    CanonicalLInfinity collision :=
  Real.exp (-(dampingRate g radius * t)) • action

/-- The integrating-factor conjugate of the genuine unclipped collision
field.  If `y(t)` solves this equation then
`exp (-lambda t) y(t)` solves the original equation. -/
def integratingFactorField
    (collision : ResonantThreeWaveMeasure Mode)
    (g radius : Real) :
    Real → CanonicalLInfinity collision → CanonicalLInfinity collision :=
  fun t action ↦
    Real.exp (dampingRate g radius * t) •
        rnCollisionVectorField collision g
          (dampedState collision g radius t action) +
      dampingRate g radius • action

theorem dampingRate_nonnegative
    (g radius : Real) (hradius : 0 ≤ radius) :
    0 ≤ dampingRate g radius := by
  unfold dampingRate
  positivity

theorem exp_damping_mul_exp_neg_damping
    (g radius t : Real) :
    Real.exp (dampingRate g radius * t) *
        Real.exp (-(dampingRate g radius * t)) = 1 := by
  rw [← Real.exp_add]
  simp

theorem dampedState_nonnegative
    (collision : ResonantThreeWaveMeasure Mode)
    (g radius t : Real) {action : CanonicalLInfinity collision}
    (haction : 0 ≤ action) :
    0 ≤ dampedState collision g radius t action := by
  exact smul_nonneg (Real.exp_pos _).le haction

theorem norm_dampedState_le
    (collision : ResonantThreeWaveMeasure Mode)
    (g radius t : Real) (hradius : 0 ≤ radius) (ht : 0 ≤ t)
    (action : CanonicalLInfinity collision) :
    ‖dampedState collision g radius t action‖ ≤ ‖action‖ := by
  rw [dampedState, norm_smul, Real.norm_eq_abs,
    abs_of_pos (Real.exp_pos _)]
  have hexponent : -(dampingRate g radius * t) ≤ 0 := by
    have := mul_nonneg (dampingRate_nonnegative g radius hradius) ht
    linarith
  have hexp : Real.exp (-(dampingRate g radius * t)) ≤ 1 := by
    simpa using (Real.exp_le_one_iff.mpr hexponent)
  exact mul_le_of_le_one_left (norm_nonneg action) hexp

/-- On a forward time interval and inside the origin ball of radius `radius`,
the integrating-factor field maps the nonnegative cone into itself.  This is
the exact ordered-Banach form of collision quasipositivity used by Picard. -/
theorem integratingFactorField_nonnegative
    (collision : ResonantThreeWaveMeasure Mode)
    (g radius t : Real) (hradius : 0 ≤ radius) (ht : 0 ≤ t)
    (action : CanonicalLInfinity collision)
    (hactionNorm : ‖action‖ ≤ radius) (haction : 0 ≤ action) :
    0 ≤ integratingFactorField collision g radius t action := by
  let rate := dampingRate g radius
  let z := dampedState collision g radius t action
  let ep := Real.exp (rate * t)
  have hz : 0 ≤ z := dampedState_nonnegative collision g radius t haction
  have hzNorm : ‖z‖ ≤ radius :=
    (norm_dampedState_le collision g radius t hradius ht action).trans hactionNorm
  have hquasi := collisionMap_add_two_mul_nonnegative collision z hz
  have hmain : 0 ≤ (ep * g ^ 2) •
      (collisionMap collision z + (2 * ‖z‖) • z) :=
    smul_nonneg (mul_nonneg (Real.exp_nonneg _) (sq_nonneg g)) hquasi
  have hextraCoefficient : 0 ≤ 2 * g ^ 2 * (radius - ‖z‖) := by
    positivity
  have hextra : 0 ≤ (2 * g ^ 2 * (radius - ‖z‖)) • action :=
    smul_nonneg hextraCoefficient haction
  have hsum := add_nonneg hmain hextra
  have hepcancel : ep • z = action := by
    change Real.exp (rate * t) •
        (Real.exp (-(rate * t)) • action) = action
    rw [smul_smul, exp_damping_mul_exp_neg_damping g radius t, one_smul]
  have hmiddle : (ep * g ^ 2 * (2 * ‖z‖)) • z =
      (2 * g ^ 2 * ‖z‖) • action := by
    rw [← hepcancel, smul_smul]
    congr 1
    ring
  change 0 ≤ ep • (g ^ 2 • collisionMap collision z) + rate • action
  rw [smul_smul]
  rw [show (ep * g ^ 2) • collisionMap collision z +
      rate • action =
      (ep * g ^ 2) • collisionMap collision z +
        (2 * g ^ 2 * ‖z‖) • action +
        (2 * g ^ 2 * (radius - ‖z‖)) • action by
    simp only [rate, dampingRate]
    module]
  rw [← hmiddle]
  have hcombine :
      (ep * g ^ 2) • collisionMap collision z +
          (ep * g ^ 2 * (2 * ‖z‖)) • z =
        (ep * g ^ 2) •
          (collisionMap collision z + (2 * ‖z‖) • z) := by
    rw [smul_add, smul_smul]
  rw [hcombine]
  exact hsum


/-- The damped-state map is norm nonexpansive at forward times. -/
theorem norm_dampedState_sub_le
    (collision : ResonantThreeWaveMeasure Mode)
    (g radius t : Real) (hradius : 0 ≤ radius) (ht : 0 ≤ t)
    (action₁ action₂ : CanonicalLInfinity collision) :
    ‖dampedState collision g radius t action₁ -
        dampedState collision g radius t action₂‖ ≤ ‖action₁ - action₂‖ := by
  simp only [dampedState, ← smul_sub]
  exact norm_dampedState_le collision g radius t hradius ht (action₁ - action₂)

/-- Uniform field bound on a forward unit time slab and an origin ball. -/
theorem norm_integratingFactorField_le
    (collision : ResonantThreeWaveMeasure Mode)
    (g radius t : Real) (hradius : 0 ≤ radius)
    (ht₀ : 0 ≤ t) (ht₁ : t ≤ 1)
    (action : CanonicalLInfinity collision) (haction : ‖action‖ ≤ radius) :
    ‖integratingFactorField collision g radius t action‖ ≤
      Real.exp (dampingRate g radius) * (3 * g ^ 2 * radius ^ 2) +
        dampingRate g radius * radius := by
  let rate := dampingRate g radius
  let z := dampedState collision g radius t action
  have hrate : 0 ≤ rate := dampingRate_nonnegative g radius hradius
  have hz : ‖z‖ ≤ radius :=
    (norm_dampedState_le collision g radius t hradius ht₀ action).trans haction
  have hexponent : rate * t ≤ rate := by nlinarith
  have hexp : Real.exp (rate * t) ≤ Real.exp rate := Real.exp_le_exp.mpr hexponent
  change ‖Real.exp (rate * t) • rnCollisionVectorField collision g z +
      rate • action‖ ≤ _
  calc
    _ ≤ ‖Real.exp (rate * t) • rnCollisionVectorField collision g z‖ +
        ‖rate • action‖ := norm_add_le _ _
    _ = Real.exp (rate * t) * ‖rnCollisionVectorField collision g z‖ +
        rate * ‖action‖ := by
      simp only [norm_smul, Real.norm_eq_abs,
        abs_of_pos (Real.exp_pos _), abs_of_nonneg hrate]
    _ ≤ Real.exp (rate * t) * (3 * g ^ 2 * ‖z‖ ^ 2) +
        rate * ‖action‖ := by
      gcongr
      exact norm_rnCollisionVectorField_le collision g z
    _ ≤ Real.exp rate * (3 * g ^ 2 * radius ^ 2) + rate * radius := by
      gcongr

/-- A uniform spatial Lipschitz constant for the integrating-factor field on
the forward unit slab. -/
theorem lipschitzOnWith_integratingFactorField
    (collision : ResonantThreeWaveMeasure Mode)
    (g radius t : Real) (hradius : 0 ≤ radius)
    (ht₀ : 0 ≤ t) (ht₁ : t ≤ 1) :
    LipschitzOnWith
      (Real.toNNReal
        (Real.exp (dampingRate g radius) * (6 * g ^ 2 * radius) +
          dampingRate g radius))
      (integratingFactorField collision g radius t)
      (closedBall (0 : CanonicalLInfinity collision) radius) := by
  let rate := dampingRate g radius
  have hrate : 0 ≤ rate := dampingRate_nonnegative g radius hradius
  have hconstant :
      0 ≤ Real.exp rate * (6 * g ^ 2 * radius) + rate := by positivity
  apply LipschitzOnWith.of_dist_le_mul
  intro action₁ haction₁ action₂ haction₂
  have hnorm₁ : ‖action₁‖ ≤ radius := by
    simpa only [mem_closedBall_iff_norm, sub_zero] using haction₁
  have hnorm₂ : ‖action₂‖ ≤ radius := by
    simpa only [mem_closedBall_iff_norm, sub_zero] using haction₂
  let z₁ := dampedState collision g radius t action₁
  let z₂ := dampedState collision g radius t action₂
  have hznorm₁ : ‖z₁‖ ≤ radius :=
    (norm_dampedState_le collision g radius t hradius ht₀ action₁).trans hnorm₁
  have hznorm₂ : ‖z₂‖ ≤ radius :=
    (norm_dampedState_le collision g radius t hradius ht₀ action₂).trans hnorm₂
  have hcollision := norm_collisionMap_sub_le collision hradius z₁ z₂
    hznorm₁ hznorm₂
  have hzsub := norm_dampedState_sub_le collision g radius t hradius ht₀
    action₁ action₂
  have hexponent : rate * t ≤ rate := by nlinarith
  have hexp : Real.exp (rate * t) ≤ Real.exp rate :=
    Real.exp_le_exp.mpr hexponent
  have hfieldSub :
      integratingFactorField collision g radius t action₁ -
          integratingFactorField collision g radius t action₂ =
        Real.exp (rate * t) •
            (g ^ 2 • (collisionMap collision z₁ - collisionMap collision z₂)) +
          rate • (action₁ - action₂) := by
    simp only [integratingFactorField, rnCollisionVectorField, rate, z₁, z₂]
    module
  rw [dist_eq_norm, hfieldSub]
  calc
    _ ≤ ‖Real.exp (rate * t) •
          (g ^ 2 • (collisionMap collision z₁ - collisionMap collision z₂))‖ +
        ‖rate • (action₁ - action₂)‖ := norm_add_le _ _
    _ = Real.exp (rate * t) *
          (g ^ 2 * ‖collisionMap collision z₁ - collisionMap collision z₂‖) +
        rate * ‖action₁ - action₂‖ := by
      simp only [norm_smul, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _),
        abs_of_nonneg (sq_nonneg g), abs_of_nonneg hrate]
    _ ≤ Real.exp (rate * t) *
          (g ^ 2 * (6 * radius * ‖z₁ - z₂‖)) +
        rate * ‖action₁ - action₂‖ := by gcongr
    _ ≤ Real.exp rate *
          (g ^ 2 * (6 * radius * ‖action₁ - action₂‖)) +
        rate * ‖action₁ - action₂‖ := by gcongr
    _ = (Real.toNNReal
          (Real.exp rate * (6 * g ^ 2 * radius) + rate) : Real) *
        dist action₁ action₂ := by
      rw [Real.coe_toNNReal _ hconstant, dist_eq_norm]
      ring

/-- Time continuity of the integrating-factor field at every fixed state. -/
theorem continuous_integratingFactorField_time
    (collision : ResonantThreeWaveMeasure Mode)
    (g radius : Real) (action : CanonicalLInfinity collision) :
    Continuous (fun t ↦ integratingFactorField collision g radius t action) := by
  change Continuous (fun t ↦
    Real.exp (dampingRate g radius * t) •
        (g ^ 2 • collisionMap collision
          (Real.exp (-(dampingRate g radius * t)) • action)) +
      dampingRate g radius • action)
  apply Continuous.add
  · have hep : Continuous (fun t : Real ↦
        Real.exp (dampingRate g radius * t)) := by fun_prop
    have hdamped : Continuous (fun t : Real ↦
        Real.exp (-(dampingRate g radius * t)) • action) := by fun_prop
    have hcollision : Continuous (fun t : Real ↦ collisionMap collision
        (Real.exp (-(dampingRate g radius * t)) • action)) :=
      (continuous_collisionMap collision).comp hdamped
    have hinner : Continuous (fun t : Real ↦ g ^ 2 • collisionMap collision
        (Real.exp (-(dampingRate g radius * t)) • action)) :=
      (continuous_const : Continuous (fun _ : Real ↦ g ^ 2)).smul hcollision
    exact hep.smul hinner
  · exact continuous_const

end

end ArchonPhysics.ResonantThreeWaveKineticLInfinityIntegratingFactor
