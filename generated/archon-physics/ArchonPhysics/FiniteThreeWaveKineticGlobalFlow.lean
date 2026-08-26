import ArchonPhysics.CoerciveHamiltonianGlobalExistence
import ArchonPhysics.FiniteThreeWaveCollisionNetwork
import ArchonPhysics.FiniteDimensionalGlobalContinuation
import ArchonPhysics.WaveKineticEquation

/-!
# Finite three-wave kinetic global-flow bridges

This module isolates the finite-dimensional analytic consequences of a supplied
three-wave collision network.  It proves smoothness of the polynomial collision
field, its inward-pointing sign on the boundary of the nonnegative orthant,
energy conservation along every supplied solution, and bounded-trajectory
continuation on a positive-frequency energy shell.

No result here identifies the network or its rates with a microscopic random
lattice collision kernel, proves that the exact-resonance network is nonempty,
or establishes relaxation.
-/

namespace ArchonPhysics.FiniteThreeWaveKineticGlobalFlow

open Set
open ArchonPhysics.FiniteDimensionalGlobalContinuation
open ArchonPhysics.FiniteThreeWaveCollisionNetwork

noncomputable section

variable {Mode Triad : Type}
variable [Fintype Mode] [DecidableEq Mode] [Fintype Triad]

/-- A finite collision network packaged as the generic wave-kinetic data. -/
def networkCollisionData (network : Network Mode Triad)
    (frequency : Mode → Real) (rate : Triad → Real) : CollisionData Mode where
  omega := frequency
  collision := collisionVectorField network rate

/-- The finite linear wave-action energy. -/
def totalKineticEnergy (frequency : Mode → Real) (action : Mode → Real) : Real :=
  ∑ i, frequency i * action i

/-- The polynomial collision vector field of a finite network is smooth. -/
theorem collisionVectorField_contDiff
    (network : Network Mode Triad) (rate : Triad → Real) :
    ContDiff Real 1 (collisionVectorField network rate) := by
  rw [contDiff_pi]
  intro i
  unfold collisionVectorField networkTriadFlux
  unfold ThreeWaveCollisionAlgebra.collisionFlux
  fun_prop

/-- Consequently the coupled wave-kinetic field is `C¹` for every coupling. -/
theorem waveKineticVectorField_contDiff
    (network : Network Mode Triad) (frequency : Mode → Real)
    (rate : Triad → Real) (g : Real) :
    ContDiff Real 1
      (waveKineticVectorField (networkCollisionData network frequency rate) g) := by
  change ContDiff Real 1
    (fun action ↦ g ^ 2 • collisionVectorField network rate action)
  exact (collisionVectorField_contDiff network rate).const_smul (g ^ 2)

omit [Fintype Mode] [Fintype Triad] in
/-- One triad contributes inward at a vanishing coordinate whenever all
actions and its rate are nonnegative.  Repeated mode labels are included. -/
theorem triadContribution_nonneg_at_boundary
    (network : Network Mode Triad) (rate : Triad → Real)
    (action : Mode → Real) (i : Mode) (a : Triad)
    (hrate : 0 ≤ rate a) (haction : ∀ j, 0 ≤ action j)
    (hi : action i = 0) :
    0 ≤ rate a * networkTriadFlux network action a *
      stoichiometricCoefficient network a i := by
  by_cases h1 : i = network.mode₁ a <;>
    by_cases h2 : i = network.mode₂ a <;>
      by_cases h3 : i = network.mode₃ a
  all_goals
    simp_all only [networkTriadFlux, ThreeWaveCollisionAlgebra.collisionFlux,
      mul_zero, sub_self, stoichiometricCoefficient, ↓reduceIte, zero_sub,
      mul_neg, mul_one, neg_zero, Std.le_refl, zero_mul, sub_zero, neg_neg]
  all_goals exact mul_nonneg hrate (mul_nonneg (haction _) (haction _))

omit [Fintype Mode] in
/-- The complete collision field points into the nonnegative orthant at every
boundary coordinate. -/
theorem collisionVectorField_nonneg_at_boundary
    (network : Network Mode Triad) (rate : Triad → Real)
    (hrate : ∀ a, 0 ≤ rate a) (action : Mode → Real)
    (haction : ∀ j, 0 ≤ action j) (i : Mode) (hi : action i = 0) :
    0 ≤ collisionVectorField network rate action i := by
  unfold collisionVectorField
  exact Finset.sum_nonneg fun a _ ↦
    triadContribution_nonneg_at_boundary network rate action i a
      (hrate a) haction hi

omit [Fintype Mode] in
/-- Multiplication by `g²` preserves the inward-pointing boundary sign. -/
theorem waveKineticVectorField_nonneg_at_boundary
    (network : Network Mode Triad) (frequency : Mode → Real)
    (rate : Triad → Real) (hrate : ∀ a, 0 ≤ rate a)
    (g : Real) (action : Mode → Real) (haction : ∀ j, 0 ≤ action j)
    (i : Mode) (hi : action i = 0) :
    0 ≤ waveKineticVectorField
      (networkCollisionData network frequency rate) g action i := by
  exact mul_nonneg (sq_nonneg g)
    (collisionVectorField_nonneg_at_boundary network rate hrate action haction i hi)

/-- The total kinetic energy has derivative zero along every supplied network
solution when every triad is frequency resonant. -/
theorem totalKineticEnergy_hasDerivWithinAt_zero
    (network : Network Mode Triad) (frequency : Mode → Real)
    (rate : Triad → Real)
    (hresonance : ∀ a, frequency (network.mode₁ a) =
      frequency (network.mode₂ a) + frequency (network.mode₃ a))
    (g : Real) {D : Real → (Mode → Real)} {s : Set Real} {t : Real}
    (hD : HasDerivWithinAt D
      (waveKineticVectorField
        (networkCollisionData network frequency rate) g (D t)) s t) :
    HasDerivWithinAt (fun u ↦ totalKineticEnergy frequency (D u)) 0 s t := by
  have hcoord := hasDerivWithinAt_pi.mp hD
  have hsum : HasDerivWithinAt
      (fun u ↦ ∑ i, frequency i * D u i)
      (∑ i, frequency i *
        waveKineticVectorField
          (networkCollisionData network frequency rate) g (D t) i) s t := by
    exact HasDerivWithinAt.fun_sum fun i _ ↦ (hcoord i).const_mul (frequency i)
  apply hsum.congr_deriv
  have hzero := totalEnergySlope_eq_zero_of_resonance
    network frequency rate (D t) hresonance
  simp only [waveKineticVectorField, networkCollisionData, Pi.smul_apply,
    smul_eq_mul]
  calc
    (∑ i, frequency i * (g ^ 2 * collisionVectorField network rate (D t) i)) =
        g ^ 2 * (∑ i, frequency i * collisionVectorField network rate (D t) i) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i _
      ring
    _ = 0 := by
      unfold totalEnergySlope weightedObservableSlope at hzero
      rw [hzero, mul_zero]

/-- Energy agrees at any two times of a convex interval carrying the network
wave-kinetic ODE. -/
theorem totalKineticEnergy_eq_of_integralCurveOn
    (network : Network Mode Triad) (frequency : Mode → Real)
    (rate : Triad → Real)
    (hresonance : ∀ a, frequency (network.mode₁ a) =
      frequency (network.mode₂ a) + frequency (network.mode₃ a))
    (g : Real) {D : Real → (Mode → Real)} {s : Set Real}
    (hs : Convex Real s)
    (hD : IsIntegralCurveOn D
      (fun _ ↦ waveKineticVectorField
        (networkCollisionData network frequency rate) g) s)
    {u v : Real} (hu : u ∈ s) (hv : v ∈ s) :
    totalKineticEnergy frequency (D u) =
      totalKineticEnergy frequency (D v) := by
  let energy : Real → Real := fun t ↦ totalKineticEnergy frequency (D t)
  have hzero : ∀ t ∈ s, HasDerivWithinAt energy 0 s t := by
    intro t ht
    exact totalKineticEnergy_hasDerivWithinAt_zero
      network frequency rate hresonance g (hD t ht)
  have hbound := hs.norm_image_sub_le_of_norm_hasDerivWithin_le
    (C := 0) hzero (fun _ _ ↦ by simp) hu hv
  have hrev : energy v = energy u := by
    simpa only [norm_zero, zero_mul, norm_le_zero_iff, sub_eq_zero] using hbound
  exact hrev.symm
omit [DecidableEq Mode] in
/-- A nonnegative state on a strictly positive frequency shell is bounded in
the finite product norm by its total energy divided by the smallest
frequency. -/
theorem norm_le_totalKineticEnergy_div
    (frequency : Mode → Real) (action : Mode → Real)
    (haction : ∀ i, 0 ≤ action i) {omegaMin : Real}
    (homegaMin : 0 < omegaMin) (homega : ∀ i, omegaMin ≤ frequency i) :
    ‖action‖ ≤ totalKineticEnergy frequency action / omegaMin := by
  have henergy : 0 ≤ totalKineticEnergy frequency action := by
    exact Finset.sum_nonneg fun i _ ↦
      mul_nonneg (homegaMin.le.trans (homega i)) (haction i)
  rw [pi_norm_le_iff_of_nonneg (div_nonneg henergy homegaMin.le)]
  intro i
  rw [Real.norm_eq_abs, abs_of_nonneg (haction i)]
  apply (le_div_iff₀ homegaMin).2
  calc
    action i * omegaMin ≤ action i * frequency i :=
      mul_le_mul_of_nonneg_left (homega i) (haction i)
    _ = frequency i * action i := by ring
    _ ≤ ∑ j, frequency j * action j := by
      apply Finset.single_le_sum (fun j _ ↦ mul_nonneg (homegaMin.le.trans (homega j))
        (haction j))
      exact Finset.mem_univ i

/-- A nonnegative resonant trajectory with uniformly positive frequencies is
bounded on every finite half-open interval. -/
theorem bounded_image_of_nonnegative_integralCurveOn
    (network : Network Mode Triad) (frequency : Mode → Real)
    (rate : Triad → Real)
    (hresonance : ∀ a, frequency (network.mode₁ a) =
      frequency (network.mode₂ a) + frequency (network.mode₃ a))
    (g : Real) {D : Real → (Mode → Real)} {t₀ b : Real} (ht : t₀ < b)
    (hD : IsIntegralCurveOn D
      (fun _ ↦ waveKineticVectorField
        (networkCollisionData network frequency rate) g) (Ico t₀ b))
    (hnonneg : ∀ t ∈ Ico t₀ b, ∀ i, 0 ≤ D t i)
    {omegaMin : Real} (homegaMin : 0 < omegaMin)
    (homega : ∀ i, omegaMin ≤ frequency i) :
    Bornology.IsBounded (D '' Ico t₀ b) := by
  rw [isBounded_iff_forall_norm_le]
  refine ⟨totalKineticEnergy frequency (D t₀) / omegaMin, ?_⟩
  rintro _ ⟨t, htInterval, rfl⟩
  apply norm_le_totalKineticEnergy_div frequency (D t)
    (hnonneg t htInterval) homegaMin homega |>.trans_eq
  congr 1
  exact totalKineticEnergy_eq_of_integralCurveOn
    network frequency rate hresonance g (convex_Ico t₀ b) hD
      htInterval ⟨le_rfl, ht⟩

/-- Under the explicit nonnegative-trajectory condition, every finite
endpoint admits a strict continuation.  Thus positivity and energy
conservation remove any separate boundedness/blow-up hypothesis. -/
theorem exists_strictForwardExtension_of_nonnegative_network_solution
    (network : Network Mode Triad) (frequency : Mode → Real)
    (rate : Triad → Real)
    (hresonance : ∀ a, frequency (network.mode₁ a) =
      frequency (network.mode₂ a) + frequency (network.mode₃ a))
    (g : Real) {D : Real → (Mode → Real)} {t₀ b : Real} (ht : t₀ < b)
    (hD : IsIntegralCurveOn D
      (fun _ ↦ waveKineticVectorField
        (networkCollisionData network frequency rate) g) (Ico t₀ b))
    (hnonneg : ∀ t ∈ Ico t₀ b, ∀ i, 0 ≤ D t i)
    {omegaMin : Real} (homegaMin : 0 < omegaMin)
    (homega : ∀ i, omegaMin ≤ frequency i) :
    ∃ (b' : Real) (delta : Real → (Mode → Real)),
      IsStrictForwardExtension
        (waveKineticVectorField
          (networkCollisionData network frequency rate) g)
        D delta t₀ b b' := by
  exact exists_strictForwardExtension_of_bounded ht
    (waveKineticVectorField_contDiff network frequency rate g) hD
    (bounded_image_of_nonnegative_integralCurveOn
      network frequency rate hresonance g ht hD hnonneg homegaMin homega)

end

end ArchonPhysics.FiniteThreeWaveKineticGlobalFlow
