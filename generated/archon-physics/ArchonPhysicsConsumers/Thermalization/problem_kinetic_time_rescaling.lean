import Mathlib
import ArchonPhysics
import Physlib.ClassicalMechanics.HamiltonsEquations

/-! Conditional time rescaling for an effective kinetic equation. -/

namespace ArchonPhysics.Generated.KineticTimeRescaling

noncomputable section

/-- A collision operator independent of the effective coupling. -/
structure EffectiveKineticModel (X : Type*) where
  collision : X → X

/-- A classical solution of `D' = g² C(D)` with prescribed initial data. -/
def SolvesKineticEquation {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
    (model : EffectiveKineticModel X) (g : ℝ) (initial : X) (D : ℝ → X) : Prop :=
  D 0 = initial ∧ ∀ t, HasDerivAt D (g ^ 2 • model.collision (D t)) t

/-- The extended first time at which an observable predicate holds along a trajectory. -/
def firstHittingTime {X : Type*} (P : X → Prop) (D : ℝ → X) : ENNReal :=
  sInf {t | 0 < t ∧ P (D t.toReal)}

/-- A named microscopic scaling conjecture, deliberately only a proposition. -/
def microscopicEquilibrationTimeScalingConjecture
    (T_eq : ℝ → ℝ → ℕ → ℝ) : Prop :=
  ∀ lam ε n, lam ≠ 0 → 0 < ε → 3 ≤ n →
    ∃ C : ℝ, 0 < C ∧
      T_eq lam ε n = C * lam⁻¹ ^ 2 * ε ^ (-((n - 2 : ℕ) : ℤ))

/-- Exact solution and compatible hitting-time scaling for the effective kinetic model.

It is conditional on classical existence and uniqueness and is not a microscopic-lattice claim. -/
theorem kinetic_time_rescaling_physics_formalization_target
    {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
    (model : EffectiveKineticModel X) (g : ℝ) (initial : X)
    (Dg D1 : ℝ → X) (P : X → Prop) (hg : g ≠ 0)
    (hDg : SolvesKineticEquation model g initial Dg)
    (hD1 : SolvesKineticEquation model 1 initial D1)
    (hunique : ∀ D E : ℝ → X,
      SolvesKineticEquation model g initial D →
      SolvesKineticEquation model g initial E → D = E) :
    (∀ t, Dg t = D1 (g ^ 2 * t)) ∧
      firstHittingTime P Dg =
        (Real.toNNReal (g ^ 2) : ENNReal)⁻¹ * firstHittingTime P D1 := by
  have hscaled : SolvesKineticEquation model g initial (fun t => D1 (g ^ 2 * t)) := by
    constructor
    · simpa using hD1.1
    · intro t
      simpa only [Function.comp_def, one_pow, one_smul] using
        (hD1.2 (g ^ 2 * t)).scomp t (hasDerivAt_const_mul (g ^ 2))
  have htrajectory : ∀ t, Dg t = D1 (g ^ 2 * t) := by
    have hEq : Dg = fun t => D1 (g ^ 2 * t) := hunique Dg _ hDg hscaled
    exact fun t => congrFun hEq t
  refine ⟨htrajectory, ?_⟩
  let a : ENNReal := Real.toNNReal (g ^ 2)
  have hg2pos : 0 < g ^ 2 := sq_pos_of_ne_zero hg
  have ha0 : a ≠ 0 := by
    dsimp [a]
    exact ENNReal.coe_ne_zero.mpr (ne_of_gt (Real.toNNReal_pos.2 hg2pos))
  have haTop : a ≠ ⊤ := by
    simp [a]
  have haUnit : IsUnit a := ENNReal.isUnit_iff.2 ⟨ha0, haTop⟩
  have haReal : a.toReal = g ^ 2 := by
    simp [a, Real.toNNReal_of_nonneg (sq_nonneg g)]
  have hsets :
      {t : ENNReal | 0 < t ∧ P (Dg t.toReal)} =
        (fun u : ENNReal => a⁻¹ * u) '' {t : ENNReal | 0 < t ∧ P (D1 t.toReal)} := by
    ext t
    constructor
    · rintro ⟨htpos, htP⟩
      refine ⟨a * t, ?_, ?_⟩
      · constructor
        · exact ENNReal.mul_pos ha0 htpos.ne'
        · simpa only [ENNReal.toReal_mul, haReal] using (htrajectory t.toReal ▸ htP)
      · dsimp
        rw [← mul_assoc, ENNReal.inv_mul_cancel ha0 haTop, one_mul]
    · rintro ⟨u, ⟨hupos, huP⟩, rfl⟩
      constructor
      · exact ENNReal.mul_pos (ENNReal.inv_ne_zero.2 haTop) hupos.ne'
      · rw [htrajectory]
        convert huP using 1
        rw [ENNReal.toReal_mul, ENNReal.toReal_inv, haReal]
        field_simp
  unfold firstHittingTime
  change sInf {t : ENNReal | 0 < t ∧ P (Dg t.toReal)} =
    a⁻¹ * sInf {t : ENNReal | 0 < t ∧ P (D1 t.toReal)}
  rw [hsets, sInf_image]
  have hainvUnit : IsUnit (a⁻¹) :=
    ENNReal.isUnit_iff.2 ⟨ENNReal.inv_ne_zero.2 haTop, ENNReal.inv_ne_top.2 ha0⟩
  exact (ENNReal.mulLeftOrderIso (a⁻¹) hainvUnit).map_sInf _ |>.symm

end

end ArchonPhysics.Generated.KineticTimeRescaling
