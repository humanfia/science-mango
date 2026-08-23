import ArchonPhysics.HittingTime
import Mathlib.Analysis.Calculus.Deriv.Comp
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Data.ENNReal.Inv

/-!
# Kinetic-equation time rescaling

For an effective kinetic equation whose collision term is multiplied by `g^2`,
uniqueness transports the unit-coupling solution by the time change
`t ↦ g^2 t`.  This formalizes Target A in Section 7 of
`references/Thermal_physics_README.md`; it makes no microscopic kinetic-limit
or thermalization claim.
-/

namespace ArchonPhysics.KineticRescaling

noncomputable section

/-- A trajectory solves the effective kinetic equation with coupling `g`. -/
def SolvesKineticEquation {X : Type} [NormedAddCommGroup X] [NormedSpace Real X]
    (collision : X → X) (g : Real) (initial : X) (D : Real → X) : Prop :=
  D 0 = initial ∧ ∀ t, HasDerivAt D (g ^ 2 • collision (D t)) t

/-- The kinetic-solution predicate unfolds to its initial-value and derivative data. -/
theorem solvesKineticEquation_iff {X : Type} [NormedAddCommGroup X] [NormedSpace Real X]
    (collision : X → X) (g : Real) (initial : X) (D : Real → X) :
    SolvesKineticEquation collision g initial D ↔
      D 0 = initial ∧ ∀ t, HasDerivAt D (g ^ 2 • collision (D t)) t := by
  rfl

/-- Uniqueness turns the `g^2` coefficient in the kinetic equation into a time rescaling. -/
theorem kineticSolution_rescale {X : Type} [NormedAddCommGroup X] [NormedSpace Real X]
    (collision : X → X) (g : Real) (initial : X) (D1 Dg : Real → X)
    (hD1 : SolvesKineticEquation collision 1 initial D1)
    (hDg : SolvesKineticEquation collision g initial Dg)
    (hunique : ∀ D E : Real → X, SolvesKineticEquation collision g initial D →
      SolvesKineticEquation collision g initial E → D = E) :
    Dg = fun t => D1 (g ^ 2 * t) := by
  apply hunique Dg (fun t => D1 (g ^ 2 * t)) hDg
  constructor
  · simpa [SolvesKineticEquation] using hD1.1
  · intro t
    simpa [Function.comp_def] using
      (hD1.2 (g ^ 2 * t)).scomp t (hasDerivAt_const_mul (g ^ 2))

/-- The first strictly positive real time at which a state predicate holds. -/
def firstStateHittingTime {X : Type} (P : X → Prop) (D : Real → X) : ENNReal :=
  HittingTime.firstHittingTime (fun t => P (D t.toReal))

/-- The state-event hitting time is the infimum of its strictly positive event times. -/
theorem firstStateHittingTime_eq_sInf {X : Type} (P : X → Prop) (D : Real → X) :
    firstStateHittingTime P D = sInf {t : ENNReal | 0 < t ∧ P (D t.toReal)} := by
  rfl

/-- Transporting a trajectory by `g^2` rescales its state-event hitting time by `g⁻²`. -/
theorem firstStateHittingTime_rescale {X : Type} (g : Real) (hg : g ≠ 0)
    (D1 Dg : Real → X) (P : X → Prop)
    (hrescale : ∀ t, Dg t = D1 (g ^ 2 * t)) :
    firstStateHittingTime P Dg =
      (Real.toNNReal (g ^ 2) : ENNReal)⁻¹ * firstStateHittingTime P D1 := by
  have hsq_pos : 0 < g ^ 2 := sq_pos_of_ne_zero hg
  have hsq_nonneg : 0 ≤ g ^ 2 := le_of_lt hsq_pos
  have hsq_ne : g ^ 2 ≠ 0 := ne_of_gt hsq_pos
  let a : ENNReal := (Real.toNNReal (g ^ 2) : ENNReal)
  have ha_pos : 0 < a := by
    change 0 < (↑(Real.toNNReal (g ^ 2)) : ENNReal)
    rw [ENNReal.coe_pos]
    exact Real.toNNReal_pos.mpr hsq_pos
  have ha_ne_zero : a ≠ 0 := ne_of_gt ha_pos
  have ha_ne_top : a ≠ ⊤ := by
    simp [a]
  have ha_unit : IsUnit a := ENNReal.isUnit_iff.mpr ⟨ha_ne_zero, ha_ne_top⟩
  have ha_toReal : a.toReal = g ^ 2 := by
    change (↑(Real.toNNReal (g ^ 2)) : ENNReal).toReal = g ^ 2
    rw [ENNReal.coe_toReal, Real.coe_toNNReal _ hsq_nonneg]
  have hmul_toReal (t : ENNReal) : (a * t).toReal = g ^ 2 * t.toReal := by
    rw [ENNReal.toReal_mul, ha_toReal]
  have hinv_mul_toReal (t : ENNReal) :
      g ^ 2 * (a⁻¹ * t).toReal = t.toReal := by
    rw [ENNReal.toReal_mul, ENNReal.toReal_inv, ha_toReal]
    rw [← mul_assoc, mul_inv_cancel₀ hsq_ne, one_mul]
  let S1 : Set ENNReal := {t | 0 < t ∧ P (D1 t.toReal)}
  let Sg : Set ENNReal := {t | 0 < t ∧ P (Dg t.toReal)}
  have hsets : S1 = (fun t : ENNReal => a * t) '' Sg := by
    ext t
    constructor
    · rintro ⟨ht_pos, ht_event⟩
      refine ⟨a⁻¹ * t, ?_, ?_⟩
      · refine ⟨ENNReal.mul_pos (ne_of_gt (ENNReal.inv_pos.mpr ha_ne_top))
          (ne_of_gt ht_pos), ?_⟩
        rw [hrescale, hinv_mul_toReal]
        exact ht_event
      · exact ENNReal.mul_inv_cancel_left ha_ne_zero ha_ne_top
    · rintro ⟨t, ⟨ht_pos, ht_event⟩, rfl⟩
      refine ⟨ENNReal.mul_pos ha_ne_zero (ne_of_gt ht_pos), ?_⟩
      rw [hmul_toReal, ← hrescale]
      exact ht_event
  have hsInf : sInf S1 = a * sInf Sg := by
    rw [hsets, sInf_image]
    exact (ENNReal.mulLeftOrderIso a ha_unit).map_sInf Sg |>.symm
  change sInf Sg = a⁻¹ * sInf S1
  rw [hsInf, ENNReal.inv_mul_cancel_left ha_ne_zero ha_ne_top]

end

end ArchonPhysics.KineticRescaling
