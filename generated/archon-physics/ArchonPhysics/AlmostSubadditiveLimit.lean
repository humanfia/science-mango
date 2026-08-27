import Mathlib.Analysis.Subadditive

/-!
# Limits for almost-subadditive finite-volume quantities

This module isolates the deterministic Fekete step used by finite-volume
integrated-density-of-states arguments.  A nonnegative sequence whose
subadditivity defect is bounded by one fixed nonnegative constant has a
limit after division by the volume.
-/

namespace ArchonPhysics.AlmostSubadditiveLimit

open Filter Set Topology

noncomputable section

/-- `u` is subadditive up to the fixed additive defect `C`. -/
def AlmostSubadditive (u : Nat → Real) (C : Real) : Prop :=
  ∀ m n, u (m + n) ≤ u m + u n + C

/-- Adding the defect converts an almost-subadditive sequence into an
exactly subadditive sequence. -/
theorem subadditive_add_defect {u : Nat → Real} {C : Real}
    (h : AlmostSubadditive u C) :
    Subadditive (fun n ↦ u n + C) := by
  intro m n
  dsimp
  linarith [h m n]

/-- A nonnegative almost-subadditive sequence has a finite normalized
limit.  The value is the Fekete limit of the defect-shifted sequence. -/
theorem exists_tendsto_div_natCast {u : Nat → Real} {C : Real}
    (hC : 0 ≤ C) (hu : ∀ n, 0 ≤ u n) (h : AlmostSubadditive u C) :
    ∃ L : Real, Tendsto (fun n : Nat ↦ u n / (n : Real)) atTop (𝓝 L) := by
  let v : Nat → Real := fun n ↦ u n + C
  have hv : Subadditive v := by
    simpa [v] using subadditive_add_defect h
  have hv_nonneg : ∀ n, 0 ≤ v n := fun n ↦ by
    dsimp [v]
    exact add_nonneg (hu n) hC
  have hv_bdd : BddBelow (range fun n : Nat ↦ v n / (n : Real)) := by
    refine ⟨0, ?_⟩
    rintro y ⟨n, rfl⟩
    exact div_nonneg (hv_nonneg n) (Nat.cast_nonneg n)
  have hv_lim :
      Tendsto (fun n : Nat ↦ v n / (n : Real)) atTop (𝓝 hv.lim) :=
    hv.tendsto_lim hv_bdd
  have hC_lim : Tendsto (fun n : Nat ↦ C / (n : Real)) atTop (𝓝 0) := by
    simpa using
      (tendsto_const_nhds.div_atTop tendsto_natCast_atTop_atTop :
        Tendsto (fun n : Nat ↦ C / (n : Real)) atTop (𝓝 0))
  refine ⟨hv.lim, ?_⟩
  convert hv_lim.sub hC_lim using 1
  · funext n
    dsimp [v]
    ring
  · simp

end

end ArchonPhysics.AlmostSubadditiveLimit
