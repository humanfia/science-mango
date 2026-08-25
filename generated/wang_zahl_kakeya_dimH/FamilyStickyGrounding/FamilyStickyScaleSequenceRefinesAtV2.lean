import FamilyStickyGrounding.FamilyStickyDividingScalesFiniteStoppingV1
import Mathlib.Order.Fin.InsertNth

set_option autoImplicit false
set_option warningAsError true

open scoped ENNReal NNReal

namespace FamilyStickyScaleSequenceRefinesAtV2

open FamilyStickyDividingScalesFiniteStoppingV1

noncomputable section

/-!
# Inserting an actual radius into a finite scale sequence

This module records the minimal, lossless refinement relation needed by a
stopping construction.  Given an adjacent interval `m` of a finite decreasing
scale sequence and a radius between its two endpoints, the constructor below
inserts that radius and increases the depth by one.

The old coordinates are transported by `Fin.succAboveOrderEmb`, so the
refinement does not merely assert that the old radii occur somewhere: it gives
the canonical order embedding which skips exactly the newly inserted slot.
-/

variable {delta : NNReal} {depth : Nat}

namespace FiniteScaleSequence

/-- The new coordinate immediately after the upper endpoint of interval `m`. -/
def insertedIndex (m : Fin depth) : Fin (depth + 2) :=
  m.castSucc.succ

/-- The canonical order embedding of the old coordinates into the refined
sequence.  Its range is the complement of `insertedIndex m`. -/
def oldIndexEmbedding (m : Fin depth) : Fin (depth + 1) ↪o Fin (depth + 2) :=
  Fin.succAboveOrderEmb (insertedIndex m)

@[simp]
theorem oldIndexEmbedding_apply (m : Fin depth) (i : Fin (depth + 1)) :
    oldIndexEmbedding m i = (insertedIndex m).succAbove i :=
  rfl

@[simp]
theorem oldIndexEmbedding_upperEndpoint (m : Fin depth) :
    oldIndexEmbedding m m.castSucc = m.castSucc.castSucc := by
  exact Fin.succAbove_succ_self m.castSucc

@[simp]
theorem oldIndexEmbedding_lowerEndpoint (m : Fin depth) :
    oldIndexEmbedding m m.succ = m.succ.succ := by
  simp only [oldIndexEmbedding_apply, insertedIndex,
    Fin.succ_succAbove_succ, Fin.succAbove_castSucc_self]

/-- A refinement at `rho` preserves every old radius through the canonical
order embedding and puts `rho` in the unique skipped coordinate. -/
structure ScaleSequenceRefinesAt
    (S : FiniteScaleSequence delta depth) (m : Fin depth) (rho : NNReal)
    (S' : FiniteScaleSequence delta (depth + 1)) : Prop where
  old_radius : forall i, S'.radius (oldIndexEmbedding m i) = S.radius i
  inserted_radius : S'.radius (insertedIndex m) = rho

/-- A buffered radius lies above the lower endpoint.  Positivity of `delta`
supplies the only positivity input needed for the quotient. -/
theorem tau_le_of_isBuffered
    (S : FiniteScaleSequence delta depth) (m : Fin depth) (rho : NNReal)
    {epsilon : Real} (delta_pos : 0 < delta) (epsilon_nonneg : 0 <= epsilon)
    (hrho : S.IsBuffered epsilon m rho) :
    S.tau m <= rho := by
  have htau_pos : 0 < S.tau m :=
    delta_pos.trans_le (S.delta_le_tau m)
  have hbaseNN : 1 <= S.theta m / S.tau m :=
    (one_le_div htau_pos).2 (S.tau_le_theta m)
  have hbaseE : (1 : ENNReal) <=
      (((S.theta m / S.tau m : NNReal) : ENNReal)) := by
    exact_mod_cast hbaseNN
  have hfactor : (1 : ENNReal) <=
      (((S.theta m / S.tau m : NNReal) : ENNReal) ^ epsilon) := by
    have hpow := ENNReal.rpow_le_rpow hbaseE epsilon_nonneg
    simpa using hpow
  have htauE : (S.tau m : ENNReal) <= (rho : ENNReal) := by
    calc
      (S.tau m : ENNReal) = (S.tau m : ENNReal) * 1 := by simp
      _ <= (S.tau m : ENNReal) *
          (((S.theta m / S.tau m : NNReal) : ENNReal) ^ epsilon) := by
        gcongr
      _ <= (rho : ENNReal) := hrho.1
  exact ENNReal.coe_le_coe.mp htauE

/-- A buffered radius lies below the upper endpoint. -/
theorem le_theta_of_isBuffered
    (S : FiniteScaleSequence delta depth) (m : Fin depth) (rho : NNReal)
    {epsilon : Real} (epsilon_nonneg : 0 <= epsilon)
    (hrho : S.IsBuffered epsilon m rho) :
    rho <= S.theta m := by
  have hratioNN : S.tau m / S.theta m <= 1 :=
    div_le_one_of_le₀ (S.tau_le_theta m) bot_le
  have hratioE :
      (((S.tau m / S.theta m : NNReal) : ENNReal)) <= 1 := by
    exact_mod_cast hratioNN
  have hfactor :
      (((S.tau m / S.theta m : NNReal) : ENNReal) ^ epsilon) <= 1 :=
    ENNReal.rpow_le_one hratioE epsilon_nonneg
  have hrhoE : (rho : ENNReal) <= (S.theta m : ENNReal) := by
    calc
      (rho : ENNReal) <= (S.theta m : ENNReal) *
          (((S.tau m / S.theta m : NNReal) : ENNReal) ^ epsilon) := hrho.2
      _ <= (S.theta m : ENNReal) * 1 := by gcongr
      _ = (S.theta m : ENNReal) := by simp
  exact ENNReal.coe_le_coe.mp hrhoE

/-- Insert `rho` in the coordinate immediately between the endpoints of `m`.
The endpoint inequalities are exactly what is needed to retain antitonicity. -/
def insertRadius
    (S : FiniteScaleSequence delta depth) (m : Fin depth) (rho : NNReal)
    (hTauRho : S.tau m <= rho) (hRhoTheta : rho <= S.theta m) :
    FiniteScaleSequence delta (depth + 1) where
  radius := (insertedIndex m).insertNth rho S.radius
  antitone_radius := by
    change Monotone
      (Fin.insertNth (α := fun _ => NNRealᵒᵈ)
        m.castSucc.succ rho S.radius)
    let f : Fin (depth + 1) → NNRealᵒᵈ := OrderDual.toDual ∘ S.radius
    have hOld : Monotone f := by
      exact S.antitone_radius.dual_right
    have hInserted : Monotone
        (Fin.insertNth m.castSucc.succ (OrderDual.toDual rho) f) := by
      apply Fin.insertNth_monotone (α := NNRealᵒᵈ) hOld m
      · change rho <= S.radius m.castSucc
        exact hRhoTheta
      · change S.radius m.succ <= rho
        exact hTauRho
    intro a b hab
    exact hInserted hab
  top_eq := by
    have hp : insertedIndex m ≠ 0 := by
      exact Fin.succ_ne_zero _
    rw [← Fin.succAbove_ne_zero_zero hp]
    simp only [Fin.insertNth_apply_succAbove]
    exact S.top_eq
  bottom_eq := by
    have hp : insertedIndex m ≠ Fin.last (depth + 1) := by
      apply Fin.ne_of_lt
      simp only [insertedIndex, Fin.lt_def, Fin.val_succ,
        Fin.val_castSucc, Fin.val_last]
      omega
    rw [← Fin.succAbove_ne_last_last hp]
    simp only [Fin.insertNth_apply_succAbove]
    exact S.bottom_eq

@[simp]
theorem insertRadius_radius_old
    (S : FiniteScaleSequence delta depth) (m : Fin depth) (rho : NNReal)
    (hTauRho : S.tau m <= rho) (hRhoTheta : rho <= S.theta m)
    (i : Fin (depth + 1)) :
    (insertRadius S m rho hTauRho hRhoTheta).radius
        (oldIndexEmbedding m i) = S.radius i := by
  exact Fin.insertNth_apply_succAbove (α := fun _ => NNReal)
    (insertedIndex m) rho S.radius i

@[simp]
theorem insertRadius_radius_inserted
    (S : FiniteScaleSequence delta depth) (m : Fin depth) (rho : NNReal)
    (hTauRho : S.tau m <= rho) (hRhoTheta : rho <= S.theta m) :
    (insertRadius S m rho hTauRho hRhoTheta).radius (insertedIndex m) = rho := by
  exact Fin.insertNth_apply_same (α := fun _ => NNReal)
    (insertedIndex m) rho S.radius

/-- The actual insertion constructor produces the refinement certificate. -/
theorem insertRadius_refinesAt
    (S : FiniteScaleSequence delta depth) (m : Fin depth) (rho : NNReal)
    (hTauRho : S.tau m <= rho) (hRhoTheta : rho <= S.theta m) :
    ScaleSequenceRefinesAt S m rho (insertRadius S m rho hTauRho hRhoTheta) := by
  constructor
  · exact insertRadius_radius_old S m rho hTauRho hRhoTheta
  · exact insertRadius_radius_inserted S m rho hTauRho hRhoTheta

/-- Insert a buffered radius without asking the caller to reprove the two
endpoint inequalities. -/
def insertBufferedRadius
    (S : FiniteScaleSequence delta depth) (m : Fin depth) (rho : NNReal)
    {epsilon : Real} (delta_pos : 0 < delta) (epsilon_nonneg : 0 <= epsilon)
    (hrho : S.IsBuffered epsilon m rho) :
    FiniteScaleSequence delta (depth + 1) :=
  insertRadius S m rho
    (tau_le_of_isBuffered S m rho delta_pos epsilon_nonneg hrho)
    (le_theta_of_isBuffered S m rho epsilon_nonneg hrho)

/-- The buffered insertion is an actual scale-sequence refinement. -/
theorem insertBufferedRadius_refinesAt
    (S : FiniteScaleSequence delta depth) (m : Fin depth) (rho : NNReal)
    {epsilon : Real} (delta_pos : 0 < delta) (epsilon_nonneg : 0 <= epsilon)
    (hrho : S.IsBuffered epsilon m rho) :
    ScaleSequenceRefinesAt S m rho
      (insertBufferedRadius S m rho delta_pos epsilon_nonneg hrho) := by
  exact insertRadius_refinesAt S m rho
    (tau_le_of_isBuffered S m rho delta_pos epsilon_nonneg hrho)
    (le_theta_of_isBuffered S m rho epsilon_nonneg hrho)

/-- Existential form convenient for a stopping step. -/
theorem exists_refinement_at
    (S : FiniteScaleSequence delta depth) (m : Fin depth) (rho : NNReal)
    (hTauRho : S.tau m <= rho) (hRhoTheta : rho <= S.theta m) :
    exists S' : FiniteScaleSequence delta (depth + 1),
      ScaleSequenceRefinesAt S m rho S' := by
  exact ⟨insertRadius S m rho hTauRho hRhoTheta,
    insertRadius_refinesAt S m rho hTauRho hRhoTheta⟩

/-- Antitonicity is retained by the actual refinement. -/
theorem insertRadius_antitone
    (S : FiniteScaleSequence delta depth) (m : Fin depth) (rho : NNReal)
    (hTauRho : S.tau m <= rho) (hRhoTheta : rho <= S.theta m) :
    Antitone (insertRadius S m rho hTauRho hRhoTheta).radius :=
  (insertRadius S m rho hTauRho hRhoTheta).antitone_radius

/-- The top endpoint is unchanged by insertion. -/
theorem insertRadius_top_eq
    (S : FiniteScaleSequence delta depth) (m : Fin depth) (rho : NNReal)
    (hTauRho : S.tau m <= rho) (hRhoTheta : rho <= S.theta m) :
    (insertRadius S m rho hTauRho hRhoTheta).radius 0 = 1 :=
  (insertRadius S m rho hTauRho hRhoTheta).top_eq

/-- The bottom endpoint is unchanged by insertion. -/
theorem insertRadius_bottom_eq
    (S : FiniteScaleSequence delta depth) (m : Fin depth) (rho : NNReal)
    (hTauRho : S.tau m <= rho) (hRhoTheta : rho <= S.theta m) :
    (insertRadius S m rho hTauRho hRhoTheta).radius (Fin.last (depth + 1)) = delta :=
  (insertRadius S m rho hTauRho hRhoTheta).bottom_eq

end FiniteScaleSequence

end

#print axioms FamilyStickyScaleSequenceRefinesAtV2.FiniteScaleSequence.insertRadius_refinesAt
#print axioms FamilyStickyScaleSequenceRefinesAtV2.FiniteScaleSequence.insertBufferedRadius_refinesAt
#print axioms FamilyStickyScaleSequenceRefinesAtV2.FiniteScaleSequence.exists_refinement_at
#print axioms FamilyStickyScaleSequenceRefinesAtV2.FiniteScaleSequence.insertRadius_antitone
