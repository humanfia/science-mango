import FamilyStickyGrounding.FamilyStickyScaleSequenceRefinesAtV2
import FamilyStickyGrounding.FamilyStickyScaleChainSelectedNumericalAllocationProducerV1

set_option autoImplicit false
set_option warningAsError true

open scoped ENNReal NNReal

namespace FamilyStickyScaleSequenceInsertionTransportV2

open FamilyStickyDividingScalesFiniteStoppingV1
open FamilyStickyDividingScalesFiniteStoppingV1.FiniteScaleSequence
open FamilyStickyScaleSequenceRefinesAtV2.FiniteScaleSequence
open FamilyStickyScaleChainSelectedNumericalAllocationProducerV1

noncomputable section

/-!
# Transport of adjacent intervals across one scale insertion

The canonical insertion adds a radius coordinate immediately after the upper
endpoint of an old interval `m`.  Thus old intervals strictly before `m` keep
their numerical index, old intervals strictly after `m` shift by one, and `m`
is represented by its upper and lower child intervals.  All statements here
allow endpoint equality: no strict refinement is claimed.
-/

variable {delta : NNReal} {depth : Nat}

namespace FiniteScaleSequence

/-- Same-index embedding used for intervals strictly before the split. -/
def beforeIntervalEmbedding (depth : Nat) : Fin depth ↪o Fin (depth + 1) :=
  Fin.castSuccOrderEmb

/-- Shift-by-one embedding used for intervals strictly after the split. -/
def afterIntervalEmbedding (depth : Nat) : Fin depth ↪o Fin (depth + 1) :=
  Fin.succOrderEmb depth

@[simp]
theorem beforeIntervalEmbedding_apply (j : Fin depth) :
    beforeIntervalEmbedding depth j = j.castSucc :=
  rfl

@[simp]
theorem afterIntervalEmbedding_apply (j : Fin depth) :
    afterIntervalEmbedding depth j = j.succ :=
  rfl

/-- Upper child of the split interval. -/
def upperChildIndex (m : Fin depth) : Fin (depth + 1) :=
  m.castSucc

/-- Lower child of the split interval. -/
def lowerChildIndex (m : Fin depth) : Fin (depth + 1) :=
  m.succ

/-- Exact adjacent-interval transport relation.  An unsplit interval has one
image, while the split interval has its two child images. -/
def AdjacentIntervalTransport (m j : Fin depth) (k : Fin (depth + 1)) : Prop :=
  (j < m ∧ k = beforeIntervalEmbedding depth j) ∨
    (j = m ∧ (k = upperChildIndex m ∨ k = lowerChildIndex m)) ∨
    (m < j ∧ k = afterIntervalEmbedding depth j)

theorem adjacentIntervalTransport_iff_of_before
    (m j : Fin depth) (k : Fin (depth + 1)) (hjm : j < m) :
    AdjacentIntervalTransport m j k ↔
      k = beforeIntervalEmbedding depth j := by
  simp [AdjacentIntervalTransport, hjm, ne_of_lt hjm,
    not_lt_of_ge hjm.le]

theorem adjacentIntervalTransport_iff_split
    (m : Fin depth) (k : Fin (depth + 1)) :
    AdjacentIntervalTransport m m k ↔
      k = upperChildIndex m ∨ k = lowerChildIndex m := by
  simp [AdjacentIntervalTransport]

theorem adjacentIntervalTransport_iff_of_after
    (m j : Fin depth) (k : Fin (depth + 1)) (hmj : m < j) :
    AdjacentIntervalTransport m j k ↔
      k = afterIntervalEmbedding depth j := by
  simp [AdjacentIntervalTransport, hmj, ne_of_gt hmj,
    not_lt_of_ge hmj.le]

/-! ## Radius-coordinate transport -/

theorem oldIndexEmbedding_castSucc_of_lt
    (m j : Fin depth) (hjm : j < m) :
    oldIndexEmbedding m j.castSucc = j.castSucc.castSucc := by
  rw [oldIndexEmbedding_apply]
  exact Fin.succAbove_succ_of_le m.castSucc j.castSucc
    (Fin.castSucc_le_castSucc_iff.mpr hjm.le)

theorem oldIndexEmbedding_succ_of_lt
    (m j : Fin depth) (hjm : j < m) :
    oldIndexEmbedding m j.succ = j.castSucc.succ := by
  rw [oldIndexEmbedding_apply]
  simpa only [insertedIndex, Fin.succ_castSucc] using
    Fin.succAbove_succ_of_le m.castSucc j.succ
      (Fin.succ_le_castSucc_iff.mpr hjm)

theorem oldIndexEmbedding_castSucc_of_gt
    (m j : Fin depth) (hmj : m < j) :
    oldIndexEmbedding m j.castSucc = j.succ.castSucc := by
  rw [oldIndexEmbedding_apply]
  simpa only [insertedIndex, Fin.succ_castSucc] using
    Fin.succAbove_succ_of_lt m.castSucc j.castSucc
      (Fin.castSucc_lt_castSucc_iff.mpr hmj)

theorem oldIndexEmbedding_succ_of_gt
    (m j : Fin depth) (hmj : m < j) :
    oldIndexEmbedding m j.succ = j.succ.succ := by
  rw [oldIndexEmbedding_apply]
  exact Fin.succAbove_succ_of_lt m.castSucc j.succ
    (Fin.castSucc_lt_succ_iff.mpr hmj.le)

/-! ## Unsplit endpoint transport -/

variable {S : FiniteScaleSequence delta depth}
  {m j : Fin depth} {rho : NNReal}
  {S' : FiniteScaleSequence delta (depth + 1)}

theorem theta_before_eq
    (href : ScaleSequenceRefinesAt S m rho S') (hjm : j < m) :
    S'.theta (beforeIntervalEmbedding depth j) = S.theta j := by
  calc
    S'.theta (beforeIntervalEmbedding depth j) =
        S'.radius j.castSucc.castSucc := rfl
    _ = S'.radius (oldIndexEmbedding m j.castSucc) :=
      congrArg S'.radius (oldIndexEmbedding_castSucc_of_lt m j hjm).symm
    _ = S.radius j.castSucc := href.old_radius j.castSucc
    _ = S.theta j := rfl

theorem tau_before_eq
    (href : ScaleSequenceRefinesAt S m rho S') (hjm : j < m) :
    S'.tau (beforeIntervalEmbedding depth j) = S.tau j := by
  calc
    S'.tau (beforeIntervalEmbedding depth j) =
        S'.radius j.castSucc.succ := rfl
    _ = S'.radius (oldIndexEmbedding m j.succ) :=
      congrArg S'.radius (oldIndexEmbedding_succ_of_lt m j hjm).symm
    _ = S.radius j.succ := href.old_radius j.succ
    _ = S.tau j := rfl

theorem theta_after_eq
    (href : ScaleSequenceRefinesAt S m rho S') (hmj : m < j) :
    S'.theta (afterIntervalEmbedding depth j) = S.theta j := by
  calc
    S'.theta (afterIntervalEmbedding depth j) =
        S'.radius j.succ.castSucc := rfl
    _ = S'.radius (oldIndexEmbedding m j.castSucc) :=
      congrArg S'.radius (oldIndexEmbedding_castSucc_of_gt m j hmj).symm
    _ = S.radius j.castSucc := href.old_radius j.castSucc
    _ = S.theta j := rfl

theorem tau_after_eq
    (href : ScaleSequenceRefinesAt S m rho S') (hmj : m < j) :
    S'.tau (afterIntervalEmbedding depth j) = S.tau j := by
  calc
    S'.tau (afterIntervalEmbedding depth j) =
        S'.radius j.succ.succ := rfl
    _ = S'.radius (oldIndexEmbedding m j.succ) :=
      congrArg S'.radius (oldIndexEmbedding_succ_of_gt m j hmj).symm
    _ = S.radius j.succ := href.old_radius j.succ
    _ = S.tau j := rfl

/-! ## Split-child endpoints -/

theorem theta_upperChild_eq
    (href : ScaleSequenceRefinesAt S m rho S') :
    S'.theta (upperChildIndex m) = S.theta m := by
  calc
    S'.theta (upperChildIndex m) = S'.radius m.castSucc.castSucc := rfl
    _ = S'.radius (oldIndexEmbedding m m.castSucc) :=
      congrArg S'.radius (oldIndexEmbedding_upperEndpoint m).symm
    _ = S.radius m.castSucc := href.old_radius m.castSucc
    _ = S.theta m := rfl

theorem tau_upperChild_eq
    (href : ScaleSequenceRefinesAt S m rho S') :
    S'.tau (upperChildIndex m) = rho := by
  simpa only [upperChildIndex, tau, insertedIndex] using href.inserted_radius

theorem theta_lowerChild_eq
    (href : ScaleSequenceRefinesAt S m rho S') :
    S'.theta (lowerChildIndex m) = rho := by
  simpa only [lowerChildIndex, theta, insertedIndex, Fin.succ_castSucc] using
    href.inserted_radius

theorem tau_lowerChild_eq
    (href : ScaleSequenceRefinesAt S m rho S') :
    S'.tau (lowerChildIndex m) = S.tau m := by
  calc
    S'.tau (lowerChildIndex m) = S'.radius m.succ.succ := rfl
    _ = S'.radius (oldIndexEmbedding m m.succ) :=
      congrArg S'.radius (oldIndexEmbedding_lowerEndpoint m).symm
    _ = S.radius m.succ := href.old_radius m.succ
    _ = S.tau m := rfl

/-! ## Literal predicate and numerical-budget transport -/

theorem isLarge_before_iff (epsilon : Real)
    (href : ScaleSequenceRefinesAt S m rho S') (hjm : j < m) :
    S'.IsLarge epsilon (beforeIntervalEmbedding depth j) ↔
      S.IsLarge epsilon j := by
  unfold IsLarge
  rw [theta_before_eq href hjm, tau_before_eq href hjm]

theorem isLong_before_iff (epsilon : Real)
    (href : ScaleSequenceRefinesAt S m rho S') (hjm : j < m) :
    S'.IsLong epsilon (beforeIntervalEmbedding depth j) ↔
      S.IsLong epsilon j := by
  unfold IsLong
  rw [theta_before_eq href hjm, tau_before_eq href hjm]

theorem isLarge_after_iff (epsilon : Real)
    (href : ScaleSequenceRefinesAt S m rho S') (hmj : m < j) :
    S'.IsLarge epsilon (afterIntervalEmbedding depth j) ↔
      S.IsLarge epsilon j := by
  unfold IsLarge
  rw [theta_after_eq href hmj, tau_after_eq href hmj]

theorem isLong_after_iff (epsilon : Real)
    (href : ScaleSequenceRefinesAt S m rho S') (hmj : m < j) :
    S'.IsLong epsilon (afterIntervalEmbedding depth j) ↔
      S.IsLong epsilon j := by
  unfold IsLong
  rw [theta_after_eq href hmj, tau_after_eq href hmj]

theorem requiredGlobalPowerAt_before_eq
    (profile : Nat -> Real) (stage : Nat)
    (href : ScaleSequenceRefinesAt S m rho S') (hjm : j < m) :
    requiredGlobalPowerAt S' profile stage (beforeIntervalEmbedding depth j) =
      requiredGlobalPowerAt S profile stage j := by
  unfold requiredGlobalPowerAt
  rw [theta_before_eq href hjm]

theorem requiredGlobalPowerAt_after_eq
    (profile : Nat -> Real) (stage : Nat)
    (href : ScaleSequenceRefinesAt S m rho S') (hmj : m < j) :
    requiredGlobalPowerAt S' profile stage (afterIntervalEmbedding depth j) =
      requiredGlobalPowerAt S profile stage j := by
  unfold requiredGlobalPowerAt
  rw [theta_after_eq href hmj]

/-! ## Canonical-constructor specializations -/

theorem insertRadius_split_endpoints
    (S : FiniteScaleSequence delta depth) (m : Fin depth) (rho : NNReal)
    (hTauRho : S.tau m <= rho) (hRhoTheta : rho <= S.theta m) :
    let S' := insertRadius S m rho hTauRho hRhoTheta
    S'.theta (upperChildIndex m) = S.theta m ∧
      S'.tau (upperChildIndex m) = rho ∧
      S'.theta (lowerChildIndex m) = rho ∧
      S'.tau (lowerChildIndex m) = S.tau m := by
  let href := insertRadius_refinesAt S m rho hTauRho hRhoTheta
  exact ⟨theta_upperChild_eq href, tau_upperChild_eq href,
    theta_lowerChild_eq href, tau_lowerChild_eq href⟩

theorem insertBufferedRadius_split_endpoints
    (S : FiniteScaleSequence delta depth) (m : Fin depth) (rho : NNReal)
    {epsilon : Real} (delta_pos : 0 < delta) (epsilon_nonneg : 0 <= epsilon)
    (hrho : S.IsBuffered epsilon m rho) :
    let S' := insertBufferedRadius S m rho delta_pos epsilon_nonneg hrho
    S'.theta (upperChildIndex m) = S.theta m ∧
      S'.tau (upperChildIndex m) = rho ∧
      S'.theta (lowerChildIndex m) = rho ∧
      S'.tau (lowerChildIndex m) = S.tau m := by
  let href := insertBufferedRadius_refinesAt S m rho
    delta_pos epsilon_nonneg hrho
  exact ⟨theta_upperChild_eq href, tau_upperChild_eq href,
    theta_lowerChild_eq href, tau_lowerChild_eq href⟩

end FiniteScaleSequence

end


#print axioms FamilyStickyScaleSequenceInsertionTransportV2.FiniteScaleSequence.theta_before_eq
#print axioms FamilyStickyScaleSequenceInsertionTransportV2.FiniteScaleSequence.isLarge_after_iff
#print axioms FamilyStickyScaleSequenceInsertionTransportV2.FiniteScaleSequence.requiredGlobalPowerAt_before_eq
#print axioms FamilyStickyScaleSequenceInsertionTransportV2.FiniteScaleSequence.insertRadius_split_endpoints
#print axioms FamilyStickyScaleSequenceInsertionTransportV2.FiniteScaleSequence.insertBufferedRadius_split_endpoints

end FamilyStickyScaleSequenceInsertionTransportV2
