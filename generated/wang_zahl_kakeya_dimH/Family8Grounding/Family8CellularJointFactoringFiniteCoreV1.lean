import Mathlib.Tactic

set_option autoImplicit false
set_option warningAsError true

open scoped BigOperators ENNReal

namespace Family8CellularJointFactoringFiniteCoreV1

noncomputable section

/-!
# A finite cellular-joint factoring core

This file contains only the finite incidence and weight bookkeeping that is
needed after a geometric cellular-joint construction has produced its edge
set.  In particular, it does not assert that such a construction exists and
does not identify labels with spatial cells or measurable shadings.

An edge `(p, q)` records that the parent label `p` is incident to the cell
label `q`.  Every parent-cell set, touched-cell set, and right degree below is
computed from this one edge set.  This makes the P2/P4 compatibility literal
rather than an additional coherence assumption.
-/

/-- A finite edge set carrying a strictly positive `ENNReal` weight on every
edge.  Values of `omega` away from `edges` are deliberately irrelevant. -/
structure WeightedCellularEdges (parent cell : Type*) where
  edges : Finset (parent × cell)
  omega : parent × cell → ENNReal
  omega_pos : ∀ e ∈ edges, 0 < omega e

section Incidence

variable {parent cell child : Type*}
variable [Fintype parent] [DecidableEq parent]
variable [Fintype cell] [DecidableEq cell]

/-- The cell labels incident to one parent, computed from `E`. -/
def parentCells (E : Finset (parent × cell)) (p : parent) : Finset cell :=
  Finset.univ.filter fun q => (p, q) ∈ E

omit [Fintype parent] in
@[simp] theorem mem_parentCells_iff
    (E : Finset (parent × cell)) (p : parent) (q : cell) :
    q ∈ parentCells E p ↔ (p, q) ∈ E := by
  simp [parentCells]

/-- The parent labels incident to one cell, computed from the same `E`. -/
def activeParentsAt (E : Finset (parent × cell)) (q : cell) : Finset parent :=
  Finset.univ.filter fun p => (p, q) ∈ E

omit [Fintype cell] in
@[simp] theorem mem_activeParentsAt_iff
    (E : Finset (parent × cell)) (p : parent) (q : cell) :
    p ∈ activeParentsAt E q ↔ (p, q) ∈ E := by
  simp [activeParentsAt]

/-- The cell labels touched by at least one edge. -/
def rightCells (E : Finset (parent × cell)) : Finset cell :=
  E.image Prod.snd

omit [Fintype parent] [DecidableEq parent] [Fintype cell] in
theorem mem_rightCells_iff
    (E : Finset (parent × cell)) (q : cell) :
    q ∈ rightCells E ↔ ∃ p : parent, (p, q) ∈ E := by
  constructor
  · intro hq
    obtain ⟨e, he, heq⟩ := Finset.mem_image.mp hq
    refine ⟨e.1, ?_⟩
    subst q
    simpa using he
  · rintro ⟨p, hp⟩
    exact Finset.mem_image.mpr ⟨(p, q), hp, rfl⟩

/-- The right degree of a cell is the number of parent labels joined to it. -/
def rightDegree (E : Finset (parent × cell)) (q : cell) : Nat :=
  (activeParentsAt E q).card

/-- `sub` is right-saturated in `E` when it is a subedge and, as soon as it
touches a cell, it contains every original edge at that cell. -/
def IsRightSaturatedSubedge
    (E sub : Finset (parent × cell)) : Prop :=
  sub ⊆ E ∧
    ∀ p q, (p, q) ∈ E → q ∈ rightCells sub → (p, q) ∈ sub

omit [Fintype parent] [DecidableEq parent] [Fintype cell] in
theorem IsRightSaturatedSubedge.mem_iff
    {E sub : Finset (parent × cell)}
    (h : IsRightSaturatedSubedge E sub) (p : parent) (q : cell) :
    (p, q) ∈ sub ↔ (p, q) ∈ E ∧ q ∈ rightCells sub := by
  constructor
  · intro hpq
    exact ⟨h.1 hpq, (mem_rightCells_iff sub q).2 ⟨p, hpq⟩⟩
  · rintro ⟨hpq, hq⟩
    exact h.2 p q hpq hq

omit [Fintype parent] [DecidableEq parent] [Fintype cell] in
theorem IsRightSaturatedSubedge.rightCells_subset
    {E sub : Finset (parent × cell)}
    (h : IsRightSaturatedSubedge E sub) :
    rightCells sub ⊆ rightCells E := by
  intro q hq
  obtain ⟨p, hpq⟩ := (mem_rightCells_iff sub q).1 hq
  exact (mem_rightCells_iff E q).2 ⟨p, h.1 hpq⟩

omit [Fintype cell] in
/-- Saturation preserves the full parent fibre, hence the right degree, on
every selected cell.  This is the finite P4 compatibility mechanism. -/
theorem IsRightSaturatedSubedge.activeParentsAt_eq
    {E sub : Finset (parent × cell)}
    (h : IsRightSaturatedSubedge E sub) {q : cell}
    (hq : q ∈ rightCells sub) :
    activeParentsAt sub q = activeParentsAt E q := by
  ext p
  simp only [mem_activeParentsAt_iff]
  constructor
  · intro hpq
    exact h.1 hpq
  · intro hpq
    exact h.2 p q hpq hq

omit [Fintype cell] in
theorem IsRightSaturatedSubedge.rightDegree_eq
    {E sub : Finset (parent × cell)}
    (h : IsRightSaturatedSubedge E sub) {q : cell}
    (hq : q ∈ rightCells sub) :
    rightDegree sub q = rightDegree E q := by
  rw [rightDegree, rightDegree, h.activeParentsAt_eq hq]

/-- A right-degree band on an explicitly selected family of cells. -/
def HasRightDegreeBand
    (E : Finset (parent × cell)) (selected : Finset cell) (d : Nat) : Prop :=
  selected ⊆ rightCells E ∧
    ∀ q ∈ selected, d ≤ rightDegree E q ∧ rightDegree E q < 2 * d

omit [Fintype cell] in
/-- A band checked in the original edge set transfers to a right-saturated
subedge, because both statements use exactly the same parent-cell edges. -/
theorem IsRightSaturatedSubedge.hasRightDegreeBand
    {E sub : Finset (parent × cell)}
    (h : IsRightSaturatedSubedge E sub) (d : Nat)
    (hband : ∀ q ∈ rightCells sub,
      d ≤ rightDegree E q ∧ rightDegree E q < 2 * d) :
    HasRightDegreeBand sub (rightCells sub) d := by
  refine ⟨Finset.Subset.rfl, ?_⟩
  intro q hq
  rw [h.rightDegree_eq hq]
  exact hband q hq

/-- A child label is retained at its labelled cell exactly when its
parent-cell pair is an edge of `E`. -/
def IsRetainedChild
    (E : Finset (parent × cell))
    (parentOf : child → parent) (cellOf : child → cell) (i : child) : Prop :=
  (parentOf i, cellOf i) ∈ E

omit [Fintype parent] in
/-- Finite P2: the very same edge that retains a child also puts its cell in
the cell family of its parent.  No independent cover can drift out of sync. -/
theorem p2_cell_mem_parentCells_of_retainedChild
    (E : Finset (parent × cell))
    (parentOf : child → parent) (cellOf : child → cell) (i : child)
    (hi : IsRetainedChild E parentOf cellOf i) :
    cellOf i ∈ parentCells E (parentOf i) := by
  exact (mem_parentCells_iff E (parentOf i) (cellOf i)).2 hi

/-- Total fine/child multiplicity at one cell, aggregated over exactly the
parents incident to that cell. -/
def totalChildMultiplicityAt
    (E : Finset (parent × cell))
    (innerMultiplicity : parent → cell → Nat) (q : cell) : Nat :=
  ∑ p ∈ activeParentsAt E q, innerMultiplicity p q

omit [Fintype cell] in
/-- Finite P5.  If every active parent contributes less than `2 * mu` and
there are less than `2 * d` active parents, then the total child
multiplicity is less than `4 * mu * d`. -/
theorem p5_totalChildMultiplicityAt_lt_four_mul
    (E : Finset (parent × cell))
    (innerMultiplicity : parent → cell → Nat) (q : cell)
    (mu d : Nat) (hmu : 0 < mu)
    (hinner : ∀ p ∈ activeParentsAt E q,
      innerMultiplicity p q < 2 * mu)
    (houter : rightDegree E q < 2 * d) :
    totalChildMultiplicityAt E innerMultiplicity q < 4 * mu * d := by
  have hsum : totalChildMultiplicityAt E innerMultiplicity q ≤
      (activeParentsAt E q).card * (2 * mu) := by
    unfold totalChildMultiplicityAt
    calc
      (∑ p ∈ activeParentsAt E q, innerMultiplicity p q) ≤
          ∑ _p ∈ activeParentsAt E q, 2 * mu := by
        apply Finset.sum_le_sum
        intro p hp
        exact Nat.le_of_lt (hinner p hp)
      _ = (activeParentsAt E q).card * (2 * mu) := by simp
  have hcard : (activeParentsAt E q).card < 2 * d := by
    simpa [rightDegree] using houter
  have hproduct : (activeParentsAt E q).card * (2 * mu) <
      (2 * d) * (2 * mu) :=
    Nat.mul_lt_mul_of_pos_right hcard (by omega)
  calc
    totalChildMultiplicityAt E innerMultiplicity q ≤
        (activeParentsAt E q).card * (2 * mu) := hsum
    _ < (2 * d) * (2 * mu) := hproduct
    _ = 4 * mu * d := by ring

end Incidence

section Weights

variable {edge : Type*} [DecidableEq edge]

/-- Total weight of a finite edge set. -/
def edgeWeight (E : Finset edge) (omega : edge → ENNReal) : ENNReal :=
  ∑ e ∈ E, omega e

/-- The half-open dyadic weight band `[w, 2w)`. -/
def InHalfOpenWeightBand
    (E : Finset edge) (omega : edge → ENNReal) (w : ENNReal) : Prop :=
  ∀ e ∈ E, w ≤ omega e ∧ omega e < 2 * w

omit [DecidableEq edge] in
theorem edgeWeight_le_card_mul_two
    (E : Finset edge) (omega : edge → ENNReal) (w : ENNReal)
    (hband : InHalfOpenWeightBand E omega w) :
    edgeWeight E omega ≤ (E.card : ENNReal) * (2 * w) := by
  unfold edgeWeight
  calc
    (∑ e ∈ E, omega e) ≤ ∑ _e ∈ E, 2 * w := by
      apply Finset.sum_le_sum
      intro e he
      exact (hband e he).2.le
    _ = (E.card : ENNReal) * (2 * w) := by
      simp [nsmul_eq_mul]

omit [DecidableEq edge] in
theorem card_mul_lower_le_edgeWeight
    (E : Finset edge) (omega : edge → ENNReal) (w : ENNReal)
    (hband : InHalfOpenWeightBand E omega w) :
    (E.card : ENNReal) * w ≤ edgeWeight E omega := by
  unfold edgeWeight
  calc
    (E.card : ENNReal) * w = ∑ _e ∈ E, w := by
      simp [nsmul_eq_mul]
    _ ≤ ∑ e ∈ E, omega e := by
      apply Finset.sum_le_sum
      intro e he
      exact (hband e he).1

omit [DecidableEq edge] in
/-- Core whole-incidence lift, in a division-free form valid in `ENNReal`:
cardinality retention by `c` inside a factor-two weight band implies
`c * originalWeight ≤ 2 * retainedWeight`. -/
theorem wholeIncidenceLift_c_mul_edgeWeight_le_two_mul
    (E sub : Finset edge) (omega : edge → ENNReal) (w c : ENNReal)
    (hsub : sub ⊆ E)
    (hband : InHalfOpenWeightBand E omega w)
    (hcard : c * (E.card : ENNReal) ≤ (sub.card : ENNReal)) :
    c * edgeWeight E omega ≤ 2 * edgeWeight sub omega := by
  have hupper := edgeWeight_le_card_mul_two E omega w hband
  have hsubband : InHalfOpenWeightBand sub omega w := by
    intro e he
    exact hband e (hsub he)
  have hlower := card_mul_lower_le_edgeWeight sub omega w hsubband
  calc
    c * edgeWeight E omega ≤
        c * ((E.card : ENNReal) * (2 * w)) :=
      mul_le_mul' le_rfl hupper
    _ = 2 * ((c * (E.card : ENNReal)) * w) := by ac_rfl
    _ ≤ 2 * ((sub.card : ENNReal) * w) := by
      exact mul_le_mul' le_rfl (mul_le_mul' hcard le_rfl)
    _ ≤ 2 * edgeWeight sub omega := mul_le_mul' le_rfl hlower

omit [DecidableEq edge] in
/-- The usual retained-fraction form of the whole-incidence lift. -/
theorem wholeIncidenceLift_half_fraction_mul_le
    (E sub : Finset edge) (omega : edge → ENNReal) (w c : ENNReal)
    (hsub : sub ⊆ E)
    (hband : InHalfOpenWeightBand E omega w)
    (hcard : c * (E.card : ENNReal) ≤ (sub.card : ENNReal)) :
    (c / 2) * edgeWeight E omega ≤ edgeWeight sub omega := by
  calc
    (c / 2) * edgeWeight E omega =
        (c * edgeWeight E omega) / 2 :=
      by
        simp only [ENNReal.div_eq_inv_mul]
        ac_rfl
    _ ≤ edgeWeight sub omega := by
      apply (ENNReal.div_le_iff (by norm_num) (by norm_num)).2
      simpa [mul_comm] using
        wholeIncidenceLift_c_mul_edgeWeight_le_two_mul
          E sub omega w c hsub hband hcard

/-- Labelled parent mass when every edge-label carries the same positive
finite cell volume.  This is bookkeeping, not a geometric existence claim. -/
def labelledParentMass (E : Finset edge) (cellVolume : ENNReal) : ENNReal :=
  (E.card : ENNReal) * cellVolume

omit [DecidableEq edge] in
theorem card_fraction_of_labelledParentMass
    (E sub : Finset edge) (cellVolume c : ENNReal)
    (hvolume0 : cellVolume ≠ 0) (hvolumeTop : cellVolume ≠ ∞)
    (hmass : c * labelledParentMass E cellVolume ≤
      labelledParentMass sub cellVolume) :
    c * (E.card : ENNReal) ≤ (sub.card : ENNReal) := by
  apply (ENNReal.mul_le_mul_iff_right hvolume0 hvolumeTop).mp
  calc
    cellVolume * (c * (E.card : ENNReal)) =
        c * labelledParentMass E cellVolume := by
      unfold labelledParentMass
      ac_rfl
    _ ≤ labelledParentMass sub cellVolume := hmass
    _ = cellVolume * (sub.card : ENNReal) := by
      unfold labelledParentMass
      ac_rfl

omit [DecidableEq edge] in
/-- Equal-volume labelled-parent mass retention feeds the same weighted
whole-incidence conclusion after cancelling the common finite cell volume. -/
theorem wholeIncidenceLift_of_labelledParentMass
    (E sub : Finset edge) (omega : edge → ENNReal)
    (w c cellVolume : ENNReal)
    (hsub : sub ⊆ E)
    (hband : InHalfOpenWeightBand E omega w)
    (hvolume0 : cellVolume ≠ 0) (hvolumeTop : cellVolume ≠ ∞)
    (hmass : c * labelledParentMass E cellVolume ≤
      labelledParentMass sub cellVolume) :
    (c / 2) * edgeWeight E omega ≤ edgeWeight sub omega := by
  apply wholeIncidenceLift_half_fraction_mul_le E sub omega w c hsub hband
  exact card_fraction_of_labelledParentMass
    E sub cellVolume c hvolume0 hvolumeTop hmass

end Weights

#print axioms mem_parentCells_iff
#print axioms IsRightSaturatedSubedge.rightDegree_eq
#print axioms IsRightSaturatedSubedge.hasRightDegreeBand
#print axioms p2_cell_mem_parentCells_of_retainedChild
#print axioms p5_totalChildMultiplicityAt_lt_four_mul
#print axioms wholeIncidenceLift_c_mul_edgeWeight_le_two_mul
#print axioms wholeIncidenceLift_half_fraction_mul_le
#print axioms wholeIncidenceLift_of_labelledParentMass

end

end Family8CellularJointFactoringFiniteCoreV1
