import ArchonPhysics.FreeFPUTBranchingHistoryDenominatorEnumeration

/-!
# Finite-union bounds for high-order small-denominator histories

The branching enumeration identifies every obstruction to deterministic
oscillatory integration by parts with a finite family of scalar denominators.
This file supplies the exact probability-theory step needed next: a uniform
one-denominator small-ball estimate controls the event that any denominator
in any finite history is small.

No independence between denominators or histories is assumed.  Consequently
the loss is the transparent product of the two finite cardinalities.  The
result is intended to be instantiated with the exact occurrence count from
`FreeFPUTBranchingHistoryDenominatorEnumeration`.
-/

namespace ArchonPhysics.FiniteHistorySmallDenominatorUnionBound

open scoped BigOperators ENNReal
open MeasureTheory

noncomputable section

variable {Omega : Type*} [MeasurableSpace Omega]

/-- The event that at least one member of a finite scalar family lies inside
the open gap `(-gamma, gamma)`. -/
def finiteSmallDenominatorEvent
    {I : Type*} [Fintype I]
    (denominator : I → Omega → Real) (gamma : Real) : Set Omega :=
  ⋃ i : I, {omega | |denominator i omega| < gamma}

omit [MeasurableSpace Omega] in
theorem mem_finiteSmallDenominatorEvent_iff
    {I : Type*} [Fintype I]
    (denominator : I → Omega → Real) (gamma : Real) (omega : Omega) :
    omega ∈ finiteSmallDenominatorEvent denominator gamma ↔
      ∃ i : I, |denominator i omega| < gamma := by
  simp [finiteSmallDenominatorEvent]

/-- Finite subadditivity in the exact form used for denominator families. -/
theorem measure_finiteSmallDenominatorEvent_le_sum
    {I : Type*} [Fintype I]
    (mu : Measure Omega) (denominator : I → Omega → Real) (gamma : Real) :
    mu (finiteSmallDenominatorEvent denominator gamma) ≤
      ∑ i : I, mu {omega | |denominator i omega| < gamma} := by
  unfold finiteSmallDenominatorEvent
  exact measure_iUnion_fintype_le mu _

/-- A uniform one-denominator small-ball estimate needs no independence to
control the complete finite family. -/
theorem measure_finiteSmallDenominatorEvent_le_card_mul
    {I : Type*} [Fintype I]
    (mu : Measure Omega) (denominator : I → Omega → Real) (gamma : Real)
    (budget : ENNReal)
    (hone : ∀ i : I,
      mu {omega | |denominator i omega| < gamma} ≤ budget) :
    mu (finiteSmallDenominatorEvent denominator gamma) ≤
      (Fintype.card I : ENNReal) * budget := by
  calc
    mu (finiteSmallDenominatorEvent denominator gamma) ≤
        ∑ i : I, mu {omega | |denominator i omega| < gamma} :=
      measure_finiteSmallDenominatorEvent_le_sum
        mu denominator gamma
    _ ≤ ∑ _i : I, budget := by
      gcongr with i
      exact hone i
    _ = (Fintype.card I : ENNReal) * budget := by simp

/-- Small denominators across a finite family of histories and a finite
family of occurrences within each history. -/
def finiteHistorySmallDenominatorEvent
    {History Denominator : Type*} [Fintype History] [Fintype Denominator]
    (value : History → Denominator → Omega → Real) (gamma : Real) : Set Omega :=
  ⋃ history : History,
    finiteSmallDenominatorEvent (value history) gamma

omit [MeasurableSpace Omega] in
theorem mem_finiteHistorySmallDenominatorEvent_iff
    {History Denominator : Type*} [Fintype History] [Fintype Denominator]
    (value : History → Denominator → Omega → Real) (gamma : Real)
    (omega : Omega) :
    omega ∈ finiteHistorySmallDenominatorEvent value gamma ↔
      ∃ history : History, ∃ denominator : Denominator,
        |value history denominator omega| < gamma := by
  simp [finiteHistorySmallDenominatorEvent,
    mem_finiteSmallDenominatorEvent_iff]

/-- Two-level union bound.  It makes the complete loss
`#histories * #denominators * oneSiteBudget` explicit. -/
theorem measure_finiteHistorySmallDenominatorEvent_le_card_mul_card_mul
    {History Denominator : Type*} [Fintype History] [Fintype Denominator]
    (mu : Measure Omega)
    (value : History → Denominator → Omega → Real) (gamma : Real)
    (budget : ENNReal)
    (hone : ∀ history : History, ∀ denominator : Denominator,
      mu {omega | |value history denominator omega| < gamma} ≤ budget) :
    mu (finiteHistorySmallDenominatorEvent value gamma) ≤
      (Fintype.card History : ENNReal) *
        (Fintype.card Denominator : ENNReal) * budget := by
  unfold finiteHistorySmallDenominatorEvent
  calc
    mu (⋃ history : History,
        finiteSmallDenominatorEvent (value history) gamma) ≤
      ∑ history : History,
        mu (finiteSmallDenominatorEvent (value history) gamma) :=
      measure_iUnion_fintype_le mu _
    _ ≤ ∑ _history : History,
        (Fintype.card Denominator : ENNReal) * budget := by
      gcongr with history
      exact measure_finiteSmallDenominatorEvent_le_card_mul
        mu (value history) gamma budget (hone history)
    _ = (Fintype.card History : ENNReal) *
        (Fintype.card Denominator : ENNReal) * budget := by
      simp [mul_assoc]

/-- If a concrete irregular-history event is identified with the explicit
finite union, the same cardinality bound transfers verbatim. -/
theorem measure_irregularEvent_le_card_mul_card_mul
    {History Denominator : Type*} [Fintype History] [Fintype Denominator]
    (mu : Measure Omega) (irregularEvent : Set Omega)
    (value : History → Denominator → Omega → Real) (gamma : Real)
    (budget : ENNReal)
    (hidentify : irregularEvent =
      finiteHistorySmallDenominatorEvent value gamma)
    (hone : ∀ history : History, ∀ denominator : Denominator,
      mu {omega | |value history denominator omega| < gamma} ≤ budget) :
    mu irregularEvent ≤
      (Fintype.card History : ENNReal) *
        (Fintype.card Denominator : ENNReal) * budget := by
  rw [hidentify]
  exact measure_finiteHistorySmallDenominatorEvent_le_card_mul_card_mul
    mu value gamma budget hone

end

end ArchonPhysics.FiniteHistorySmallDenominatorUnionBound
