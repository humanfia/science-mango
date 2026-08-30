import ArchonPhysics.FiniteHistorySmallDenominatorUnionBound

/-! Consumer audit for the all-history small-denominator union bound. -/

open MeasureTheory
open ArchonPhysics.FiniteHistorySmallDenominatorUnionBound

example {Omega History Denominator : Type*}
    [MeasurableSpace Omega] [Fintype History] [Fintype Denominator]
    (mu : Measure Omega)
    (value : History → Denominator → Omega → Real) (gamma : Real)
    (budget : ENNReal)
    (hone : ∀ history : History, ∀ denominator : Denominator,
      mu {omega | |value history denominator omega| < gamma} ≤ budget) :
    mu (finiteHistorySmallDenominatorEvent value gamma) ≤
      (Fintype.card History : ENNReal) *
        (Fintype.card Denominator : ENNReal) * budget :=
  measure_finiteHistorySmallDenominatorEvent_le_card_mul_card_mul
    mu value gamma budget hone

#print axioms measure_finiteSmallDenominatorEvent_le_sum
#print axioms measure_finiteSmallDenominatorEvent_le_card_mul
#print axioms measure_finiteHistorySmallDenominatorEvent_le_card_mul_card_mul
#print axioms measure_irregularEvent_le_card_mul_card_mul
