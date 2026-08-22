import FamilyStickyGrounding.FamilyStickyActualTubeTranslationGridV1

open scoped BigOperators

namespace FamilyStickyRandomPaperTailNumericsV1

open FamilyStickyActualTubeTranslationGridV1

noncomputable section

/-!
# Paper-shaped exponential tail room

With Chernoff parameter `lambda = cap⁻¹`, the local chord factor is
`1 + (mean/cap) * (exp 1 - 1)`.  If `repetitions * mean <= cap`, its product
is bounded by the fixed constant `exp (exp 1 - 1)`.  This turns the exact
finite numerical condition into the source-shaped requirement
`#tests * exp (exp 1 - 1) < exp A` and yields threshold `A * cap`.
-/

/-- The local chord moment accumulated across all independent choices costs
only a fixed exponential constant in the paper's regime. -/
theorem chord_factor_pow_le_exp_fixed
    (repetitions : Nat) {mean cap : Real}
    (hmean : 0 <= mean) (hcap : 0 < cap)
    (hscale : (repetitions : Real) * mean <= cap) :
    (1 + (mean / cap) * (Real.exp 1 - 1)) ^ repetitions <=
      Real.exp (Real.exp 1 - 1) := by
  let a : Real := (mean / cap) * (Real.exp 1 - 1)
  have hexp : 0 <= Real.exp 1 - 1 := by
    exact sub_nonneg.mpr (Real.one_le_exp_iff.mpr zero_le_one)
  have ha : 0 <= a := mul_nonneg (div_nonneg hmean hcap.le) hexp
  have hratio : (repetitions : Real) * mean / cap <= 1 :=
    (div_le_one hcap).mpr hscale
  have hJa : (repetitions : Real) * a <= Real.exp 1 - 1 := by
    calc
      (repetitions : Real) * a =
          ((repetitions : Real) * mean / cap) *
            (Real.exp 1 - 1) := by
        simp only [a]
        ring
      _ <= 1 * (Real.exp 1 - 1) :=
        mul_le_mul_of_nonneg_right hratio hexp
      _ = Real.exp 1 - 1 := one_mul _
  calc
    (1 + (mean / cap) * (Real.exp 1 - 1)) ^ repetitions =
        (1 + a) ^ repetitions := by rfl
    _ <= (Real.exp a) ^ repetitions := by
      apply pow_le_pow_left₀
      · positivity
      · simpa [add_comm] using Real.add_one_le_exp a
    _ = Real.exp ((repetitions : Real) * a) :=
      (Real.exp_nat_mul a repetitions).symm
    _ <= Real.exp (Real.exp 1 - 1) := Real.exp_le_exp.mpr hJa

namespace ActualTubeTranslationGrid

open FamilyStickyActualTubeTranslationV1
open FamilyStickyRandomFiniteChernoffV3
open FamilyStickyRandomTranslationIncidenceV1
open FamilyStickyRandomTranslationGridAdapterV1

variable {delta : NNReal} {translation tubeIndex : Type*}
  [Fintype translation] [Nonempty translation]
  [DecidableEq translation] [DecidableEq tubeIndex]

/-- Paper-shaped finite random-motion producer.  The awkward full moment
inequality is discharged from the scale balance and one explicit tail-room
condition. -/
theorem exists_grid_translations_singleLoad_le_A_mul_cap
    (G : ActualTubeTranslationGrid delta translation tubeIndex)
    (translationBudget : Fin G.testCard -> Nat) (repetitions : Nat)
    {cap mean A : Real}
    (hcap : 0 < cap) (hmean : 0 <= mean)
    (hscale : (repetitions : Real) * mean <= cap)
    (hloadCap : forall K, K ∈ G.activeTests -> forall g,
      (G.singleLoad K g : Real) <= cap)
    (hgrid : forall K, K ∈ G.activeTests -> forall i, i ∈ G.tubes ->
      G.tubeHitCount K i <= translationBudget K)
    (hbalance : forall K, K ∈ G.activeTests ->
      (G.tubes.card : Real) * (translationBudget K : Real) <=
        (Fintype.card translation : Real) * mean)
    (htailRoom :
      (G.activeTests.card : Real) * Real.exp (Real.exp 1 - 1) <
        Real.exp A) :
    exists omega : Fin repetitions -> translation,
      forall K, K ∈ G.activeTests ->
        (∑ j, (G.singleLoad K (omega j) : Real)) <= A * cap := by
  have hfactor :=
    chord_factor_pow_le_exp_fixed repetitions hmean hcap hscale
  have hcardPos : 0 < (Fintype.card translation : Real) := by
    exact_mod_cast Fintype.card_pos
  have hcardPowPos :
      0 < (Fintype.card translation : Real) ^ repetitions :=
    pow_pos hcardPos repetitions
  have hmoment :
      ((Fintype.card translation : Real) *
          (1 + (mean / cap) * (Real.exp 1 - 1))) ^ repetitions <=
        (Fintype.card translation : Real) ^ repetitions *
          Real.exp (Real.exp 1 - 1) := by
    rw [mul_pow]
    exact mul_le_mul_of_nonneg_left hfactor
      (pow_nonneg (Nat.cast_nonneg _) repetitions)
  have hcore :
      (G.activeTests.card : Real) *
          ((Fintype.card translation : Real) *
            (1 + (mean / cap) * (Real.exp 1 - 1))) ^ repetitions <
        (Fintype.card translation : Real) ^ repetitions * Real.exp A := by
    calc
      (G.activeTests.card : Real) *
          ((Fintype.card translation : Real) *
            (1 + (mean / cap) * (Real.exp 1 - 1))) ^ repetitions <=
        (G.activeTests.card : Real) *
          ((Fintype.card translation : Real) ^ repetitions *
            Real.exp (Real.exp 1 - 1)) :=
        mul_le_mul_of_nonneg_left hmoment (Nat.cast_nonneg _)
      _ = (Fintype.card translation : Real) ^ repetitions *
          ((G.activeTests.card : Real) *
            Real.exp (Real.exp 1 - 1)) := by ring
      _ < (Fintype.card translation : Real) ^ repetitions * Real.exp A :=
        mul_lt_mul_of_pos_left htailRoom hcardPowPos
  have hinvCap : cap⁻¹ * cap = 1 := by
    exact inv_mul_cancel₀ hcap.ne'
  have hinvThreshold : cap⁻¹ * (A * cap) = A := by
    field_simp [hcap.ne']
  have hcardOutcomes :
      ((Finset.univ : Finset (Fin repetitions -> translation)).card : Real) =
        (Fintype.card translation : Real) ^ repetitions := by
    simp
  apply G.exists_grid_translations_singleLoad_le translationBudget repetitions
    hcap (inv_nonneg.mpr hcap.le) hloadCap hgrid hbalance
  simpa only [hinvCap, hinvThreshold, hcardOutcomes] using hcore

#print axioms exists_grid_translations_singleLoad_le_A_mul_cap

end ActualTubeTranslationGrid

#print axioms chord_factor_pow_le_exp_fixed

end

end FamilyStickyRandomPaperTailNumericsV1
