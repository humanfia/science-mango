import FamilyStickyGrounding.FamilyStickyActualTranslationPointHitV1
import FamilyStickyGrounding.FamilyStickyDenseLatticeMultiBoxPointCountV1

open Set MeasureTheory
open scoped BigOperators ENNReal NNReal

namespace FamilyStickyActualDenseLatticePointBalanceV1

open LeanEval.Analysis.WangZahlKakeya
open Submission.Kakeya.ConvexGeometry
open FamilyStickyActualTubeTranslationGridV1
open FamilyStickyActualTranslationPointHitV1
open FamilyStickyLatticeBoxPointCountV1
open FamilyStickyDenseLatticeBoxPointCountV1
open FamilyStickyDenseLatticeMultiBoxPointCountV1

noncomputable section

/-!
# Actual dense product-lattice incidence and balance

The literal point-hit budget is

`card(other blocks) * blockHitBudget(K)`

where `blockHitBudget(K) = prod_i (ceil(side_i / spacing_i) + 1)`.
Consequently the exact local feasibility condition for the Chernoff mean is

`#tubes * blockHitBudget(K) <= card(block K) * mean`.

This module proves that implication and its paper-shaped volume form.
-/

namespace ActualTubeTranslationGrid

variable {delta : NNReal} {translation tubeIndex : Type*}
  [Fintype translation] [DecidableEq translation]
  [DecidableEq tubeIndex]

structure IsDenseMultiBoxLatticeRealization
    (G : ActualTubeTranslationGrid delta translation tubeIndex)
    (L : DenseMultiBoxLattice (Fin G.testCard)) where
  decode : translation ≃ L.Choice
  gridVector_eq : forall g, G.gridVector g = L.choiceVector (decode g)
  testBody_subset_box : forall K,
    (G.testBody K : Set Space) ⊆ (L.box K).carrier

namespace IsDenseMultiBoxLatticeRealization

variable {G : ActualTubeTranslationGrid delta translation tubeIndex}
  {L : DenseMultiBoxLattice (Fin G.testCard)}

/-- Exact enlarged dense-grid translation budget. -/
def translationBudget
    (_R : IsDenseMultiBoxLatticeRealization G L) (K : Fin G.testCard) : Nat :=
  Fintype.card (L.OtherChoice K) * L.blockHitBudget K

theorem pointHitCount_le_translationBudget
    (R : IsDenseMultiBoxLatticeRealization G L)
    (K : Fin G.testCard) (x : Space) :
    FamilyStickyActualTranslationPointHitV1.ActualTubeTranslationGrid.pointHitCount G K x <=
      R.translationBudget K := by
  classical
  let hits : Finset translation := Finset.univ.filter fun g =>
    G.gridVector g + x ∈ (G.testBody K : Set Space)
  let encode : ↥hits ->
      L.OtherChoice K × BoxLatticeResidues (L.hitBudget K) :=
    fun g =>
      (L.dropChoice K (R.decode g.1),
        boxLatticeResidue (L.hitBudget_pos K) (R.decode g.1 K))
  have hencode : Function.Injective encode := by
    intro g h heq
    apply Subtype.ext
    apply R.decode.injective
    apply L.choice_eq_of_dropChoice_eq_of_residue_eq_of_add_mem_box K x
    · apply R.testBody_subset_box K
      have hg := (Finset.mem_filter.mp g.2).2
      simpa only [R.gridVector_eq g.1, add_comm] using hg
    · apply R.testBody_subset_box K
      have hh := (Finset.mem_filter.mp h.2).2
      simpa only [R.gridVector_eq h.1, add_comm] using hh
    · exact congrArg Prod.fst heq
    · exact congrArg Prod.snd heq
  have hcard := Fintype.card_le_of_injective encode hencode
  simpa only [FamilyStickyActualTranslationPointHitV1.ActualTubeTranslationGrid.pointHitCount,
    translationBudget, hits, Fintype.card_coe, Fintype.card_prod,
    L.card_residues_eq_blockHitBudget K] using hcard

theorem hasPointHitCap
    (R : IsDenseMultiBoxLatticeRealization G L) :
    FamilyStickyActualTranslationPointHitV1.ActualTubeTranslationGrid.HasPointHitCap
      G R.translationBudget := by
  intro K _hK x
  exact R.pointHitCount_le_translationBudget K x

theorem tubeHitCount_le_translationBudget
    (R : IsDenseMultiBoxLatticeRealization G L) :
    forall K, K ∈ G.activeTests -> forall i, i ∈ G.tubes ->
      G.tubeHitCount K i <= R.translationBudget K :=
  FamilyStickyActualTranslationPointHitV1.ActualTubeTranslationGrid.tubeHitCount_le_of_hasPointHitCap
    G R.translationBudget R.hasPointHitCap

theorem card_translation_eq_card_block_mul_card_other
    (R : IsDenseMultiBoxLatticeRealization G L) (K : Fin G.testCard) :
    Fintype.card translation =
      Fintype.card (L.Block K) * Fintype.card (L.OtherChoice K) := by
  calc
    Fintype.card translation = Fintype.card L.Choice :=
      Fintype.card_congr R.decode
    _ = Fintype.card (L.Block K) * Fintype.card (L.OtherChoice K) :=
      L.card_choice_eq_card_block_mul_card_other K

/-- Exact dense feasibility inequality after cancelling the common number of
other-block choices. -/
theorem balance_of_tubeCard_mul_hitBudget_le_blockCard_mul_mean
    (R : IsDenseMultiBoxLatticeRealization G L) (K : Fin G.testCard)
    {mean : Real}
    (hlocal : (G.tubes.card : Real) * (L.blockHitBudget K : Real) <=
      (Fintype.card (L.Block K) : Real) * mean) :
    (G.tubes.card : Real) * (R.translationBudget K : Real) <=
      (Fintype.card translation : Real) * mean := by
  have hother : 0 <= (Fintype.card (L.OtherChoice K) : Real) :=
    Nat.cast_nonneg _
  calc
    (G.tubes.card : Real) * (R.translationBudget K : Real) =
        ((G.tubes.card : Real) * (L.blockHitBudget K : Real)) *
          (Fintype.card (L.OtherChoice K) : Real) := by
      simp only [translationBudget, Nat.cast_mul]
      ring
    _ <= ((Fintype.card (L.Block K) : Real) * mean) *
          (Fintype.card (L.OtherChoice K) : Real) :=
      mul_le_mul_of_nonneg_right hlocal hother
    _ = ((Fintype.card (L.Block K) : Real) *
          (Fintype.card (L.OtherChoice K) : Real)) * mean := by ring
    _ = (Fintype.card translation : Real) * mean := by
      rw [R.card_translation_eq_card_block_mul_card_other K]
      norm_num

/-- Paper-shaped volume feasibility.  The first inequality is the exact
dense-grid requirement: the reference motion volume times the enlarged hit
budget must fit inside `card(block) * volume(test)`. -/
theorem balance_of_volumeBudgets
    (R : IsDenseMultiBoxLatticeRealization G L) (K : Fin G.testCard)
    {referenceVolume mean : Real}
    (hrefPos : 0 < referenceVolume)
    (hgridVolume :
      referenceVolume * (L.blockHitBudget K : Real) <=
        (Fintype.card (L.Block K) : Real) *
          (volume (G.testBody K : Set Space)).toReal)
    (hmeanVolume :
      (G.tubes.card : Real) *
          (volume (G.testBody K : Set Space)).toReal <=
        referenceVolume * mean) :
    (G.tubes.card : Real) * (R.translationBudget K : Real) <=
      (Fintype.card translation : Real) * mean := by
  have hblockNonneg : 0 <= (Fintype.card (L.Block K) : Real) :=
    Nat.cast_nonneg _
  have htubeNonneg : 0 <= (G.tubes.card : Real) := Nat.cast_nonneg _
  have hgridRatio :
      (L.blockHitBudget K : Real) <=
        (Fintype.card (L.Block K) : Real) *
          (volume (G.testBody K : Set Space)).toReal / referenceVolume := by
    apply (le_div_iff₀ hrefPos).2
    simpa [mul_assoc, mul_comm, mul_left_comm] using hgridVolume
  have hmeanRatio :
      (G.tubes.card : Real) *
          (volume (G.testBody K : Set Space)).toReal / referenceVolume <=
        mean := by
    apply (div_le_iff₀ hrefPos).2
    simpa [mul_assoc, mul_comm] using hmeanVolume
  apply R.balance_of_tubeCard_mul_hitBudget_le_blockCard_mul_mean K
  calc
    (G.tubes.card : Real) * (L.blockHitBudget K : Real) <=
        (G.tubes.card : Real) *
          ((Fintype.card (L.Block K) : Real) *
            (volume (G.testBody K : Set Space)).toReal / referenceVolume) :=
      mul_le_mul_of_nonneg_left hgridRatio htubeNonneg
    _ = (Fintype.card (L.Block K) : Real) *
        ((G.tubes.card : Real) *
          (volume (G.testBody K : Set Space)).toReal / referenceVolume) := by
      ring
    _ <= (Fintype.card (L.Block K) : Real) * mean :=
      mul_le_mul_of_nonneg_left hmeanRatio hblockNonneg

#print axioms pointHitCount_le_translationBudget
#print axioms tubeHitCount_le_translationBudget
#print axioms card_translation_eq_card_block_mul_card_other
#print axioms balance_of_tubeCard_mul_hitBudget_le_blockCard_mul_mean
#print axioms balance_of_volumeBudgets

end IsDenseMultiBoxLatticeRealization

end ActualTubeTranslationGrid

end

end FamilyStickyActualDenseLatticePointBalanceV1
