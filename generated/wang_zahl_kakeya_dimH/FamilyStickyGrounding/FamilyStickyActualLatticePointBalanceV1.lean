import FamilyStickyGrounding.FamilyStickyActualTranslationPointHitV1
import FamilyStickyGrounding.FamilyStickyLatticeMultiBoxPointCountV1

open Set MeasureTheory
open scoped BigOperators ENNReal NNReal

namespace FamilyStickyActualLatticePointBalanceV1

open LeanEval.Analysis.WangZahlKakeya
open Submission.Kakeya.ConvexGeometry
open FamilyStickyActualTubeTranslationGridV1
open FamilyStickyActualTranslationPointHitV1
open FamilyStickyLatticeBoxPointCountV1
open FamilyStickyLatticeMultiBoxPointCountV1

noncomputable section

/-!
# Actual tube-grid adapter for the simultaneous box lattice

An arbitrary finite translation type is identified with the explicit product
lattice.  Its actual vectors are the product-lattice vectors, and every
actual convex test body is contained in its certified oriented frame box.
The finite fibre count then supplies the literal point cap and hence the
per-tube grid-incidence cap.  A separate theorem converts the exact product
cardinality into the `hbalance` inequality used by the Chernoff adapter.
-/

namespace ActualTubeTranslationGrid

variable {delta : NNReal} {translation tubeIndex : Type*}
  [Fintype translation] [DecidableEq translation]
  [DecidableEq tubeIndex]

/-- Concrete identification of an actual translation grid with the
test-indexed product of explicit oriented box lattices. -/
structure IsMultiBoxLatticeRealization
    (G : ActualTubeTranslationGrid delta translation tubeIndex)
    (L : MultiBoxLattice (Fin G.testCard)) where
  decode : translation ≃ L.Choice
  gridVector_eq : forall g, G.gridVector g = L.choiceVector (decode g)
  testBody_subset_box : forall K,
    (G.testBody K : Set Space) ⊆ (L.box K).carrier

namespace IsMultiBoxLatticeRealization

variable {G : ActualTubeTranslationGrid delta translation tubeIndex}
  {L : MultiBoxLattice (Fin G.testCard)}

/-- Exact integer budget supplied to one actual test by all lattice blocks
other than that test's own block. -/
def translationBudget
    (_R : IsMultiBoxLatticeRealization G L) (K : Fin G.testCard) : Nat :=
  Fintype.card (L.OtherChoice K)

/-- Literal actual point hits are bounded by the explicit product-lattice
fibre cardinality. -/
theorem pointHitCount_le_translationBudget
    (R : IsMultiBoxLatticeRealization G L)
    (K : Fin G.testCard) (x : Space) :
    FamilyStickyActualTranslationPointHitV1.ActualTubeTranslationGrid.pointHitCount G K x <= R.translationBudget K := by
  classical
  let hits : Finset translation := Finset.univ.filter fun g =>
    G.gridVector g + x ∈ (G.testBody K : Set Space)
  let drop : ↥hits -> L.OtherChoice K :=
    fun g => L.dropChoice K (R.decode g.1)
  have hdrop : Function.Injective drop := by
    intro g h heq
    apply Subtype.ext
    apply R.decode.injective
    apply L.choice_eq_of_dropChoice_eq_of_add_mem_box K x
    · apply R.testBody_subset_box K
      have hg := (Finset.mem_filter.mp g.2).2
      simpa only [R.gridVector_eq g.1, add_comm] using hg
    · apply R.testBody_subset_box K
      have hh := (Finset.mem_filter.mp h.2).2
      simpa only [R.gridVector_eq h.1, add_comm] using hh
    · exact heq
  have hcard := Fintype.card_le_of_injective drop hdrop
  simpa only [FamilyStickyActualTranslationPointHitV1.ActualTubeTranslationGrid.pointHitCount,
    translationBudget, hits, Fintype.card_coe] using hcard

/-- The explicit lattice supplies the `HasPointHitCap` interface without a
point-count assumption. -/
theorem hasPointHitCap
    (R : IsMultiBoxLatticeRealization G L) :
    FamilyStickyActualTranslationPointHitV1.ActualTubeTranslationGrid.HasPointHitCap G R.translationBudget := by
  intro K _hK x
  exact R.pointHitCount_le_translationBudget K x

/-- Therefore every actual tube has the grid-incidence cap required by the
finite Chernoff adapter. -/
theorem tubeHitCount_le_translationBudget
    (R : IsMultiBoxLatticeRealization G L) :
    forall K, K ∈ G.activeTests -> forall i, i ∈ G.tubes ->
      G.tubeHitCount K i <= R.translationBudget K :=
  FamilyStickyActualTranslationPointHitV1.ActualTubeTranslationGrid.tubeHitCount_le_of_hasPointHitCap G R.translationBudget R.hasPointHitCap

/-- The actual translation cardinality splits exactly into one distinguished
lattice block and the other-block budget. -/
theorem card_translation_eq_card_block_mul_translationBudget
    (R : IsMultiBoxLatticeRealization G L) (K : Fin G.testCard) :
    Fintype.card translation =
      Fintype.card (L.Block K) * R.translationBudget K := by
  calc
    Fintype.card translation = Fintype.card L.Choice :=
      Fintype.card_congr R.decode
    _ = Fintype.card (L.Block K) * Fintype.card (L.OtherChoice K) :=
      L.card_choice_eq_card_block_mul_card_other K
    _ = Fintype.card (L.Block K) * R.translationBudget K := rfl

/-- Exact product-cardinality balance.  It remains only to show that the
single distinguished block is large enough for the requested mean. -/
theorem balance_of_tubeCard_le_blockCard_mul_mean
    (R : IsMultiBoxLatticeRealization G L) (K : Fin G.testCard)
    {mean : Real}
    (hlocal : (G.tubes.card : Real) <=
      (Fintype.card (L.Block K) : Real) * mean) :
    (G.tubes.card : Real) * (R.translationBudget K : Real) <=
      (Fintype.card translation : Real) * mean := by
  have hother : 0 <= (R.translationBudget K : Real) := Nat.cast_nonneg _
  calc
    (G.tubes.card : Real) * (R.translationBudget K : Real) <=
        ((Fintype.card (L.Block K) : Real) * mean) *
          (R.translationBudget K : Real) :=
      mul_le_mul_of_nonneg_right hlocal hother
    _ = ((Fintype.card (L.Block K) : Real) *
          (R.translationBudget K : Real)) * mean := by ring
    _ = (Fintype.card translation : Real) * mean := by
      rw [R.card_translation_eq_card_block_mul_translationBudget K]
      norm_num

/-- Paper-shaped volume form of the local balance.  The first hypothesis says
the finite block has enough sites relative to the reference motion volume;
the second is the desired mean budget for the actual test-body volume. -/
theorem balance_of_volumeBudgets
    (R : IsMultiBoxLatticeRealization G L) (K : Fin G.testCard)
    {referenceVolume mean : Real}
    (hrefPos : 0 < referenceVolume)
    (hblockVolume : referenceVolume <=
      (Fintype.card (L.Block K) : Real) *
        (volume (G.testBody K : Set Space)).toReal)
    (hmeanVolume :
      (G.tubes.card : Real) *
          (volume (G.testBody K : Set Space)).toReal <=
        referenceVolume * mean) :
    (G.tubes.card : Real) * (R.translationBudget K : Real) <=
      (Fintype.card translation : Real) * mean := by
  have hvolumeNonneg :
      0 <= (volume (G.testBody K : Set Space)).toReal := ENNReal.toReal_nonneg
  have hblockNonneg : 0 <= (Fintype.card (L.Block K) : Real) :=
    Nat.cast_nonneg _
  have htubeNonneg : 0 <= (G.tubes.card : Real) := Nat.cast_nonneg _
  have hone :
      1 <= (Fintype.card (L.Block K) : Real) *
          (volume (G.testBody K : Set Space)).toReal / referenceVolume := by
    apply (le_div_iff₀ hrefPos).2
    simpa using hblockVolume
  have hratioMean :
      (G.tubes.card : Real) *
          (volume (G.testBody K : Set Space)).toReal / referenceVolume <=
        mean := by
    apply (div_le_iff₀ hrefPos).2
    simpa [mul_assoc, mul_comm] using hmeanVolume
  apply R.balance_of_tubeCard_le_blockCard_mul_mean K
  calc
    (G.tubes.card : Real) <=
        (G.tubes.card : Real) *
          ((Fintype.card (L.Block K) : Real) *
            (volume (G.testBody K : Set Space)).toReal / referenceVolume) := by
      simpa only [mul_one] using mul_le_mul_of_nonneg_left hone htubeNonneg
    _ = (Fintype.card (L.Block K) : Real) *
        ((G.tubes.card : Real) *
          (volume (G.testBody K : Set Space)).toReal / referenceVolume) := by
      ring
    _ <= (Fintype.card (L.Block K) : Real) * mean :=
      mul_le_mul_of_nonneg_left hratioMean hblockNonneg

#print axioms pointHitCount_le_translationBudget
#print axioms hasPointHitCap
#print axioms tubeHitCount_le_translationBudget
#print axioms card_translation_eq_card_block_mul_translationBudget
#print axioms balance_of_tubeCard_le_blockCard_mul_mean
#print axioms balance_of_volumeBudgets

end IsMultiBoxLatticeRealization

end ActualTubeTranslationGrid

end

end FamilyStickyActualLatticePointBalanceV1
