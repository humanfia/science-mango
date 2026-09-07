import Family8Grounding.Family8FiniteRandomRigidMotionPaperFixedJohnAutomaticDensityRepetitionsV2
import FamilyStickyGrounding.FamilyStickyFiniteFamilyMaximalConcentrationV1
import Mathlib.Tactic

open Set MeasureTheory
open scoped ENNReal NNReal BigOperators InnerProductSpace

namespace Family8FiniteRandomRigidMotionPaperFixedJohnDensityNondegeneracyV3

open LeanEval.Analysis.WangZahlKakeya
open Submission.Kakeya.ConvexGeometry
open Submission.Kakeya.ConvexFactoring
open Family8KatzTaoFrostmanPropertiesV1
open Family8GeneralizedFrostmanMultiplicityV1
open Family8FiniteRandomRigidMotionIncidenceV1
open Family8FiniteRandomRigidMotionB2FreshGreedyV1
open Family8FiniteRandomRigidMotionB2NormalizationCoreV1
open Family8FiniteRandomRigidMotionPaperCanonicalTestGridV1
open Family8FiniteRandomRigidMotionPaperAutomaticElongatedConflictV2
open Family8FiniteRandomRigidMotionPaperTranslationBodyGridV1
open Family8FiniteRandomRigidMotionPaperFixedJohnConflictGridV4
open Family8FiniteRandomRigidMotionPaperFixedJohnAutomaticConflictCapV2
open Family8FiniteRandomRigidMotionPaperNormalizedTranslationUnitSupportV1
open Family8FiniteRandomRigidMotionPaperFixedJohnExactMeanSelectorV4
open Family8FiniteRandomRigidMotionPaperFixedJohnBoundedPackingMeanV5
open Family8FiniteRandomRigidMotionPaperFixedJohnCapVsLongMeanV2
open Family8FiniteRandomRigidMotionPaperFixedJohnAutomaticDensityRepetitionsV2

noncomputable section

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 4000000

/-! Nondegeneracy of the literal normalized maximal concentration, following
the positive-member argument of `FamilyStickyPaperRandomMotionNondegeneracyV1`.
Empty families are kept as a separate, honest branch. -/

theorem one_le_maximalConcentration_of_member_volume_pos
    {index : Type} [Fintype index]
    (F : ConvexFamily index) (i : index)
    (hvolPos : 0 < volume (F i : Set Space)) :
    (1 : ENNReal) ≤ maximalConcentration F := by
  classical
  have hi : i ∈ containedIndices F (F i) :=
    (mem_containedIndices F (F i) i).2 Set.Subset.rfl
  have hvolTop : volume (F i : Set Space) < ∞ :=
    (F i).isCompact.measure_lt_top
  have hmass : volume (F i : Set Space) ≤
      ∑ j ∈ containedIndices F (F i), volume (F j : Set Space) :=
    Finset.single_le_sum
      (fun j _hj ↦ (show (0 : ENNReal) ≤
        volume (F j : Set Space) from bot_le)) hi
  have hconc : (1 : ENNReal) ≤ concentration F (F i) := by
    unfold concentration
    apply (ENNReal.le_div_iff_mul_le
      (Or.inl hvolPos.ne') (Or.inl hvolTop.ne)).2
    simpa using hmass
  exact hconc.trans (concentration_le_maximalConcentration F (F i))

theorem one_le_fixedJohnPackingMaximalConcentration
    {delta : NNReal} {iota : Type}
    [Fintype iota] [DecidableEq iota]
    (D : ActualTubeDatum delta iota) (hD : D.IsAdmissible)
    (hcard : Fintype.card iota ≠ 0) :
    (1 : ENNReal) ≤ fixedJohnPackingMaximalConcentration D hD := by
  classical
  have hindex : Nonempty iota :=
    Fintype.card_pos_iff.mp (Nat.pos_of_ne_zero hcard)
  let j : iota := Classical.choice hindex
  let i : {k // k ∈ (Finset.univ : Finset iota)} :=
    ⟨j, Finset.mem_univ j⟩
  apply one_le_maximalConcentration_of_member_volume_pos
    (fixedJohnNormalizedActiveFamily D) i
  simpa only [fixedJohnNormalizedActiveFamily, Tube.coe_body] using
    Tube.volume_pos (eighthNormalizedTube (D.family.tubes i.1))
      (admissibleNormalizedRadiusPos hD)

theorem one_le_fixedJohnPackingMaximalConcentration_toReal
    {delta : NNReal} {iota : Type}
    [Fintype iota] [DecidableEq iota]
    (D : ActualTubeDatum delta iota) (hD : D.IsAdmissible)
    (hcard : Fintype.card iota ≠ 0) :
    (1 : Real) ≤ (fixedJohnPackingMaximalConcentration D hD).toReal := by
  have htop : fixedJohnPackingMaximalConcentration D hD ≠ ∞ :=
    (FamilyStickyFiniteFamilyMaximalConcentrationV1.maximalConcentration_lt_top
      (fixedJohnNormalizedActiveFamily D)).ne
  simpa using ENNReal.toReal_mono htop
    (one_le_fixedJohnPackingMaximalConcentration D hD hcard)

theorem fixedJohnAutomaticDensityRepetitions_eq_one_of_card_eq_zero
    {delta : NNReal} {iota : Type}
    [Fintype iota] [DecidableEq iota]
    (D : ActualTubeDatum delta iota) (hD : D.IsAdmissible)
    (hcard : Fintype.card iota = 0) :
    fixedJohnAutomaticDensityRepetitions D hD = 1 := by
  norm_num [fixedJohnAutomaticDensityRepetitions, fixedJohnDensityRatio,
    fixedJohnDensityUnitCost, hcard]

/-- If one normalized tube already pays the requested scalar cost, the
automatic density ratio selects at least `J0` copies. -/
theorem repetitions_lower_of_unit_maximalConcentration
    {delta : NNReal} {iota : Type}
    [Fintype iota] [DecidableEq iota]
    (D : ActualTubeDatum delta iota) (hD : D.IsAdmissible)
    (hcard : Fintype.card iota ≠ 0) (J0 : Nat)
    (hscale :
      9504 * ((J0 : Real) + 1) * (Fintype.card iota : Real) *
          (((delta / 8 : NNReal) : Real) ^ 2) ≤ 1) :
    J0 ≤ fixedJohnAutomaticDensityRepetitions D hD := by
  let cost := fixedJohnDensityUnitCost delta iota
  let mass := (fixedJohnPackingMaximalConcentration D hD).toReal
  have hcost : 0 < cost := by
    simpa only [cost] using
      fixedJohnDensityUnitCost_pos hD.delta_pos hcard
  have hmass : 1 ≤ mass := by
    simpa only [mass] using
      one_le_fixedJohnPackingMaximalConcentration_toReal D hD hcard
  have hmul : ((J0 : Real) + 1) * cost ≤ mass := by
    calc
      ((J0 : Real) + 1) * cost =
          9504 * ((J0 : Real) + 1) * (Fintype.card iota : Real) *
            (((delta / 8 : NNReal) : Real) ^ 2) := by
        simp only [cost, fixedJohnDensityUnitCost]
        ring
      _ ≤ 1 := hscale
      _ ≤ mass := hmass
  apply repetitions_lower_of_densityRatio D hD J0
  change (J0 : Real) + 1 ≤ mass / cost
  exact (le_div_iff₀ hcost).2 hmul

theorem exists_boundedPackingTuple_with_repetitions_lower
    {delta : NNReal} {iota : Type}
    [Fintype iota] [DecidableEq iota]
    (D : ActualTubeDatum delta iota) (hD : D.IsAdmissible)
    (hcard : Fintype.card iota ≠ 0) (J0 : Nat)
    (hscale :
      9504 * ((J0 : Real) + 1) * (Fintype.card iota : Real) *
          (((delta / 8 : NNReal) : Real) ^ 2) ≤ 1) :
    ∃ omega : Fin (fixedJohnAutomaticDensityRepetitions D hD) →
        FixedJohnPackingTranslation D hD,
      J0 ≤ fixedJohnAutomaticDensityRepetitions D hD ∧
      (∀ K : FixedJohnTest D hD,
        (∑ j, (normalizedTranslationBodyLoadNat
          (fixedJohnPackingGridVector D hD) D
          (fixedJohnCatalogueBody hD) K (omega j) : Real)) ≤
          fixedJohnTailParameter D hD *
            fixedJohnTranslationPaperCap
              (fixedJohnPackingGridVector D hD) D hD K) ∧
      (∀ a,
        (normalizedConflictIndices
          (indexedRigidCopyDatum
            (fun j ↦ translationRigidMotion
              (fixedJohnPackingGridVector D hD (omega j))) D)
          a).card ≤
            fixedJohnLoadThreshold
              (fixedJohnPackingGridVector D hD) D hD) := by
  obtain ⟨omega, hload, hconflict⟩ :=
    exists_boundedPackingTuple_automaticDensityRepetitions D hD
  exact ⟨omega,
    repetitions_lower_of_unit_maximalConcentration
      D hD hcard J0 hscale,
    hload, hconflict⟩

/-- Existentially packaged downstream endpoint: consumers need not unfold
the automatic repetition definition to recover the chosen `J`. -/
theorem exists_repetitionCount_boundedPackingTuple_with_lower
    {delta : NNReal} {iota : Type}
    [Fintype iota] [DecidableEq iota]
    (D : ActualTubeDatum delta iota) (hD : D.IsAdmissible)
    (hcard : Fintype.card iota ≠ 0) (J0 : Nat)
    (hscale :
      9504 * ((J0 : Real) + 1) * (Fintype.card iota : Real) *
          (((delta / 8 : NNReal) : Real) ^ 2) ≤ 1) :
    ∃ J : Nat, ∃ omega : Fin J → FixedJohnPackingTranslation D hD,
      J0 ≤ J ∧
      (∀ K : FixedJohnTest D hD,
        (∑ j, (normalizedTranslationBodyLoadNat
          (fixedJohnPackingGridVector D hD) D
          (fixedJohnCatalogueBody hD) K (omega j) : Real)) ≤
          fixedJohnTailParameter D hD *
            fixedJohnTranslationPaperCap
              (fixedJohnPackingGridVector D hD) D hD K) ∧
      (∀ a,
        (normalizedConflictIndices
          (indexedRigidCopyDatum
            (fun j ↦ translationRigidMotion
              (fixedJohnPackingGridVector D hD (omega j))) D)
          a).card ≤
            fixedJohnLoadThreshold
              (fixedJohnPackingGridVector D hD) D hD) := by
  refine ⟨fixedJohnAutomaticDensityRepetitions D hD, ?_⟩
  exact exists_boundedPackingTuple_with_repetitions_lower
    D hD hcard J0 hscale

#print axioms one_le_maximalConcentration_of_member_volume_pos
#print axioms one_le_fixedJohnPackingMaximalConcentration
#print axioms one_le_fixedJohnPackingMaximalConcentration_toReal
#print axioms fixedJohnAutomaticDensityRepetitions_eq_one_of_card_eq_zero
#print axioms repetitions_lower_of_unit_maximalConcentration
#print axioms exists_boundedPackingTuple_with_repetitions_lower
#print axioms exists_repetitionCount_boundedPackingTuple_with_lower

end
end Family8FiniteRandomRigidMotionPaperFixedJohnDensityNondegeneracyV3
