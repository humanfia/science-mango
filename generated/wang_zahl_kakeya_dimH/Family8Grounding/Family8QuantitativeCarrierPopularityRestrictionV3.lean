import Family8Grounding.Family8PositiveCarrierShadingRestrictionV4
import Family8Grounding.Family8StickyParentPopularCanonicalUnionV1
import Submission.Kakeya.ConvexFactoring.RefinementMultiplicity

/-!
# Quantitative carrier popularity for a finite shading, V3

For a nonzero finite shading, retain the pieces whose carrier mass is at
least half the average carrier mass.  Their complement has total mass at
most one half of the original mass.  In the zero-mass branch the harmless
floor is `1`.  Deleting the resulting zero carriers gives a true finite
subtype on which the declared floor holds memberwise.
-/

open Set MeasureTheory
open scoped BigOperators ENNReal NNReal

namespace Family8QuantitativeCarrierPopularityRestrictionV3

open LeanEval.Analysis.WangZahlKakeya
open Submission.Kakeya.ConvexGeometry
open Submission.Kakeya.ConvexFactoring
open Family8ExactAssemblyActualAverageBridgeV1
open Family8PositiveCarrierShadingRestrictionV4
open Family8StickyParentPopularCanonicalUnionV1
open FamilyStickyHierarchyWZ2TranslatedCollisionCellCanonicalRowScaleFloorV1
open FamilyStickyHierarchyWZ2TranslatedCollisionCellPopularFloorUnionV1
open FamilyStickyWZ2ShadingPopularityV2

noncomputable section

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 3000000
set_option linter.unusedSectionVars false

local instance (p : Prop) : Decidable p := Classical.propDecidable p

universe u

variable {iota : Type u} [Fintype iota] [DecidableEq iota]
  {F : ConvexFamily iota}

noncomputable def carrierAverageMassReal (Y : Shading F) : Real :=
  Y.shadingMass.toReal / Fintype.card iota

noncomputable def quantitativeCarrierFloor (Y : Shading F) : ENNReal :=
  if Y.shadingMass = 0 then 1
  else popularCarrierFloor (carrierAverageMassReal Y) 1

noncomputable def quantitativeCarrierIndices (Y : Shading F) : Finset iota :=
  Finset.univ.filter fun i =>
    quantitativeCarrierFloor Y ≤ volume (Y.carrier i)

noncomputable def quantitativeCarrierRefinement (Y : Shading F) :
    IndexedShadingRefinement Y where
  indices := quantitativeCarrierIndices Y
  shading := retainCarrierFloor Y (quantitativeCarrierFloor Y)
  carrier_subset := by
    intro i
    rw [retainCarrierFloor_carrier]
    split_ifs
    · exact Subset.rfl
    · exact empty_subset _
  carrier_eq_empty_of_not_mem := by
    intro i hi
    have hnot : ¬ quantitativeCarrierFloor Y ≤ volume (Y.carrier i) := by
      simpa only [quantitativeCarrierIndices, Finset.mem_filter,
        Finset.mem_univ, true_and] using hi
    simp only [retainCarrierFloor_carrier, if_neg hnot]

abbrev quantitativePositiveCarrierFamily (Y : Shading F) :
    ConvexFamily
      {i // i ∈ positiveCarrierIndices
        (quantitativeCarrierRefinement Y).shading} :=
  positiveCarrierFamily (quantitativeCarrierRefinement Y).shading

noncomputable def quantitativePositiveCarrierShading (Y : Shading F) :
    Shading (quantitativePositiveCarrierFamily Y) :=
  positiveCarrierShading (quantitativeCarrierRefinement Y).shading

theorem carrierAverageMassReal_pos
    (Y : Shading F) (hmass : Y.shadingMass ≠ 0) :
    0 < carrierAverageMassReal Y := by
  have hmassPos : 0 < Y.shadingMass := bot_lt_iff_ne_bot.mpr hmass
  have hiota : Nonempty iota := nonempty_of_shadingMass_pos Y hmassPos
  have hcardPos : (0 : Real) < Fintype.card iota := by
    exact_mod_cast (Fintype.card_pos_iff.mpr hiota)
  exact div_pos
    (ENNReal.toReal_pos hmass Y.shadingMass_lt_top.ne) hcardPos

theorem quantitativeCarrierFloor_ne_zero (Y : Shading F) :
    quantitativeCarrierFloor Y ≠ 0 := by
  by_cases hmass : Y.shadingMass = 0
  · simp [quantitativeCarrierFloor, hmass]
  · apply ne_of_gt
    rw [quantitativeCarrierFloor, if_neg hmass,
      popularCarrierFloor, ENNReal.ofReal_pos]
    exact mul_pos
      (div_pos (carrierAverageMassReal_pos Y hmass) (by norm_num))
      (by norm_num)

theorem quantitativeCarrierFloor_ne_top (Y : Shading F) :
    quantitativeCarrierFloor Y ≠ ∞ := by
  by_cases hmass : Y.shadingMass = 0
  · simp [quantitativeCarrierFloor, hmass]
  · rw [quantitativeCarrierFloor, if_neg hmass, popularCarrierFloor]
    exact ENNReal.ofReal_ne_top

theorem quantitativeCarrierFloor_eq_mass_div_card_mul_two
    (Y : Shading F) (hmass : Y.shadingMass ≠ 0) :
    quantitativeCarrierFloor Y =
      Y.shadingMass / ((Fintype.card iota : ENNReal) * 2) := by
  have hiota : Nonempty iota :=
    nonempty_of_shadingMass_pos Y (bot_lt_iff_ne_bot.mpr hmass)
  have hcardPos : (0 : Real) < Fintype.card iota := by
    exact_mod_cast (Fintype.card_pos_iff.mpr hiota)
  rw [quantitativeCarrierFloor, if_neg hmass, popularCarrierFloor,
    mul_one, carrierAverageMassReal, div_div]
  rw [ENNReal.ofReal_div_of_pos
    (mul_pos hcardPos (by norm_num : (0 : Real) < 2))]
  rw [ENNReal.ofReal_toReal Y.shadingMass_lt_top.ne]
  norm_num [ENNReal.ofReal_mul]

theorem quantitativeCarrierRefinement_withinFactor_two (Y : Shading F) :
    WithinFactor 2 Y.shadingMass
      (quantitativeCarrierRefinement Y).shading.shadingMass := by
  by_cases hmass : Y.shadingMass = 0
  · simp [WithinFactor, hmass]
  · have hiota : Nonempty iota :=
      nonempty_of_shadingMass_pos Y (bot_lt_iff_ne_bot.mpr hmass)
    have hcardPos : (0 : Real) < Fintype.card iota := by
      exact_mod_cast (Fintype.card_pos_iff.mpr hiota)
    have haveragePos : 0 < carrierAverageMassReal Y :=
      carrierAverageMassReal_pos Y hmass
    have hmassReal :
        carrierAverageMassReal Y *
            (Finset.univ : Finset iota).card * 1 ≤
          ∑ i ∈ (Finset.univ : Finset iota),
            restrictedMassReal Y Set.univ i := by
      rw [sum_restrictedMassReal_univ_eq_shadingMass_toReal]
      simp only [Finset.card_univ, mul_one, carrierAverageMassReal]
      exact le_of_eq (div_mul_cancel₀ _ (ne_of_gt hcardPos))
    have hraw :=
      popularRestricted_halfMass_le_retainCarrierFloor_shadingMass
        Y (Finset.univ : Finset iota) Set.univ
          (carrierAverageMassReal Y) 1 haveragePos.le (by norm_num) hmassReal
    have hleft :
        ENNReal.ofReal
            (carrierAverageMassReal Y / 2 *
              (Fintype.card iota : Real)) =
          Y.shadingMass / 2 := by
      have hreal :
          (Y.shadingMass.toReal / (Fintype.card iota : Real)) / 2 *
              (Fintype.card iota : Real) =
            Y.shadingMass.toReal / 2 := by
        calc
          _ = (Y.shadingMass.toReal / 2) /
                (Fintype.card iota : Real) *
                Fintype.card iota := by ring
          _ = Y.shadingMass.toReal / 2 :=
            div_mul_cancel₀ _ (ne_of_gt hcardPos)
      rw [carrierAverageMassReal, hreal]
      rw [ENNReal.ofReal_div_of_pos (by norm_num : (0 : Real) < 2)]
      rw [ENNReal.ofReal_toReal Y.shadingMass_lt_top.ne]
      norm_num
    have hhalf :
        Y.shadingMass / 2 ≤
          (quantitativeCarrierRefinement Y).shading.shadingMass := by
      simpa only [quantitativeCarrierRefinement, quantitativeCarrierFloor,
        if_neg hmass, mul_one, Finset.card_univ, hleft] using hraw
    unfold WithinFactor
    have hmul : Y.shadingMass ≤
        (quantitativeCarrierRefinement Y).shading.shadingMass * 2 :=
      (ENNReal.div_le_iff_le_mul
        (Or.inl (by norm_num)) (Or.inl (by norm_num))).mp hhalf
    simpa only [nsmul_eq_mul, Nat.cast_ofNat, mul_comm] using hmul

theorem quantitativeCarrierFloor_le
    (Y : Shading F)
    (q : {i // i ∈ positiveCarrierIndices
      (quantitativeCarrierRefinement Y).shading}) :
    quantitativeCarrierFloor Y ≤
      volume ((quantitativePositiveCarrierShading Y).carrier q) := by
  apply lower_le_volume_retainCarrierFloor_of_ne_zero
    Y (quantitativeCarrierFloor Y) q.1
  exact (mem_positiveCarrierIndices
    (quantitativeCarrierRefinement Y).shading q.1).mp q.2

theorem averageMultiplicity_le_two_mul_quantitativePositiveCarrier
    (Y : Shading F) :
    Y.averageMultiplicity ≤
      2 * (quantitativePositiveCarrierShading Y).averageMultiplicity := by
  have h := (quantitativeCarrierRefinement Y).averageMultiplicity_le 2
    (quantitativeCarrierRefinement_withinFactor_two Y)
  rw [← positiveCarrierShading_averageMultiplicity
    (quantitativeCarrierRefinement Y).shading] at h
  simpa only [nsmul_eq_mul, Nat.cast_ofNat,
    quantitativePositiveCarrierShading] using h

#print axioms carrierAverageMassReal_pos
#print axioms quantitativeCarrierFloor_ne_zero
#print axioms quantitativeCarrierFloor_ne_top
#print axioms quantitativeCarrierFloor_eq_mass_div_card_mul_two
#print axioms quantitativeCarrierRefinement_withinFactor_two
#print axioms quantitativeCarrierFloor_le
#print axioms averageMultiplicity_le_two_mul_quantitativePositiveCarrier

end

end Family8QuantitativeCarrierPopularityRestrictionV3
