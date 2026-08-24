import FamilyStickyGrounding.Cinematic.FamilyStickyCinematicL32Prop41AlternatingSignIccThreeRootsV1
import FamilyStickyGrounding.Cinematic.FamilyStickyCinematicL32Prop41K23AlternatingScalarSignsV1

set_option autoImplicit false

namespace FamilyStickyCinematicL32Prop41K23IccRootContradictionV1

open Set
open FamilyStickyCinematicL32Prop41AlternatingSignIccThreeRootsV1
open FamilyStickyCinematicL32Prop41AlternatingSignThreeRootsV1
open FamilyStickyCinematicL32Prop41MarcusTardosFact1BoolParityV1
open FamilyStickyCinematicL32Prop41K23AlternatingScalarSignsV1
open FamilyStickyCinematicL32Prop41K23BalancedRankReductionCleanV1
open FamilyStickyCinematicL32Prop41RankedIntervalSamplesV1
open FamilyStickyCinematicL32Prop41SixSeparatedIntervalRankV1

noncomputable section

/-!
# The finite `K_{2,3}` alternation contradicts pair root-cardinality two

This endpoint keeps the root carrier restricted to the ambient paper
interval.  Four alternating host labels force three roots of a host-graph
difference; four alternating neighbor labels force three roots of a
neighbor-graph difference.  Own/foreign midpoint signs and pair root bounds
remain separate local inputs, so the theorem contains no forbidden-triple or
intersection-reverse premise.
-/

theorem not_hostAlternatingFour_of_Icc_rootCard_le_two
    (S : SixSeparatedIntervals)
    (hostGraph : Fin 2 -> Real -> Real)
    (neighborGraph : Fin 3 -> Real -> Real)
    {A B : Real}
    (hmidAB : forall e, intervalMidpoint S e ∈ Icc A B)
    (hown : K23OwnMidpointSign S hostGraph neighborGraph)
    (hforeign : K23ForeignMidpointSign S hostGraph neighborGraph)
    (hcontinuous : forall h, ContinuousOn (hostGraph h) (Icc A B))
    (hrootCard : forall h0 h1, h0 ≠ h1 ->
      ({theta | theta ∈ Icc A B ∧
        hostGraph h0 theta = hostGraph h1 theta} : Set Real).encard <= 2) :
    ¬ AlternatingFour S.rank (fun e => e.1) := by
  rintro halt
  rcases alternatingMidpointWitness_of_alternatingFour S (fun e => e.1) halt with
    ⟨e0, e1, e2, e3, h01, h12, h23, _, _, _, _, h02, h13, hne⟩
  change e0.1 = e2.1 at h02
  change e1.1 = e3.1 at h13
  change e0.1 ≠ e1.1 at hne
  have hne21 : e2.1 ≠ e1.1 := fun heq => hne (h02.trans heq)
  have hne30 : e3.1 ≠ e0.1 := fun heq => hne (h13.trans heq).symm
  have hown0 := hown e0
  have hforeign0 : hostGraph e1.1 (intervalMidpoint S e0) <
      neighborGraph e0.2 (intervalMidpoint S e0) := by
    simpa using hforeign e0 (e1.1, e0.2) (edge_ne_replace_fst hne)
  have hown1 := hown e1
  have hforeign1 : hostGraph e0.1 (intervalMidpoint S e1) <
      neighborGraph e1.2 (intervalMidpoint S e1) := by
    simpa using hforeign e1 (e0.1, e1.2) (edge_ne_replace_fst hne.symm)
  have hown2 := hown e2
  have hforeign2 : hostGraph e1.1 (intervalMidpoint S e2) <
      neighborGraph e2.2 (intervalMidpoint S e2) := by
    simpa using hforeign e2 (e1.1, e2.2) (edge_ne_replace_fst hne21)
  have hown3 := hown e3
  have hforeign3 : hostGraph e0.1 (intervalMidpoint S e3) <
      neighborGraph e3.2 (intervalMidpoint S e3) := by
    simpa using hforeign e3 (e0.1, e3.2) (edge_ne_replace_fst hne30)
  rw [← h02] at hown2
  rw [← h13] at hown3
  have hsign : AlternatingStrictSign
      (fun theta => hostGraph e0.1 theta - hostGraph e1.1 theta)
      (intervalMidpoint S e0) (intervalMidpoint S e1)
      (intervalMidpoint S e2) (intervalMidpoint S e3) :=
    Or.inr ⟨by linarith, by linarith, by linarith, by linarith⟩
  have hsub : Icc (intervalMidpoint S e0) (intervalMidpoint S e3) ⊆
      Icc A B := Icc_subset_Icc (hmidAB e0).1 (hmidAB e3).2
  have hcont : ContinuousOn
      (fun theta => hostGraph e0.1 theta - hostGraph e1.1 theta)
      (Icc (intervalMidpoint S e0) (intervalMidpoint S e3)) :=
    ((hcontinuous e0.1).sub (hcontinuous e1.1)).mono hsub
  apply not_Icc_rootSet_encard_le_two_of_alternatingStrictSign
    (fun theta => hostGraph e0.1 theta - hostGraph e1.1 theta)
    h01 h12 h23 (hmidAB e0) (hmidAB e3) hcont hsign
  simpa only [sub_eq_zero] using hrootCard e0.1 e1.1 hne

theorem not_neighborAlternatingFour_of_Icc_rootCard_le_two
    (S : SixSeparatedIntervals)
    (hostGraph : Fin 2 -> Real -> Real)
    (neighborGraph : Fin 3 -> Real -> Real)
    {A B : Real}
    (hmidAB : forall e, intervalMidpoint S e ∈ Icc A B)
    (hown : K23OwnMidpointSign S hostGraph neighborGraph)
    (hforeign : K23ForeignMidpointSign S hostGraph neighborGraph)
    (hcontinuous : forall j, ContinuousOn (neighborGraph j) (Icc A B))
    (hrootCard : forall j0 j1, j0 ≠ j1 ->
      ({theta | theta ∈ Icc A B ∧
        neighborGraph j0 theta = neighborGraph j1 theta} : Set Real).encard <= 2) :
    ¬ AlternatingFour S.rank (fun e => e.2) := by
  rintro halt
  rcases alternatingMidpointWitness_of_alternatingFour S (fun e => e.2) halt with
    ⟨e0, e1, e2, e3, h01, h12, h23, _, _, _, _, h02, h13, hne⟩
  change e0.2 = e2.2 at h02
  change e1.2 = e3.2 at h13
  change e0.2 ≠ e1.2 at hne
  have hne21 : e2.2 ≠ e1.2 := fun heq => hne (h02.trans heq)
  have hne30 : e3.2 ≠ e0.2 := fun heq => hne (h13.trans heq).symm
  have hown0 := hown e0
  have hforeign0 : hostGraph e0.1 (intervalMidpoint S e0) <
      neighborGraph e1.2 (intervalMidpoint S e0) := by
    simpa using hforeign e0 (e0.1, e1.2) (edge_ne_replace_snd hne)
  have hown1 := hown e1
  have hforeign1 : hostGraph e1.1 (intervalMidpoint S e1) <
      neighborGraph e0.2 (intervalMidpoint S e1) := by
    simpa using hforeign e1 (e1.1, e0.2) (edge_ne_replace_snd hne.symm)
  have hown2 := hown e2
  have hforeign2 : hostGraph e2.1 (intervalMidpoint S e2) <
      neighborGraph e1.2 (intervalMidpoint S e2) := by
    simpa using hforeign e2 (e2.1, e1.2) (edge_ne_replace_snd hne21)
  have hown3 := hown e3
  have hforeign3 : hostGraph e3.1 (intervalMidpoint S e3) <
      neighborGraph e0.2 (intervalMidpoint S e3) := by
    simpa using hforeign e3 (e3.1, e0.2) (edge_ne_replace_snd hne30)
  rw [← h02] at hown2
  rw [← h13] at hown3
  have hsign : AlternatingStrictSign
      (fun theta => neighborGraph e0.2 theta - neighborGraph e1.2 theta)
      (intervalMidpoint S e0) (intervalMidpoint S e1)
      (intervalMidpoint S e2) (intervalMidpoint S e3) :=
    Or.inl ⟨by linarith, by linarith, by linarith, by linarith⟩
  have hsub : Icc (intervalMidpoint S e0) (intervalMidpoint S e3) ⊆
      Icc A B := Icc_subset_Icc (hmidAB e0).1 (hmidAB e3).2
  have hcont : ContinuousOn
      (fun theta => neighborGraph e0.2 theta - neighborGraph e1.2 theta)
      (Icc (intervalMidpoint S e0) (intervalMidpoint S e3)) :=
    ((hcontinuous e0.2).sub (hcontinuous e1.2)).mono hsub
  apply not_Icc_rootSet_encard_le_two_of_alternatingStrictSign
    (fun theta => neighborGraph e0.2 theta - neighborGraph e1.2 theta)
    h01 h12 h23 (hmidAB e0) (hmidAB e3) hcont hsign
  simpa only [sub_eq_zero] using hrootCard e0.2 e1.2 hne

#print axioms not_hostAlternatingFour_of_Icc_rootCard_le_two
#print axioms not_neighborAlternatingFour_of_Icc_rootCard_le_two

end

end FamilyStickyCinematicL32Prop41K23IccRootContradictionV1
