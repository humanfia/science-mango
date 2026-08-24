import FamilyStickyGrounding.Cinematic.FamilyStickyCinematicL32Prop41AlternatingSignThreeRootsV1
import FamilyStickyGrounding.Cinematic.FamilyStickyCinematicL32Prop41RankedIntervalSamplesV1

set_option autoImplicit false

namespace FamilyStickyCinematicL32Prop41K23AlternatingScalarSignsV1

open FamilyStickyCinematicL32Prop41AlternatingSignThreeRootsV1
open FamilyStickyCinematicL32Prop41MarcusTardosFact1BoolParityV1
open FamilyStickyCinematicL32Prop41K23BalancedRankReductionCleanV1
open FamilyStickyCinematicL32Prop41RankedIntervalSamplesV1
open FamilyStickyCinematicL32Prop41SixSeparatedIntervalRankV1

noncomputable section

/-!
# Alternating scalar graph signs from separated `K_{2,3}` incidences

At its own midpoint each neighbor lies below its host.  At the midpoint of
any different interval, that incidence has the strict opposite sign.  Four
alternating host labels therefore alternate a host-graph difference; four
alternating neighbor labels alternate a neighbor-graph difference.
-/

def K23OwnMidpointSign (S : SixSeparatedIntervals)
    (hostGraph : Fin 2 -> Real -> Real)
    (neighborGraph : Fin 3 -> Real -> Real) : Prop :=
  forall e : K23Edge,
    neighborGraph e.2 (intervalMidpoint S e) <
      hostGraph e.1 (intervalMidpoint S e)

def K23ForeignMidpointSign (S : SixSeparatedIntervals)
    (hostGraph : Fin 2 -> Real -> Real)
    (neighborGraph : Fin 3 -> Real -> Real) : Prop :=
  forall e q : K23Edge, e ≠ q ->
    hostGraph q.1 (intervalMidpoint S e) <
      neighborGraph q.2 (intervalMidpoint S e)

def HostAlternatingSignWitness
    (hostGraph : Fin 2 -> Real -> Real) : Prop :=
  exists h0 h1 : Fin 2, h0 ≠ h1 ∧
    exists a b c d : Real,
      a < b ∧ b < c ∧ c < d ∧
        AlternatingStrictSign
          (fun theta => hostGraph h0 theta - hostGraph h1 theta) a b c d

def NeighborAlternatingSignWitness
    (neighborGraph : Fin 3 -> Real -> Real) : Prop :=
  exists n0 n1 : Fin 3, n0 ≠ n1 ∧
    exists a b c d : Real,
      a < b ∧ b < c ∧ c < d ∧
        AlternatingStrictSign
          (fun theta => neighborGraph n0 theta - neighborGraph n1 theta)
          a b c d

theorem edge_ne_replace_fst {e : K23Edge} {h : Fin 2}
    (hne : e.1 ≠ h) : e ≠ (h, e.2) := by
  intro heq
  apply hne
  have hh := congrArg (fun q : K23Edge => q.1) heq
  simpa using hh

theorem edge_ne_replace_snd {e : K23Edge} {j : Fin 3}
    (hne : e.2 ≠ j) : e ≠ (e.1, j) := by
  intro heq
  apply hne
  have hh := congrArg (fun q : K23Edge => q.2) heq
  simpa using hh

theorem hostAlternatingSignWitness_of_alternatingFour
    (S : SixSeparatedIntervals)
    (hostGraph : Fin 2 -> Real -> Real)
    (neighborGraph : Fin 3 -> Real -> Real)
    (hown : K23OwnMidpointSign S hostGraph neighborGraph)
    (hforeign : K23ForeignMidpointSign S hostGraph neighborGraph)
    (halt : AlternatingFour S.rank (fun e => e.1)) :
    HostAlternatingSignWitness hostGraph := by
  rcases alternatingMidpointWitness_of_alternatingFour S (fun e => e.1) halt with
    ⟨e0, e1, e2, e3, h01, h12, h23, _, _, _, _, h02, h13, hne⟩
  change e0.1 = e2.1 at h02
  change e1.1 = e3.1 at h13
  change e0.1 ≠ e1.1 at hne
  have hne21 : e2.1 ≠ e1.1 := fun heq => hne (h02.trans heq)
  have hne30 : e3.1 ≠ e0.1 := fun heq => hne (h13.trans heq).symm
  refine ⟨e0.1, e1.1, hne, intervalMidpoint S e0,
    intervalMidpoint S e1, intervalMidpoint S e2,
    intervalMidpoint S e3, h01, h12, h23, Or.inr ?_⟩
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
  exact ⟨by linarith, by linarith, by linarith, by linarith⟩

theorem neighborAlternatingSignWitness_of_alternatingFour
    (S : SixSeparatedIntervals)
    (hostGraph : Fin 2 -> Real -> Real)
    (neighborGraph : Fin 3 -> Real -> Real)
    (hown : K23OwnMidpointSign S hostGraph neighborGraph)
    (hforeign : K23ForeignMidpointSign S hostGraph neighborGraph)
    (halt : AlternatingFour S.rank (fun e => e.2)) :
    NeighborAlternatingSignWitness neighborGraph := by
  rcases alternatingMidpointWitness_of_alternatingFour S (fun e => e.2) halt with
    ⟨e0, e1, e2, e3, h01, h12, h23, _, _, _, _, h02, h13, hne⟩
  change e0.2 = e2.2 at h02
  change e1.2 = e3.2 at h13
  change e0.2 ≠ e1.2 at hne
  have hne21 : e2.2 ≠ e1.2 := fun heq => hne (h02.trans heq)
  have hne30 : e3.2 ≠ e0.2 := fun heq => hne (h13.trans heq).symm
  refine ⟨e0.2, e1.2, hne, intervalMidpoint S e0,
    intervalMidpoint S e1, intervalMidpoint S e2,
    intervalMidpoint S e3, h01, h12, h23, Or.inl ?_⟩
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
  exact ⟨by linarith, by linarith, by linarith, by linarith⟩

#print axioms hostAlternatingSignWitness_of_alternatingFour
#print axioms neighborAlternatingSignWitness_of_alternatingFour

end

end FamilyStickyCinematicL32Prop41K23AlternatingScalarSignsV1
