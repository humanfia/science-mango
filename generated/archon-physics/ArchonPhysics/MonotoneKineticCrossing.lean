import Mathlib
import ArchonPhysics.QuantitativeKineticRelaxation

/-!
# Robust crossings from monotone kinetic decay

A continuous strictly decreasing nonnegative-time distance that starts above a
positive threshold and tends to zero has a unique positive threshold crossing.
Strict decrease then supplies the quantitative margins required by
RobustKineticFirstCrossing.

All analytic and order-theoretic input is explicit.  In particular, this file
does not assert that a microscopic lattice observable satisfies continuity,
strict decrease, or decay to zero.
-/

namespace ArchonPhysics

open Filter Set

noncomputable section

/--
A continuous strictly decreasing distance on nonnegative time, starting above
a positive threshold and tending to zero, crosses the threshold at one unique
positive time.
-/
theorem existsUnique_positive_monotone_crossing
    {distance : Real → Real} {delta : Real}
    (hcontinuous : ContinuousOn distance (Ici 0))
    (hstrict : StrictAntiOn distance (Ici 0))
    (hdelta_pos : 0 < delta)
    (hdelta_below_initial : delta < distance 0)
    (hdecay : Tendsto distance atTop (nhds 0)) :
    ∃! tauStar, 0 < tauStar ∧ distance tauStar = delta := by
  have hbelow_eventually : ∀ᶠ t : Real in atTop, distance t < delta :=
    (tendsto_order.mp hdecay).2 delta hdelta_pos
  have hpositive_eventually : ∀ᶠ t : Real in atTop, 0 < t :=
    Filter.Ioi_mem_atTop 0
  obtain ⟨right, hright_below, hright_pos⟩ :=
    (hbelow_eventually.and hpositive_eventually).exists
  have hright_nonneg : 0 ≤ right := le_of_lt hright_pos
  have hcontinuous_Icc : ContinuousOn distance (Icc 0 right) :=
    hcontinuous.mono Set.Icc_subset_Ici_self
  have hdelta_mem : delta ∈ Icc (distance right) (distance 0) :=
    ⟨le_of_lt hright_below, le_of_lt hdelta_below_initial⟩
  have hdelta_image : delta ∈ distance '' Icc 0 right :=
    intermediate_value_Icc' hright_nonneg hcontinuous_Icc hdelta_mem
  obtain ⟨tauStar, htau_mem, htau_eq⟩ := hdelta_image
  have htau_pos : 0 < tauStar := by
    by_contra hnot
    have htau_zero : tauStar = 0 :=
      le_antisymm (le_of_not_gt hnot) htau_mem.1
    subst tauStar
    linarith
  refine ⟨tauStar, ⟨htau_pos, htau_eq⟩, ?_⟩
  intro other hother
  exact (hstrict.injOn
    (Set.mem_Ici.mpr (le_of_lt htau_pos))
    (Set.mem_Ici.mpr (le_of_lt hother.1))
    (htau_eq.trans hother.2.symm)).symm

/--
Strict decrease constructs both margins of the corrected robust-crossing
contract from an already identified positive threshold root.
-/
theorem robustKineticFirstCrossing_of_strictAntiOn
    {distance : Real → Real} {delta tauStar : Real}
    (hstrict : StrictAntiOn distance (Ici 0))
    (htau_pos : 0 < tauStar)
    (htau_eq : distance tauStar = delta) :
    RobustKineticFirstCrossing distance delta tauStar := by
  constructor
  · exact htau_pos
  · intro ε hε_pos hε_lt
    have hcutoff_pos : 0 < tauStar - ε := sub_pos.mpr hε_lt
    have hcutoff_lt : tauStar - ε < tauStar := by
      linarith
    have hgap : delta < distance (tauStar - ε) := by
      rw [← htau_eq]
      exact hstrict
        (Set.mem_Ici.mpr (le_of_lt hcutoff_pos))
        (Set.mem_Ici.mpr (le_of_lt htau_pos))
        hcutoff_lt
    refine ⟨distance (tauStar - ε) - delta, sub_pos.mpr hgap, ?_⟩
    intro t ht_pos ht_le
    have hbound : distance (tauStar - ε) ≤ distance t :=
      hstrict.antitoneOn
        (Set.mem_Ici.mpr (le_of_lt ht_pos))
        (Set.mem_Ici.mpr (le_of_lt hcutoff_pos))
        ht_le
    linarith
  · intro ε hε_pos
    let hitTime := tauStar + ε / 2
    have htau_lt_hit : tauStar < hitTime := by
      dsimp [hitTime]
      linarith
    have hhit_lt_right : hitTime < tauStar + ε := by
      dsimp [hitTime]
      linarith
    have hhit_pos : 0 < hitTime := lt_trans htau_pos htau_lt_hit
    have hhit_below : distance hitTime < delta := by
      rw [← htau_eq]
      exact hstrict
        (Set.mem_Ici.mpr (le_of_lt htau_pos))
        (Set.mem_Ici.mpr (le_of_lt hhit_pos))
        htau_lt_hit
    refine
      ⟨hitTime, delta - distance hitTime, htau_lt_hit, hhit_lt_right,
        sub_pos.mpr hhit_below, ?_⟩
    linarith

/--
The monotone-decay hypotheses produce one unique positive root together with
its fully derived robust-crossing witness.
-/
theorem existsUnique_robustKineticFirstCrossing_of_monotone_decay
    {distance : Real → Real} {delta : Real}
    (hcontinuous : ContinuousOn distance (Ici 0))
    (hstrict : StrictAntiOn distance (Ici 0))
    (hdelta_pos : 0 < delta)
    (hdelta_below_initial : delta < distance 0)
    (hdecay : Tendsto distance atTop (nhds 0)) :
    ∃! tauStar,
      0 < tauStar ∧ distance tauStar = delta ∧
        RobustKineticFirstCrossing distance delta tauStar := by
  obtain ⟨tauStar, htau, hunique⟩ :=
    existsUnique_positive_monotone_crossing
      hcontinuous hstrict hdelta_pos hdelta_below_initial hdecay
  have hrobust : RobustKineticFirstCrossing distance delta tauStar :=
    robustKineticFirstCrossing_of_strictAntiOn hstrict htau.1 htau.2
  refine ⟨tauStar, ⟨htau.1, htau.2, hrobust⟩, ?_⟩
  intro other hother
  exact hunique other ⟨hother.1, hother.2.1⟩

end

end ArchonPhysics
