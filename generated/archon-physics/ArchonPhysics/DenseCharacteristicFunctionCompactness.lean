import Mathlib.MeasureTheory.Measure.LevyConvergence
import Mathlib.MeasureTheory.Measure.CharacteristicFunction.TaylorExpansion
import Mathlib.Topology.Instances.RatLemmas

/-!
# Tight probability measures determined on rational Fourier frequencies

For probability measures on the real line, tightness plus convergence of the
characteristic functions at every rational frequency already forces weak
convergence.  The proof extracts compact cluster points using Prokhorov and
uses continuity of characteristic functions to identify any two cluster
points from their values on the dense set of rational frequencies.

This formulation is useful when each frequency carries its own almost-sure
event: only the countable family of rational frequencies must be intersected.
-/

open scoped Topology

namespace ArchonPhysics.DenseCharacteristicFunctionCompactness

open Filter MeasureTheory Set

noncomputable section

/-- Two probability measures on `Real` agree if their characteristic
functions agree at every rational frequency. -/
theorem probabilityMeasure_eq_of_charFun_rat_eq
    (mu nu : ProbabilityMeasure Real)
    (h : forall q : Rat,
      charFun (mu : Measure Real) (q : Real) =
        charFun (nu : Measure Real) (q : Real)) :
    mu = nu := by
  apply ProbabilityMeasure.toMeasure_injective
  apply Measure.ext_of_charFun
  refine Rat.isDenseEmbedding_coe_real.dense.equalizer
    (continuous_charFun (μ := (mu : Measure Real)))
    (continuous_charFun (μ := (nu : Measure Real))) ?_
  funext q
  exact h q

/-- A tight sequence of probability measures on `Real` converges weakly as
soon as its characteristic functions have limits at every rational
frequency.  Neither a candidate limiting function nor a candidate limiting
measure has to be supplied.

The result is deliberately countable: it is designed to combine with a
countable intersection of almost-sure events. -/
theorem exists_tendsto_of_tight_of_charFun_rat
    (mu : Nat -> ProbabilityMeasure Real)
    (hTight : IsTightMeasureSet
      {((nu : ProbabilityMeasure Real) : Measure Real) |
        nu ∈ Set.range mu})
    (hRat : forall q : Rat, exists z : Complex,
      Tendsto
        (fun n => charFun (mu n : Measure Real) (q : Real))
        atTop (nhds z)) :
    exists target : ProbabilityMeasure Real,
      Tendsto mu atTop (nhds target) := by
  let K : Set (ProbabilityMeasure Real) := closure (Set.range mu)
  have hK : IsCompact K := by
    exact isCompact_closure_of_isTightMeasureSet hTight
  have hmem : ∀ᶠ n in atTop, mu n ∈ K :=
    Filter.Eventually.of_forall fun n => subset_closure (Set.mem_range_self n)
  have hfrequent : ∃ᶠ n in atTop, mu n ∈ K := hmem.frequently
  obtain ⟨target, htargetK, htargetCluster⟩ :=
    hK.exists_mapClusterPt_of_frequently hfrequent
  refine ⟨target, hK.tendsto_nhds_of_unique_mapClusterPt hmem ?_⟩
  intro nu _hnuK hnuCluster
  apply probabilityMeasure_eq_of_charFun_rat_eq
  intro q
  obtain ⟨z, hz⟩ := hRat q
  obtain ⟨psiNu, hpsiNuMono, hpsiNu⟩ := hnuCluster.tendsto_subseq
  obtain ⟨psiTarget, hpsiTargetMono, hpsiTarget⟩ :=
    htargetCluster.tendsto_subseq
  have hnuChar : Tendsto
      (fun n => charFun (mu (psiNu n) : Measure Real) (q : Real))
      atTop (nhds (charFun (nu : Measure Real) (q : Real))) :=
    (ProbabilityMeasure.tendsto_iff_tendsto_charFun.mp hpsiNu) (q : Real)
  have htargetChar : Tendsto
      (fun n => charFun (mu (psiTarget n) : Measure Real) (q : Real))
      atTop (nhds (charFun (target : Measure Real) (q : Real))) :=
    (ProbabilityMeasure.tendsto_iff_tendsto_charFun.mp hpsiTarget) (q : Real)
  have hnuLimit :
      charFun (nu : Measure Real) (q : Real) = z :=
    tendsto_nhds_unique hnuChar (hz.comp hpsiNuMono.tendsto_atTop)
  have htargetLimit :
      charFun (target : Measure Real) (q : Real) = z :=
    tendsto_nhds_unique htargetChar (hz.comp hpsiTargetMono.tendsto_atTop)
  exact hnuLimit.trans htargetLimit.symm

end

end ArchonPhysics.DenseCharacteristicFunctionCompactness
