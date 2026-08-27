import Mathlib.MeasureTheory.Measure.LevyConvergence
import Mathlib.MeasureTheory.Measure.CharacteristicFunction.TaylorExpansion
import Mathlib.Topology.Instances.RatLemmas

/-!
# Tight joint measures determined on a rational Fourier grid

For probability measures on the fixed three-frequency space
`Fin 3 -> Real`, values of the characteristic function on the countable dense
grid `Fin 3 -> Rat` determine the measure.  Tightness plus convergence at all
grid points therefore forces convergence of the whole sequence.
-/

open scoped Topology RealInnerProductSpace

namespace ArchonPhysics.DenseJointCharacteristicFunctionCompactness

open Filter MeasureTheory Set

noncomputable section

/-- Coordinatewise embedding of the rational three-frequency grid. -/
def rationalFrequencyTriple (q : Fin 3 -> Rat) :
    EuclideanSpace Real (Fin 3) :=
  (PiLp.homeomorph 2 (fun _r : Fin 3 => Real)).symm
    (fun r => (q r : Real))

/-- The coordinatewise rational grid is dense in the real
three-frequency space. -/
theorem denseRange_rationalFrequencyTriple :
    DenseRange rationalFrequencyTriple := by
  have hplain : DenseRange
      (Pi.map (fun _r : Fin 3 => fun q : Rat => (q : Real))) :=
    DenseRange.piMap fun _r => Rat.isDenseEmbedding_coe_real.dense
  have heuc : DenseRange
      (PiLp.homeomorph 2 (fun _r : Fin 3 => Real)).symm :=
    (PiLp.homeomorph 2 (fun _r : Fin 3 => Real)).symm.surjective.denseRange
  have hcomp := heuc.comp hplain
    (PiLp.homeomorph 2 (fun _r : Fin 3 => Real)).symm.continuous
  change DenseRange
    ((PiLp.homeomorph 2 (fun _r : Fin 3 => Real)).symm ∘
      Pi.map (fun _r : Fin 3 => fun q : Rat => (q : Real)))
  exact hcomp

/-- Two joint probability measures agree if their characteristic functions
agree at every rational parameter triple. -/
theorem probabilityMeasure_eq_of_charFun_rationalTriple_eq
    (mu nu : ProbabilityMeasure (EuclideanSpace Real (Fin 3)))
    (h : forall q : Fin 3 -> Rat,
      charFun (mu : Measure (EuclideanSpace Real (Fin 3))) (rationalFrequencyTriple q) =
        charFun (nu : Measure (EuclideanSpace Real (Fin 3)))
          (rationalFrequencyTriple q)) :
    mu = nu := by
  apply ProbabilityMeasure.toMeasure_injective
  apply Measure.ext_of_charFun
  refine denseRange_rationalFrequencyTriple.equalizer
    (continuous_charFun (μ := (mu : Measure (EuclideanSpace Real (Fin 3)))))
    (continuous_charFun (μ := (nu : Measure (EuclideanSpace Real (Fin 3))))) ?_
  funext q
  exact h q

/-- A tight sequence of joint three-frequency probability measures converges
weakly once its characteristic functions converge on the countable rational
grid.  No candidate limit function or measure is supplied. -/
theorem exists_tendsto_of_tight_of_charFun_rationalTriple
    (mu : Nat -> ProbabilityMeasure (EuclideanSpace Real (Fin 3)))
    (hTight : IsTightMeasureSet
      {((nu : ProbabilityMeasure (EuclideanSpace Real (Fin 3))) :
          Measure (EuclideanSpace Real (Fin 3))) |
        nu ∈ Set.range mu})
    (hRat : forall q : Fin 3 -> Rat, exists z : Complex,
      Tendsto
        (fun n => charFun
          (mu n : Measure (EuclideanSpace Real (Fin 3))) (rationalFrequencyTriple q))
        atTop (nhds z)) :
    exists target : ProbabilityMeasure (EuclideanSpace Real (Fin 3)),
      Tendsto mu atTop (nhds target) := by
  let K : Set (ProbabilityMeasure (EuclideanSpace Real (Fin 3))) :=
    closure (Set.range mu)
  have hK : IsCompact K := by
    exact isCompact_closure_of_isTightMeasureSet hTight
  have hmem : ∀ᶠ n in atTop, mu n ∈ K :=
    Filter.Eventually.of_forall fun n =>
      subset_closure (Set.mem_range_self n)
  have hfrequent : ∃ᶠ n in atTop, mu n ∈ K := hmem.frequently
  obtain ⟨target, htargetK, htargetCluster⟩ :=
    hK.exists_mapClusterPt_of_frequently hfrequent
  refine ⟨target, hK.tendsto_nhds_of_unique_mapClusterPt hmem ?_⟩
  intro nu _hnuK hnuCluster
  apply probabilityMeasure_eq_of_charFun_rationalTriple_eq
  intro q
  obtain ⟨z, hz⟩ := hRat q
  obtain ⟨psiNu, hpsiNuMono, hpsiNu⟩ := hnuCluster.tendsto_subseq
  obtain ⟨psiTarget, hpsiTargetMono, hpsiTarget⟩ :=
    htargetCluster.tendsto_subseq
  have hnuChar : Tendsto
      (fun n => charFun
        (mu (psiNu n) : Measure (EuclideanSpace Real (Fin 3)))
          (rationalFrequencyTriple q))
      atTop
      (nhds (charFun (nu : Measure (EuclideanSpace Real (Fin 3)))
        (rationalFrequencyTriple q))) :=
    (ProbabilityMeasure.tendsto_iff_tendsto_charFun.mp hpsiNu)
      (rationalFrequencyTriple q)
  have htargetChar : Tendsto
      (fun n => charFun
        (mu (psiTarget n) : Measure (EuclideanSpace Real (Fin 3)))
          (rationalFrequencyTriple q))
      atTop
      (nhds (charFun (target : Measure (EuclideanSpace Real (Fin 3)))
        (rationalFrequencyTriple q))) :=
    (ProbabilityMeasure.tendsto_iff_tendsto_charFun.mp hpsiTarget)
      (rationalFrequencyTriple q)
  have hnuLimit :
      charFun (nu : Measure (EuclideanSpace Real (Fin 3)))
          (rationalFrequencyTriple q) = z :=
    tendsto_nhds_unique hnuChar (hz.comp hpsiNuMono.tendsto_atTop)
  have htargetLimit :
      charFun (target : Measure (EuclideanSpace Real (Fin 3)))
          (rationalFrequencyTriple q) = z :=
    tendsto_nhds_unique htargetChar
      (hz.comp hpsiTargetMono.tendsto_atTop)
  exact hnuLimit.trans htargetLimit.symm

end

end ArchonPhysics.DenseJointCharacteristicFunctionCompactness
