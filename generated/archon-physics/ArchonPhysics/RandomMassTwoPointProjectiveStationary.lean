import ArchonPhysics.RandomMassTwoPointProjectiveMarkov
import Mathlib.Analysis.Asymptotics.SpecificAsymptotics
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.Topology.Sequences

/-!
# A stationary law for the two-point projective transfer dynamics

This file implements the Krylov--Bogolyubov construction for the concrete
equal-weight two-atom projective Markov operator.  Starting from an arbitrary
direction law, it normalizes the finite sum of its first `n + 1` Markov
iterates.  Compactness gives a weakly convergent subsequence, while an exact
telescoping identity for continuous observables makes the limit stationary.

This is only an invariant probability measure for the oriented projective
Markov dynamics.  No Furstenberg positivity theorem, positive Lyapunov
exponent, EFC, or localization statement is asserted.
-/

open scoped NNReal Topology BoundedContinuousFunction

namespace ArchonPhysics.RandomMassTwoPointProjectiveStationary

open ArchonPhysics.RandomMassTwoPointProjectiveMarkov
open Filter MeasureTheory Set Topology

noncomputable section

local instance : Nonempty OrientedProjectiveDirection :=
  Set.Nonempty.to_subtype (NormedSpace.sphere_nonempty.mpr zero_le_one)

/-- The `n`th law in the Markov orbit of an initial projective law. -/
def projectiveMarkovOrbit
    (lambda mass0 mass1 : Real)
    (initial : ProbabilityMeasure OrientedProjectiveDirection)
    (n : Nat) : ProbabilityMeasure OrientedProjectiveDirection :=
  (twoPointProjectiveMarkovOperator lambda mass0 mass1)^[n] initial

@[simp]
theorem projectiveMarkovOrbit_zero
    (lambda mass0 mass1 : Real)
    (initial : ProbabilityMeasure OrientedProjectiveDirection) :
    projectiveMarkovOrbit lambda mass0 mass1 initial 0 = initial := by
  simp [projectiveMarkovOrbit]

@[simp]
theorem projectiveMarkovOrbit_succ
    (lambda mass0 mass1 : Real)
    (initial : ProbabilityMeasure OrientedProjectiveDirection) (n : Nat) :
    projectiveMarkovOrbit lambda mass0 mass1 initial (n + 1) =
      twoPointProjectiveMarkovOperator lambda mass0 mass1
        (projectiveMarkovOrbit lambda mass0 mass1 initial n) := by
  simp [projectiveMarkovOrbit, Function.iterate_succ_apply']

/-- The unnormalized finite sum of the first `n` Markov orbit laws. -/
def projectiveMarkovOrbitSum
    (lambda mass0 mass1 : Real)
    (initial : ProbabilityMeasure OrientedProjectiveDirection)
    (n : Nat) : FiniteMeasure OrientedProjectiveDirection :=
  ∑ k ∈ Finset.range n,
    (projectiveMarkovOrbit lambda mass0 mass1 initial k).toFiniteMeasure

@[simp]
theorem projectiveMarkovOrbitSum_mass
    (lambda mass0 mass1 : Real)
    (initial : ProbabilityMeasure OrientedProjectiveDirection) (n : Nat) :
    (projectiveMarkovOrbitSum lambda mass0 mass1 initial n).mass = n := by
  unfold projectiveMarkovOrbitSum
  induction n with
  | zero =>
      simp only [Finset.range_zero, Finset.sum_empty,
        FiniteMeasure.zero_mass, Nat.cast_zero]
  | succ n ih =>
      rw [Finset.sum_range_succ]
      unfold FiniteMeasure.mass at ih ⊢
      rw [congrFun (FiniteMeasure.coeFn_add
        (∑ k ∈ Finset.range n,
          (projectiveMarkovOrbit lambda mass0 mass1 initial k).toFiniteMeasure)
        (projectiveMarkovOrbit lambda mass0 mass1 initial n).toFiniteMeasure)
        Set.univ]
      rw [Pi.add_apply]
      rw [ih]
      simp only [ProbabilityMeasure.toFiniteMeasure_apply_eq_apply,
        ProbabilityMeasure.coeFn_univ, Nat.cast_add, Nat.cast_one]

theorem projectiveMarkovOrbitSum_succ_ne_zero
    (lambda mass0 mass1 : Real)
    (initial : ProbabilityMeasure OrientedProjectiveDirection) (n : Nat) :
    projectiveMarkovOrbitSum lambda mass0 mass1 initial (n + 1) ≠ 0 := by
  rw [← FiniteMeasure.mass_nonzero_iff,
    projectiveMarkovOrbitSum_mass]
  exact_mod_cast Nat.succ_ne_zero n

/-- The empirical law of the first `n + 1` Markov iterates. -/
def projectiveMarkovCesaroLaw
    (lambda mass0 mass1 : Real)
    (initial : ProbabilityMeasure OrientedProjectiveDirection)
    (n : Nat) : ProbabilityMeasure OrientedProjectiveDirection :=
  (projectiveMarkovOrbitSum lambda mass0 mass1 initial (n + 1)).normalize

/-- A bounded observable precomposed with one normalized transfer action. -/
def observableAfterNormalizedTransfer
    (lambda mass : Real)
    (observable : OrientedProjectiveDirection →ᵇ Real) :
    OrientedProjectiveDirection →ᵇ Real :=
  observable.compContinuous
    ⟨normalizedTransferDirection lambda mass,
      continuous_normalizedTransferDirection lambda mass⟩

@[simp]
theorem observableAfterNormalizedTransfer_apply
    (lambda mass : Real)
    (observable : OrientedProjectiveDirection →ᵇ Real)
    (direction : OrientedProjectiveDirection) :
    observableAfterNormalizedTransfer lambda mass observable direction =
      observable (normalizedTransferDirection lambda mass direction) :=
  rfl

/-- Markov/Feller duality for a bounded continuous observable. -/
theorem integral_twoPointProjectiveMarkovOperator
    (lambda mass0 mass1 : Real)
    (law : ProbabilityMeasure OrientedProjectiveDirection)
    (observable : OrientedProjectiveDirection →ᵇ Real) :
    (∫ direction, observable direction
      ∂(twoPointProjectiveMarkovOperator lambda mass0 mass1 law :
        Measure OrientedProjectiveDirection)) =
      ((∫ direction, observable
          (normalizedTransferDirection lambda mass0 direction)
          ∂(law : Measure OrientedProjectiveDirection)) +
        ∫ direction, observable
          (normalizedTransferDirection lambda mass1 direction)
          ∂(law : Measure OrientedProjectiveDirection)) / 2 := by
  unfold twoPointProjectiveMarkovOperator
  change (∫ direction, observable direction
    ∂((probabilityAverage
      (transferDirectionPushforward lambda mass0 law)
      (transferDirectionPushforward lambda mass1 law)).toFiniteMeasure :
        Measure OrientedProjectiveDirection)) = _
  rw [probabilityAverage_toFiniteMeasure]
  simp only [FiniteMeasure.toMeasure_add, FiniteMeasure.toMeasure_smul,
    ProbabilityMeasure.toMeasure_comp_toFiniteMeasure_eq_toMeasure]
  unfold transferDirectionPushforward
  simp only [ProbabilityMeasure.toMeasure_map]
  rw [integral_add_measure (observable.integrable _)
    (observable.integrable _)]
  simp only [integral_smul_nnreal_measure, NNReal.smul_def]
  rw [integral_map
    (continuous_normalizedTransferDirection lambda mass0).measurable.aemeasurable
    (observable.integrable _).aestronglyMeasurable]
  rw [integral_map
    (continuous_normalizedTransferDirection lambda mass1).measurable.aemeasurable
    (observable.integrable _).aestronglyMeasurable]
  norm_num
  ring

/-- Integrating against the empirical law is the arithmetic mean of the
corresponding orbit integrals. -/
theorem integral_projectiveMarkovCesaroLaw
    (lambda mass0 mass1 : Real)
    (initial : ProbabilityMeasure OrientedProjectiveDirection)
    (observable : OrientedProjectiveDirection →ᵇ Real) (n : Nat) :
    (∫ direction, observable direction
      ∂(projectiveMarkovCesaroLaw lambda mass0 mass1 initial n :
        Measure OrientedProjectiveDirection)) =
      (((n + 1 : Nat) : NNReal)⁻¹ : Real) *
        ∑ k ∈ Finset.range (n + 1),
          ∫ direction, observable direction
            ∂(projectiveMarkovOrbit lambda mass0 mass1 initial k :
              Measure OrientedProjectiveDirection) := by
  unfold projectiveMarkovCesaroLaw
  rw [FiniteMeasure.toMeasure_normalize_eq_of_nonzero
    (projectiveMarkovOrbitSum lambda mass0 mass1 initial (n + 1))
    (projectiveMarkovOrbitSum_succ_ne_zero
      lambda mass0 mass1 initial n)]
  rw [integral_smul_nnreal_measure]
  rw [projectiveMarkovOrbitSum_mass]
  unfold projectiveMarkovOrbitSum
  rw [FiniteMeasure.toMeasure_sum]
  rw [integral_finsetSum_measure]
  · rfl
  · intro k hk
    exact observable.integrable _

/-- Applying the Markov operator to an empirical law shifts every orbit
observable by one step. -/
theorem integral_markov_projectiveMarkovCesaroLaw
    (lambda mass0 mass1 : Real)
    (initial : ProbabilityMeasure OrientedProjectiveDirection)
    (observable : OrientedProjectiveDirection →ᵇ Real) (n : Nat) :
    (∫ direction, observable direction
      ∂(twoPointProjectiveMarkovOperator lambda mass0 mass1
        (projectiveMarkovCesaroLaw lambda mass0 mass1 initial n) :
          Measure OrientedProjectiveDirection)) =
      (((n + 1 : Nat) : NNReal)⁻¹ : Real) *
        ∑ k ∈ Finset.range (n + 1),
          ∫ direction, observable direction
            ∂(projectiveMarkovOrbit lambda mass0 mass1 initial (k + 1) :
              Measure OrientedProjectiveDirection) := by
  rw [integral_twoPointProjectiveMarkovOperator]
  change ((∫ direction,
      observableAfterNormalizedTransfer lambda mass0 observable direction
      ∂(projectiveMarkovCesaroLaw lambda mass0 mass1 initial n :
        Measure OrientedProjectiveDirection)) +
    ∫ direction,
      observableAfterNormalizedTransfer lambda mass1 observable direction
      ∂(projectiveMarkovCesaroLaw lambda mass0 mass1 initial n :
        Measure OrientedProjectiveDirection)) / 2 = _
  rw [integral_projectiveMarkovCesaroLaw,
    integral_projectiveMarkovCesaroLaw]
  rw [← mul_add, div_eq_mul_inv, mul_assoc]
  congr 1
  rw [← Finset.sum_add_distrib, Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro k hk
  rw [projectiveMarkovOrbit_succ]
  simpa only [div_eq_mul_inv, observableAfterNormalizedTransfer_apply] using
    (integral_twoPointProjectiveMarkovOperator lambda mass0 mass1
      (projectiveMarkovOrbit lambda mass0 mass1 initial k) observable).symm

/-- Exact boundary-term identity for the failure of a finite empirical law to
be stationary. -/
theorem integral_markov_cesaro_sub
    (lambda mass0 mass1 : Real)
    (initial : ProbabilityMeasure OrientedProjectiveDirection)
    (observable : OrientedProjectiveDirection →ᵇ Real) (n : Nat) :
    (∫ direction, observable direction
      ∂(twoPointProjectiveMarkovOperator lambda mass0 mass1
        (projectiveMarkovCesaroLaw lambda mass0 mass1 initial n) :
          Measure OrientedProjectiveDirection)) -
      (∫ direction, observable direction
        ∂(projectiveMarkovCesaroLaw lambda mass0 mass1 initial n :
          Measure OrientedProjectiveDirection)) =
      (((n + 1 : Nat) : NNReal)⁻¹ : Real) *
        ((∫ direction, observable direction
          ∂(projectiveMarkovOrbit lambda mass0 mass1 initial (n + 1) :
            Measure OrientedProjectiveDirection)) -
        ∫ direction, observable direction
          ∂(initial : Measure OrientedProjectiveDirection)) := by
  rw [integral_markov_projectiveMarkovCesaroLaw,
    integral_projectiveMarkovCesaroLaw]
  rw [← mul_sub, ← Finset.sum_sub_distrib]
  congr 1
  simpa only [projectiveMarkovOrbit_zero] using
    (Finset.sum_range_sub
      (fun k => ∫ direction, observable direction
        ∂(projectiveMarkovOrbit lambda mass0 mass1 initial k :
          Measure OrientedProjectiveDirection))
      (n + 1))

/-- The observable discrepancy between an empirical law and its Markov image
vanishes as the averaging length tends to infinity. -/
theorem tendsto_integral_markov_cesaro_sub
    (lambda mass0 mass1 : Real)
    (initial : ProbabilityMeasure OrientedProjectiveDirection)
    (observable : OrientedProjectiveDirection →ᵇ Real) :
    Tendsto (fun n : Nat =>
      (∫ direction, observable direction
        ∂(twoPointProjectiveMarkovOperator lambda mass0 mass1
          (projectiveMarkovCesaroLaw lambda mass0 mass1 initial n) :
            Measure OrientedProjectiveDirection)) -
      ∫ direction, observable direction
        ∂(projectiveMarkovCesaroLaw lambda mass0 mass1 initial n :
          Measure OrientedProjectiveDirection))
      atTop (𝓝 0) := by
  rw [tendsto_zero_iff_norm_tendsto_zero]
  refine squeeze_zero
    (g := fun n : Nat => (2 * ‖observable‖) / ((n : Real) + 1))
    (fun n => norm_nonneg _) (fun n => ?_) ?_
  · rw [integral_markov_cesaro_sub]
    rw [norm_mul]
    have hboundary :
        ‖(∫ direction, observable direction
            ∂(projectiveMarkovOrbit lambda mass0 mass1 initial (n + 1) :
              Measure OrientedProjectiveDirection)) -
          ∫ direction, observable direction
            ∂(initial : Measure OrientedProjectiveDirection)‖ ≤
          2 * ‖observable‖ := by
      calc
        _ ≤ ‖∫ direction, observable direction
              ∂(projectiveMarkovOrbit lambda mass0 mass1 initial (n + 1) :
                Measure OrientedProjectiveDirection)‖ +
            ‖∫ direction, observable direction
              ∂(initial : Measure OrientedProjectiveDirection)‖ :=
          norm_sub_le _ _
        _ ≤ ‖observable‖ + ‖observable‖ :=
          add_le_add (observable.norm_integral_le_norm _)
            (observable.norm_integral_le_norm _)
        _ = 2 * ‖observable‖ := by ring
    have hcoefficient :
        ‖(((n + 1 : Nat) : NNReal)⁻¹ : Real)‖ =
          1 / ((n : Real) + 1) := by
      rw [Real.norm_of_nonneg]
      · rw [one_div]
        norm_cast
      · positivity
    rw [hcoefficient]
    calc
      _ ≤ (1 / ((n : Real) + 1)) * (2 * ‖observable‖) :=
        mul_le_mul_of_nonneg_left hboundary (by positivity)
      _ = (2 * ‖observable‖) / ((n : Real) + 1) := by ring
  · have h := (tendsto_const_nhds (x := 2 * ‖observable‖)).mul
      (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := Real))
    simpa only [mul_zero, div_eq_mul_inv, one_mul] using h

/-- Compactness supplies a weakly convergent subsequence of empirical laws. -/
theorem exists_projectiveMarkovCesaro_tendsto_subseq
    (lambda mass0 mass1 : Real)
    (initial : ProbabilityMeasure OrientedProjectiveDirection) :
    ∃ (limitLaw : ProbabilityMeasure OrientedProjectiveDirection)
      (subsequence : Nat → Nat),
      StrictMono subsequence ∧
        Tendsto (projectiveMarkovCesaroLaw lambda mass0 mass1 initial ∘
          subsequence) atTop (𝓝 limitLaw) :=
  CompactSpace.tendsto_subseq
    (projectiveMarkovCesaroLaw lambda mass0 mass1 initial)

/-- Any weak limit of an empirical-law subsequence is also the weak limit of
the corresponding Markov images. -/
theorem tendsto_markov_of_cesaro_subseq_tendsto
    (lambda mass0 mass1 : Real)
    (initial : ProbabilityMeasure OrientedProjectiveDirection)
    {limitLaw : ProbabilityMeasure OrientedProjectiveDirection}
    {subsequence : Nat → Nat} (hsubsequence : StrictMono subsequence)
    (hlimit : Tendsto
      (projectiveMarkovCesaroLaw lambda mass0 mass1 initial ∘ subsequence)
      atTop (𝓝 limitLaw)) :
    Tendsto (fun n =>
      twoPointProjectiveMarkovOperator lambda mass0 mass1
        (projectiveMarkovCesaroLaw lambda mass0 mass1 initial
          (subsequence n)))
      atTop (𝓝 limitLaw) := by
  rw [ProbabilityMeasure.tendsto_iff_forall_integral_tendsto]
  intro observable
  have hbase :=
    (ProbabilityMeasure.tendsto_iff_forall_integral_tendsto.mp hlimit)
      observable
  have hdiscrepancy :=
    (tendsto_integral_markov_cesaro_sub
      lambda mass0 mass1 initial observable).comp
        hsubsequence.tendsto_atTop
  simpa only [Function.comp_apply, sub_add_cancel, zero_add] using
    hdiscrepancy.add hbase

/-- A stationary law exists starting from every initial projective law. -/
theorem exists_twoPointProjectiveStationary_of_initial
    (lambda mass0 mass1 : Real)
    (initial : ProbabilityMeasure OrientedProjectiveDirection) :
    ∃ law : ProbabilityMeasure OrientedProjectiveDirection,
      IsTwoPointProjectiveStationary lambda mass0 mass1 law := by
  obtain ⟨limitLaw, subsequence, hsubsequence, hlimit⟩ :=
    exists_projectiveMarkovCesaro_tendsto_subseq
      lambda mass0 mass1 initial
  refine ⟨limitLaw, ?_⟩
  unfold IsTwoPointProjectiveStationary
  have hmarkovLimit : Tendsto (fun n =>
      twoPointProjectiveMarkovOperator lambda mass0 mass1
        (projectiveMarkovCesaroLaw lambda mass0 mass1 initial
          (subsequence n)))
      atTop (𝓝 (twoPointProjectiveMarkovOperator
        lambda mass0 mass1 limitLaw)) := by
    change Tendsto
      (twoPointProjectiveMarkovOperator lambda mass0 mass1 ∘
        (projectiveMarkovCesaroLaw lambda mass0 mass1 initial ∘
          subsequence)) atTop
      (𝓝 (twoPointProjectiveMarkovOperator lambda mass0 mass1 limitLaw))
    exact ((continuous_twoPointProjectiveMarkovOperator
      lambda mass0 mass1).tendsto limitLaw).comp hlimit
  have hsameLimit := tendsto_markov_of_cesaro_subseq_tendsto
    lambda mass0 mass1 initial hsubsequence hlimit
  exact tendsto_nhds_unique hmarkovLimit hsameLimit

/-- The concrete equal-weight two-point projective Markov operator has a
stationary probability law for every choice of its parameters. -/
theorem exists_twoPointProjectiveStationary
    (lambda mass0 mass1 : Real) :
    ∃ law : ProbabilityMeasure OrientedProjectiveDirection,
      IsTwoPointProjectiveStationary lambda mass0 mass1 law := by
  let direction : OrientedProjectiveDirection :=
    Classical.choice (inferInstance : Nonempty OrientedProjectiveDirection)
  let initial : ProbabilityMeasure OrientedProjectiveDirection :=
    ⟨Measure.dirac direction, Measure.dirac.isProbabilityMeasure⟩
  exact exists_twoPointProjectiveStationary_of_initial
    lambda mass0 mass1 initial

end

end ArchonPhysics.RandomMassTwoPointProjectiveStationary
