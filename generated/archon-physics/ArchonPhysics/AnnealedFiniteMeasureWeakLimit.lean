import Mathlib.MeasureTheory.Integral.Lebesgue.DominatedConvergence
import Mathlib.MeasureTheory.Measure.FiniteMeasure
import Mathlib.MeasureTheory.Measure.GiryMonad

/-!
# Annealed finite measures and weak limits

For a measurable family of finite measures with an almost-everywhere uniform
mass ceiling, its barycenter is again a finite measure.  If the random finite
measures converge almost everywhere weakly to one deterministic target, the
barycenters converge weakly to the same target.

The construction uses the Giry `Measure.bind`.  Consequently its
measurability premise is deliberately stated for the measure-valued Giry
sigma algebra, rather than inferred from strong measurability for the weak
topology.
-/

open scoped Topology ENNReal BoundedContinuousFunction

namespace ArchonPhysics.AnnealedFiniteMeasureWeakLimit

open Filter MeasureTheory Set

noncomputable section

/-- The barycenter of a Giry-measurable family of finite measures.  An
almost-everywhere uniform mass ceiling makes the bound measure finite. -/
def annealedFiniteMeasure
    {Omega X : Type*} [MeasurableSpace Omega] [MeasurableSpace X]
    (probability : Measure Omega) [IsFiniteMeasure probability]
    (randomMeasure : Omega → FiniteMeasure X)
    (hmeasure : Measurable fun omega ↦
      (randomMeasure omega : Measure X))
    (massCeiling : NNReal)
    (hmass : ∀ᵐ omega ∂probability,
      (randomMeasure omega).mass ≤ massCeiling) :
    FiniteMeasure X := by
  let barycenter : Measure X :=
    probability.bind fun omega ↦ (randomMeasure omega : Measure X)
  have hbarycenterFinite : barycenter Set.univ < ∞ := by
    rw [Measure.bind_apply MeasurableSet.univ hmeasure.aemeasurable]
    calc
      (∫⁻ omega, (randomMeasure omega : Measure X) Set.univ
          ∂probability) ≤
          ∫⁻ _omega, (massCeiling : ENNReal) ∂probability := by
        apply lintegral_mono_ae
        filter_upwards [hmass] with omega homega
        simpa only [FiniteMeasure.ennreal_mass] using
          ENNReal.coe_le_coe.mpr homega
      _ < ∞ := by
        rw [lintegral_const]
        exact ENNReal.mul_lt_top ENNReal.coe_lt_top
          (measure_lt_top probability Set.univ)
  exact ⟨barycenter, ⟨hbarycenterFinite⟩⟩

/-- Evaluation of the annealed measure is the expectation of the random
measure evaluations. -/
theorem annealedFiniteMeasure_apply
    {Omega X : Type*} [MeasurableSpace Omega] [MeasurableSpace X]
    (probability : Measure Omega) [IsFiniteMeasure probability]
    (randomMeasure : Omega → FiniteMeasure X)
    (hmeasure : Measurable fun omega ↦
      (randomMeasure omega : Measure X))
    (massCeiling : NNReal)
    (hmass : ∀ᵐ omega ∂probability,
      (randomMeasure omega).mass ≤ massCeiling)
    {A : Set X} (hA : MeasurableSet A) :
    (annealedFiniteMeasure probability randomMeasure hmeasure massCeiling hmass :
      Measure X) A =
      ∫⁻ omega, (randomMeasure omega : Measure X) A ∂probability := by
  exact Measure.bind_apply hA hmeasure.aemeasurable

/-- A bounded nonnegative continuous test is controlled by a mass ceiling
and any pointwise bound on the test. -/
theorem lintegral_boundedContinuous_le_massCeiling
    {X : Type*} [MeasurableSpace X] [TopologicalSpace X]
    [OpensMeasurableSpace X]
    (measure : FiniteMeasure X) (massCeiling : NNReal)
    (hmass : measure.mass ≤ massCeiling)
    (f : X →ᵇ NNReal) (c : NNReal)
    (hf_le : ∀ x, f x ≤ c) :
    ∫⁻ x, (f x : ENNReal) ∂(measure : Measure X) ≤
      (c : ENNReal) * (massCeiling : ENNReal) := by
  have hf_le_fun : (f : X → NNReal) ≤
      (BoundedContinuousFunction.const X c : X → NNReal) := by
    intro x
    simpa only [BoundedContinuousFunction.const_apply] using hf_le x
  have htest := measure.testAgainstNN_mono hf_le_fun
  rw [FiniteMeasure.testAgainstNN_const] at htest
  have htestENN := ENNReal.coe_le_coe.mpr htest
  rw [FiniteMeasure.testAgainstNN_coe_eq, ENNReal.coe_mul] at htestENN
  exact htestENN.trans
    (mul_le_mul_right (ENNReal.coe_le_coe.mpr hmass) (c : ENNReal))

/-- Almost-sure weak convergence to a deterministic target, together with
one almost-sure uniform mass ceiling, passes through barycentering. -/
theorem annealedFiniteMeasure_tendsto_of_tendsto_ae_of_mass_le
    {Omega X : Type*} [MeasurableSpace Omega]
    [MeasurableSpace X] [TopologicalSpace X] [OpensMeasurableSpace X]
    (probability : Measure Omega) [IsProbabilityMeasure probability]
    (source : Nat → Omega → FiniteMeasure X)
    (target : FiniteMeasure X)
    (hmeasure : ∀ n, Measurable fun omega ↦
      (source n omega : Measure X))
    (massCeiling : NNReal)
    (hmass : ∀ n, ∀ᵐ omega ∂probability,
      (source n omega).mass ≤ massCeiling)
    (hlimit : ∀ᵐ omega ∂probability,
      Tendsto (fun n ↦ source n omega) atTop (nhds target)) :
    Tendsto
      (fun n ↦ annealedFiniteMeasure probability (source n)
        (hmeasure n) massCeiling (hmass n))
      atTop (nhds target) := by
  apply FiniteMeasure.tendsto_iff_forall_lintegral_tendsto.mpr
  intro f
  obtain ⟨c, hc⟩ := f.isBounded_range.bddAbove
  have hf_le : ∀ x, f x ≤ c := fun x ↦ hc (mem_range_self x)
  let bound : ENNReal := (c : ENNReal) * (massCeiling : ENNReal)
  let test : Nat → Omega → ENNReal := fun n omega ↦
    ∫⁻ x, (f x : ENNReal) ∂(source n omega : Measure X)
  have htestMeasurable (n : Nat) : Measurable (test n) := by
    exact (Measure.measurable_lintegral f.measurable_coe_ennreal_comp).comp
      (hmeasure n)
  have htestBound (n : Nat) :
      test n ≤ᵐ[probability] (fun _ ↦ bound) := by
    filter_upwards [hmass n] with omega homega
    exact lintegral_boundedContinuous_le_massCeiling
      (source n omega) massCeiling homega f c hf_le
  have hboundFinite :
      ∫⁻ _omega : Omega, bound ∂probability ≠ ∞ := by
    rw [lintegral_const]
    simp only [measure_univ, mul_one]
    exact ENNReal.mul_ne_top ENNReal.coe_ne_top ENNReal.coe_ne_top
  have htestLimit :
      ∀ᵐ omega ∂probability,
        Tendsto (fun n ↦ test n omega) atTop
          (nhds (∫⁻ x, (f x : ENNReal) ∂(target : Measure X))) := by
    filter_upwards [hlimit] with omega homega
    exact (FiniteMeasure.tendsto_iff_forall_lintegral_tendsto.mp homega) f
  have hdct := tendsto_lintegral_of_dominated_convergence
    (fun _omega : Omega ↦ bound) htestMeasurable htestBound
      hboundFinite htestLimit
  have hsourceIntegral (n : Nat) :
      ∫⁻ x, (f x : ENNReal)
          ∂(annealedFiniteMeasure probability (source n)
            (hmeasure n) massCeiling (hmass n) : Measure X) =
        ∫⁻ omega, test n omega ∂probability := by
    change
      ∫⁻ x, (f x : ENNReal)
          ∂(probability.bind fun omega ↦
            (source n omega : Measure X)) = _
    exact Measure.lintegral_bind (hmeasure n).aemeasurable
      f.measurable_coe_ennreal_comp.aemeasurable
  have htargetIntegral :
      ∫⁻ _omega : Omega,
          (∫⁻ x, (f x : ENNReal) ∂(target : Measure X))
          ∂probability =
        ∫⁻ x, (f x : ENNReal) ∂(target : Measure X) := by
    rw [lintegral_const, measure_univ, mul_one]
  rw [← htargetIntegral]
  simpa only [hsourceIntegral] using hdct

end

end ArchonPhysics.AnnealedFiniteMeasureWeakLimit
