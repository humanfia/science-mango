import ArchonPhysics.FiniteMeasureVanishingErrorLInfinityWeakLimit

/-!
# Uniform frequency-marginal domination under weak limits

A time-uniform Lebesgue-density bound for a continuous one-leg frequency
pushforward passes to every finite-measure weak limit.  This is the final
topological step needed after the joint frequency--mismatch coarea estimate;
finite-time absolute continuity without a uniform constant would not suffice.
-/

open scoped ENNReal Topology

namespace ArchonPhysics.FrequencyMarginalWeakLimitDomination

open ArchonPhysics.FiniteMeasureVanishingErrorLInfinityWeakLimit
open Filter MeasureTheory

noncomputable section

/-- Uniform domination of continuous frequency marginals is closed under weak
convergence of finite Borel measures. -/
theorem map_le_smul_volume_of_tendsto_of_uniform_map_le
    {X : Type*} [PseudoMetricSpace X] [MeasurableSpace X]
    [BorelSpace X] [Nonempty X]
    (source : Nat → FiniteMeasure X) (target : FiniteMeasure X)
    (hlimit : Tendsto source atTop (nhds target))
    (frequency : X → Real) (hfrequency : Continuous frequency)
    (C : ENNReal) (hC : C ≠ ∞)
    (hdomination : ∀ n,
      ((source n).map frequency : Measure Real) ≤
        C • (volume : Measure Real)) :
    (target.map frequency : Measure Real) ≤
      C • (volume : Measure Real) := by
  have hmappedLimit : Tendsto (fun n => (source n).map frequency)
      atTop (nhds (target.map frequency)) :=
    FiniteMeasure.tendsto_map_of_tendsto_of_continuous
      source target hlimit hfrequency
  apply finiteMeasure_le_smul_of_tendsto_of_apply_le_add_vanishingError
    (fun n => (source n).map frequency) (target.map frequency)
      hmappedLimit (volume : Measure Real) C hC (fun _ => 0)
      tendsto_const_nhds
  intro n A hA
  calc
    ((source n).map frequency : Measure Real) A ≤
        (C • (volume : Measure Real)) A := hdomination n A
    _ = C * (volume : Measure Real) A + 0 := by
      rw [Measure.smul_apply, smul_eq_mul, add_zero]

/-- In particular the weak-limit frequency marginal is absolutely continuous
with respect to one-dimensional Lebesgue measure. -/
theorem map_absolutelyContinuous_volume_of_tendsto_of_uniform_map_le
    {X : Type*} [PseudoMetricSpace X] [MeasurableSpace X]
    [BorelSpace X] [Nonempty X]
    (source : Nat → FiniteMeasure X) (target : FiniteMeasure X)
    (hlimit : Tendsto source atTop (nhds target))
    (frequency : X → Real) (hfrequency : Continuous frequency)
    (C : ENNReal) (hC : C ≠ ∞)
    (hdomination : ∀ n,
      ((source n).map frequency : Measure Real) ≤
        C • (volume : Measure Real)) :
    (target.map frequency : Measure Real) ≪
      (volume : Measure Real) := by
  exact
    (map_le_smul_volume_of_tendsto_of_uniform_map_le
      source target hlimit frequency hfrequency C hC
        hdomination).absolutelyContinuous.trans
      Measure.smul_absolutelyContinuous

end

end ArchonPhysics.FrequencyMarginalWeakLimitDomination
