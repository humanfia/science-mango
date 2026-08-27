import Mathlib.MeasureTheory.Measure.MeasureSpace
import Mathlib.Topology.MetricSpace.Cauchy

/-!
# Vanishing uniform approximation limits

A two-parameter approximation can be closed without choosing a diagonal:
uniform error tending to zero makes the exact sequence Cauchy, while the
limits of the fixed approximants converge to the same point.  A countable
almost-everywhere version extracts one point from a nonzero measure and then
uses the deterministic limit sequence to identify the common limit.
-/

namespace ArchonPhysics.VanishingUniformApproximationLimit

open Filter MeasureTheory Topology

variable {X : Type*} [PseudoMetricSpace X] [CompleteSpace X]

/-- Uniform approximation by convergent rows, with error vanishing in the row
index, gives one common limit for the exact sequence and all row limits. -/
theorem exists_commonLimit_of_vanishing_uniformApproximation
    (exact : Nat → X) (approx : Nat → Nat → X)
    (limit : Nat → X) (error : Nat → Real)
    (herror : Tendsto error atTop (𝓝 0))
    (happrox : ∀ k, Tendsto (approx k) atTop (𝓝 (limit k)))
    (huniform : ∀ k n, dist (exact n) (approx k n) ≤ error k) :
    ∃ L, Tendsto exact atTop (𝓝 L) ∧
      Tendsto limit atTop (𝓝 L) := by
  have hexactCauchy : CauchySeq exact := Metric.cauchySeq_iff.2 (by
    intro epsilon hepsilon
    have hepsilonThird : 0 < epsilon / 3 := div_pos hepsilon (by norm_num)
    obtain ⟨k, hk⟩ :=
      (herror.eventually (gt_mem_nhds hepsilonThird)).exists
    obtain ⟨N, hN⟩ := Metric.cauchySeq_iff.1
      (happrox k).cauchySeq (epsilon / 3) hepsilonThird
    refine ⟨N, fun m hm n hn ↦ ?_⟩
    calc
      dist (exact m) (exact n) ≤
          dist (exact m) (approx k m) +
            dist (approx k m) (approx k n) +
              dist (approx k n) (exact n) := by
        calc
          dist (exact m) (exact n) ≤
              dist (exact m) (approx k m) +
                dist (approx k m) (exact n) := dist_triangle _ _ _
          _ ≤ dist (exact m) (approx k m) +
                (dist (approx k m) (approx k n) +
                  dist (approx k n) (exact n)) :=
            add_le_add le_rfl (dist_triangle _ _ _)
          _ = _ := by ring
      _ ≤ error k + dist (approx k m) (approx k n) + error k := by
        exact add_le_add (add_le_add (huniform k m) le_rfl)
          (by simpa only [dist_comm] using huniform k n)
      _ < epsilon := by
        linarith [hN m hm n hn])
  obtain ⟨L, hL⟩ := cauchySeq_tendsto_of_complete hexactCauchy
  have hlimitError : ∀ k, dist (limit k) L ≤ error k := by
    intro k
    exact le_of_tendsto ((happrox k).dist hL)
      (Eventually.of_forall fun n ↦ by
        simpa only [dist_comm] using huniform k n)
  have hlimitDist :
      Tendsto (fun k ↦ dist (limit k) L) atTop (𝓝 0) :=
    squeeze_zero (fun _ ↦ dist_nonneg) hlimitError herror
  exact ⟨L, hL, tendsto_iff_dist_tendsto_zero.2 hlimitDist⟩

variable {Omega : Type*} [MeasurableSpace Omega]

/-- Almost-everywhere form of the uniform-approximation closure.  Nonzeroness
of the measure is the minimal witness assumption needed to select one point
from the common full-measure set. -/
theorem exists_commonLimit_ae_of_vanishing_uniformApproximation
    (mu : Measure Omega) [NeZero mu]
    (exact : Nat → Omega → X) (approx : Nat → Nat → Omega → X)
    (limit : Nat → X) (error : Nat → Real)
    (herror : Tendsto error atTop (𝓝 0))
    (happrox : ∀ k, ∀ᵐ omega ∂mu,
      Tendsto (fun n ↦ approx k n omega) atTop (𝓝 (limit k)))
    (huniform : ∀ᵐ omega ∂mu, ∀ k n,
      dist (exact n omega) (approx k n omega) ≤ error k) :
    ∃ L, Tendsto limit atTop (𝓝 L) ∧
      ∀ᵐ omega ∂mu,
        Tendsto (fun n ↦ exact n omega) atTop (𝓝 L) := by
  have happroxAll : ∀ᵐ omega ∂mu, ∀ k,
      Tendsto (fun n ↦ approx k n omega) atTop (𝓝 (limit k)) :=
    MeasureTheory.ae_all_iff.2 happrox
  have hgood : ∀ᵐ omega ∂mu,
      (∀ k, Tendsto (fun n ↦ approx k n omega)
        atTop (𝓝 (limit k))) ∧
      (∀ k n, dist (exact n omega) (approx k n omega) ≤ error k) :=
    happroxAll.and huniform
  obtain ⟨omegaZero, homegaZero⟩ := hgood.exists
  obtain ⟨L, _hexactZero, hlimit⟩ :=
    exists_commonLimit_of_vanishing_uniformApproximation
      (fun n ↦ exact n omegaZero)
      (fun k n ↦ approx k n omegaZero) limit error herror
      homegaZero.1 homegaZero.2
  refine ⟨L, hlimit, ?_⟩
  filter_upwards [hgood] with omega homega
  obtain ⟨Lomega, hexact, hlimitOmega⟩ :=
    exists_commonLimit_of_vanishing_uniformApproximation
      (fun n ↦ exact n omega) (fun k n ↦ approx k n omega)
      limit error herror homega.1 homega.2
  have hzero : dist Lomega L = 0 :=
    tendsto_nhds_unique_dist hlimitOmega hlimit
  have hinseparable : Inseparable Lomega L :=
    Metric.inseparable_iff.2 hzero
  change 𝓝 Lomega = 𝓝 L at hinseparable
  rw [← hinseparable]
  exact hexact

end ArchonPhysics.VanishingUniformApproximationLimit
