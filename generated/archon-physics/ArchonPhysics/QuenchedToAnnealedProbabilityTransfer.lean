import Mathlib.MeasureTheory.Integral.Lebesgue.DominatedConvergence
import Mathlib.MeasureTheory.Measure.Prod

/-!
# Quenched-to-annealed probability transfer

The canonical random-mass/random-phase law is a product measure.  Positive-
time RPA is naturally proved after freezing the mass configuration and
averaging only over the Haar phases.  This module records the exact measure-
theoretic bridge needed afterwards: almost-everywhere convergence of the
quenched bad-event probability implies convergence of the full annealed
bad-event probability.

The proof is Fubini followed by dominated convergence.  No independence of
mass-dependent observables is asserted, and no dynamical or RPA estimate is
hidden in the statement.
-/

namespace ArchonPhysics.QuenchedToAnnealedProbabilityTransfer

open Filter MeasureTheory Set Topology

variable {Mass Phase : Type*}
  [MeasurableSpace Mass] [MeasurableSpace Phase]

noncomputable section

/-- If the phase-section probability of every measurable bad event tends to
zero for almost every frozen mass, then its probability under the product law
tends to zero.  Finiteness of both component measures supplies the uniform
dominating constant. -/
theorem prod_measure_tendsto_zero_of_ae_section_measure_tendsto_zero
    (massLaw : Measure Mass) (phaseLaw : Measure Phase)
    [IsFiniteMeasure massLaw] [IsFiniteMeasure phaseLaw]
    (bad : Nat -> Set (Mass × Phase))
    (hbad : forall n, MeasurableSet (bad n))
    (hsection : ∀ᵐ mass ∂massLaw,
      Tendsto (fun n => phaseLaw (Prod.mk mass ⁻¹' bad n))
        atTop (nhds 0)) :
    Tendsto (fun n => (massLaw.prod phaseLaw) (bad n))
      atTop (nhds 0) := by
  have hmeas : forall n,
      Measurable (fun mass => phaseLaw (Prod.mk mass ⁻¹' bad n)) := by
    intro n
    exact measurable_measure_prodMk_left (hbad n)
  have hbound : forall n,
      (fun mass => phaseLaw (Prod.mk mass ⁻¹' bad n))
        ≤ᵐ[massLaw] fun _ => phaseLaw Set.univ := by
    intro n
    filter_upwards with mass
    exact measure_mono (Set.subset_univ _)
  have hfinite :
      (∫⁻ _mass, phaseLaw Set.univ ∂massLaw) ≠ ⊤ := by
    rw [lintegral_const]
    exact ENNReal.mul_ne_top
      (measure_ne_top phaseLaw Set.univ)
      (measure_ne_top massLaw Set.univ)
  have hlim : ∀ᵐ mass ∂massLaw,
      Tendsto
        (fun n => phaseLaw (Prod.mk mass ⁻¹' bad n))
        atTop (nhds ((fun _mass : Mass => (0 : ENNReal)) mass)) := by
    simpa using hsection
  have hintegral := tendsto_lintegral_of_dominated_convergence
    (μ := massLaw) (fun _mass => phaseLaw Set.univ)
    hmeas hbound hfinite hlim
  simpa only [Measure.prod_apply (hbad _), lintegral_zero] using hintegral

end

end ArchonPhysics.QuenchedToAnnealedProbabilityTransfer
