import ArchonPhysics.FiniteMeasureVanishingErrorLInfinityWeakLimit

/-!
# Annealed weak-test domination

This file records the scientifically safe way to transfer an annealed
absolute-continuity estimate to a subsequential quenched limit.  It does not
claim a setwise estimate for the finite-volume quenched measures (which are
typically atomic).  Instead it assumes asymptotic self-averaging only against
bounded continuous nonnegative tests.  That is exactly the topology of weak
convergence of finite measures.
-/

open scoped Topology ENNReal BoundedContinuousFunction

namespace ArchonPhysics.FiniteMeasureAnnealedWeakTestDomination

open Filter MeasureTheory

noncomputable section

/-- If a quenched sequence converges weakly and its bounded-continuous tests
are asymptotically equal to those of an annealed sequence, then the annealed
sequence has the same weak limit. -/
theorem finiteMeasure_annealed_tendsto_of_quenched_tendsto_of_testAgainstNN_dist
    {X : Type*} [MeasurableSpace X] [TopologicalSpace X]
    [OpensMeasurableSpace X]
    (quenched annealed : Nat → FiniteMeasure X)
    (target : FiniteMeasure X)
    (hquenched : Tendsto quenched atTop (nhds target))
    (hclose : ∀ f : X →ᵇ NNReal,
      Tendsto
        (fun n ↦ dist ((quenched n).testAgainstNN f)
          ((annealed n).testAgainstNN f))
        atTop (nhds 0)) :
    Tendsto annealed atTop (nhds target) := by
  apply FiniteMeasure.tendsto_iff_forall_testAgainstNN_tendsto.mpr
  intro f
  have htest :=
    (FiniteMeasure.tendsto_iff_forall_testAgainstNN_tendsto.mp hquenched) f
  exact htest.congr_dist (hclose f)

/-- Annealed domination, up to a vanishing error, passes to a quenched weak
limit once bounded-continuous tests self-average.  Notice that `hbound` is an
estimate on `annealed`, not on the atomic finite-volume quenched measures. -/
theorem finiteMeasure_le_smul_of_annealed_apply_le_of_quenched_tendsto_of_testAgainstNN_dist
    {X : Type*} [PseudoMetricSpace X] [MeasurableSpace X]
    [BorelSpace X] [Nonempty X]
    (quenched annealed : Nat → FiniteMeasure X)
    (target : FiniteMeasure X)
    (hquenched : Tendsto quenched atTop (nhds target))
    (hclose : ∀ f : X →ᵇ NNReal,
      Tendsto
        (fun n ↦ dist ((quenched n).testAgainstNN f)
          ((annealed n).testAgainstNN f))
        atTop (nhds 0))
    (reference : Measure X) [reference.OuterRegular]
    (C : ENNReal) (hC : C ≠ ∞)
    (error : Nat → ENNReal) (herror : Tendsto error atTop (nhds 0))
    (hbound : ∀ n A, MeasurableSet A →
      (annealed n : Measure X) A ≤ C * reference A + error n) :
    (target : Measure X) ≤ C • reference := by
  apply ArchonPhysics.FiniteMeasureVanishingErrorLInfinityWeakLimit.finiteMeasure_le_smul_of_tendsto_of_apply_le_add_vanishingError
      annealed target
      (finiteMeasure_annealed_tendsto_of_quenched_tendsto_of_testAgainstNN_dist
        quenched annealed target hquenched hclose)
      reference C hC error herror hbound

/-- The corresponding absolute-continuity endpoint. -/
theorem finiteMeasure_absolutelyContinuous_of_annealed_apply_le_of_quenched_tendsto_of_testAgainstNN_dist
    {X : Type*} [PseudoMetricSpace X] [MeasurableSpace X]
    [BorelSpace X] [Nonempty X]
    (quenched annealed : Nat → FiniteMeasure X)
    (target : FiniteMeasure X)
    (hquenched : Tendsto quenched atTop (nhds target))
    (hclose : ∀ f : X →ᵇ NNReal,
      Tendsto
        (fun n ↦ dist ((quenched n).testAgainstNN f)
          ((annealed n).testAgainstNN f))
        atTop (nhds 0))
    (reference : Measure X) [reference.OuterRegular]
    (C : ENNReal) (hC : C ≠ ∞)
    (error : Nat → ENNReal) (herror : Tendsto error atTop (nhds 0))
    (hbound : ∀ n A, MeasurableSet A →
      (annealed n : Measure X) A ≤ C * reference A + error n) :
    (target : Measure X) ≪ reference := by
  exact
    (finiteMeasure_le_smul_of_annealed_apply_le_of_quenched_tendsto_of_testAgainstNN_dist
      quenched annealed target hquenched hclose reference C hC error herror
      hbound).absolutelyContinuous.trans Measure.smul_absolutelyContinuous

end

end ArchonPhysics.FiniteMeasureAnnealedWeakTestDomination
