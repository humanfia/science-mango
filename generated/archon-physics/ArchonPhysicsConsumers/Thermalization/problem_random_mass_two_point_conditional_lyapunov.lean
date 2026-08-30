import ArchonPhysics.RandomMassTwoPointConditionalLyapunov

/-!
# Consumer: conditional two-point Lyapunov growth

This consumer specializes the stationary logarithmic-growth machinery to two
distinct atoms in the frozen mass interval.  Its sole analytic premise is the
explicit classical Furstenberg positivity implication from the core module.
Under that premise it returns a reusable endpoint containing a positive
stationary exponent, exact linear `n`-step expected log growth, and the exact
geometric-mean power law.

This conditional endpoint is intended as an honest input for later Jacobian
or small-denominator work.  It does not itself prove such an estimate, EFC,
localization, or positivity for the full continuous uniform mass law.
-/

namespace ArchonPhysicsConsumers.Thermalization

open ArchonPhysics
open ArchonPhysics.RandomMassTwoPointConditionalLyapunov
open ArchonPhysics.RandomMassTwoPointProjectiveLogGrowth
open ArchonPhysics.RandomMassTwoPointProjectiveMarkov
open ArchonPhysics.RandomMassTwoPointProjectiveStationary
open MeasureTheory

noncomputable section

/-- Conditional Lyapunov endpoint for any two distinct atoms in the frozen
mass support.  The only unproved input is the single named classical
Furstenberg positivity interface. -/
theorem frozen_twoMass_conditionalLyapunovEndpoint
    (hfurstenberg : ClassicalTwoPointFurstenbergPositivity)
    {lambda mass0 mass1 : Real} (hlambda : 0 < lambda)
    (hmass0 : mass0 ∈ RandomEnsemble.massSupport)
    (hmass1 : mass1 ∈ RandomEnsemble.massSupport)
    (hmass : mass0 ≠ mass1) :
    mass0 ∈ RandomEnsemble.massSupport ∧
      mass1 ∈ RandomEnsemble.massSupport ∧
      Nonempty (TwoPointConditionalLyapunovEndpoint
        lambda mass0 mass1) := by
  refine ⟨hmass0, hmass1, ?_⟩
  obtain ⟨law, hstationary⟩ :=
    exists_twoPointProjectiveStationary lambda mass0 mass1
  let certificate : TwoPointFurstenbergIntegralCertificate
      lambda mass0 mass1 law :=
    twoPointFurstenbergIntegralCertificate_of_stationary
      hlambda hmass hstationary
  exact ⟨twoPointConditionalLyapunovEndpoint_of_Furstenberg
    hfurstenberg certificate⟩

/-- The concrete endpoint atoms `4/5` and `6/5` satisfy all kernel-checked
hypotheses, so the same single classical premise gives a conditional endpoint
at every positive spectral parameter. -/
theorem frozen_endpointMasses_conditionalLyapunovEndpoint
    (hfurstenberg : ClassicalTwoPointFurstenbergPositivity)
    {lambda : Real} (hlambda : 0 < lambda) :
    Nonempty (TwoPointConditionalLyapunovEndpoint lambda
      RandomEnsemble.massLower RandomEnsemble.massUpper) := by
  have hlower : RandomEnsemble.massLower ∈
      RandomEnsemble.massSupport := by
    simp [RandomEnsemble.massSupport, RandomEnsemble.massLower,
      RandomEnsemble.massUpper]
    norm_num
  have hupper : RandomEnsemble.massUpper ∈
      RandomEnsemble.massSupport := by
    simp [RandomEnsemble.massSupport, RandomEnsemble.massLower,
      RandomEnsemble.massUpper]
    norm_num
  have hdistinct : RandomEnsemble.massLower ≠
      RandomEnsemble.massUpper := by
    norm_num [RandomEnsemble.massLower, RandomEnsemble.massUpper]
  exact (frozen_twoMass_conditionalLyapunovEndpoint
    hfurstenberg hlambda hlower hupper hdistinct).2.2

/-- Explicit downstream-facing form: after the single classical premise,
there are a stationary law and a positive exponent with exact linear expected
log growth and exact geometric-mean power growth at every step count. -/
theorem frozen_endpointMasses_conditionalLyapunovGrowth
    (hfurstenberg : ClassicalTwoPointFurstenbergPositivity)
    {lambda : Real} (hlambda : 0 < lambda) :
    ∃ (law : ProbabilityMeasure OrientedProjectiveDirection)
      (exponent : Real),
      0 < exponent ∧
      (∀ n : Nat,
        (∫ direction,
          twoPointAccumulatedLogGrowthObservable lambda
            RandomEnsemble.massLower RandomEnsemble.massUpper n direction
          ∂(law : Measure OrientedProjectiveDirection)) =
          (n : Real) * exponent) ∧
      ∀ n : Nat,
        twoPointStationaryGeometricMean lambda
          RandomEnsemble.massLower RandomEnsemble.massUpper law n =
          (Real.exp exponent) ^ n := by
  let endpoint := Classical.choice
    (frozen_endpointMasses_conditionalLyapunovEndpoint
      hfurstenberg hlambda)
  exact ⟨endpoint.law, endpoint.exponent, endpoint.exponent_pos,
    endpoint.stationaryExpectedLogGrowth,
    endpoint.stationaryGeometricMean⟩

#print axioms transferLogNormCocycle_add
#print axioms integral_twoPointAccumulatedLogGrowthObservable_eq_nat_mul
#print axioms frozen_endpointMasses_conditionalLyapunovGrowth

end

end ArchonPhysicsConsumers.Thermalization
