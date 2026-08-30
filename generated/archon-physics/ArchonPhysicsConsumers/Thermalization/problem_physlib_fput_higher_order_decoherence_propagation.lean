import ArchonPhysics.PhyslibFPUTHigherOrderDecoherencePropagation

/-!
# Consumer: arbitrary-order decoherence propagation

This consumer checks that the result is genuinely arbitrary order and uses
the exact full coercive alpha-beta FPUT hierarchy.  The hierarchy-source
smallness remains visible as a premise; no positive-time random-phase or
Markov assumption is hidden.
-/

namespace ArchonPhysicsConsumers.Thermalization

open ArchonPhysics
open ArchonPhysics.CoerciveHamiltonianPhyslib
open ArchonPhysics.FinitePhaseMonomials
open ArchonPhysics.PhyslibFPUTCoercivePositiveTimeCumulantHierarchy
open ArchonPhysics.PhyslibFPUTHigherOrderDecoherencePropagation
open ArchonPhysics.PhyslibFPUTPositiveTimeCumulantHierarchy

noncomputable section

/-- Any finite joint order `I`, not merely two points, is propagated by the
full coercive hierarchy-source bound. -/
theorem fiveSite_higherOrder_decoherence_propagation_consumer
    {Omega I : Type*}
    [Fintype Omega]
    [Fintype I] [DecidableEq I] [Nonempty I]
    (weight : Omega → Real)
    (mass : Omega → Lattice.PositiveMassConfig 5)
    (kappa beta g : Real)
    (entry : I → PhaseSign × Lattice.Site 5)
    (p q : Omega → Time → HilbertConfiguration 5)
    (hp : ∀ omega, Differentiable Real (p omega))
    (hq : ∀ omega, Differentiable Real (q omega))
    (hHamilton : ∀ omega,
      SatisfiesHamiltonEquations (mass omega) kappa beta g
        (p omega) (q omega))
    (homega : ∀ omega i,
      0 < modeFrequency (mass omega) (entry i).2)
    (hzero : actualFiniteCubicEnsembleConnectedCumulant
      weight mass entry p q 0 = 0)
    (time epsilon : Real)
    (hsource : ∀ s ∈ Set.uIcc 0 time,
      ‖actualFiniteCoerciveEnsembleConnectedCumulantHierarchySource
        weight mass kappa beta g entry p q s‖ ≤ epsilon) :
    ‖actualFiniteCubicEnsembleConnectedCumulant
      weight mass entry p q time‖ ≤ epsilon * |time| :=
  norm_actualFiniteCoerciveEnsembleConnectedCumulant_le_of_initial_eq_zero
    weight mass kappa beta g entry p q hp hq hHamilton homega
    hzero time epsilon hsource

/-- The abstract thermodynamic/kinetic criterion checks the actual limiting
statement: source-size times observation-time going to zero forces every
selected fixed-order connected cumulant to zero. -/
theorem higherOrder_decoherence_limit_consumer
    (cumulant source : Nat → Real → Complex)
    (time epsilon : Nat → Real)
    (hzero : ∀ n, cumulant n 0 = 0)
    (hderiv : ∀ n s ∈ Set.uIcc 0 (time n),
      HasDerivAt (cumulant n) (source n s) s)
    (hsource : ∀ n s ∈ Set.uIcc 0 (time n),
      ‖source n s‖ ≤ epsilon n)
    (hvanish : Filter.Tendsto (fun n ↦ epsilon n * |time n|)
      Filter.atTop (nhds 0)) :
    Filter.Tendsto (fun n ↦ cumulant n (time n))
      Filter.atTop (nhds 0) :=
  connectedCumulant_tendsto_zero_of_source_timescale_tendsto_zero
    cumulant source time epsilon hzero hderiv hsource hvanish

#print axioms fiveSite_higherOrder_decoherence_propagation_consumer
#print axioms higherOrder_decoherence_limit_consumer

end

end ArchonPhysicsConsumers.Thermalization
