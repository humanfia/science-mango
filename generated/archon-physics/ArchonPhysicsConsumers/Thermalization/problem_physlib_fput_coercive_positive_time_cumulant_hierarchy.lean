import ArchonPhysics.PhyslibFPUTCoercivePositiveTimeCumulantHierarchy

/-!
# Consumer: full coercive alpha-beta positive-time cumulant hierarchy

This consumer checks that the arbitrary-order positive-time hierarchy uses
the frozen v0.3 potential with its stabilizing quartic term, rather than the
noncoercive `beta = 0` truncation.  It also exercises the theorem constructing
actual two-sided global Physlib trajectories from arbitrary finite families
of reduced initial states.

These are exact Hamiltonian and cumulant identities.  They do not assert
kinetic-scale cumulant decay or thermalization.
-/

namespace ArchonPhysicsConsumers.Thermalization

open ArchonPhysics
open ArchonPhysics.CoerciveHamiltonianContinuation
open ArchonPhysics.CoerciveHamiltonianPhyslib
open ArchonPhysics.FinitePhaseMonomials
open ArchonPhysics.ModalPhaseMismatch
open ArchonPhysics.PhyslibFPUTCoercivePositiveTimeCumulantHierarchy
open ArchonPhysics.PhyslibFPUTPositiveTimeCumulantHierarchy

noncomputable section

/-- The physical full source keeps both nonlinear pieces. -/
theorem fiveSite_coercive_source_split_consumer
    (m : Lattice.PositiveMassConfig 5) (kappa beta g : Real)
    (mode : Lattice.Site 5)
    (q : Time → HilbertConfiguration 5) (time : Real) :
    physlibCoerciveRotatedSource m kappa beta g mode q time =
      ArchonPhysics.PhyslibFPUTFirstPicardDecomposition.physlibQuadraticRotatedSource
          m kappa g mode q time +
        physlibQuarticForceRotatedSource m beta g mode q time :=
  physlibCoerciveRotatedSource_eq_quadratic_add_quarticForce
    m kappa beta g mode q time

/-- One actual full alpha-beta trajectory differentiates to the full source. -/
theorem fiveSite_actual_coercive_mode_derivative_consumer
    (m : Lattice.PositiveMassConfig 5) (kappa beta g : Real)
    (mode : Lattice.Site 5)
    (p q : Time → HilbertConfiguration 5)
    (hp : Differentiable Real p) (hq : Differentiable Real q)
    (hHamilton : SatisfiesHamiltonEquations m kappa beta g p q)
    (homega : 0 < modeFrequency m mode) (time : Real) :
    HasDerivAt (physlibInteractionModePath m mode p q)
      (physlibCoerciveRotatedSource m kappa beta g mode q time) time :=
  hasDerivAt_physlibInteractionModePath_coercive
    m kappa beta g mode p q hp hq hHamilton homega time

/-- Arbitrary finite-order connected cumulants of actual full alpha-beta
trajectories obey the exact one-slot source-insertion hierarchy. -/
theorem fiveSite_actual_coercive_cumulant_hierarchy_consumer
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
    (time : Real) :
    HasDerivAt
      (fun s ↦ actualFiniteCubicEnsembleConnectedCumulant
        weight mass entry p q s)
      (actualFiniteCoerciveEnsembleConnectedCumulantHierarchySource
        weight mass kappa beta g entry p q time) time :=
  hasDerivAt_actualFiniteCoerciveEnsembleConnectedCumulant
    weight mass kappa beta g entry p q hp hq hHamilton homega time

/-- Frozen coercivity constructs genuine two-sided global trajectories and
therefore removes a supplied-flow assumption from the finite-ensemble
hierarchy. -/
theorem fiveSite_exists_global_coercive_cumulant_hierarchy_consumer
    {Omega I : Type*}
    [Fintype Omega]
    [Fintype I] [DecidableEq I] [Nonempty I]
    (weight : Omega → Real)
    (mass : Omega → Lattice.PositiveMassConfig 5)
    {kappa beta : Real} (hbeta : 2 * kappa ^ 2 / 9 < beta)
    (g : Real)
    (initial : ∀ omega, ReducedPhaseSpace (mass omega))
    (entry : I → PhaseSign × Lattice.Site 5)
    (homega : ∀ omega i,
      0 < modeFrequency (mass omega) (entry i).2) :
    ∃ p q : Omega → Time → HilbertConfiguration 5,
      (∀ omega, Differentiable Real (p omega)) ∧
      (∀ omega, Differentiable Real (q omega)) ∧
      (∀ omega, p omega 0 =
        ((initial omega).2 : HilbertConfiguration 5)) ∧
      (∀ omega, q omega 0 =
        ((initial omega).1 : HilbertConfiguration 5)) ∧
      (∀ omega, SatisfiesHamiltonEquations (mass omega) kappa beta g
        (p omega) (q omega)) ∧
      ∀ time : Real,
        HasDerivAt
          (fun s ↦ actualFiniteCubicEnsembleConnectedCumulant
            weight mass entry p q s)
          (actualFiniteCoerciveEnsembleConnectedCumulantHierarchySource
            weight mass kappa beta g entry p q time) time :=
  exists_global_actualFiniteCoerciveEnsembleCumulantHierarchy
    weight mass hbeta g initial entry homega

#print axioms fiveSite_coercive_source_split_consumer
#print axioms fiveSite_actual_coercive_mode_derivative_consumer
#print axioms fiveSite_actual_coercive_cumulant_hierarchy_consumer
#print axioms fiveSite_exists_global_coercive_cumulant_hierarchy_consumer

end

end ArchonPhysicsConsumers.Thermalization
