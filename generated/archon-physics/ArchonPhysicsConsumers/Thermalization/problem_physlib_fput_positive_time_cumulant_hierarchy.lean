import ArchonPhysics.PhyslibFPUTPositiveTimeCumulantHierarchy

/-!
# Consumer: exact positive-time high-order FPUT cumulant hierarchy

This consumer exercises the arbitrary finite-order Leibniz hierarchy, its
finite weighted joint-moment and connected-cumulant forms, and the final
five-site adapter to actual random-mass cubic-leading Physlib trajectories.

The result is the exact backbone needed for a high-order decoherence proof:
at `t = 0` the imported Haar selector controls every fixed finite charge
moment, while at positive time the same Hamiltonian orbit obeys the hierarchy
below.  Nothing here says that charge-balanced or genuinely resonant
connected clusters vanish.  Nor does pairwise decoherence imply the
higher-order closure.  A kinetic-scale proof must still bound the
nonresonant, recollision/repeated-index, and exceptional connected sectors.
-/

namespace ArchonPhysicsConsumers.Thermalization

open ArchonPhysics
open ArchonPhysics.CoerciveHamiltonianPhyslib
open ArchonPhysics.FinitePhaseMonomials
open ArchonPhysics.ModalPhaseMismatch
open ArchonPhysics.PhyslibFPUTPositiveTimeCumulantHierarchy

noncomputable section

/-- Arbitrary fixed-order signed products differentiate by inserting the
supplied source in exactly one slot. -/
theorem arbitrary_fixed_order_signed_block_hierarchy_consumer
    {I : Type*} [DecidableEq I]
    (path source : I → Real → Complex)
    (block : Finset I) (time : Real)
    (hpath : ∀ i ∈ block, HasDerivAt (path i) (source i time) time) :
    HasDerivAt (fun s ↦ signedBlockMonomial path block s)
      (signedBlockSlotInsertion path source block time) time :=
  hasDerivAt_signedBlockMonomial path source block time hpath

/-- Finite weighted connected cumulants obey the exact partition/Mobius
hierarchy at arbitrary finite joint order. -/
theorem arbitrary_fixed_order_finite_weighted_cumulant_hierarchy_consumer
    {Omega I : Type*}
    [Fintype Omega] [DecidableEq Omega]
    [Fintype I] [DecidableEq I] [Nonempty I]
    (weight : Omega → Real)
    (path source : Omega → I → Real → Complex)
    (time : Real)
    (hpath : ∀ omega i,
      HasDerivAt (path omega i) (source omega i time) time) :
    HasDerivAt
      (fun s ↦ finiteWeightedConnectedCumulant weight path s)
      (finiteWeightedConnectedCumulantHierarchySource
        weight path source time) time :=
  hasDerivAt_finiteWeightedConnectedCumulant
    weight path source time hpath

/-- The source used by the physical hierarchy is definitionally the exact
quadratic part of the verified random-mass modal Hamilton equation. -/
theorem fiveSite_actual_source_is_quadratic_tensor_consumer
    (m : Lattice.PositiveMassConfig 5) (kappa g : Real)
    (mode : Lattice.Site 5)
    (q : Time → HilbertConfiguration 5) (time : Real) :
    physlibCubicLeadingQuadraticSource m kappa g mode q time =
      ArchonPhysics.PhyslibFPUTFirstPicardDecomposition.physlibQuadraticRotatedSource
        m kappa g mode q time :=
  physlibCubicLeadingQuadraticSource_eq_quadraticRotatedSource
    m kappa g mode q time

/-- Five-site actual random-mass endpoint.  Every ensemble member has its own
positive mass realization and follows the corresponding unmodified Physlib
Hamiltonian flow with `beta = 0`; the derivative is the exact partition sum
of one-slot insertions of the physical quadratic source. -/
theorem fiveSite_actual_random_mass_cubic_cumulant_hierarchy_consumer
    {Omega I : Type*}
    [Fintype Omega] [DecidableEq Omega]
    [Fintype I] [DecidableEq I] [Nonempty I]
    (weight : Omega → Real)
    (mass : Omega → Lattice.PositiveMassConfig 5)
    (kappa g : Real)
    (entry : I → PhaseSign × Lattice.Site 5)
    (p q : Omega → Time → HilbertConfiguration 5)
    (hp : ∀ omega, Differentiable Real (p omega))
    (hq : ∀ omega, Differentiable Real (q omega))
    (hHamilton : ∀ omega,
      SatisfiesHamiltonEquations (mass omega) kappa 0 g
        (p omega) (q omega))
    (homega : ∀ omega i,
      0 < modeFrequency (mass omega) (entry i).2)
    (time : Real) :
    HasDerivAt
      (fun s ↦ actualFiniteCubicEnsembleConnectedCumulant
        weight mass entry p q s)
      (actualFiniteCubicEnsembleConnectedCumulantHierarchySource
        weight mass kappa g entry p q time) time :=
  hasDerivAt_actualFiniteCubicEnsembleConnectedCumulant
    weight mass kappa g entry p q hp hq hHamilton homega time

#print axioms arbitrary_fixed_order_signed_block_hierarchy_consumer
#print axioms arbitrary_fixed_order_finite_weighted_cumulant_hierarchy_consumer
#print axioms fiveSite_actual_source_is_quadratic_tensor_consumer
#print axioms fiveSite_actual_random_mass_cubic_cumulant_hierarchy_consumer

end

end ArchonPhysicsConsumers.Thermalization
