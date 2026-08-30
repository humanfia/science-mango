import ArchonPhysics.FreeFPUTArbitraryOrderInitialHaarSelection

/-!
Consumer for the exact arbitrary-order initial Haar selection rule on
fixed-root FPUT Duhamel histories.
-/

namespace ArchonPhysicsConsumers.Thermalization

open MeasureTheory
open UnitAddTorus
open ArchonPhysics
open ArchonPhysics.FinitePhaseMonomials
open ArchonPhysics.FreeFPUTArbitraryOrderInitialHaarSelection
open ArchonPhysics.FreeFPUTBinaryTreeCatalanMomentumCounting
open ArchonPhysics.Lattice
open ArchonPhysics.PhyslibFPUTBinaryInteractionTreeCouples
open ArchonPhysics.RandomPhaseMoments

noncomputable section

theorem arbitrary_degree_initial_Haar_selection_consumer
    {Mode : Type*} [Fintype Mode] [DecidableEq Mode]
    (factors : List (SignedMode Mode)) :
    (∫ phase : UnitAddTorus Mode, unitSignedMonomial factors phase
      ∂finitePhaseHaarLaw Mode) =
      if (∀ mode, phaseMultiplicity factors mode =
          conjugateMultiplicity factors mode) then 1 else 0 :=
  integral_unitSignedMonomial_eq_multiplicitySelector factors

theorem initial_Haar_triad_selection_consumer
    {Mode : Type*} [Fintype Mode]
    (first second third : Mode) :
    (∫ phase : UnitAddTorus Mode,
      unitSignedMonomial
        [⟨first, .phase⟩, ⟨second, .phase⟩, ⟨third, .conjugate⟩]
        phase ∂finitePhaseHaarLaw Mode) = 0 :=
  integral_phase_phase_conjugate_triad_eq_zero first second third

theorem arbitrary_tree_forest_recursive_charge_consumer
    {Mode : Type*} [Fintype Mode] [DecidableEq Mode]
    (entry : SignedInteractionTree Mode)
    (forest : List (SignedInteractionTree Mode)) :
    signedInteractionForestCharge (entry :: forest) =
      phaseSignActCharge entry.1 (binaryTreePhaseCharge entry.2) +
        signedInteractionForestCharge forest :=
  signedInteractionForestCharge_cons entry forest

theorem fixed_root_raw_history_realization_order_consumer
    {N r : Nat} [NeZero N] (rootMomentum : Site N)
    (history : FixedRootRawHistoryIndex N r rootMomentum) :
    (realizeFixedRootRawHistory rootMomentum history).shape.order = r :=
  realizeFixedRootRawHistory_shape_order rootMomentum history

theorem actual_iid_fixed_root_history_selection_consumer
    {Omega : Type*} [MeasurableSpace Omega]
    (ensemble : IIDMassPhaseEnsemble Omega)
    {N r : Nat} [NeZero N] (rootMomentum : Site N)
    (forest : List (PhaseSign ×
      FixedRootRawHistoryIndex N r rootMomentum)) :
    (∫ omega,
      fixedRootRawHistoryForestMonomial rootMomentum forest
        (ensemble.restrictPhase omega)
      ∂ensemble.probability) =
      if fixedRootRawHistoryForestCharge rootMomentum forest = 0
      then 1 else 0 :=
  ensemble_fixedRootRawHistoryForestMonomial_expectation
    ensemble rootMomentum forest

theorem unmatched_fixed_root_raw_history_couple_consumer
    {N r : Nat} [NeZero N] (rootMomentum mode : Site N)
    (couple : FixedRootRawCoupleIndex N r rootMomentum)
    (hunmatched :
      binaryTreePhaseCharge
          (realizeFixedRootRawHistory rootMomentum couple.1) mode ≠
        binaryTreePhaseCharge
          (realizeFixedRootRawHistory rootMomentum couple.2) mode) :
    (∫ phase : UnitAddTorus (Site N),
      fixedRootRawHistoryCoupleCharacter rootMomentum couple phase
      ∂finitePhaseHaarLaw (Site N)) = 0 :=
  integral_fixedRootRawHistoryCoupleCharacter_eq_zero_of_charge_ne
    rootMomentum mode couple hunmatched

#print axioms arbitrary_degree_initial_Haar_selection_consumer
#print axioms initial_Haar_triad_selection_consumer
#print axioms arbitrary_tree_forest_recursive_charge_consumer
#print axioms fixed_root_raw_history_realization_order_consumer
#print axioms actual_iid_fixed_root_history_selection_consumer
#print axioms unmatched_fixed_root_raw_history_couple_consumer

end


end ArchonPhysicsConsumers.Thermalization
