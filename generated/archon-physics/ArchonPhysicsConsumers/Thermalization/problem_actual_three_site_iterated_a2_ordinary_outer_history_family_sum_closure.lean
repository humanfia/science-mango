import ArchonPhysics.ActualThreeSiteIteratedA2OrdinaryOuterHistoryFamilySumClosure

namespace ArchonPhysicsConsumers.Thermalization

open ArchonPhysics
open ArchonPhysics.ActualThreeSiteIteratedA2OrdinaryOuterHistoryFamily
open ArchonPhysics.ActualThreeSiteIteratedA2OrdinaryOuterHistoryFamilySumClosure
open ArchonPhysics.ActualThreeSiteIteratedA2OuterJacobianEliminant
open ArchonPhysics.CanonicalIIDCoerciveIteratedA2SignedGroundedQualitativeKineticClosure
open ArchonPhysics.RandomEnsemble
open Filter MeasureTheory Set
open scoped BigOperators Topology

noncomputable section

/-! The aggregate is literally the sum over the four `Fin 2 × Fin 2`
histories, rather than a claim about every A2 history. -/

example {Omega : Type*} [MeasurableSpace Omega]
    (ensemble : IIDMassPhaseEnsemble Omega)
    (kappa : Real) (radius : Omega → Lattice.Site 3 → Real)
    (g : Real) :
    actualThreeSiteOrdinaryOuterHistoryFamilySignedWeakCouplingAccumulation
        ensemble kappa radius g =
      ∑ index : Fin 2 × Fin 2,
        actualSignedIteratedA2StaticExternalWeakCouplingAccumulation ensemble
          .outer kappa radius firstPositivePhysicalModeThree
          (threeSiteOrdinaryOuterHistoryTerm index) g := rfl

/-! The four per-term certificates are available as one reusable family. -/

example {Omega : Type*} [MeasurableSpace Omega]
    (ensemble : IIDMassPhaseEnsemble Omega)
    (kappa R : Real) (hR : 0 ≤ R)
    (radius : Omega → Lattice.Site 3 → Real)
    (hradiusMeasurable : ∀ mode,
      Measurable fun sample => radius sample mode)
    (hradiusBound : ∀ sample mode, |radius sample mode| ≤ R) :
    ActualThreeSiteOrdinaryOuterHistorySignedL1FamilyCertificate ensemble
      kappa radius :=
  actualThreeSiteOrdinaryOuterHistorySignedL1FamilyCertificate ensemble
    kappa R hR radius hradiusMeasurable hradiusBound

/-! Consumer-facing aggregate endpoint.  Its displayed hypotheses contain no
spectrum, Jacobian, transversality, or acoustic premise. -/

example {Omega : Type*} [MeasurableSpace Omega]
    (ensemble : IIDMassPhaseEnsemble Omega)
    (kappa R : Real) (hR : 0 ≤ R)
    (radius : Omega → Lattice.Site 3 → Real)
    (hradiusMeasurable : ∀ mode,
      Measurable fun sample => radius sample mode)
    (hradiusBound : ∀ sample mode, |radius sample mode| ≤ R) :
    Tendsto
      (actualThreeSiteOrdinaryOuterHistoryFamilySignedWeakCouplingAccumulation
        ensemble kappa radius)
      (nhdsWithin 0 (Ioi 0)) (nhds 0) :=
  tendsto_actualThreeSiteOrdinaryOuterHistoryFamilySignedWeakCouplingAccumulation
    ensemble kappa R hR radius hradiusMeasurable hradiusBound

#check actualThreeSiteOrdinaryOuterHistoryFamilySignedWeakCouplingAccumulation
#check ActualThreeSiteOrdinaryOuterHistorySignedL1FamilyCertificate
#check actualThreeSiteOrdinaryOuterHistorySignedL1FamilyCertificate
#check actualThreeSiteOrdinaryOuterHistorySignedPerTerm_endToEnd
#check tendsto_actualThreeSiteOrdinaryOuterHistoryFamilySignedWeakCouplingAccumulation
#check actualThreeSiteOrdinaryOuterHistoryFamilySignedFixedVolume_endToEnd

#print axioms actualThreeSiteOrdinaryOuterHistorySignedPerTerm_endToEnd
#print axioms
  tendsto_actualThreeSiteOrdinaryOuterHistoryFamilySignedWeakCouplingAccumulation
#print axioms
  actualThreeSiteOrdinaryOuterHistoryFamilySignedFixedVolume_endToEnd

end

end ArchonPhysicsConsumers.Thermalization
