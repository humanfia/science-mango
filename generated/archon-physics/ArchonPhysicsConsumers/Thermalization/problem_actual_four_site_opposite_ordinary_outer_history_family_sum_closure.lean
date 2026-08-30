import ArchonPhysics.ActualFourSiteOppositeOrdinaryOuterHistoryFamilySumClosure

namespace ArchonPhysicsConsumers.Thermalization

open ArchonPhysics
open ArchonPhysics.ActualFourSiteOppositeOrdinaryOuterHistoryFamilySumClosure
open ArchonPhysics.CanonicalIIDCoerciveIteratedA2SignedGroundedQualitativeKineticClosure
open ArchonPhysics.FourSiteOppositeSingleFrequencyOuterHistory
open ArchonPhysics.ModalPhaseMismatch
open ArchonPhysics.PhyslibFPUTIteratedA2AnnealedMismatchDomination
open ArchonPhysics.PhyslibFPUTIteratedA2PairFiberAlgebraicBadSet
open ArchonPhysics.PhyslibFPUTIteratedA2PairFiberTransversalityAtlas
open ArchonPhysics.PhyslibFPUTIteratedQuadraticSecondPicardCharacterFamily
open ArchonPhysics.RandomEnsemble
open Filter MeasureTheory Set
open scoped BigOperators Topology

noncomputable section

/-! The constructor is an injective four-member family of raw histories. -/

example : Fintype.card FourSiteOppositeOrdinaryOuterHistoryIndex = 4 := by
  exact card_fourSiteOppositeOrdinaryOuterHistoryIndex

example : Function.Injective fourSiteOppositeOrdinaryOuterHistoryTerm :=
  fourSiteOppositeOrdinaryOuterHistoryTerm_injective

example :
    fourSiteOppositeOrdinaryOuterHistoryTerm
        ((0 : Fin 2), (0 : Fin 2)) ≠
      fourSiteOppositeOrdinaryOuterHistoryTerm
        ((1 : Fin 2), (1 : Fin 2)) := by
  apply fourSiteOppositeOrdinaryOuterHistoryTerm_injective.ne
  norm_num

/-! The two branches realize the two nonzero signs of the same ordered
positive frequency. -/

example (m : Lattice.PositiveMassConfig 4) :
    iteratedQuadraticOuterMismatch m firstPositivePhysicalModeFour
        (fourSiteOppositeOrdinaryOuterHistoryTerm
          ((0 : Fin 2), (0 : Fin 2))) =
      -modeFrequency m secondPositivePhysicalModeFour := by
  rw [fourSiteOppositeOrdinaryOuterHistory_outerMismatch_eq]
  norm_num

example (m : Lattice.PositiveMassConfig 4) :
    iteratedQuadraticOuterMismatch m firstPositivePhysicalModeFour
        (fourSiteOppositeOrdinaryOuterHistoryTerm
          ((1 : Fin 2), (1 : Fin 2))) =
      modeFrequency m secondPositivePhysicalModeFour := by
  rw [fourSiteOppositeOrdinaryOuterHistory_outerMismatch_eq]
  norm_num

example (index : FourSiteOppositeOrdinaryOuterHistoryIndex) :
    IteratedA2ChannelAvoidsAcoustic .outer
      firstPositivePhysicalModeFour
      (fourSiteOppositeOrdinaryOuterHistoryTerm index) :=
  fourSiteOppositeOrdinaryOuterHistory_avoidsAcoustic index

/-! Each family member has a full-iid absolutely continuous mismatch law
and a signed fixed-volume endpoint. -/

example {Omega : Type*} [MeasurableSpace Omega]
    (ensemble : IIDMassPhaseEnsemble Omega)
    (index : FourSiteOppositeOrdinaryOuterHistoryIndex) :
    physlibIteratedA2MismatchLaw ensemble .outer
        firstPositivePhysicalModeFour
        (fourSiteOppositeOrdinaryOuterHistoryTerm index) ≪
      (volume : Measure Real) :=
  actualFourSiteOppositeOrdinaryOuterHistoryMismatchLaw_absolutelyContinuous
    ensemble index

example {Omega : Type*} [MeasurableSpace Omega]
    (ensemble : IIDMassPhaseEnsemble Omega)
    (index : FourSiteOppositeOrdinaryOuterHistoryIndex)
    (kappa R : Real) (hR : 0 ≤ R)
    (radius : Omega → Lattice.Site 4 → Real)
    (hradiusMeasurable : ∀ mode,
      Measurable fun sample => radius sample mode)
    (hradiusBound : ∀ sample mode, |radius sample mode| ≤ R) :
    Tendsto
      (actualSignedIteratedA2StaticExternalWeakCouplingAccumulation ensemble
        .outer kappa radius firstPositivePhysicalModeFour
        (fourSiteOppositeOrdinaryOuterHistoryTerm index))
      (nhdsWithin 0 (Ioi 0)) (nhds 0) :=
  tendsto_actualFourSiteOppositeOrdinaryOuterHistorySignedWeakCoupling
    ensemble index kappa R hR radius hradiusMeasurable hradiusBound

/-! The aggregate is exactly the finite sum of the four displayed per-history
norm accumulations, not a cancellation-aware complex-amplitude sum and not a
sum over every A2 history.  The raw histories are distinct, while the mismatch
maps are the two signs of the same frequency, each counted with slot
multiplicity. -/

example {Omega : Type*} [MeasurableSpace Omega]
    (ensemble : IIDMassPhaseEnsemble Omega)
    (kappa : Real) (radius : Omega → Lattice.Site 4 → Real)
    (g : Real) :
    actualFourSiteOppositeOrdinaryOuterHistoryFamilySignedWeakCouplingAccumulation
        ensemble kappa radius g =
      ∑ index : Fin 2 × Fin 2,
        actualSignedIteratedA2StaticExternalWeakCouplingAccumulation ensemble
          .outer kappa radius firstPositivePhysicalModeFour
          (fourSiteOppositeOrdinaryOuterHistoryTerm index) g := rfl

example {Omega : Type*} [MeasurableSpace Omega]
    (ensemble : IIDMassPhaseEnsemble Omega)
    (kappa R : Real) (hR : 0 ≤ R)
    (radius : Omega → Lattice.Site 4 → Real)
    (hradiusMeasurable : ∀ mode,
      Measurable fun sample => radius sample mode)
    (hradiusBound : ∀ sample mode, |radius sample mode| ≤ R) :
    Tendsto
      (actualFourSiteOppositeOrdinaryOuterHistoryFamilySignedWeakCouplingAccumulation
        ensemble kappa radius)
      (nhdsWithin 0 (Ioi 0)) (nhds 0) :=
  tendsto_actualFourSiteOppositeOrdinaryOuterHistoryFamilySignedWeakCoupling
    ensemble kappa R hR radius hradiusMeasurable hradiusBound

#check actualFourSiteOppositeOrdinaryOuterHistorySignedPerTerm_endToEnd
#check ActualFourSiteOppositeOrdinaryOuterHistorySignedL1FamilyCertificate
#check actualFourSiteOppositeOrdinaryOuterHistorySignedL1FamilyCertificate
#check
  actualFourSiteOppositeOrdinaryOuterHistoryFamilySignedFixedVolume_endToEnd

#print axioms fourSiteOppositeOrdinaryOuterHistory_outerMismatch_eq
#print axioms fourSiteOppositeOrdinaryOuterHistory_avoidsAcoustic
#print axioms
  actualFourSiteOppositeOrdinaryOuterHistoryMismatchLaw_absolutelyContinuous
#print axioms actualFourSiteOppositeOrdinaryOuterHistorySignedPerTerm_endToEnd
#print axioms
  tendsto_actualFourSiteOppositeOrdinaryOuterHistoryFamilySignedWeakCoupling
#print axioms
  actualFourSiteOppositeOrdinaryOuterHistoryFamilySignedFixedVolume_endToEnd

end

end ArchonPhysicsConsumers.Thermalization
