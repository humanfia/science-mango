import ArchonPhysics.ActualThreeSiteIteratedA2OrdinaryOuterHistoryFamily

namespace ArchonPhysicsConsumers.Thermalization

open ArchonPhysics
open ArchonPhysics.ActualThreeSiteIteratedA2OrdinaryOuterHistoryFamily
open ArchonPhysics.ActualThreeSiteIteratedA2OuterJacobianEliminant
open ArchonPhysics.ActualThreeSiteIteratedA2OuterJacobianFrozenFiber
open ArchonPhysics.CanonicalIIDCoerciveIteratedA2ExpectationFourierDecay
open ArchonPhysics.CanonicalIIDCoerciveIteratedA2SignedGroundedQualitativeKineticClosure
open ArchonPhysics.ModalPhaseMismatch
open ArchonPhysics.PhyslibFPUTIteratedA2PairFiberAlgebraicBadSet
open ArchonPhysics.PhyslibFPUTIteratedQuadraticSecondPicardCharacterFamily
open ArchonPhysics.RandomEnsemble
open Filter MeasureTheory Set
open scoped Topology

noncomputable section

/-! The index type really has four members, and the history constructor does
not identify any of them. -/

example : Fintype.card ThreeSiteOrdinaryOuterHistoryIndex = 4 := by
  exact card_threeSiteOrdinaryOuterHistoryIndex

example : Function.Injective threeSiteOrdinaryOuterHistoryTerm :=
  threeSiteOrdinaryOuterHistoryTerm_injective

example :
    threeSiteOrdinaryOuterHistoryTerm
        ((0 : Fin 2), (0 : Fin 2)) ≠
      threeSiteOrdinaryOuterHistoryTerm
        ((1 : Fin 2), (1 : Fin 2)) := by
  apply threeSiteOrdinaryOuterHistoryTerm_injective.ne
  norm_num

/-! Two explicit, different terms realize the two possible nonzero signs. -/

example (m : Lattice.PositiveMassConfig 3) :
    iteratedQuadraticOuterMismatch m firstPositivePhysicalModeThree
        (threeSiteOrdinaryOuterHistoryTerm
          ((0 : Fin 2), (0 : Fin 2))) =
      -modeFrequency m secondPositivePhysicalModeThree := by
  rw [threeSiteOrdinaryOuterHistory_outerMismatch_eq]
  norm_num

example (m : Lattice.PositiveMassConfig 3) :
    iteratedQuadraticOuterMismatch m firstPositivePhysicalModeThree
        (threeSiteOrdinaryOuterHistoryTerm
          ((1 : Fin 2), (1 : Fin 2))) =
      modeFrequency m secondPositivePhysicalModeThree := by
  rw [threeSiteOrdinaryOuterHistory_outerMismatch_eq]
  norm_num

example (index : ThreeSiteOrdinaryOuterHistoryIndex) :
    IteratedA2ChannelAvoidsAcoustic .outer
      firstPositivePhysicalModeThree
      (threeSiteOrdinaryOuterHistoryTerm index) :=
  threeSiteOrdinaryOuterHistory_avoidsAcoustic index

/-! The certificate factory uses the same explicit frozen-fiber polynomial
for every family member. -/

example (fixed : Lattice.PositiveMassConfig 3)
    (index : ThreeSiteOrdinaryOuterHistoryIndex) :
    IteratedA2PairAlgebraicRegularityCertificate fixed
      (0 : Lattice.Site 3) (1 : Lattice.Site 3) .outer
      firstPositivePhysicalModeThree
      (threeSiteOrdinaryOuterHistoryTerm index) :=
  frozenFiberThreeSiteOrdinaryOuterHistoryAlgebraicRegularityCertificate
    fixed index

example (fixed : Lattice.PositiveMassConfig 3)
    (index : ThreeSiteOrdinaryOuterHistoryIndex) :
    (frozenFiberThreeSiteOrdinaryOuterHistoryAlgebraicRegularityCertificate
      fixed index).jacobianPolynomial =
        frozenFiberThreeSiteOuterJacobianPolynomial fixed := rfl

/-! Consumer-level signed fixed-volume endpoint for an arbitrary member. -/

example {Omega : Type*} [MeasurableSpace Omega]
    (ensemble : IIDMassPhaseEnsemble Omega)
    (index : ThreeSiteOrdinaryOuterHistoryIndex)
    (kappa R : Real) (hR : 0 ≤ R)
    (radius : Omega → Lattice.Site 3 → Real)
    (hradiusMeasurable : ∀ mode,
      Measurable fun sample => radius sample mode)
    (hradiusBound : ∀ sample mode, |radius sample mode| ≤ R) :
    Tendsto
      (actualSignedIteratedA2StaticExternalWeakCouplingAccumulation ensemble
        .outer kappa radius firstPositivePhysicalModeThree
        (threeSiteOrdinaryOuterHistoryTerm index))
      (nhdsWithin 0 (Ioi 0)) (nhds 0) :=
  tendsto_actualThreeSiteOrdinaryOuterHistorySignedWeakCoupling ensemble
    index kappa R hR radius hradiusMeasurable hradiusBound

#print axioms outerMismatch_eq_signed_secondPositive_of_history
#print axioms threeSiteOrdinaryOuterHistoryTerm_injective
#print axioms threeSiteOrdinaryOuterHistory_outerMismatch_eq
#print axioms threeSiteOrdinaryOuterHistory_avoidsAcoustic
#print axioms threeSiteOrdinaryOuterHistory_verticalJacobian_zero_forces_polynomial_zero
#print axioms frozenFiberThreeSiteOrdinaryOuterHistoryAlgebraicRegularityCertificate
#print axioms actualThreeSiteOrdinaryOuterHistoryMismatchLaw_absolutelyContinuous
#print axioms tendsto_actualThreeSiteOrdinaryOuterHistorySignedWeakCoupling

end


end ArchonPhysicsConsumers.Thermalization
