import ArchonPhysics.DependentVolumeActualA2AlmostEverywhereJacobianThermodynamicDiagonal

namespace ArchonPhysicsConsumers.Thermalization

open ArchonPhysics
open ArchonPhysics.ActualTwoMassSpectralChart
open ArchonPhysics.DependentVolumeActualA2AlmostEverywhereJacobianThermodynamicDiagonal
open ArchonPhysics.DependentVolumeActualA2FamilyKineticAccumulation
open ArchonPhysics.DependentVolumeActualA2SignedQualitativeDiagonal
open ArchonPhysics.IIDMassPairFiniteVolumeReconstruction
open ArchonPhysics.IIDMassTripleFiniteEnvironment
open ArchonPhysics.MeasurableOrderedSpectrum
open ArchonPhysics.OrderedSingleModeProjector
open ArchonPhysics.PhyslibFPUTIteratedA2PairFiberAlgebraicBadSet
open ArchonPhysics.PhyslibFPUTIteratedA2PairFiberTransversalityAtlas
open ArchonPhysics.PhyslibFPUTIteratedQuadraticSecondPicardCharacterFamily
open ArchonPhysics.RandomEnsemble
open ArchonPhysics.TwoParameterSpectralAveragingAtlas
open ArchonPhysics.TwoParameterSpectralPolynomialAvoidance
open Filter MeasureTheory Set
open scoped Topology

noncomputable section

/-- Consumer-facing thermodynamic diagonal with a separately selected pair
and almost-everywhere frozen-rest Jacobian eliminant at every volume. -/
theorem problem_dependent_volume_actual_a2_ae_jacobian_thermodynamic_diagonal
    {Omega : Type*} [MeasurableSpace Omega]
    (ensemble : IIDMassPhaseEnsemble Omega)
    (datum : Nat → DependentActualA2ChannelDatum Omega)
    (hvolume : Tendsto (fun n => (datum n).N) atTop atTop)
    (hN : ∀ n, 2 ≤ (datum n).N)
    (site₁ site₂ : ∀ n, Lattice.Site (datum n).N)
    (hsite : ∀ n, site₁ n ≠ site₂ n)
    (R : Nat → Real) (hR : ∀ n, 0 ≤ R n)
    (hradiusMeasurable : ∀ n mode,
      Measurable fun sample => (datum n).radius sample mode)
    (hradiusBound : ∀ n sample mode,
      |(datum n).radius sample mode| ≤ R n)
    (jacobianPolynomial : ∀ n,
      FrozenPairJacobianPolynomial (datum n) (site₁ n) (site₂ n))
    (hjacobianPolynomial : ∀ n,
      JacobianPolynomialNonzeroAE
        (datum n) (site₁ n) (site₂ n) (jacobianPolynomial n))
    (hjacobianZero : ∀ n,
      JacobianZeroImpliesPolynomialZeroAE
        (datum n) (site₁ n) (site₂ n) (jacobianPolynomial n))
    (havoid : ∀ n, ChannelAvoidsAcoustic (datum n)) :
    ∃ coupling : Nat → Real,
      (∀ n, 0 < coupling n) ∧
      Tendsto (fun n => (datum n).N) atTop atTop ∧
      Tendsto coupling atTop (nhds 0) ∧
      Tendsto
        (fun n => signedExternalWeakCouplingAccumulation
          (datum n) ensemble (coupling n))
        atTop (nhds 0) := by
  exact
    exists_positive_thermodynamic_diagonal_of_ae_frozenPair_jacobian
      ensemble datum hvolume hN site₁ site₂ hsite R hR
        hradiusMeasurable hradiusBound jacobianPolynomial
        hjacobianPolynomial hjacobianZero havoid

#print axioms
  tendsto_signedExternalWeakCouplingAccumulation_of_ae_frozenPair_jacobian
#print axioms
  exists_positive_thermodynamic_diagonal_of_ae_frozenPair_jacobian
#print axioms
  problem_dependent_volume_actual_a2_ae_jacobian_thermodynamic_diagonal

end

end ArchonPhysicsConsumers.Thermalization
