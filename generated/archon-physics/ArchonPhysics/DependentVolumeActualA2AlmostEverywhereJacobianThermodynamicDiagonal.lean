import ArchonPhysics.DependentVolumeActualA2SignedQualitativeDiagonal
import ArchonPhysics.PhyslibFPUTIteratedA2AlmostEverywhereJacobianOnlySignedClosure

/-!
# Thermodynamic signed-A2 diagonal from almost-everywhere Jacobians

For each member of a genuinely varying finite-volume family, a distinct pair
of mass coordinates is selected and the complementary masses are frozen.  An
almost-everywhere nonzero Jacobian eliminant, the implication from Jacobian
vanishing to eliminant vanishing, and acoustic-channel avoidance give the
fixed-volume signed weak-coupling limit.  The pointwise diagonal theorem then
selects positive couplings tending to zero while the volumes tend to infinity.

This is deliberately qualitative: the selection can depend on all of the
finite-volume data.  No rate uniform in volume and no prescribed relation
between coupling and volume is asserted.
-/

namespace ArchonPhysics
namespace DependentVolumeActualA2AlmostEverywhereJacobianThermodynamicDiagonal

open ArchonPhysics
open ArchonPhysics.ActualTwoMassSpectralChart
open ArchonPhysics.CanonicalIIDCoerciveIteratedA2ExpectationFourierDecay
open ArchonPhysics.DependentVolumeActualA2FamilyKineticAccumulation
open ArchonPhysics.DependentVolumeActualA2SignedQualitativeDiagonal
open ArchonPhysics.IIDMassPairFiniteVolumeReconstruction
open ArchonPhysics.IIDMassTripleFiniteEnvironment
open ArchonPhysics.MeasurableOrderedSpectrum
open ArchonPhysics.OrderedSingleModeProjector
open ArchonPhysics.PhyslibFPUTIteratedA2AlmostEverywhereJacobianOnlySignedClosure
open ArchonPhysics.PhyslibFPUTIteratedA2PairFiberAlgebraicBadSet
open ArchonPhysics.PhyslibFPUTIteratedA2PairFiberTransversalityAtlas
open ArchonPhysics.PhyslibFPUTIteratedQuadraticSecondPicardCharacterFamily
open ArchonPhysics.RandomEnsemble
open ArchonPhysics.TwoParameterSpectralAveragingAtlas
open ArchonPhysics.TwoParameterSpectralPolynomialAvoidance
open ArchonPhysics.WeakCouplingPointwiseVolumeDiagonal
open Filter MeasureTheory Set
open scoped Topology

noncomputable section

variable {Omega : Type*} [MeasurableSpace Omega]

/-- The type of a two-variable Jacobian eliminant after freezing the
complement of a selected pair in one dependent-volume datum. -/
abbrev FrozenPairJacobianPolynomial
    (datum : DependentActualA2ChannelDatum Omega)
    (site₁ site₂ : Lattice.Site datum.N) : Type :=
  letI : NeZero datum.N := datum.neZero
  FiniteMassVector (finiteVolumeMassPairComplement site₁ site₂) →
    MvPolynomial (Fin 2) Real

/-- The selected-pair eliminant is nonzero for almost every frozen
complementary mass environment. -/
def JacobianPolynomialNonzeroAE
    (datum : DependentActualA2ChannelDatum Omega)
    (site₁ site₂ : Lattice.Site datum.N)
    (jacobianPolynomial :
      FrozenPairJacobianPolynomial datum site₁ site₂) : Prop :=
  letI : NeZero datum.N := datum.neZero
  ∀ᵐ rest ∂(iidFiniteMassVectorLaw
      (finiteVolumeMassPairComplement site₁ site₂)),
    jacobianPolynomial rest ≠ 0

/-- For almost every frozen complement, every regular interior zero of the
selected-pair vertical Jacobian lies in the eliminant zero set. -/
def JacobianZeroImpliesPolynomialZeroAE
    (datum : DependentActualA2ChannelDatum Omega)
    (site₁ site₂ : Lattice.Site datum.N)
    (jacobianPolynomial :
      FrozenPairJacobianPolynomial datum site₁ site₂) : Prop :=
  letI : NeZero datum.N := datum.neZero
  ∀ᵐ rest ∂(iidFiniteMassVectorLaw
      (finiteVolumeMassPairComplement site₁ site₂)),
    ∀ pair,
      pair ∈ interior iidMassPairSupport →
      SimpleOrderedSpectrum
          (twoSiteHarmonicHermitian
            (finitePairEnvironmentPositiveMassConfig site₁ site₂ rest)
            site₁ site₂ pair) →
      physlibIteratedA2PairMismatchVerticalJacobian
          (finitePairEnvironmentPositiveMassConfig site₁ site₂ rest)
          site₁ site₂ datum.channel datum.observed datum.term pair = 0 →
      MvPolynomial.eval (iidInverseMassPairCoordinates pair)
          (jacobianPolynomial rest) = 0

/-- Acoustic-channel avoidance with the datum's positive-volume instance
restored locally. -/
def ChannelAvoidsAcoustic
    (datum : DependentActualA2ChannelDatum Omega) : Prop :=
  letI : NeZero datum.N := datum.neZero
  IteratedA2ChannelAvoidsAcoustic
    datum.channel datum.observed datum.term

/-- One dependent-volume datum has the signed fixed-volume weak-coupling
limit under its almost-everywhere frozen-pair Jacobian certificates. -/
theorem tendsto_signedExternalWeakCouplingAccumulation_of_ae_frozenPair_jacobian
    (ensemble : IIDMassPhaseEnsemble Omega)
    (datum : DependentActualA2ChannelDatum Omega)
    (hN : 2 ≤ datum.N)
    (site₁ site₂ : Lattice.Site datum.N) (hsite : site₁ ≠ site₂)
    (R : Real) (hR : 0 ≤ R)
    (hradiusMeasurable : ∀ mode,
      Measurable fun sample => datum.radius sample mode)
    (hradiusBound : ∀ sample mode, |datum.radius sample mode| ≤ R)
    (jacobianPolynomial :
      FrozenPairJacobianPolynomial datum site₁ site₂)
    (hjacobianPolynomial :
      JacobianPolynomialNonzeroAE datum site₁ site₂ jacobianPolynomial)
    (hjacobianZero :
      JacobianZeroImpliesPolynomialZeroAE
        datum site₁ site₂ jacobianPolynomial)
    (havoid : ChannelAvoidsAcoustic datum) :
    Tendsto (signedExternalWeakCouplingAccumulation datum ensemble)
      (nhdsWithin 0 (Ioi 0)) (nhds 0) := by
  let _ : NeZero datum.N := datum.neZero
  exact
    tendsto_actualSignedIteratedA2WeakCoupling_of_ae_frozenPair_jacobianCertificates
      ensemble hN site₁ site₂ hsite datum.channel datum.kappa R hR
        datum.radius hradiusMeasurable hradiusBound datum.observed datum.term
        jacobianPolynomial hjacobianPolynomial hjacobianZero havoid

/-- Honest thermodynamic diagonal for actual signed iterated `A2`.  Every
index may use its own volume, selected pair, channel, term, radii, bound, and
almost-everywhere Jacobian eliminant.  The coupling is selected only
existentially; no rate or coupling-volume relation is asserted. -/
theorem exists_positive_thermodynamic_diagonal_of_ae_frozenPair_jacobian
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
  obtain ⟨coupling, hpositive, _hupper, _herror, hcoupling, haccumulation⟩ :=
    exists_positive_diagonal_of_pointwise_nhdsGT_zero
      (fun n g =>
        signedExternalWeakCouplingAccumulation (datum n) ensemble g)
      (fun n =>
        tendsto_signedExternalWeakCouplingAccumulation_of_ae_frozenPair_jacobian
          ensemble (datum n) (hN n) (site₁ n) (site₂ n) (hsite n)
            (R n) (hR n) (hradiusMeasurable n) (hradiusBound n)
            (jacobianPolynomial n) (hjacobianPolynomial n)
            (hjacobianZero n) (havoid n))
  exact ⟨coupling, hpositive, hvolume, hcoupling, haccumulation⟩

end

end DependentVolumeActualA2AlmostEverywhereJacobianThermodynamicDiagonal
end ArchonPhysics
