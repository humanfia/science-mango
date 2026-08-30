import ArchonPhysics.PhyslibFPUTIteratedA2PairFiberSpectrumNonvanishing

namespace ArchonPhysicsConsumers.Thermalization

open ArchonPhysics
open ArchonPhysics.ActualTwoMassSpectralChart
open ArchonPhysics.OrderedSingleModeProjector
open ArchonPhysics.PhyslibFPUTIteratedA2PairFiberAlgebraicBadSet
open ArchonPhysics.PhyslibFPUTIteratedA2PairFiberSpectrumNonvanishing
open ArchonPhysics.TwoParameterSpectralAveragingAtlas

noncomputable section

example {N : Nat} [NeZero N] (fixed : Lattice.PositiveMassConfig N)
    {site₁ site₂ : Lattice.Site N} (hsite : site₁ ≠ site₂) :
    twoSiteRepeatedRootSlicePolynomial fixed site₁ site₂ ≠ 0 :=
  twoSiteRepeatedRootSlicePolynomial_ne_zero fixed hsite

example {N : Nat} [NeZero N] (fixed : Lattice.PositiveMassConfig N)
    {site₁ site₂ : Lattice.Site N} (hsite : site₁ ≠ site₂)
    (hwitness : ∃ pair : Real × Real,
      pair ∈ iidMassPairSupport ∧
      SimpleOrderedSpectrum
        (twoSiteHarmonicHermitian fixed site₁ site₂ pair)) :
    twoSiteRepeatedRootSlicePolynomial fixed site₁ site₂ ≠ 0 :=
  twoSiteRepeatedRootSlicePolynomial_ne_zero_of_exists_supported_simple
    fixed hsite hwitness

#print axioms weightedPath_eigenvector_zero_of_zero_cut
#print axioms weightedPath_charpoly_separable
#print axioms twoSiteRepeatedRootSlicePolynomial_ne_zero
#print axioms algebraicRegularityCertificateOfJacobian
#print axioms twoSiteRepeatedRootSlicePolynomial_ne_zero_of_exists_supported_simple

end

end ArchonPhysicsConsumers.Thermalization
