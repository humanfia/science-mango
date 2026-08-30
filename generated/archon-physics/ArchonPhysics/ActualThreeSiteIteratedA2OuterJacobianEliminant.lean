import ArchonPhysics.ActualTwoMassSpectralJacobianPolynomial
import ArchonPhysics.HarmonicNormalizedEdgeFrame
import ArchonPhysics.PhyslibFPUTIteratedA2PairFiberAlgebraicBadSet

/-!
# An explicit actual A2 Jacobian eliminant on the three-site chain

This file closes one nontrivial finite-volume instance of the remaining
iterated-`A2` Jacobian-elimination obligation.  On the genuine three-site
random-mass harmonic chain, a concrete ordinary outer history has mismatch
exactly the negative second positive ordered frequency.  Differentiating its
explicit characteristic quadratic in the second raw mass shows

`vertical Jacobian = 0  ->  m_0^{-1} - 1 = 0`.

Thus `X 0 - 1` is an explicit nonzero inverse-mass eliminant.  Together with
the already-proved nonzero repeated-root slice, this gives an actual
`IteratedA2PairAlgebraicRegularityCertificate`; no eliminant premise is added.
The result is intentionally a kernel-checked `N = 3` ordinary-channel base
case, not a claim that the arbitrary-volume eliminant has been computed.
-/

namespace ArchonPhysics.ActualThreeSiteIteratedA2OuterJacobianEliminant

open ArchonPhysics
open ArchonPhysics.ActualTwoMassSimpleEigenvalueDifferentiability
open ArchonPhysics.ActualTwoMassSpectralChart
open ArchonPhysics.ActualTwoMassSpectralJacobianPolynomial
open ArchonPhysics.HarmonicNormalizedEdgeFrame
open ArchonPhysics.MeasurableOrderedModeCoupling.Harmonic
open ArchonPhysics.MeasurableOrderedSpectrum
open ArchonPhysics.ModalPhaseMismatch
open ArchonPhysics.OrderedSingleModeProjector
open ArchonPhysics.OrderedSpectrumContinuity
open ArchonPhysics.OrderedTranslationLastMode
open ArchonPhysics.PhyslibFPUTIteratedA2PairFiberAlgebraicBadSet
open ArchonPhysics.PhyslibFPUTIteratedA2PairFiberTransversalityAtlas
open ArchonPhysics.PhyslibFPUTBinaryInteractionTreeCouples
open ArchonPhysics.PhyslibFPUTIteratedQuadraticSecondPicardCharacterFamily
open ArchonPhysics.RandomEnsemble
open ArchonPhysics.TwoParameterSpectralAveragingAtlas
open ArchonPhysics.TwoParameterSpectralPolynomialAvoidance
open Filter Set

noncomputable section

/-- Physical label of the largest positive ordered mode on three sites. -/
def firstPositivePhysicalModeThree : Lattice.Site 3 :=
  orderedIndexEquiv (0 : Fin 3)

/-- Physical label of the second positive ordered mode on three sites. -/
def secondPositivePhysicalModeThree : Lattice.Site 3 :=
  orderedIndexEquiv (1 : Fin 3)

/-- A concrete ordinary outer history.  Its observed and free legs coincide,
with the same positive phase sign, so they cancel in the outer mismatch.  The
remaining first-Picard carrier is the second positive mode. -/
def threeSiteSingleFrequencyOuterTerm :
    IteratedQuadraticSecondPicardCharacterTerm 3 :=
  (![secondPositivePhysicalModeThree, firstPositivePhysicalModeThree],
    (0, (0,
      ((![firstPositivePhysicalModeThree, firstPositivePhysicalModeThree],
          (0, 0)), 0))))

/-- The selected actual outer mismatch is definitionally one negative
positive frequency; the inner child data does not enter this channel. -/
theorem threeSiteSingleFrequency_outerMismatch_eq
    (m : Lattice.PositiveMassConfig 3) :
    iteratedQuadraticOuterMismatch m firstPositivePhysicalModeThree
        threeSiteSingleFrequencyOuterTerm =
      -modeFrequency m secondPositivePhysicalModeThree := by
  simp [iteratedQuadraticOuterMismatch, threeSiteSingleFrequencyOuterTerm,
    iteratedQuadraticFreeCharge, iteratedQuadraticFreeMode,
    iteratedQuadraticOuterModes, iteratedQuadraticFirstPicardSlot,
    iteratedQuadraticFirstPicardMode, iteratedQuadraticFreeSign,
    iteratedQuadraticInnerEntry, otherQuadraticSlot,
    chargeFrequency_binarySignedMode, phaseSignActReal]

end

end ArchonPhysics.ActualThreeSiteIteratedA2OuterJacobianEliminant
