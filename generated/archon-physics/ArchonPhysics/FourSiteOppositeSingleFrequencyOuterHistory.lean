import ArchonPhysics.PhyslibFPUTIteratedA2PairFiberAlgebraicBadSet

/-!
# A concrete four-site opposite-pair single-frequency outer history

On four sites, choose the first positive physical mode as both the observed
mode and the free outer leg, with the same positive phase sign.  These two
frequencies cancel in the ordinary outer mismatch.  Choose the second
positive physical mode as the first-Picard carrier.  The resulting mismatch
is exactly the negative second positive ordered frequency.

This module records only the channel syntax and its exact spectral identity.
It does not assume or prove a frozen-background resultant statement and does
not invoke an annealed or signed closure theorem.
-/

namespace ArchonPhysics.FourSiteOppositeSingleFrequencyOuterHistory

open ArchonPhysics
open ArchonPhysics.ActualTwoMassSpectralChart
open ArchonPhysics.FreeFPUTCollisionMismatchBridge
open ArchonPhysics.MeasurableOrderedModeCoupling.Harmonic
open ArchonPhysics.MeasurableOrderedSpectrum
open ArchonPhysics.ModalPhaseMismatch
open ArchonPhysics.OrderedSingleModeProjector
open ArchonPhysics.OrderedTranslationLastMode
open ArchonPhysics.PhyslibFPUTIteratedA2PairFiberAlgebraicBadSet
open ArchonPhysics.PhyslibFPUTIteratedA2PairFiberTransversalityAtlas
open ArchonPhysics.PhyslibFPUTBinaryInteractionTreeCouples
open ArchonPhysics.PhyslibFPUTIteratedQuadraticSecondPicardCharacterFamily

noncomputable section

/-- The largest positive ordered mode, transported to a physical mode label. -/
def firstPositivePhysicalModeFour : Lattice.Site 4 :=
  orderedIndexEquiv (0 : Fin (Fintype.card (Lattice.Site 4)))

/-- The ordered index of the frequency surviving in the concrete mismatch. -/
def fourSiteSingleFrequencyOrderedMode :
    Fin (Fintype.card (Lattice.Site 4)) :=
  1

/-- The second positive ordered mode, transported to a physical mode label. -/
def secondPositivePhysicalModeFour : Lattice.Site 4 :=
  orderedIndexEquiv fourSiteSingleFrequencyOrderedMode

/-- The nonzero scalar multiplying the surviving ordered frequency. -/
def fourSiteSingleFrequencyOuterSign : Real :=
  -1

/-- A concrete ordinary outer history.  Its observed and free legs coincide,
while the first-Picard carrier is the second positive mode. -/
def fourSiteSingleFrequencyOuterTerm :
    IteratedQuadraticSecondPicardCharacterTerm 4 :=
  (![secondPositivePhysicalModeFour, firstPositivePhysicalModeFour],
    (0, (0,
      ((![firstPositivePhysicalModeFour, firstPositivePhysicalModeFour],
          (0, 0)), 0))))

@[simp] theorem orderedIndexEquiv_symm_firstPositivePhysicalModeFour :
    orderedIndexEquiv.symm firstPositivePhysicalModeFour =
      (0 : Fin (Fintype.card (Lattice.Site 4))) := by
  change orderedIndexEquiv.symm
      (orderedIndexEquiv
        (0 : Fin (Fintype.card (Lattice.Site 4)))) = 0
  exact orderedIndexEquiv.symm_apply_apply _

@[simp] theorem orderedIndexEquiv_symm_secondPositivePhysicalModeFour :
    orderedIndexEquiv.symm secondPositivePhysicalModeFour =
      fourSiteSingleFrequencyOrderedMode := by
  change orderedIndexEquiv.symm
      (orderedIndexEquiv fourSiteSingleFrequencyOrderedMode) =
        fourSiteSingleFrequencyOrderedMode
  exact orderedIndexEquiv.symm_apply_apply _

/-- The selected actual outer mismatch is exactly the negative second
positive frequency.  This is a pointwise identity for every positive mass
configuration. -/
theorem fourSiteSingleFrequency_outerMismatch_eq
    (m : Lattice.PositiveMassConfig 4) :
    iteratedQuadraticOuterMismatch m firstPositivePhysicalModeFour
        fourSiteSingleFrequencyOuterTerm =
      -modeFrequency m secondPositivePhysicalModeFour := by
  simp [iteratedQuadraticOuterMismatch, fourSiteSingleFrequencyOuterTerm,
    iteratedQuadraticFreeCharge, iteratedQuadraticFreeMode,
    iteratedQuadraticOuterModes, iteratedQuadraticFirstPicardSlot,
    iteratedQuadraticFirstPicardMode, iteratedQuadraticFreeSign,
    iteratedQuadraticInnerEntry, otherQuadraticSlot,
    chargeFrequency_binarySignedMode, phaseSignActReal]

/-- On the opposite-site pair fiber `0,2`, the concrete mismatch chart is
the negative surviving ordered frequency. -/
theorem fourSiteOpposite_outerMismatchChart_eq
    (fixed : Lattice.PositiveMassConfig 4) :
    physlibIteratedA2PairMismatchChart fixed
        (0 : Lattice.Site 4) (2 : Lattice.Site 4) .outer
        firstPositivePhysicalModeFour fourSiteSingleFrequencyOuterTerm =
      fun pair => -orderedModeFrequency
        (twoSiteHarmonicHermitian fixed
          (0 : Lattice.Site 4) (2 : Lattice.Site 4) pair)
        fourSiteSingleFrequencyOrderedMode := by
  funext pair
  change iteratedQuadraticOuterMismatch
      (twoSiteMassConfig fixed
        (0 : Lattice.Site 4) (2 : Lattice.Site 4) pair)
      firstPositivePhysicalModeFour fourSiteSingleFrequencyOuterTerm = _
  rw [fourSiteSingleFrequency_outerMismatch_eq]
  rw [← orderedPullbackFrequency_eq_modeFrequency]
  unfold orderedPullbackFrequency
  rw [orderedIndexEquiv_symm_secondPositivePhysicalModeFour]
  rfl

/-- The same chart identity in the exact signed-single-frequency form used
by the canonical Jacobian interface. -/
theorem fourSiteOpposite_outerMismatchChart_eq_signedFrequency
    (fixed : Lattice.PositiveMassConfig 4) :
    physlibIteratedA2PairMismatchChart fixed
        (0 : Lattice.Site 4) (2 : Lattice.Site 4) .outer
        firstPositivePhysicalModeFour fourSiteSingleFrequencyOuterTerm =
      fun pair => fourSiteSingleFrequencyOuterSign * orderedModeFrequency
        (twoSiteHarmonicHermitian fixed
          (0 : Lattice.Site 4) (2 : Lattice.Site 4) pair)
        fourSiteSingleFrequencyOrderedMode := by
  simpa [fourSiteSingleFrequencyOuterSign] using
    fourSiteOpposite_outerMismatchChart_eq fixed

/-- The surviving coefficient is genuinely nonzero. -/
@[simp] theorem fourSiteSingleFrequencyOuterSign_ne_zero :
    fourSiteSingleFrequencyOuterSign ≠ 0 := by
  norm_num [fourSiteSingleFrequencyOuterSign]

/-- The surviving ordered mode is not the deterministic acoustic index. -/
@[simp] theorem fourSiteSingleFrequencyOrderedMode_ne_last :
    fourSiteSingleFrequencyOrderedMode ≠
      lastOrderedIndex (ι := Lattice.Site 4) := by
  change (1 : Fin 4) ≠ 3
  decide

/-- Every participating mode of the concrete ordinary outer channel avoids
the deterministic acoustic mode. -/
theorem fourSiteSingleFrequencyOuter_avoidsAcoustic :
    IteratedA2ChannelAvoidsAcoustic .outer firstPositivePhysicalModeFour
      fourSiteSingleFrequencyOuterTerm := by
  intro mode hmode
  simp [iteratedA2ChannelParticipatingModes, iteratedA2ChannelActiveTerm,
    fourSiteSingleFrequencyOuterTerm, iteratedQuadraticFreeMode,
    iteratedQuadraticFirstPicardMode, iteratedQuadraticInnerEntry,
    iteratedQuadraticOuterModes, iteratedQuadraticFirstPicardSlot,
    otherQuadraticSlot, quadraticCollisionModes] at hmode
  rcases hmode with rfl | ⟨r, rfl⟩
  · rw [orderedIndexEquiv_symm_firstPositivePhysicalModeFour]
    change (0 : Fin 4) ≠ 3
    decide
  · fin_cases r
    · change orderedIndexEquiv.symm secondPositivePhysicalModeFour ≠
          lastOrderedIndex
      rw [orderedIndexEquiv_symm_secondPositivePhysicalModeFour]
      exact fourSiteSingleFrequencyOrderedMode_ne_last
    · change orderedIndexEquiv.symm firstPositivePhysicalModeFour ≠
          lastOrderedIndex
      rw [orderedIndexEquiv_symm_firstPositivePhysicalModeFour]
      change (0 : Fin 4) ≠ 3
      decide
    · change orderedIndexEquiv.symm firstPositivePhysicalModeFour ≠
          lastOrderedIndex
      rw [orderedIndexEquiv_symm_firstPositivePhysicalModeFour]
      change (0 : Fin 4) ≠ 3
      decide

end

end ArchonPhysics.FourSiteOppositeSingleFrequencyOuterHistory
