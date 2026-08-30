import ArchonPhysics.ActualFourSiteOppositeSingleFrequencySignedFixedVolumeClosure

/-!
# A four-site opposite ordinary outer-history family and its finite sum

This module extends the concrete four-site opposite-pair history from one raw
term to a four-element family.  The two binary choices are the outer slot of
the first-Picard carrier and its original/conjugate coordinate branch.  Every
member has the same cancellation syntax: the observed first positive mode
cancels the free outer leg, leaving the second positive ordered frequency with
coefficient `-1` or `1`.

The exact frozen-resultant theorem for the opposite pair `0,2` therefore
applies almost everywhere to each member.  We obtain full-iid absolute
continuity, signed `L1` certificates, the fixed-volume weak-coupling limit for
each term, and the corresponding finite sum of four per-history norm
accumulations.  The four raw terms are distinct, although their mismatch maps
take only the two values `-omega_1` and `+omega_1` with slot multiplicity.  The
aggregate is therefore a nonnegative error budget, not a cancellation-aware
sum of complex amplitudes.  This is only the displayed ordinary outer-history
family, not all Hamiltonian histories and not a thermodynamic-limit theorem.
-/

namespace
  ArchonPhysics.ActualFourSiteOppositeOrdinaryOuterHistoryFamilySumClosure

open ArchonPhysics
open ArchonPhysics.ActualFourSiteOppositeSingleFrequencySignedFixedVolumeClosure
open ArchonPhysics.ActualTwoMassSpectralChart
open ArchonPhysics.CanonicalIIDCoerciveIteratedA2SignedGroundedQualitativeKineticClosure
open ArchonPhysics.FourSiteOppositeCanonicalResultantFrozenFiberAlmostEverywhere
open ArchonPhysics.FourSiteOppositeSingleFrequencyOuterHistory
open ArchonPhysics.FreeFPUTCollisionMismatchBridge
open ArchonPhysics.FreeFPUTTensorPhaseExpansion
open ArchonPhysics.IIDMassPairFiniteVolumeReconstruction
open ArchonPhysics.IIDMassTripleFiniteEnvironment
open ArchonPhysics.MeasurableOrderedModeCoupling.Harmonic
open ArchonPhysics.MeasurableOrderedSpectrum
open ArchonPhysics.ModalPhaseMismatch
open ArchonPhysics.OrderedSingleModeProjector
open ArchonPhysics.OrderedTranslationLastMode
open ArchonPhysics.PhyslibFPUTBinaryInteractionTreeCouples
open ArchonPhysics.PhyslibFPUTIteratedA2AnnealedMismatchDomination
open ArchonPhysics.PhyslibFPUTIteratedA2PairFiberAlgebraicBadSet
open ArchonPhysics.PhyslibFPUTIteratedA2PairFiberTransversalityAtlas
open ArchonPhysics.PhyslibFPUTIteratedA2SingleFrequencyCanonicalResultantClosure
open ArchonPhysics.PhyslibFPUTIteratedQuadraticSecondPicardCharacterFamily
open ArchonPhysics.RandomEnsemble
open Filter MeasureTheory Set
open scoped BigOperators Topology

noncomputable section

/-! ## Syntactic family and exact mismatch -/

/-- Projection-level cancellation condition for the four-site channel. -/
def IsFourSiteOppositeSingleFrequencyOuterHistory
    (term : IteratedQuadraticSecondPicardCharacterTerm 4) : Prop :=
  iteratedQuadraticFreeMode term = firstPositivePhysicalModeFour ∧
    iteratedQuadraticFreeSign term = 0 ∧
    iteratedQuadraticFirstPicardMode term =
      secondPositivePhysicalModeFour

/-- The surviving frequency coefficient, determined by the coordinate
branch of the first-Picard entry. -/
def fourSiteOppositeOuterHistoryMismatchSign
    (term : IteratedQuadraticSecondPicardCharacterTerm 4) : Real :=
  -firstPicardCoordinateBranchSign
    (iteratedQuadraticInnerEntry term).2

/-- The cancellation syntax leaves exactly the signed second positive
frequency. -/
theorem fourSiteOpposite_outerMismatch_eq_signedFrequency_of_history
    (m : Lattice.PositiveMassConfig 4)
    (term : IteratedQuadraticSecondPicardCharacterTerm 4)
    (hterm : IsFourSiteOppositeSingleFrequencyOuterHistory term) :
    iteratedQuadraticOuterMismatch m firstPositivePhysicalModeFour term =
      fourSiteOppositeOuterHistoryMismatchSign term *
        modeFrequency m secondPositivePhysicalModeFour := by
  rcases hterm with ⟨hfreeMode, hfreeSign, hcarrier⟩
  unfold iteratedQuadraticOuterMismatch
  unfold iteratedQuadraticFreeCharge
  rw [hfreeMode, hfreeSign, chargeFrequency_binarySignedMode, hcarrier]
  simp [fourSiteOppositeOuterHistoryMismatchSign, phaseSignActReal]

theorem fourSiteOppositeOuterHistoryMismatchSign_eq_neg_one_or_one
    (term : IteratedQuadraticSecondPicardCharacterTerm 4) :
    fourSiteOppositeOuterHistoryMismatchSign term = -1 ∨
      fourSiteOppositeOuterHistoryMismatchSign term = 1 := by
  generalize hbranch : (iteratedQuadraticInnerEntry term).2 = branch
  fin_cases branch <;>
    simp [fourSiteOppositeOuterHistoryMismatchSign, hbranch]

theorem fourSiteOppositeOuterHistoryMismatchSign_ne_zero
    (term : IteratedQuadraticSecondPicardCharacterTerm 4) :
    fourSiteOppositeOuterHistoryMismatchSign term ≠ 0 := by
  rcases fourSiteOppositeOuterHistoryMismatchSign_eq_neg_one_or_one term with
    hsign | hsign <;> rw [hsign] <;> norm_num

/-- The slot and coordinate-branch choices give four raw histories. -/
abbrev FourSiteOppositeOrdinaryOuterHistoryIndex := Fin 2 × Fin 2

/-- Put the second positive carrier in `slot` and the observed/free first
positive mode in the other outer slot. -/
def fourSiteOppositeOrdinaryOuterModes (slot : Fin 2) :
    Fin 2 → Lattice.Site 4 :=
  fun r => if r = slot then secondPositivePhysicalModeFour
    else firstPositivePhysicalModeFour

/-- Four genuine raw character terms.  At index `(0,0)` this is the original
single-frequency history. -/
def fourSiteOppositeOrdinaryOuterHistoryTerm
    (index : FourSiteOppositeOrdinaryOuterHistoryIndex) :
    IteratedQuadraticSecondPicardCharacterTerm 4 :=
  (fourSiteOppositeOrdinaryOuterModes index.1,
    (index.1, (0,
      ((![firstPositivePhysicalModeFour,
          firstPositivePhysicalModeFour], (0, 0)), index.2))))

@[simp] theorem fourSiteOppositeOrdinaryOuterHistoryTerm_firstPicardSlot
    (index : FourSiteOppositeOrdinaryOuterHistoryIndex) :
    iteratedQuadraticFirstPicardSlot
        (fourSiteOppositeOrdinaryOuterHistoryTerm index) = index.1 := rfl

@[simp] theorem fourSiteOppositeOrdinaryOuterHistoryTerm_innerBranch
    (index : FourSiteOppositeOrdinaryOuterHistoryIndex) :
    (iteratedQuadraticInnerEntry
        (fourSiteOppositeOrdinaryOuterHistoryTerm index)).2 = index.2 := rfl

theorem fourSiteOppositeOrdinaryOuterHistoryTerm_injective :
    Function.Injective fourSiteOppositeOrdinaryOuterHistoryTerm := by
  intro left right heq
  apply Prod.ext
  · simpa using congrArg iteratedQuadraticFirstPicardSlot heq
  · simpa using congrArg
      (fun term => (iteratedQuadraticInnerEntry term).2) heq

@[simp] theorem card_fourSiteOppositeOrdinaryOuterHistoryIndex :
    Fintype.card FourSiteOppositeOrdinaryOuterHistoryIndex = 4 := by
  norm_num [FourSiteOppositeOrdinaryOuterHistoryIndex]

theorem fourSiteOppositeOrdinaryOuterHistoryTerm_is_history
    (index : FourSiteOppositeOrdinaryOuterHistoryIndex) :
    IsFourSiteOppositeSingleFrequencyOuterHistory
      (fourSiteOppositeOrdinaryOuterHistoryTerm index) := by
  rcases index with ⟨slot, branch⟩
  fin_cases slot <;>
    simp [IsFourSiteOppositeSingleFrequencyOuterHistory,
      fourSiteOppositeOrdinaryOuterHistoryTerm,
      fourSiteOppositeOrdinaryOuterModes, iteratedQuadraticFreeMode,
      iteratedQuadraticFirstPicardMode, iteratedQuadraticOuterModes,
      iteratedQuadraticFirstPicardSlot, iteratedQuadraticFreeSign,
      otherQuadraticSlot]

/-- Every displayed history has mismatch `-omega_1` or `+omega_1`. -/
theorem fourSiteOppositeOrdinaryOuterHistory_outerMismatch_eq
    (m : Lattice.PositiveMassConfig 4)
    (index : FourSiteOppositeOrdinaryOuterHistoryIndex) :
    iteratedQuadraticOuterMismatch m firstPositivePhysicalModeFour
        (fourSiteOppositeOrdinaryOuterHistoryTerm index) =
      fourSiteOppositeOuterHistoryMismatchSign
          (fourSiteOppositeOrdinaryOuterHistoryTerm index) *
        modeFrequency m secondPositivePhysicalModeFour := by
  exact fourSiteOpposite_outerMismatch_eq_signedFrequency_of_history m _
    (fourSiteOppositeOrdinaryOuterHistoryTerm_is_history index)

@[simp] theorem fourSiteOppositeOrdinaryOuterHistoryMismatchSign_eq
    (index : FourSiteOppositeOrdinaryOuterHistoryIndex) :
    fourSiteOppositeOuterHistoryMismatchSign
        (fourSiteOppositeOrdinaryOuterHistoryTerm index) =
      if index.2 = 0 then -1 else 1 := by
  rcases index with ⟨slot, branch⟩
  fin_cases branch <;>
    simp [fourSiteOppositeOuterHistoryMismatchSign,
      fourSiteOppositeOrdinaryOuterHistoryTerm,
      iteratedQuadraticInnerEntry]

/-! ## Acoustic avoidance and opposite-fiber spectral identity -/

theorem fourSiteOppositeOrdinaryOuterHistory_avoidsAcoustic
    (index : FourSiteOppositeOrdinaryOuterHistoryIndex) :
    IteratedA2ChannelAvoidsAcoustic .outer
      firstPositivePhysicalModeFour
      (fourSiteOppositeOrdinaryOuterHistoryTerm index) := by
  rcases index with ⟨slot, branch⟩
  fin_cases slot
  · intro mode hmode
    simp [iteratedA2ChannelParticipatingModes,
      iteratedA2ChannelActiveTerm,
      fourSiteOppositeOrdinaryOuterHistoryTerm,
      fourSiteOppositeOrdinaryOuterModes, iteratedQuadraticFreeMode,
      iteratedQuadraticFirstPicardMode, iteratedQuadraticInnerEntry,
      iteratedQuadraticOuterModes, iteratedQuadraticFirstPicardSlot,
      iteratedQuadraticFreeSign, otherQuadraticSlot,
      quadraticCollisionModes] at hmode
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
  · intro mode hmode
    simp [iteratedA2ChannelParticipatingModes,
      iteratedA2ChannelActiveTerm,
      fourSiteOppositeOrdinaryOuterHistoryTerm,
      fourSiteOppositeOrdinaryOuterModes, iteratedQuadraticFreeMode,
      iteratedQuadraticFirstPicardMode, iteratedQuadraticInnerEntry,
      iteratedQuadraticOuterModes, iteratedQuadraticFirstPicardSlot,
      iteratedQuadraticFreeSign, otherQuadraticSlot,
      quadraticCollisionModes] at hmode
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

/-- Exact signed single-frequency chart on every frozen opposite-site
fiber. -/
theorem fourSiteOppositeOrdinaryOuterHistory_mismatchChart_eq_signedFrequency
    (fixed : Lattice.PositiveMassConfig 4)
    (index : FourSiteOppositeOrdinaryOuterHistoryIndex) :
    physlibIteratedA2PairMismatchChart fixed
        (0 : Lattice.Site 4) (2 : Lattice.Site 4) .outer
        firstPositivePhysicalModeFour
        (fourSiteOppositeOrdinaryOuterHistoryTerm index) =
      fun pair =>
        fourSiteOppositeOuterHistoryMismatchSign
            (fourSiteOppositeOrdinaryOuterHistoryTerm index) *
          orderedModeFrequency
            (twoSiteHarmonicHermitian fixed
              (0 : Lattice.Site 4) (2 : Lattice.Site 4) pair)
            fourSiteSingleFrequencyOrderedMode := by
  funext pair
  change iteratedQuadraticOuterMismatch
      (twoSiteMassConfig fixed
        (0 : Lattice.Site 4) (2 : Lattice.Site 4) pair)
      firstPositivePhysicalModeFour
      (fourSiteOppositeOrdinaryOuterHistoryTerm index) = _
  rw [fourSiteOppositeOrdinaryOuterHistory_outerMismatch_eq]
  rw [← orderedPullbackFrequency_eq_modeFrequency]
  unfold orderedPullbackFrequency
  rw [orderedIndexEquiv_symm_secondPositivePhysicalModeFour]
  rfl

theorem
    fourSiteOppositeOrdinaryOuterHistory_mismatchChart_eq_signedFrequency_ae
    (index : FourSiteOppositeOrdinaryOuterHistoryIndex) :
    ∀ᵐ rest ∂(iidFiniteMassVectorLaw
        (finiteVolumeMassPairComplement
          (0 : Lattice.Site 4) (2 : Lattice.Site 4))),
      physlibIteratedA2PairMismatchChart
          (finitePairEnvironmentPositiveMassConfig
            (0 : Lattice.Site 4) (2 : Lattice.Site 4) rest)
          (0 : Lattice.Site 4) (2 : Lattice.Site 4) .outer
          firstPositivePhysicalModeFour
          (fourSiteOppositeOrdinaryOuterHistoryTerm index) =
        fun pair =>
          fourSiteOppositeOuterHistoryMismatchSign
              (fourSiteOppositeOrdinaryOuterHistoryTerm index) *
            orderedModeFrequency
              (twoSiteHarmonicHermitian
                (finitePairEnvironmentPositiveMassConfig
                  (0 : Lattice.Site 4) (2 : Lattice.Site 4) rest)
                (0 : Lattice.Site 4) (2 : Lattice.Site 4) pair)
              fourSiteSingleFrequencyOrderedMode := by
  exact Filter.Eventually.of_forall fun rest =>
    fourSiteOppositeOrdinaryOuterHistory_mismatchChart_eq_signedFrequency
      (finitePairEnvironmentPositiveMassConfig
        (0 : Lattice.Site 4) (2 : Lattice.Site 4) rest) index

/-! ## Per-term full-iid and signed fixed-volume closure -/

theorem
    actualFourSiteOppositeOrdinaryOuterHistoryMismatchLaw_absolutelyContinuous
    {Omega : Type*} [MeasurableSpace Omega]
    (ensemble : IIDMassPhaseEnsemble Omega)
    (index : FourSiteOppositeOrdinaryOuterHistoryIndex) :
    physlibIteratedA2MismatchLaw ensemble .outer
        firstPositivePhysicalModeFour
        (fourSiteOppositeOrdinaryOuterHistoryTerm index) ≪
      (volume : Measure Real) := by
  exact
    physlibIteratedA2MismatchLaw_absolutelyContinuous_volume_of_ae_frozenPair_singleFrequencyCanonicalResultant
      ensemble (0 : Lattice.Site 4) (2 : Lattice.Site 4) (by decide)
        .outer firstPositivePhysicalModeFour
        (fourSiteOppositeOrdinaryOuterHistoryTerm index)
        fourSiteSingleFrequencyOrderedMode
        fourSiteSingleFrequencyOrderedMode_ne_last
        (fourSiteOppositeOuterHistoryMismatchSign
          (fourSiteOppositeOrdinaryOuterHistoryTerm index))
        (fourSiteOppositeOuterHistoryMismatchSign_ne_zero _)
        (fourSiteOppositeOrdinaryOuterHistory_mismatchChart_eq_signedFrequency_ae
          index)
        twoSitePositiveCharacteristicJacobianResultant_zero_two_ne_zero_ae
        (fourSiteOppositeOrdinaryOuterHistory_avoidsAcoustic index)

def actualFourSiteOppositeOrdinaryOuterHistorySignedL1Certificate
    {Omega : Type*} [MeasurableSpace Omega]
    (ensemble : IIDMassPhaseEnsemble Omega)
    (index : FourSiteOppositeOrdinaryOuterHistoryIndex)
    (kappa R : Real) (hR : 0 ≤ R)
    (radius : Omega → Lattice.Site 4 → Real)
    (hradiusMeasurable : ∀ mode,
      Measurable fun sample => radius sample mode)
    (hradiusBound : ∀ sample mode, |radius sample mode| ≤ R) :
    ActualSignedIteratedA2StaticL1FourierCertificate ensemble .outer kappa
      radius firstPositivePhysicalModeFour
      (fourSiteOppositeOrdinaryOuterHistoryTerm index) := by
  exact
    actualSignedIteratedA2StaticL1Certificate_of_mismatchLaw_absolutelyContinuous
      ensemble (by norm_num) .outer kappa R hR radius hradiusMeasurable
        hradiusBound firstPositivePhysicalModeFour
        (fourSiteOppositeOrdinaryOuterHistoryTerm index)
        (actualFourSiteOppositeOrdinaryOuterHistoryMismatchLaw_absolutelyContinuous
          ensemble index)

theorem tendsto_actualFourSiteOppositeOrdinaryOuterHistorySignedWeakCoupling
    {Omega : Type*} [MeasurableSpace Omega]
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
      (nhdsWithin 0 (Ioi 0)) (nhds 0) := by
  exact
    (singleFrequencyCanonicalResultant_signedFixedVolume_endToEnd
      ensemble (by norm_num) (0 : Lattice.Site 4) (2 : Lattice.Site 4)
        (by decide) .outer kappa R hR radius hradiusMeasurable hradiusBound
        firstPositivePhysicalModeFour
        (fourSiteOppositeOrdinaryOuterHistoryTerm index)
        fourSiteSingleFrequencyOrderedMode
        fourSiteSingleFrequencyOrderedMode_ne_last
        (fourSiteOppositeOuterHistoryMismatchSign
          (fourSiteOppositeOrdinaryOuterHistoryTerm index))
        (fourSiteOppositeOuterHistoryMismatchSign_ne_zero _)
        (fourSiteOppositeOrdinaryOuterHistory_mismatchChart_eq_signedFrequency_ae
          index)
        twoSitePositiveCharacteristicJacobianResultant_zero_two_ne_zero_ae
        (fourSiteOppositeOrdinaryOuterHistory_avoidsAcoustic index)).2

/-- Per-term package: full-iid absolute continuity, an `L1` certificate and
signed fixed-volume convergence. -/
theorem actualFourSiteOppositeOrdinaryOuterHistorySignedPerTerm_endToEnd
    {Omega : Type*} [MeasurableSpace Omega]
    (ensemble : IIDMassPhaseEnsemble Omega)
    (index : FourSiteOppositeOrdinaryOuterHistoryIndex)
    (kappa R : Real) (hR : 0 ≤ R)
    (radius : Omega → Lattice.Site 4 → Real)
    (hradiusMeasurable : ∀ mode,
      Measurable fun sample => radius sample mode)
    (hradiusBound : ∀ sample mode, |radius sample mode| ≤ R) :
    physlibIteratedA2MismatchLaw ensemble .outer
          firstPositivePhysicalModeFour
          (fourSiteOppositeOrdinaryOuterHistoryTerm index) ≪
        (volume : Measure Real) ∧
      Nonempty
        (ActualSignedIteratedA2StaticL1FourierCertificate ensemble .outer
          kappa radius firstPositivePhysicalModeFour
          (fourSiteOppositeOrdinaryOuterHistoryTerm index)) ∧
      Tendsto
        (actualSignedIteratedA2StaticExternalWeakCouplingAccumulation ensemble
          .outer kappa radius firstPositivePhysicalModeFour
          (fourSiteOppositeOrdinaryOuterHistoryTerm index))
        (nhdsWithin 0 (Ioi 0)) (nhds 0) := by
  exact
    ⟨actualFourSiteOppositeOrdinaryOuterHistoryMismatchLaw_absolutelyContinuous
        ensemble index,
      ⟨actualFourSiteOppositeOrdinaryOuterHistorySignedL1Certificate
        ensemble index kappa R hR radius hradiusMeasurable hradiusBound⟩,
      tendsto_actualFourSiteOppositeOrdinaryOuterHistorySignedWeakCoupling
        ensemble index kappa R hR radius hradiusMeasurable hradiusBound⟩

/-! ## Four-term aggregate -/

def actualFourSiteOppositeOrdinaryOuterHistoryFamilySignedWeakCouplingAccumulation
    {Omega : Type*} [MeasurableSpace Omega]
    (ensemble : IIDMassPhaseEnsemble Omega)
    (kappa : Real) (radius : Omega → Lattice.Site 4 → Real)
    (g : Real) : Real :=
  ∑ index : FourSiteOppositeOrdinaryOuterHistoryIndex,
    actualSignedIteratedA2StaticExternalWeakCouplingAccumulation ensemble
      .outer kappa radius firstPositivePhysicalModeFour
      (fourSiteOppositeOrdinaryOuterHistoryTerm index) g

abbrev ActualFourSiteOppositeOrdinaryOuterHistorySignedL1FamilyCertificate
    {Omega : Type*} [MeasurableSpace Omega]
    (ensemble : IIDMassPhaseEnsemble Omega)
    (kappa : Real) (radius : Omega → Lattice.Site 4 → Real) :=
  ∀ index : FourSiteOppositeOrdinaryOuterHistoryIndex,
    ActualSignedIteratedA2StaticL1FourierCertificate ensemble .outer kappa
      radius firstPositivePhysicalModeFour
      (fourSiteOppositeOrdinaryOuterHistoryTerm index)

def actualFourSiteOppositeOrdinaryOuterHistorySignedL1FamilyCertificate
    {Omega : Type*} [MeasurableSpace Omega]
    (ensemble : IIDMassPhaseEnsemble Omega)
    (kappa R : Real) (hR : 0 ≤ R)
    (radius : Omega → Lattice.Site 4 → Real)
    (hradiusMeasurable : ∀ mode,
      Measurable fun sample => radius sample mode)
    (hradiusBound : ∀ sample mode, |radius sample mode| ≤ R) :
    ActualFourSiteOppositeOrdinaryOuterHistorySignedL1FamilyCertificate
      ensemble kappa radius :=
  fun index =>
    actualFourSiteOppositeOrdinaryOuterHistorySignedL1Certificate ensemble
      index kappa R hR radius hradiusMeasurable hradiusBound

theorem
    tendsto_actualFourSiteOppositeOrdinaryOuterHistoryFamilySignedWeakCoupling
    {Omega : Type*} [MeasurableSpace Omega]
    (ensemble : IIDMassPhaseEnsemble Omega)
    (kappa R : Real) (hR : 0 ≤ R)
    (radius : Omega → Lattice.Site 4 → Real)
    (hradiusMeasurable : ∀ mode,
      Measurable fun sample => radius sample mode)
    (hradiusBound : ∀ sample mode, |radius sample mode| ≤ R) :
    Tendsto
      (actualFourSiteOppositeOrdinaryOuterHistoryFamilySignedWeakCouplingAccumulation
        ensemble kappa radius)
      (nhdsWithin 0 (Ioi 0)) (nhds 0) := by
  unfold
    actualFourSiteOppositeOrdinaryOuterHistoryFamilySignedWeakCouplingAccumulation
  simpa using
    tendsto_finsetSum Finset.univ (fun index _hindex =>
      tendsto_actualFourSiteOppositeOrdinaryOuterHistorySignedWeakCoupling
        ensemble index kappa R hR radius hradiusMeasurable hradiusBound)

/-- Aggregate endpoint for exactly the four displayed histories.  Its second
component concerns the sum of the four per-history norm accumulations, not the
norm of a signed complex-amplitude sum. -/
theorem
    actualFourSiteOppositeOrdinaryOuterHistoryFamilySignedFixedVolume_endToEnd
    {Omega : Type*} [MeasurableSpace Omega]
    (ensemble : IIDMassPhaseEnsemble Omega)
    (kappa R : Real) (hR : 0 ≤ R)
    (radius : Omega → Lattice.Site 4 → Real)
    (hradiusMeasurable : ∀ mode,
      Measurable fun sample => radius sample mode)
    (hradiusBound : ∀ sample mode, |radius sample mode| ≤ R) :
    Nonempty
        (ActualFourSiteOppositeOrdinaryOuterHistorySignedL1FamilyCertificate
          ensemble kappa radius) ∧
      Tendsto
        (actualFourSiteOppositeOrdinaryOuterHistoryFamilySignedWeakCouplingAccumulation
          ensemble kappa radius)
        (nhdsWithin 0 (Ioi 0)) (nhds 0) := by
  exact
    ⟨⟨actualFourSiteOppositeOrdinaryOuterHistorySignedL1FamilyCertificate
        ensemble kappa R hR radius hradiusMeasurable hradiusBound⟩,
      tendsto_actualFourSiteOppositeOrdinaryOuterHistoryFamilySignedWeakCoupling
        ensemble kappa R hR radius hradiusMeasurable hradiusBound⟩

end

end
  ArchonPhysics.ActualFourSiteOppositeOrdinaryOuterHistoryFamilySumClosure
