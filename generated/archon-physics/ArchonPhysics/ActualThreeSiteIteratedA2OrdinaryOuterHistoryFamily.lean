import ArchonPhysics.ActualThreeSiteIteratedA2OuterAlgebraicCertificate
import ArchonPhysics.PhyslibFPUTIteratedA2JacobianOnlySignedClosure

/-!
# A nontrivial ordinary outer-history family on three sites

This file enlarges the single concrete outer history used by the explicit
three-site Jacobian calculation to a four-element family.  The two independent
binary choices are the outer slot occupied by the first-Picard coordinate and
the original/conjugate branch of that coordinate.

The family is selected by a directly checkable syntactic cancellation
condition: the free outer leg is the observed first positive mode with positive
phase sign, while the first-Picard carrier is the second positive mode.  For
every term satisfying this condition, the actual outer mismatch is exactly
`-branchSign * omega_2`, hence has coefficient `-1` or `1`.  The four constructed
terms also use only the two positive modes in their inner children, so each
avoids the deterministic acoustic mode.

Consequently the already computed frozen-fiber eliminant `X 0 - C z` applies
to every member.  The result is a certificate factory and a signed
fixed-volume weak-coupling endpoint for this explicit family.  No assertion is
made about outer histories outside the displayed syntactic class.
-/

namespace ArchonPhysics.ActualThreeSiteIteratedA2OrdinaryOuterHistoryFamily

open ArchonPhysics
open ArchonPhysics.ActualThreeSiteIteratedA2OuterAlgebraicCertificate
open ArchonPhysics.ActualThreeSiteIteratedA2OuterJacobianEliminant
open ArchonPhysics.ActualThreeSiteIteratedA2OuterJacobianFrozenFiber
open ArchonPhysics.ActualTwoMassSpectralChart
open ArchonPhysics.CanonicalIIDCoerciveIteratedA2ExpectationFourierDecay
open ArchonPhysics.CanonicalIIDCoerciveIteratedA2SignedGroundedQualitativeKineticClosure
open ArchonPhysics.FreeFPUTCollisionMismatchBridge
open ArchonPhysics.FreeFPUTTensorPhaseExpansion
open ArchonPhysics.IIDMassPairFiniteVolumeReconstruction
open ArchonPhysics.IIDMassTripleFiniteEnvironment
open ArchonPhysics.MeasurableOrderedModeCoupling.Harmonic
open ArchonPhysics.MeasurableOrderedSpectrum
open ArchonPhysics.OrderedSingleModeProjector
open ArchonPhysics.OrderedSpectrumContinuity
open ArchonPhysics.OrderedTranslationLastMode
open ArchonPhysics.ModalPhaseMismatch
open ArchonPhysics.PhyslibFPUTBinaryInteractionTreeCouples
open ArchonPhysics.PhyslibFPUTIteratedA2AnnealedMismatchDomination
open ArchonPhysics.PhyslibFPUTIteratedA2CountableLocalAbsoluteContinuity
open ArchonPhysics.PhyslibFPUTIteratedA2JacobianOnlySignedClosure
open ArchonPhysics.PhyslibFPUTIteratedA2PairFiberAlgebraicBadSet
open ArchonPhysics.PhyslibFPUTIteratedA2PairFiberSpectrumNonvanishing
open ArchonPhysics.PhyslibFPUTIteratedA2PairFiberTransversalityAtlas
open ArchonPhysics.PhyslibFPUTIteratedQuadraticSecondPicardCharacterFamily
open ArchonPhysics.RandomEnsemble
open ArchonPhysics.TwoParameterSpectralAveragingAtlas
open ArchonPhysics.TwoParameterSpectralPolynomialAvoidance
open Filter MeasureTheory Set
open scoped Topology

noncomputable section

/-! ## Syntactic cancellation and its semantic mismatch identity -/

/-- Direct projection-level condition forcing cancellation of the observed
frequency against the free outer leg.  It does not mention the mismatch or a
Jacobian. -/
def IsThreeSiteSingleFrequencyOuterHistory
    (term : IteratedQuadraticSecondPicardCharacterTerm 3) : Prop :=
  iteratedQuadraticFreeMode term = firstPositivePhysicalModeThree ∧
    iteratedQuadraticFreeSign term = 0 ∧
    iteratedQuadraticFirstPicardMode term =
      secondPositivePhysicalModeThree

/-- The explicit coefficient of the surviving second-positive frequency. -/
def threeSiteOuterHistoryMismatchSign
    (term : IteratedQuadraticSecondPicardCharacterTerm 3) : Real :=
  -firstPicardCoordinateBranchSign
    (iteratedQuadraticInnerEntry term).2

/-- Every syntactically selected history has exactly one surviving frequency.
The proof expands the actual outer mismatch and the signed free-leg charge. -/
theorem outerMismatch_eq_signed_secondPositive_of_history
    (m : Lattice.PositiveMassConfig 3)
    (term : IteratedQuadraticSecondPicardCharacterTerm 3)
    (hterm : IsThreeSiteSingleFrequencyOuterHistory term) :
    iteratedQuadraticOuterMismatch m firstPositivePhysicalModeThree term =
      threeSiteOuterHistoryMismatchSign term *
        modeFrequency m secondPositivePhysicalModeThree := by
  rcases hterm with ⟨hfreeMode, hfreeSign, hcarrier⟩
  unfold iteratedQuadraticOuterMismatch
  unfold iteratedQuadraticFreeCharge
  rw [hfreeMode, hfreeSign, chargeFrequency_binarySignedMode, hcarrier]
  simp [threeSiteOuterHistoryMismatchSign, phaseSignActReal]

/-- The surviving coefficient is literally `-1` or `1`, according to the
ordinary/conjugate coordinate branch. -/
theorem threeSiteOuterHistoryMismatchSign_eq_neg_one_or_one
    (term : IteratedQuadraticSecondPicardCharacterTerm 3) :
    threeSiteOuterHistoryMismatchSign term = -1 ∨
      threeSiteOuterHistoryMismatchSign term = 1 := by
  generalize hbranch : (iteratedQuadraticInnerEntry term).2 = branch
  fin_cases branch <;>
    simp [threeSiteOuterHistoryMismatchSign, hbranch]

theorem threeSiteOuterHistoryMismatchSign_ne_zero
    (term : IteratedQuadraticSecondPicardCharacterTerm 3) :
    threeSiteOuterHistoryMismatchSign term ≠ 0 := by
  rcases threeSiteOuterHistoryMismatchSign_eq_neg_one_or_one term with
    hsign | hsign <;> rw [hsign] <;> norm_num

/-! ## A four-element concrete family -/

/-- The first coordinate chooses the outer first-Picard slot; the second
chooses the original/conjugate first-Picard coordinate branch. -/
abbrev ThreeSiteOrdinaryOuterHistoryIndex := Fin 2 × Fin 2

/-- Outer modes with the second positive carrier in `slot` and the observed
first positive free leg in the other slot. -/
def threeSiteOrdinaryOuterModes (slot : Fin 2) :
    Fin 2 → Lattice.Site 3 :=
  fun r => if r = slot then secondPositivePhysicalModeThree
    else firstPositivePhysicalModeThree

/-- A four-member ordinary outer-history family.  The inner children are the
two positive modes; their signs are fixed because they do not enter the outer
mismatch. -/
def threeSiteOrdinaryOuterHistoryTerm
    (index : ThreeSiteOrdinaryOuterHistoryIndex) :
    IteratedQuadraticSecondPicardCharacterTerm 3 :=
  (threeSiteOrdinaryOuterModes index.1,
    (index.1, (0,
      ((![firstPositivePhysicalModeThree,
          secondPositivePhysicalModeThree], (0, 0)), index.2))))

@[simp] theorem threeSiteOrdinaryOuterHistoryTerm_firstPicardSlot
    (index : ThreeSiteOrdinaryOuterHistoryIndex) :
    iteratedQuadraticFirstPicardSlot
        (threeSiteOrdinaryOuterHistoryTerm index) = index.1 := rfl

@[simp] theorem threeSiteOrdinaryOuterHistoryTerm_innerBranch
    (index : ThreeSiteOrdinaryOuterHistoryIndex) :
    (iteratedQuadraticInnerEntry
        (threeSiteOrdinaryOuterHistoryTerm index)).2 = index.2 := rfl

/-- Different slot/branch indices give genuinely different raw history
terms. -/
theorem threeSiteOrdinaryOuterHistoryTerm_injective :
    Function.Injective threeSiteOrdinaryOuterHistoryTerm := by
  intro left right heq
  apply Prod.ext
  · simpa using congrArg iteratedQuadraticFirstPicardSlot heq
  · simpa using congrArg
      (fun term => (iteratedQuadraticInnerEntry term).2) heq

@[simp] theorem card_threeSiteOrdinaryOuterHistoryIndex :
    Fintype.card ThreeSiteOrdinaryOuterHistoryIndex = 4 := by
  norm_num [ThreeSiteOrdinaryOuterHistoryIndex]

/-- Every one of the four constructed terms satisfies the explicit
cancellation syntax. -/
theorem threeSiteOrdinaryOuterHistoryTerm_is_history
    (index : ThreeSiteOrdinaryOuterHistoryIndex) :
    IsThreeSiteSingleFrequencyOuterHistory
      (threeSiteOrdinaryOuterHistoryTerm index) := by
  rcases index with ⟨slot, branch⟩
  fin_cases slot <;>
    simp [IsThreeSiteSingleFrequencyOuterHistory,
      threeSiteOrdinaryOuterHistoryTerm, threeSiteOrdinaryOuterModes,
      iteratedQuadraticFreeMode, iteratedQuadraticFirstPicardMode,
      iteratedQuadraticOuterModes, iteratedQuadraticFirstPicardSlot,
      iteratedQuadraticFreeSign,
      otherQuadraticSlot]

/-- Pointwise mismatch identity for the whole concrete family. -/
theorem threeSiteOrdinaryOuterHistory_outerMismatch_eq
    (m : Lattice.PositiveMassConfig 3)
    (index : ThreeSiteOrdinaryOuterHistoryIndex) :
    iteratedQuadraticOuterMismatch m firstPositivePhysicalModeThree
        (threeSiteOrdinaryOuterHistoryTerm index) =
      threeSiteOuterHistoryMismatchSign
          (threeSiteOrdinaryOuterHistoryTerm index) *
        modeFrequency m secondPositivePhysicalModeThree := by
  exact outerMismatch_eq_signed_secondPositive_of_history m _
    (threeSiteOrdinaryOuterHistoryTerm_is_history index)

@[simp] theorem threeSiteOrdinaryOuterHistoryMismatchSign_eq
    (index : ThreeSiteOrdinaryOuterHistoryIndex) :
    threeSiteOuterHistoryMismatchSign
        (threeSiteOrdinaryOuterHistoryTerm index) =
      if index.2 = 0 then -1 else 1 := by
  rcases index with ⟨slot, branch⟩
  fin_cases branch <;>
    simp [threeSiteOuterHistoryMismatchSign,
      threeSiteOrdinaryOuterHistoryTerm, iteratedQuadraticInnerEntry]

/-! ## Acoustic avoidance and transport of the explicit eliminant -/

/-- Every constructed history uses only ordered modes zero and one. -/
theorem threeSiteOrdinaryOuterHistory_avoidsAcoustic
    (index : ThreeSiteOrdinaryOuterHistoryIndex) :
    IteratedA2ChannelAvoidsAcoustic .outer
      firstPositivePhysicalModeThree
      (threeSiteOrdinaryOuterHistoryTerm index) := by
  rcases index with ⟨slot, branch⟩
  fin_cases slot
  · intro mode hmode
    simp [iteratedA2ChannelParticipatingModes,
      iteratedA2ChannelActiveTerm, threeSiteOrdinaryOuterHistoryTerm,
      threeSiteOrdinaryOuterModes, iteratedQuadraticFreeMode,
      iteratedQuadraticFirstPicardMode, iteratedQuadraticInnerEntry,
      iteratedQuadraticOuterModes, iteratedQuadraticFirstPicardSlot,
      iteratedQuadraticFreeSign, otherQuadraticSlot,
      quadraticCollisionModes] at hmode
    rcases hmode with rfl | hmode
    · rw [orderedIndexEquiv_symm_firstPositivePhysicalModeThree]
      change (0 : Fin 3) ≠ 2
      decide
    · rcases hmode with ⟨r, rfl⟩
      fin_cases r
      · change orderedIndexEquiv.symm secondPositivePhysicalModeThree ≠
          lastOrderedIndex
        rw [orderedIndexEquiv_symm_secondPositivePhysicalModeThree]
        change (1 : Fin 3) ≠ 2
        decide
      · change orderedIndexEquiv.symm firstPositivePhysicalModeThree ≠
          lastOrderedIndex
        rw [orderedIndexEquiv_symm_firstPositivePhysicalModeThree]
        change (0 : Fin 3) ≠ 2
        decide
      · change orderedIndexEquiv.symm secondPositivePhysicalModeThree ≠
          lastOrderedIndex
        rw [orderedIndexEquiv_symm_secondPositivePhysicalModeThree]
        change (1 : Fin 3) ≠ 2
        decide
  · intro mode hmode
    simp [iteratedA2ChannelParticipatingModes,
      iteratedA2ChannelActiveTerm, threeSiteOrdinaryOuterHistoryTerm,
      threeSiteOrdinaryOuterModes, iteratedQuadraticFreeMode,
      iteratedQuadraticFirstPicardMode, iteratedQuadraticInnerEntry,
      iteratedQuadraticOuterModes, iteratedQuadraticFirstPicardSlot,
      iteratedQuadraticFreeSign, otherQuadraticSlot,
      quadraticCollisionModes] at hmode
    rcases hmode with rfl | hmode
    · rw [orderedIndexEquiv_symm_firstPositivePhysicalModeThree]
      change (0 : Fin 3) ≠ 2
      decide
    · rcases hmode with ⟨r, rfl⟩
      fin_cases r
      · change orderedIndexEquiv.symm secondPositivePhysicalModeThree ≠
          lastOrderedIndex
        rw [orderedIndexEquiv_symm_secondPositivePhysicalModeThree]
        change (1 : Fin 3) ≠ 2
        decide
      · change orderedIndexEquiv.symm firstPositivePhysicalModeThree ≠
          lastOrderedIndex
        rw [orderedIndexEquiv_symm_firstPositivePhysicalModeThree]
        change (0 : Fin 3) ≠ 2
        decide
      · change orderedIndexEquiv.symm secondPositivePhysicalModeThree ≠
          lastOrderedIndex
        rw [orderedIndexEquiv_symm_secondPositivePhysicalModeThree]
        change (1 : Fin 3) ≠ 2
        decide

/-- The family chart differs from the already certified concrete chart only
by the nonzero original/conjugate branch sign. -/
theorem threeSiteOrdinaryOuterHistory_mismatchChart_eq_branch_mul_single
    (fixed : Lattice.PositiveMassConfig 3)
    (index : ThreeSiteOrdinaryOuterHistoryIndex) :
    physlibIteratedA2PairMismatchChart fixed
        (0 : Lattice.Site 3) (1 : Lattice.Site 3) .outer
        firstPositivePhysicalModeThree
        (threeSiteOrdinaryOuterHistoryTerm index) =
      fun pair => firstPicardCoordinateBranchSign index.2 *
        physlibIteratedA2PairMismatchChart fixed
          (0 : Lattice.Site 3) (1 : Lattice.Site 3) .outer
          firstPositivePhysicalModeThree
          threeSiteSingleFrequencyOuterTerm pair := by
  funext pair
  rw [show physlibIteratedA2PairMismatchChart fixed
      (0 : Lattice.Site 3) (1 : Lattice.Site 3) .outer
      firstPositivePhysicalModeThree
      (threeSiteOrdinaryOuterHistoryTerm index) pair =
        iteratedQuadraticOuterMismatch
          (frozenFiberThreeSiteMassConfig fixed pair)
          firstPositivePhysicalModeThree
          (threeSiteOrdinaryOuterHistoryTerm index) by rfl]
  rw [threeSiteOrdinaryOuterHistory_outerMismatch_eq,
    show physlibIteratedA2PairMismatchChart fixed
      (0 : Lattice.Site 3) (1 : Lattice.Site 3) .outer
      firstPositivePhysicalModeThree threeSiteSingleFrequencyOuterTerm pair =
        iteratedQuadraticOuterMismatch
          (frozenFiberThreeSiteMassConfig fixed pair)
          firstPositivePhysicalModeThree
          threeSiteSingleFrequencyOuterTerm by rfl,
    threeSiteSingleFrequency_outerMismatch_eq]
  simp [threeSiteOuterHistoryMismatchSign]

/-- Vanishing of a family-member vertical Jacobian forces vanishing for the
single history used in the explicit eliminant calculation. -/
theorem threeSiteOrdinaryOuterHistory_verticalJacobian_zero_forces_single_zero
    (fixed : Lattice.PositiveMassConfig 3)
    (index : ThreeSiteOrdinaryOuterHistoryIndex)
    (pair : Real × Real)
    (hjacobian : physlibIteratedA2PairMismatchVerticalJacobian fixed
      (0 : Lattice.Site 3) (1 : Lattice.Site 3) .outer
      firstPositivePhysicalModeThree
      (threeSiteOrdinaryOuterHistoryTerm index) pair = 0) :
    physlibIteratedA2PairMismatchVerticalJacobian fixed
      (0 : Lattice.Site 3) (1 : Lattice.Site 3) .outer
      firstPositivePhysicalModeThree threeSiteSingleFrequencyOuterTerm pair =
        0 := by
  rcases index with ⟨slot, branch⟩
  fin_cases branch
  · simpa [physlibIteratedA2PairMismatchVerticalJacobian,
      threeSiteOrdinaryOuterHistory_mismatchChart_eq_branch_mul_single]
      using hjacobian
  · have hneg :
        fderiv Real
          (fun nearby =>
            -physlibIteratedA2PairMismatchChart fixed
              (0 : Lattice.Site 3) (1 : Lattice.Site 3) .outer
              firstPositivePhysicalModeThree
              threeSiteSingleFrequencyOuterTerm nearby)
          pair (0, 1) = 0 := by
      simpa [physlibIteratedA2PairMismatchVerticalJacobian,
        threeSiteOrdinaryOuterHistory_mismatchChart_eq_branch_mul_single]
        using hjacobian
    change
      (fderiv Real
        (-physlibIteratedA2PairMismatchChart fixed
          (0 : Lattice.Site 3) (1 : Lattice.Site 3) .outer
          firstPositivePhysicalModeThree threeSiteSingleFrequencyOuterTerm)
        pair) (0, 1) = 0 at hneg
    rw [fderiv_neg, neg_apply] at hneg
    unfold physlibIteratedA2PairMismatchVerticalJacobian
    exact neg_eq_zero.mp hneg

/-- The same polynomial `X 0 - C z` eliminates every family-member vertical
Jacobian on every positive frozen fiber. -/
theorem threeSiteOrdinaryOuterHistory_verticalJacobian_zero_forces_polynomial_zero
    (fixed : Lattice.PositiveMassConfig 3)
    (index : ThreeSiteOrdinaryOuterHistoryIndex)
    (pair : Real × Real) (hpair : pair ∈ interior iidMassPairSupport)
    (hsimple : SimpleOrderedSpectrum
      (twoSiteHarmonicHermitian fixed
        (0 : Lattice.Site 3) (1 : Lattice.Site 3) pair))
    (hjacobian : physlibIteratedA2PairMismatchVerticalJacobian fixed
      (0 : Lattice.Site 3) (1 : Lattice.Site 3) .outer
      firstPositivePhysicalModeThree
      (threeSiteOrdinaryOuterHistoryTerm index) pair = 0) :
    MvPolynomial.eval (iidInverseMassPairCoordinates pair)
      (frozenFiberThreeSiteOuterJacobianPolynomial fixed) = 0 := by
  apply frozenFiberThreeSite_outerVerticalJacobian_zero_forces_polynomial_zero
    fixed pair hpair hsimple
  exact
    threeSiteOrdinaryOuterHistory_verticalJacobian_zero_forces_single_zero
      fixed index pair hjacobian

/-! ## Certificate and signed fixed-volume factories -/

/-- Complete algebraic regularity certificate for each of the four histories.
The Jacobian polynomial is definitionally the same `X 0 - C z` eliminant. -/
def frozenFiberThreeSiteOrdinaryOuterHistoryAlgebraicRegularityCertificate
    (fixed : Lattice.PositiveMassConfig 3)
    (index : ThreeSiteOrdinaryOuterHistoryIndex) :
    IteratedA2PairAlgebraicRegularityCertificate fixed
      (0 : Lattice.Site 3) (1 : Lattice.Site 3) .outer
      firstPositivePhysicalModeThree
      (threeSiteOrdinaryOuterHistoryTerm index) :=
  algebraicRegularityCertificateOfJacobian
    (site₁ := (0 : Lattice.Site 3)) (site₂ := (1 : Lattice.Site 3))
    fixed .outer firstPositivePhysicalModeThree
      (threeSiteOrdinaryOuterHistoryTerm index) (by decide)
      (frozenFiberThreeSiteOuterJacobianPolynomial fixed)
      (frozenFiberThreeSiteOuterJacobianPolynomial_ne_zero fixed)
      (threeSiteOrdinaryOuterHistory_verticalJacobian_zero_forces_polynomial_zero
        fixed index)

/-- Every family-member mismatch law is absolutely continuous under the
three-mass iid ensemble. -/
theorem actualThreeSiteOrdinaryOuterHistoryMismatchLaw_absolutelyContinuous
    {Omega : Type*} [MeasurableSpace Omega]
    (ensemble : IIDMassPhaseEnsemble Omega)
    (index : ThreeSiteOrdinaryOuterHistoryIndex) :
    physlibIteratedA2MismatchLaw ensemble .outer
        firstPositivePhysicalModeThree
        (threeSiteOrdinaryOuterHistoryTerm index) ≪
      (volume : Measure Real) := by
  apply
    physlibIteratedA2MismatchLaw_absolutelyContinuous_volume_of_frozenPair_algebraicCertificates
      ensemble (0 : Lattice.Site 3) (1 : Lattice.Site 3) (by decide)
        .outer firstPositivePhysicalModeThree
        (threeSiteOrdinaryOuterHistoryTerm index)
  · intro rest
    exact
      frozenFiberThreeSiteOrdinaryOuterHistoryAlgebraicRegularityCertificate
        (finitePairEnvironmentPositiveMassConfig
          (0 : Lattice.Site 3) (1 : Lattice.Site 3) rest) index
  · exact threeSiteOrdinaryOuterHistory_avoidsAcoustic index

/-- Signed `L1` Fourier certificate for any member of the explicit family. -/
def actualThreeSiteOrdinaryOuterHistorySignedL1Certificate
    {Omega : Type*} [MeasurableSpace Omega]
    (ensemble : IIDMassPhaseEnsemble Omega)
    (index : ThreeSiteOrdinaryOuterHistoryIndex)
    (kappa R : Real) (hR : 0 ≤ R)
    (radius : Omega → Lattice.Site 3 → Real)
    (hradiusMeasurable : ∀ mode,
      Measurable fun sample => radius sample mode)
    (hradiusBound : ∀ sample mode, |radius sample mode| ≤ R) :
    ActualSignedIteratedA2StaticL1FourierCertificate ensemble .outer kappa
      radius firstPositivePhysicalModeThree
      (threeSiteOrdinaryOuterHistoryTerm index) := by
  exact
    actualSignedIteratedA2StaticL1Certificate_of_mismatchLaw_absolutelyContinuous
      ensemble (by norm_num) .outer kappa R hR radius hradiusMeasurable
        hradiusBound firstPositivePhysicalModeThree
        (threeSiteOrdinaryOuterHistoryTerm index)
        (actualThreeSiteOrdinaryOuterHistoryMismatchLaw_absolutelyContinuous
          ensemble index)

/-- Signed fixed-volume weak-coupling conclusion, uniformly quantified over
the explicit four-element history index (with no uniform-in-volume claim). -/
theorem tendsto_actualThreeSiteOrdinaryOuterHistorySignedWeakCoupling
    {Omega : Type*} [MeasurableSpace Omega]
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
      (nhdsWithin 0 (Ioi 0)) (nhds 0) := by
  apply
    tendsto_actualSignedIteratedA2WeakCoupling_of_frozenPair_jacobianCertificates
      ensemble (by norm_num) (0 : Lattice.Site 3) (1 : Lattice.Site 3)
        (by decide) .outer kappa R hR radius hradiusMeasurable hradiusBound
        firstPositivePhysicalModeThree
        (threeSiteOrdinaryOuterHistoryTerm index)
        (fun rest => frozenFiberThreeSiteOuterJacobianPolynomial
          (finitePairEnvironmentPositiveMassConfig
            (0 : Lattice.Site 3) (1 : Lattice.Site 3) rest))
  · intro rest
    exact frozenFiberThreeSiteOuterJacobianPolynomial_ne_zero
      (finitePairEnvironmentPositiveMassConfig
        (0 : Lattice.Site 3) (1 : Lattice.Site 3) rest)
  · intro rest pair hpair hsimple hjacobian
    exact
      threeSiteOrdinaryOuterHistory_verticalJacobian_zero_forces_polynomial_zero
        (finitePairEnvironmentPositiveMassConfig
          (0 : Lattice.Site 3) (1 : Lattice.Site 3) rest)
        index pair hpair hsimple hjacobian
  · exact threeSiteOrdinaryOuterHistory_avoidsAcoustic index

end

end ArchonPhysics.ActualThreeSiteIteratedA2OrdinaryOuterHistoryFamily
