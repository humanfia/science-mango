import Mathlib.Analysis.Calculus.FDeriv.Measurable
import Mathlib.Analysis.Calculus.InverseFunctionTheorem.FDeriv
import ArchonPhysics.CanonicalIIDCoerciveIteratedA2ExpectationFourierDecay
import ArchonPhysics.FreeFPUTA0IteratedQuadraticFeedbackIdentity
import ArchonPhysics.PhyslibFPUTA1PairFiberTransversalityAtlas
import ArchonPhysics.PhyslibFPUTBinaryInteractionTreeCouples

/-!
# Actual iterated-A2 pair-fiber transversality atlas

This module gives the iterated-quadratic `A2` mismatch channels the same
honest two-mass spectral audit previously available for `A1`.  The mismatch
is evaluated on the genuine periodic random-mass harmonic spectrum.  At an
interior mass pair with simple spectrum and positive participating ordered
eigenvalues, strict differentiability is derived mode by mode from the
actual characteristic-polynomial implicit-function theorem.  It is not an
abstract differentiability premise.

For each of the five physical channels (outer, inner, total, and the two
twisted channels), a nonzero vertical derivative yields a local open,
measurable, injective one-mass patch.  Reciprocal-natural good levels and
their measurable bad complements expose exactly what remains for a global
small-ball estimate: boundary/nonsimple/nonpositive spectral points and
quantitatively small actual Jacobian.

The mismatch spectrum contains neither the fixed FPUT coefficient `kappa`
nor the external weak parameter `g`; those enter the amplitude and kinetic
time scaling, not this transversality statement.  No uniform lower bound on
the Jacobian, bad-set probability estimate, thermodynamic limit, RPA, or
recollision estimate is asserted here.  Moreover, charge-matched return trees
have an identically zero total mismatch; the exact obstruction below keeps
those trees in the resonant/feedback block rather than the injective atlas.
-/

namespace ArchonPhysics.PhyslibFPUTIteratedA2PairFiberTransversalityAtlas

open ArchonPhysics
open ArchonPhysics.ActualTwoMassSimpleEigenvalueDifferentiability
open ArchonPhysics.ActualTwoMassSpectralChart
open ArchonPhysics.CanonicalIIDCoerciveIteratedA2ExpectationFourierDecay
open ArchonPhysics.FreeFPUTA0DirectCubicBridge
open ArchonPhysics.FreeFPUTA0IteratedQuadraticFeedbackIdentity
open ArchonPhysics.FreeFPUTCollisionMismatchBridge
open ArchonPhysics.FreeFPUTMismatchPhaseExpansion
open ArchonPhysics.FreeFPUTTadpoleFeedbackCancellation
open ArchonPhysics.FrozenCollisionMassPositivity
open ArchonPhysics.MeasurableOrderedModeCoupling.Harmonic
open ArchonPhysics.MeasurableOrderedSpectrum
open ArchonPhysics.ModalPhaseMismatch
open ArchonPhysics.ModeCoupling
open ArchonPhysics.OrderedSingleModeProjector
open ArchonPhysics.OrderedSpectrumContinuity
open ArchonPhysics.PhyslibFPUTBinaryInteractionTreeCouples
open ArchonPhysics.PhyslibFPUTIteratedQuadraticSecondPicardCharacterFamily
open ArchonPhysics.PhyslibFPUTA1PairFiberTransversalityAtlas
open ArchonPhysics.RandomEnsemble
open ArchonPhysics.TwoParameterSpectralAveragingAtlas
open Filter Function MeasureTheory Set

noncomputable section

/-- The term whose modes are used by a selected mismatch channel.  A twist
changes only signs/branches, but retaining it here makes the channel algebra
definitionally transparent. -/
def iteratedA2ChannelActiveTerm {N : Nat}
    (channel : IteratedA2MismatchChannel)
    (term : IteratedQuadraticSecondPicardCharacterTerm N) :
    IteratedQuadraticSecondPicardCharacterTerm N :=
  match channel with
  | .outerTwist | .innerTwist => flipIteratedQuadraticInnerBranch term
  | _ => term

/-- A uniform finite tree-level superset of the modes needed by one selected
`A2` channel: the final observed mode, the free outer mode, and the three
signed legs of the inner quadratic mismatch.  Outer and inner channels each
retain harmless redundant modes; repetitions are removed by `Finset`.
-/
def iteratedA2ChannelParticipatingModes
    {N : Nat} [NeZero N] (channel : IteratedA2MismatchChannel)
    (observed : Lattice.Site N)
    (term : IteratedQuadraticSecondPicardCharacterTerm N) :
    Finset (Lattice.Site N) :=
  let active := iteratedA2ChannelActiveTerm channel term
  {observed, iteratedQuadraticFreeMode active} ∪
    Finset.univ.image (quadraticCollisionModes
      (iteratedQuadraticFirstPicardMode active)
      (iteratedQuadraticInnerEntry active).1)

/-- The genuine two-raw-mass chart of one actual iterated-`A2` mismatch. -/
def physlibIteratedA2PairMismatchChart
    {N : Nat} [NeZero N] (fixed : Lattice.PositiveMassConfig N)
    (site₁ site₂ : Lattice.Site N) (channel : IteratedA2MismatchChannel)
    (observed : Lattice.Site N)
    (term : IteratedQuadraticSecondPicardCharacterTerm N)
    (pair : Real × Real) : Real :=
  channel.value (twoSiteMassConfig fixed site₁ site₂ pair) observed term

/-- Total second-coordinate Jacobian of the actual `A2` mismatch chart. -/
def physlibIteratedA2PairMismatchVerticalJacobian
    {N : Nat} [NeZero N] (fixed : Lattice.PositiveMassConfig N)
    (site₁ site₂ : Lattice.Site N) (channel : IteratedA2MismatchChannel)
    (observed : Lattice.Site N)
    (term : IteratedQuadraticSecondPicardCharacterTerm N)
    (pair : Real × Real) : Real :=
  fderiv Real
    (physlibIteratedA2PairMismatchChart fixed site₁ site₂ channel observed term)
    pair (0, 1)

/-- Charge matching of a return tree makes its total mismatch identically
zero for every actual mass pair.  This is a genuine resonant obstruction,
not a small-Jacobian event to be estimated by the regular atlas. -/
theorem physlibIteratedA2TotalPairMismatchChart_eq_zero_of_chargeMatched
    {N : Nat} [NeZero N] (fixed : Lattice.PositiveMassConfig N)
    (site₁ site₂ observed : Lattice.Site N)
    (term : IteratedQuadraticSecondPicardCharacterTerm N)
    (hcharge : freeInitialPhaseCharge observed 0 =
      iteratedQuadraticSecondPicardCharge term) (pair : Real × Real) :
    physlibIteratedA2PairMismatchChart fixed site₁ site₂ .total observed term
      pair = 0 := by
  change iteratedQuadraticOuterMismatch
      (twoSiteMassConfig fixed site₁ site₂ pair) observed term +
    iteratedQuadraticInnerMismatch
      (twoSiteMassConfig fixed site₁ site₂ pair) term = 0
  rw [iteratedQuadraticOuterMismatch_eq_neg_inner_of_charge_eq_freeInitial
    _ observed term hcharge]
  ring

/-- Accordingly, the actual vertical Jacobian of a charge-matched total
channel is exactly zero everywhere. -/
theorem physlibIteratedA2TotalPairMismatchVerticalJacobian_eq_zero_of_chargeMatched
    {N : Nat} [NeZero N] (fixed : Lattice.PositiveMassConfig N)
    (site₁ site₂ observed : Lattice.Site N)
    (term : IteratedQuadraticSecondPicardCharacterTerm N)
    (hcharge : freeInitialPhaseCharge observed 0 =
      iteratedQuadraticSecondPicardCharge term) (pair : Real × Real) :
    physlibIteratedA2PairMismatchVerticalJacobian
      fixed site₁ site₂ .total observed term pair = 0 := by
  unfold physlibIteratedA2PairMismatchVerticalJacobian
  have hfun :
      physlibIteratedA2PairMismatchChart fixed site₁ site₂
          .total observed term = fun _ => 0 := by
    funext nearby
    exact physlibIteratedA2TotalPairMismatchChart_eq_zero_of_chargeMatched
      fixed site₁ site₂ observed term hcharge nearby
  rw [hfun]
  simp

/-- A charge-matched total channel cannot be injective on the nontrivial
physical one-mass support. -/
theorem not_injOn_physlibIteratedA2ChargeMatchedTotalPairFiber_massSupport
    {N : Nat} [NeZero N] (fixed : Lattice.PositiveMassConfig N)
    (site₁ site₂ observed : Lattice.Site N)
    (term : IteratedQuadraticSecondPicardCharacterTerm N)
    (hcharge : freeInitialPhaseCharge observed 0 =
      iteratedQuadraticSecondPicardCharge term) (first : Real) :
    ¬ InjOn
      (fun second => physlibIteratedA2PairMismatchChart fixed site₁ site₂
        .total observed term (first, second)) massSupport := by
  intro hinjective
  have hlower : massLower ∈ massSupport :=
    ⟨le_rfl, massLower_le_massUpper⟩
  have hupper : massUpper ∈ massSupport :=
    ⟨massLower_le_massUpper, le_rfl⟩
  have heq := hinjective hlower hupper (by
    change physlibIteratedA2PairMismatchChart fixed site₁ site₂ .total
        observed term (first, massLower) =
      physlibIteratedA2PairMismatchChart fixed site₁ site₂ .total
        observed term (first, massUpper)
    rw [physlibIteratedA2TotalPairMismatchChart_eq_zero_of_chargeMatched
      fixed site₁ site₂ observed term hcharge (first, massLower),
      physlibIteratedA2TotalPairMismatchChart_eq_zero_of_chargeMatched
        fixed site₁ site₂ observed term hcharge (first, massUpper)])
  have hne : massLower ≠ massUpper := by
    norm_num [massLower, massUpper]
  exact hne heq

/-- Exact physical differentiability source for one channel: interior
positive masses, simple actual spectrum, and positivity on the uniform finite
tree-level mode superset above.  This is sufficient and deliberately
conservative for the outer-only and inner-only channels. -/
def physlibIteratedA2PairMismatchDifferentiabilitySource
    {N : Nat} [NeZero N] (fixed : Lattice.PositiveMassConfig N)
    (site₁ site₂ : Lattice.Site N) (channel : IteratedA2MismatchChannel)
    (observed : Lattice.Site N)
    (term : IteratedQuadraticSecondPicardCharacterTerm N) :
    Set (Real × Real) :=
  {pair |
    pair ∈ interior iidMassPairSupport ∧
    SimpleOrderedSpectrum
      (twoSiteHarmonicHermitian fixed site₁ site₂ pair) ∧
    ∀ mode ∈ iteratedA2ChannelParticipatingModes channel observed term,
      0 < orderedEigenvalue
        (twoSiteHarmonicHermitian fixed site₁ site₂ pair)
        (orderedIndexEquiv.symm mode)}

/-- Public ordered-frequency differentiability, transported to the physical
site labeling and normalized to Mathlib's canonical total `fderiv`. -/
private theorem hasStrictFDerivAt_actualTwoMassModeFrequency
    {N : Nat} [NeZero N] (fixed : Lattice.PositiveMassConfig N)
    {site₁ site₂ : Lattice.Site N} (hsite : site₁ ≠ site₂)
    {pair : Real × Real} (hpair : pair ∈ interior iidMassPairSupport)
    (hsimple : SimpleOrderedSpectrum
      (twoSiteHarmonicHermitian fixed site₁ site₂ pair))
    (mode : Lattice.Site N)
    (hpositive : 0 < orderedEigenvalue
      (twoSiteHarmonicHermitian fixed site₁ site₂ pair)
        (orderedIndexEquiv.symm mode)) :
    HasStrictFDerivAt
      (fun nearby =>
        modeFrequency (twoSiteMassConfig fixed site₁ site₂ nearby) mode)
      (fderiv Real (fun nearby =>
        modeFrequency (twoSiteMassConfig fixed site₁ site₂ nearby) mode)
        pair) pair := by
  obtain ⟨derivative, hderivative⟩ :=
    exists_hasStrictFDerivAt_actualTwoMassOrderedModeFrequency
      fixed hsite hpair hsimple (orderedIndexEquiv.symm mode) hpositive
  have hphysical : HasStrictFDerivAt
      (fun nearby =>
        modeFrequency (twoSiteMassConfig fixed site₁ site₂ nearby) mode)
      derivative pair := by
    simpa [twoSiteHarmonicHermitian,
      orderedModeFrequency_harmonicHermitian_eq] using hderivative
  simpa [hphysical.hasFDerivAt.fderiv] using hphysical

private theorem hasStrictFDerivAt_iteratedQuadraticOuterMismatch
    {N : Nat} [NeZero N] (fixed : Lattice.PositiveMassConfig N)
    {site₁ site₂ : Lattice.Site N} (hsite : site₁ ≠ site₂)
    {pair : Real × Real} (hpair : pair ∈ interior iidMassPairSupport)
    (hsimple : SimpleOrderedSpectrum
      (twoSiteHarmonicHermitian fixed site₁ site₂ pair))
    (observed : Lattice.Site N)
    (term : IteratedQuadraticSecondPicardCharacterTerm N)
    (hpositive : ∀ mode ∈
      iteratedA2ChannelParticipatingModes .outer observed term,
      0 < orderedEigenvalue
        (twoSiteHarmonicHermitian fixed site₁ site₂ pair)
        (orderedIndexEquiv.symm mode)) :
    HasStrictFDerivAt
      (fun nearby => iteratedQuadraticOuterMismatch
        (twoSiteMassConfig fixed site₁ site₂ nearby) observed term)
      (fderiv Real (fun nearby => iteratedQuadraticOuterMismatch
        (twoSiteMassConfig fixed site₁ site₂ nearby) observed term) pair) pair := by
  let frequency := fun mode : Lattice.Site N => fun nearby : Real × Real =>
    modeFrequency (twoSiteMassConfig fixed site₁ site₂ nearby) mode
  have hobserved : HasStrictFDerivAt (frequency observed)
      (fderiv Real (frequency observed) pair) pair :=
    hasStrictFDerivAt_actualTwoMassModeFrequency fixed hsite hpair hsimple
      observed (hpositive observed (by
        simp [iteratedA2ChannelParticipatingModes,
          iteratedA2ChannelActiveTerm]))
  have hfree : HasStrictFDerivAt
      (frequency (iteratedQuadraticFreeMode term))
      (fderiv Real (frequency (iteratedQuadraticFreeMode term)) pair) pair :=
    hasStrictFDerivAt_actualTwoMassModeFrequency fixed hsite hpair hsimple _
      (hpositive _ (by
        simp [iteratedA2ChannelParticipatingModes,
          iteratedA2ChannelActiveTerm]))
  have hcarrier : HasStrictFDerivAt
      (frequency (iteratedQuadraticFirstPicardMode term))
      (fderiv Real (frequency (iteratedQuadraticFirstPicardMode term)) pair)
        pair :=
    hasStrictFDerivAt_actualTwoMassModeFrequency fixed hsite hpair hsimple _
      (hpositive _ (by
        simp [iteratedA2ChannelParticipatingModes,
          iteratedA2ChannelActiveTerm]
        exact Or.inr (Or.inr ⟨0, rfl⟩)))
  have hcombined :=
    (hobserved.sub
      (hfree.const_mul
        (firstPicardCoordinateBranchSign
          (iteratedQuadraticFreeSign term)))).sub
      (hcarrier.const_mul
        (firstPicardCoordinateBranchSign
          (iteratedQuadraticInnerEntry term).2))
  have hfun :
      (fun nearby => iteratedQuadraticOuterMismatch
        (twoSiteMassConfig fixed site₁ site₂ nearby) observed term) =
      (frequency observed -
        fun nearby => firstPicardCoordinateBranchSign
          (iteratedQuadraticFreeSign term) *
            frequency (iteratedQuadraticFreeMode term) nearby) -
        fun nearby => firstPicardCoordinateBranchSign
          (iteratedQuadraticInnerEntry term).2 *
            frequency (iteratedQuadraticFirstPicardMode term) nearby := by
    funext nearby
    simp [iteratedQuadraticOuterMismatch, iteratedQuadraticFreeCharge,
      chargeFrequency_binarySignedMode, phaseSignActReal_binaryPhaseSign,
      frequency]
  rw [hfun]
  simpa [hcombined.hasFDerivAt.fderiv] using hcombined

private theorem hasStrictFDerivAt_iteratedQuadraticInnerMismatch
    {N : Nat} [NeZero N] (fixed : Lattice.PositiveMassConfig N)
    {site₁ site₂ : Lattice.Site N} (hsite : site₁ ≠ site₂)
    {pair : Real × Real} (hpair : pair ∈ interior iidMassPairSupport)
    (hsimple : SimpleOrderedSpectrum
      (twoSiteHarmonicHermitian fixed site₁ site₂ pair))
    (observed : Lattice.Site N)
    (term : IteratedQuadraticSecondPicardCharacterTerm N)
    (hpositive : ∀ mode ∈
      iteratedA2ChannelParticipatingModes .inner observed term,
      0 < orderedEigenvalue
        (twoSiteHarmonicHermitian fixed site₁ site₂ pair)
        (orderedIndexEquiv.symm mode)) :
    HasStrictFDerivAt
      (fun nearby => iteratedQuadraticInnerMismatch
        (twoSiteMassConfig fixed site₁ site₂ nearby) term)
      (fderiv Real (fun nearby => iteratedQuadraticInnerMismatch
        (twoSiteMassConfig fixed site₁ site₂ nearby) term) pair) pair := by
  let innerObserved := iteratedQuadraticFirstPicardMode term
  let innerTerm := (iteratedQuadraticInnerEntry term).1
  let modeFunction := fun r : Fin 3 => fun nearby : Real × Real =>
    modeFrequency (twoSiteMassConfig fixed site₁ site₂ nearby)
      (quadraticCollisionModes innerObserved innerTerm r)
  have hmode : ∀ r, HasStrictFDerivAt (modeFunction r)
      (fderiv Real (modeFunction r) pair) pair := by
    intro r
    apply hasStrictFDerivAt_actualTwoMassModeFrequency
      fixed hsite hpair hsimple
    apply hpositive
    simp [iteratedA2ChannelParticipatingModes,
      iteratedA2ChannelActiveTerm, innerObserved, innerTerm]
  have hsum : HasStrictFDerivAt
      (fun nearby => ∑ r : Fin 3,
        (quadraticCollisionSign innerTerm r).coefficient *
          modeFunction r nearby)
      (∑ r : Fin 3, (quadraticCollisionSign innerTerm r).coefficient •
        fderiv Real (modeFunction r) pair) pair := by
    apply HasStrictFDerivAt.fun_sum
    intro r _hr
    exact (hmode r).const_mul _
  have hscaled := hsum.const_mul
    (firstPicardCoordinateBranchSign (iteratedQuadraticInnerEntry term).2)
  have hfun :
      (fun nearby => iteratedQuadraticInnerMismatch
        (twoSiteMassConfig fixed site₁ site₂ nearby) term) =
      fun nearby => firstPicardCoordinateBranchSign
        (iteratedQuadraticInnerEntry term).2 *
        ∑ r : Fin 3, (quadraticCollisionSign innerTerm r).coefficient *
          modeFunction r nearby := by
    funext nearby
    simp [iteratedQuadraticInnerMismatch,
      firstPicardCoordinateBranchMismatch,
      quadraticPhaseMismatch_eq_signedCollisionSum, innerObserved, innerTerm,
      modeFunction]
  rw [hfun]
  simpa [hscaled.hasFDerivAt.fderiv] using hscaled

/-- Main physical derivative theorem.  Every branch derivative comes from
the actual ordered eigenvalue implicit-function theorem; channel algebra is
then handled by the exact outer/inner mismatch definitions. -/
theorem hasStrictFDerivAt_physlibIteratedA2PairMismatchChart
    {N : Nat} [NeZero N] (fixed : Lattice.PositiveMassConfig N)
    {site₁ site₂ : Lattice.Site N} (hsite : site₁ ≠ site₂)
    (channel : IteratedA2MismatchChannel) (observed : Lattice.Site N)
    (term : IteratedQuadraticSecondPicardCharacterTerm N)
    {pair : Real × Real}
    (hregular : pair ∈
      physlibIteratedA2PairMismatchDifferentiabilitySource
        fixed site₁ site₂ channel observed term) :
    HasStrictFDerivAt
      (physlibIteratedA2PairMismatchChart
        fixed site₁ site₂ channel observed term)
      (fderiv Real (physlibIteratedA2PairMismatchChart
        fixed site₁ site₂ channel observed term) pair) pair := by
  rcases hregular with ⟨hpair, hsimple, hpositive⟩
  have outerFor (active : IteratedQuadraticSecondPicardCharacterTerm N)
      (hactive : iteratedA2ChannelActiveTerm channel term = active) :
      HasStrictFDerivAt
        (fun nearby => iteratedQuadraticOuterMismatch
          (twoSiteMassConfig fixed site₁ site₂ nearby) observed active)
        (fderiv Real (fun nearby => iteratedQuadraticOuterMismatch
          (twoSiteMassConfig fixed site₁ site₂ nearby) observed active) pair)
        pair := by
    subst active
    apply hasStrictFDerivAt_iteratedQuadraticOuterMismatch
      fixed hsite hpair hsimple
    intro mode hmode
    apply hpositive mode
    simpa [iteratedA2ChannelParticipatingModes,
      iteratedA2ChannelActiveTerm] using hmode
  have innerFor (active : IteratedQuadraticSecondPicardCharacterTerm N)
      (hactive : iteratedA2ChannelActiveTerm channel term = active) :
      HasStrictFDerivAt
        (fun nearby => iteratedQuadraticInnerMismatch
          (twoSiteMassConfig fixed site₁ site₂ nearby) active)
        (fderiv Real (fun nearby => iteratedQuadraticInnerMismatch
          (twoSiteMassConfig fixed site₁ site₂ nearby) active) pair) pair := by
    subst active
    apply hasStrictFDerivAt_iteratedQuadraticInnerMismatch
      fixed hsite hpair hsimple observed
    intro mode hmode
    apply hpositive mode
    simpa [iteratedA2ChannelParticipatingModes,
      iteratedA2ChannelActiveTerm] using hmode
  cases channel with
  | outer =>
      have h := outerFor term rfl
      change HasStrictFDerivAt
        (fun nearby => iteratedQuadraticOuterMismatch
          (twoSiteMassConfig fixed site₁ site₂ nearby) observed term)
        (fderiv Real (fun nearby => iteratedQuadraticOuterMismatch
          (twoSiteMassConfig fixed site₁ site₂ nearby) observed term) pair) pair
      exact h
  | inner =>
      have h := innerFor term rfl
      change HasStrictFDerivAt
        (fun nearby => iteratedQuadraticInnerMismatch
          (twoSiteMassConfig fixed site₁ site₂ nearby) term)
        (fderiv Real (fun nearby => iteratedQuadraticInnerMismatch
          (twoSiteMassConfig fixed site₁ site₂ nearby) term) pair) pair
      exact h
  | total =>
      have houter := outerFor term rfl
      have hinner := innerFor term rfl
      have hsum := houter.add hinner
      have hfun :
          physlibIteratedA2PairMismatchChart fixed site₁ site₂
              .total observed term =
            fun nearby => iteratedQuadraticOuterMismatch
              (twoSiteMassConfig fixed site₁ site₂ nearby) observed term +
            iteratedQuadraticInnerMismatch
              (twoSiteMassConfig fixed site₁ site₂ nearby) term := by
        rfl
      rw [hfun]
      have hpointwise :
          (fun nearby => iteratedQuadraticOuterMismatch
              (twoSiteMassConfig fixed site₁ site₂ nearby) observed term +
            iteratedQuadraticInnerMismatch
              (twoSiteMassConfig fixed site₁ site₂ nearby) term) =
          ((fun nearby => iteratedQuadraticOuterMismatch
              (twoSiteMassConfig fixed site₁ site₂ nearby) observed term) +
            fun nearby => iteratedQuadraticInnerMismatch
              (twoSiteMassConfig fixed site₁ site₂ nearby) term) := by
        rfl
      rw [hpointwise]
      simpa [hsum.hasFDerivAt.fderiv] using hsum
  | outerTwist =>
      have h := outerFor (flipIteratedQuadraticInnerBranch term) rfl
      change HasStrictFDerivAt
        (fun nearby => iteratedQuadraticOuterMismatch
          (twoSiteMassConfig fixed site₁ site₂ nearby) observed
            (flipIteratedQuadraticInnerBranch term))
        (fderiv Real (fun nearby => iteratedQuadraticOuterMismatch
          (twoSiteMassConfig fixed site₁ site₂ nearby) observed
            (flipIteratedQuadraticInnerBranch term)) pair) pair
      exact h
  | innerTwist =>
      have h := innerFor (flipIteratedQuadraticInnerBranch term) rfl
      change HasStrictFDerivAt
        (fun nearby => iteratedQuadraticInnerMismatch
          (twoSiteMassConfig fixed site₁ site₂ nearby)
            (flipIteratedQuadraticInnerBranch term))
        (fderiv Real (fun nearby => iteratedQuadraticInnerMismatch
          (twoSiteMassConfig fixed site₁ site₂ nearby)
            (flipIteratedQuadraticInnerBranch term)) pair) pair
      exact h

/-- Strict scalar derivative of the second-mass fiber, with derivative equal
to the genuine vertical Jacobian defined above. -/
theorem hasStrictDerivAt_physlibIteratedA2PairMismatchFiber
    {N : Nat} [NeZero N] (fixed : Lattice.PositiveMassConfig N)
    {site₁ site₂ : Lattice.Site N} (hsite : site₁ ≠ site₂)
    (channel : IteratedA2MismatchChannel) (observed : Lattice.Site N)
    (term : IteratedQuadraticSecondPicardCharacterTerm N)
    {pair : Real × Real}
    (hregular : pair ∈
      physlibIteratedA2PairMismatchDifferentiabilitySource
        fixed site₁ site₂ channel observed term) :
    HasStrictDerivAt
      (fun second => physlibIteratedA2PairMismatchChart
        fixed site₁ site₂ channel observed term (pair.1, second))
      (physlibIteratedA2PairMismatchVerticalJacobian
        fixed site₁ site₂ channel observed term pair) pair.2 := by
  have hchart := hasStrictFDerivAt_physlibIteratedA2PairMismatchChart
    fixed hsite channel observed term hregular
  have hline : HasStrictFDerivAt
      (fun second : Real => (pair.1, second))
      (ContinuousLinearMap.inr Real Real Real) pair.2 := by
    convert (hasStrictFDerivAt_const pair.1 pair.2).prodMk
      (hasStrictFDerivAt_id pair.2) using 1 <;>
      ext x <;> simp
  have hcomp := hchart.comp pair.2 hline
  simpa [physlibIteratedA2PairMismatchVerticalJacobian,
    ContinuousLinearMap.comp_apply] using hcomp.hasStrictDerivAt

/-- Reciprocal-natural quantitative-good level of one actual `A2` fiber. -/
def physlibIteratedA2PairFiberGoodLevel
    {N : Nat} [NeZero N] (fixed : Lattice.PositiveMassConfig N)
    (site₁ site₂ : Lattice.Site N) (channel : IteratedA2MismatchChannel)
    (observed : Lattice.Site N)
    (term : IteratedQuadraticSecondPicardCharacterTerm N)
    (first : Real) (n : Nat) : Set Real :=
  {second |
    (first, second) ∈ physlibIteratedA2PairMismatchDifferentiabilitySource
      fixed site₁ site₂ channel observed term ∧
    1 / ((n : Real) + 1) ≤
      |physlibIteratedA2PairMismatchVerticalJacobian
        fixed site₁ site₂ channel observed term (first, second)|}

/-- Physical support left outside a chosen quantitative-good level. -/
def physlibIteratedA2PairFiberBadLevel
    {N : Nat} [NeZero N] (fixed : Lattice.PositiveMassConfig N)
    (site₁ site₂ : Lattice.Site N) (channel : IteratedA2MismatchChannel)
    (observed : Lattice.Site N)
    (term : IteratedQuadraticSecondPicardCharacterTerm N)
    (first : Real) (n : Nat) : Set Real :=
  massSupport \ physlibIteratedA2PairFiberGoodLevel
    fixed site₁ site₂ channel observed term first n

/-- Exact logical decomposition of the retained bad event. -/
theorem mem_physlibIteratedA2PairFiberBadLevel_iff
    {N : Nat} [NeZero N] (fixed : Lattice.PositiveMassConfig N)
    (site₁ site₂ : Lattice.Site N) (channel : IteratedA2MismatchChannel)
    (observed : Lattice.Site N)
    (term : IteratedQuadraticSecondPicardCharacterTerm N)
    (first second : Real) (n : Nat) :
    second ∈ physlibIteratedA2PairFiberBadLevel
        fixed site₁ site₂ channel observed term first n ↔
      second ∈ massSupport ∧
      ((first, second) ∉ interior iidMassPairSupport ∨
       ¬ SimpleOrderedSpectrum
          (twoSiteHarmonicHermitian fixed site₁ site₂ (first, second)) ∨
       (∃ mode,
          mode ∈ iteratedA2ChannelParticipatingModes channel observed term ∧
          orderedEigenvalue
            (twoSiteHarmonicHermitian fixed site₁ site₂ (first, second))
              (orderedIndexEquiv.symm mode) ≤ 0) ∨
       |physlibIteratedA2PairMismatchVerticalJacobian
          fixed site₁ site₂ channel observed term (first, second)| <
            1 / ((n : Real) + 1)) := by
  classical
  simp only [physlibIteratedA2PairFiberBadLevel, mem_diff,
    physlibIteratedA2PairFiberGoodLevel,
    physlibIteratedA2PairMismatchDifferentiabilitySource, mem_setOf_eq,
    not_and_or, not_forall, not_lt, not_le]
  aesop

/-- A regular point with nonzero genuine vertical Jacobian has a local open
measurable injective fiber patch inside the physical mass support. -/
theorem exists_physlibIteratedA2PairFiber_localInjectivePatch
    {N : Nat} [NeZero N] (fixed : Lattice.PositiveMassConfig N)
    {site₁ site₂ : Lattice.Site N} (hsite : site₁ ≠ site₂)
    (channel : IteratedA2MismatchChannel) (observed : Lattice.Site N)
    (term : IteratedQuadraticSecondPicardCharacterTerm N)
    {pair : Real × Real}
    (hregular : pair ∈
      physlibIteratedA2PairMismatchDifferentiabilitySource
        fixed site₁ site₂ channel observed term)
    (hjac : physlibIteratedA2PairMismatchVerticalJacobian
      fixed site₁ site₂ channel observed term pair ≠ 0) :
    ∃ patch : Set Real,
      pair.2 ∈ patch ∧ IsOpen patch ∧ MeasurableSet patch ∧
      patch ⊆ massSupport ∧
      InjOn
        (fun second => physlibIteratedA2PairMismatchChart
          fixed site₁ site₂ channel observed term (pair.1, second)) patch := by
  let jacobian := physlibIteratedA2PairMismatchVerticalJacobian
    fixed site₁ site₂ channel observed term pair
  let derivativeEquiv : Real ≃L[Real] Real :=
    ContinuousLinearEquiv.smulLeft (Units.mk0 jacobian hjac)
  have hequiv : (derivativeEquiv : Real →L[Real] Real) =
      ContinuousLinearMap.toSpanSingleton Real jacobian := by
    apply ContinuousLinearMap.ext
    intro x
    simp [derivativeEquiv, jacobian, mul_comm]
  have hstrict := hasStrictDerivAt_physlibIteratedA2PairMismatchFiber
    fixed hsite channel observed term hregular
  have hstrictEquiv : HasStrictFDerivAt
      (fun second => physlibIteratedA2PairMismatchChart
        fixed site₁ site₂ channel observed term (pair.1, second))
      (derivativeEquiv : Real →L[Real] Real) pair.2 := by
    rw [hequiv]
    exact hstrict
  let localChart : OpenPartialHomeomorph Real Real :=
    hstrictEquiv.toOpenPartialHomeomorph _
  have hpointSource : pair.2 ∈ localChart.source :=
    hstrictEquiv.mem_toOpenPartialHomeomorph_source
  have hsecondInterior : pair.2 ∈ interior massSupport := by
    have hpairInterior := hregular.1
    rw [iidMassPairSupport, interior_prod_eq] at hpairInterior
    exact hpairInterior.2
  let patch := localChart.source ∩ interior massSupport
  refine ⟨patch, ⟨hpointSource, hsecondInterior⟩,
    localChart.open_source.inter isOpen_interior,
    (localChart.open_source.inter isOpen_interior).measurableSet, ?_, ?_⟩
  · intro second hsecond
    exact interior_subset hsecond.2
  · exact localChart.injOn.mono inter_subset_left

end

/-- Global measurability of the totalized actual `A2` vertical Jacobian. -/
theorem measurable_physlibIteratedA2PairMismatchVerticalJacobian
    {N : Nat} [NeZero N] (fixed : Lattice.PositiveMassConfig N)
    (site₁ site₂ : Lattice.Site N) (channel : IteratedA2MismatchChannel)
    (observed : Lattice.Site N)
    (term : IteratedQuadraticSecondPicardCharacterTerm N) :
    Measurable (physlibIteratedA2PairMismatchVerticalJacobian
      fixed site₁ site₂ channel observed term) := by
  unfold physlibIteratedA2PairMismatchVerticalJacobian
  exact (ContinuousLinearMap.apply Real Real (0, 1)).continuous.measurable.comp
    (measurable_fderiv Real
      (physlibIteratedA2PairMismatchChart
        fixed site₁ site₂ channel observed term))

/-- Measurability of the exact simple-positive differentiability source. -/
theorem measurableSet_physlibIteratedA2PairMismatchDifferentiabilitySource
    {N : Nat} [NeZero N] (fixed : Lattice.PositiveMassConfig N)
    (site₁ site₂ : Lattice.Site N) (channel : IteratedA2MismatchChannel)
    (observed : Lattice.Site N)
    (term : IteratedQuadraticSecondPicardCharacterTerm N) :
    MeasurableSet (physlibIteratedA2PairMismatchDifferentiabilitySource
      fixed site₁ site₂ channel observed term) := by
  have hsimpleOpen : IsOpen
      {pair : Real × Real | SimpleOrderedSpectrum
        (twoSiteHarmonicHermitian fixed site₁ site₂ pair)} := by
    rw [isOpen_iff_mem_nhds]
    intro pair hsimple
    exact eventually_simple_twoSiteHarmonicHermitian
      fixed site₁ site₂ pair hsimple
  have hpositive : MeasurableSet
      {pair : Real × Real |
        ∀ mode ∈ iteratedA2ChannelParticipatingModes channel observed term,
          0 < orderedEigenvalue
            (twoSiteHarmonicHermitian fixed site₁ site₂ pair)
            (orderedIndexEquiv.symm mode)} := by
    rw [show {pair : Real × Real |
        ∀ mode ∈ iteratedA2ChannelParticipatingModes channel observed term,
          0 < orderedEigenvalue
            (twoSiteHarmonicHermitian fixed site₁ site₂ pair)
            (orderedIndexEquiv.symm mode)} =
      ⋂ mode, if mode ∈
          iteratedA2ChannelParticipatingModes channel observed term then
        {pair : Real × Real | 0 < orderedEigenvalue
          (twoSiteHarmonicHermitian fixed site₁ site₂ pair)
          (orderedIndexEquiv.symm mode)} else Set.univ by
        ext pair
        simp]
    apply MeasurableSet.iInter
    intro mode
    split_ifs
    · exact measurableSet_Ioi.preimage
        ((continuous_orderedEigenvalue (orderedIndexEquiv.symm mode)).measurable.comp
          (continuous_twoSiteHarmonicHermitian
            fixed site₁ site₂).measurable)
    · exact MeasurableSet.univ
  exact isOpen_interior.measurableSet.inter
    (hsimpleOpen.measurableSet.inter hpositive)

/-- Every reciprocal-natural good fiber is measurable. -/
theorem measurableSet_physlibIteratedA2PairFiberGoodLevel
    {N : Nat} [NeZero N] (fixed : Lattice.PositiveMassConfig N)
    (site₁ site₂ : Lattice.Site N) (channel : IteratedA2MismatchChannel)
    (observed : Lattice.Site N)
    (term : IteratedQuadraticSecondPicardCharacterTerm N)
    (first : Real) (n : Nat) :
    MeasurableSet (physlibIteratedA2PairFiberGoodLevel
      fixed site₁ site₂ channel observed term first n) := by
  let line : Real → Real × Real := fun second => (first, second)
  have hline : Measurable line := measurable_const.prodMk measurable_id
  have hsource :=
    (measurableSet_physlibIteratedA2PairMismatchDifferentiabilitySource
      fixed site₁ site₂ channel observed term).preimage hline
  have hjac : Measurable fun second =>
      |physlibIteratedA2PairMismatchVerticalJacobian
        fixed site₁ site₂ channel observed term (first, second)| :=
    (measurable_physlibIteratedA2PairMismatchVerticalJacobian
      fixed site₁ site₂ channel observed term).comp hline |>.abs
  exact hsource.inter (measurableSet_Ici.preimage hjac)

/-- The physical bad-Jacobian event is measurable. -/
theorem measurableSet_physlibIteratedA2PairFiberBadLevel
    {N : Nat} [NeZero N] (fixed : Lattice.PositiveMassConfig N)
    (site₁ site₂ : Lattice.Site N) (channel : IteratedA2MismatchChannel)
    (observed : Lattice.Site N)
    (term : IteratedQuadraticSecondPicardCharacterTerm N)
    (first : Real) (n : Nat) :
    MeasurableSet (physlibIteratedA2PairFiberBadLevel
      fixed site₁ site₂ channel observed term first n) := by
  exact measurableSet_Icc.diff
    (measurableSet_physlibIteratedA2PairFiberGoodLevel
      fixed site₁ site₂ channel observed term first n)

/-- Reciprocal-natural levels cover every regular noncritical fiber point.
No quantitative assertion about the complementary mass is hidden here. -/
theorem regularNoncriticalIteratedA2Fiber_subset_iUnion_goodLevel
    {N : Nat} [NeZero N] (fixed : Lattice.PositiveMassConfig N)
    (site₁ site₂ : Lattice.Site N) (channel : IteratedA2MismatchChannel)
    (observed : Lattice.Site N)
    (term : IteratedQuadraticSecondPicardCharacterTerm N)
    (first : Real) :
    {second |
      (first, second) ∈
        physlibIteratedA2PairMismatchDifferentiabilitySource
          fixed site₁ site₂ channel observed term ∧
      physlibIteratedA2PairMismatchVerticalJacobian
        fixed site₁ site₂ channel observed term (first, second) ≠ 0} ⊆
      ⋃ n, physlibIteratedA2PairFiberGoodLevel
        fixed site₁ site₂ channel observed term first n := by
  intro second hsecond
  obtain ⟨n, hn⟩ := exists_nat_one_div_lt (abs_pos.mpr hsecond.2)
  exact mem_iUnion.mpr ⟨n, hsecond.1, hn.le⟩

end ArchonPhysics.PhyslibFPUTIteratedA2PairFiberTransversalityAtlas
