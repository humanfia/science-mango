import Mathlib.Analysis.Calculus.FDeriv.Measurable
import Mathlib.Analysis.Calculus.InverseFunctionTheorem.FDeriv
import ArchonPhysics.ActualTwoMassSimpleEigenvalueDifferentiability
import ArchonPhysics.FreeFPUTCollisionMismatchBridge
import ArchonPhysics.FreeFPUTZeroModeDiagonalRemainder
import ArchonPhysics.OrderedTranslationLastMode
import ArchonPhysics.PhyslibFPUTA1AnnealedMismatchSmallBall

/-!
# Actual A1 pair-fiber Jacobians and their honest good/bad atlas

This file audits the scalar transversality premise left by
`PhyslibFPUTA1AnnealedMismatchSmallBall`.  It defines the genuine vertical
Jacobian of the actual two-mass mismatch chart, proves its strict derivative
formula at interior simple-spectrum positive-mode points, and exposes a
measurable hierarchy of quantitative-good levels.  Every noncritical point
has a local open injective fiber patch by the strict inverse function theorem.

There is an unavoidable global obstruction.  The signed term consisting of
the observed mode and the deterministic acoustic mode has mismatch exactly
zero for every mass configuration.  Hence a positive Jacobian lower bound or
injectivity uniform over all signed A1 terms is false.  The same term has
exactly zero cubic coefficient because its acoustic tensor leg vanishes, so
it must be removed structurally rather than inserted into a small-ball bound.

For a fixed higher-order ordered/branching history, apply the good/bad event
below separately to each of its finitely many cumulative denominators and
take their finite union.  The union-cardinality loss is therefore explicitly
order dependent (for the existing linear histories it is one contribution
per enumerated cumulative denominator).  Identically resonant or
charge-balanced blocks remain in the resonant remainder unless their full
coefficient is proved zero.  No pairwise phase cancellation, initial Haar
law, re-Haar step, Markov property, `g,N` limit, or recollision estimate is
used or implied here; in particular this is not a higher-order RPA theorem.
-/

namespace ArchonPhysics.PhyslibFPUTA1PairFiberTransversalityAtlas

open ArchonPhysics
open ArchonPhysics.ActualTwoMassSimpleEigenvalueDifferentiability
open ArchonPhysics.ActualTwoMassSpectralChart
open ArchonPhysics.FreeFPUTCollisionMismatchBridge
open ArchonPhysics.FreeFPUTDuhamelResonanceBridge
open ArchonPhysics.FreeFPUTMismatchPhaseExpansion
open ArchonPhysics.FreeFPUTTensorPhaseExpansion
open ArchonPhysics.FreeFPUTZeroModeDiagonalRemainder
open ArchonPhysics.FrozenCollisionMassPositivity
open ArchonPhysics.MeasurableOrderedModeCoupling.Harmonic
open ArchonPhysics.MeasurableOrderedSpectrum
open ArchonPhysics.ModeCoupling
open ArchonPhysics.ModalPhaseMismatch
open ArchonPhysics.OrderedSingleModeProjector
open ArchonPhysics.OrderedSpectrumContinuity
open ArchonPhysics.OrderedTranslationLastMode
open ArchonPhysics.PhyslibFPUTA1AnnealedMismatchSmallBall
open ArchonPhysics.RandomEnsemble
open ArchonPhysics.TwoParameterSpectralAveragingAtlas
open Filter Function MeasureTheory Set

noncomputable section

/-- Physical representative of the last ordered mode, which is the exact
translation/acoustic zero mode for every positive mass configuration. -/
def physlibAcousticMode (N : Nat) [NeZero N] : Lattice.Site N :=
  orderedIndexEquiv (lastOrderedIndex (ι := Lattice.Site N))

/-- The obstruction term: one copy of the observed mode and one acoustic
input, both in the phase (`+1` charge) sector. -/
def physlibA1AcousticCopyTerm {N : Nat} [NeZero N]
    (observed : Lattice.Site N) : QuadraticPhaseTerm N :=
  (Fin.cons observed (fun _ : Fin 1 => physlibAcousticMode N), (0, 0))

theorem modeFrequency_physlibAcousticMode_eq_zero
    {N : Nat} [NeZero N] (m : Lattice.PositiveMassConfig N) :
    modeFrequency m (physlibAcousticMode N) = 0 := by
  unfold physlibAcousticMode
  rw [← orderedModeFrequency_harmonicHermitian_eq]
  simp [orderedModeFrequency, harmonic_lastOrderedEigenvalue_eq_zero]

/-- The obstruction term is identically resonant, for every positive mass
configuration and without any simplicity hypothesis. -/
theorem physlibA1AcousticCopyTerm_mismatch_eq_zero
    {N : Nat} [NeZero N] (m : Lattice.PositiveMassConfig N)
    (observed : Lattice.Site N) :
    quadraticPhaseMismatch (modeFrequency m) observed
      (physlibA1AcousticCopyTerm observed) = 0 := by
  rw [quadraticPhaseMismatch_eq_output_sub_chargeFrequency,
    chargeFrequency_quadraticPhaseCharge]
  simp [physlibA1AcousticCopyTerm, binaryPhaseSign,
    modeFrequency_physlibAcousticMode_eq_zero]

theorem physlibA1AcousticCopyTerm_pairMismatch_eq_zero
    {N : Nat} [NeZero N] (fixed : Lattice.PositiveMassConfig N)
    (site₁ site₂ observed : Lattice.Site N) (pair : Real × Real) :
    physlibA1PairMismatchChart fixed site₁ site₂ observed
      (physlibA1AcousticCopyTerm observed) pair = 0 := by
  exact physlibA1AcousticCopyTerm_mismatch_eq_zero _ observed

/-- The identically resonant obstruction is nevertheless structurally null:
its cubic interaction tensor contains the acoustic input leg. -/
theorem physlibA1AcousticCopyTerm_interactionTensor_eq_zero
    {N : Nat} [NeZero N] (m : Lattice.PositiveMassConfig N)
    (observed : Lattice.Site N) :
    interactionTensor m 3
      (Fin.cons observed (physlibA1AcousticCopyTerm observed).1) = 0 := by
  exact interactionTensor_eq_zero_of_modeFrequency_eq_zero m _ 2
    (modeFrequency_physlibAcousticMode_eq_zero m)

/-- Consequently the full deterministic Duhamel coefficient of the
identically resonant obstruction is zero for all couplings and radii. -/
theorem physlibA1AcousticCopyTerm_coefficient_eq_zero
    {N : Nat} [NeZero N] (coupling : Complex)
    (m : Lattice.PositiveMassConfig N) (observed : Lattice.Site N)
    (radius : Lattice.Site N → Real) :
    freeQuadraticDuhamelCoefficient coupling m observed radius
      (physlibA1AcousticCopyTerm observed) = 0 := by
  unfold freeQuadraticDuhamelCoefficient quadraticPhaseCoefficient
  rw [physlibA1AcousticCopyTerm_interactionTensor_eq_zero]
  simp

/-- The actual second-coordinate Jacobian: the Fréchet derivative of the
genuine pair mismatch chart evaluated on the vertical basis vector `(0,1)`.
This total definition is measurable even off the differentiability locus. -/
def physlibA1PairMismatchVerticalJacobian
    {N : Nat} [NeZero N] (fixed : Lattice.PositiveMassConfig N)
    (site₁ site₂ observed : Lattice.Site N)
    (term : QuadraticPhaseTerm N) (pair : Real × Real) : Real :=
  fderiv Real
    (physlibA1PairMismatchChart fixed site₁ site₂ observed term) pair
      (0, 1)

/-- The corresponding actual one-site frequency derivative for one physical
mode. -/
def actualTwoMassModeVerticalJacobian
    {N : Nat} [NeZero N] (fixed : Lattice.PositiveMassConfig N)
    (site₁ site₂ mode : Lattice.Site N) (pair : Real × Real) : Real :=
  fderiv Real
    (fun nearby =>
      modeFrequency (twoSiteMassConfig fixed site₁ site₂ nearby) mode)
    pair (0, 1)

/-- Exact locus on which all three actual ordered frequency branches needed
by one signed A1 mismatch are strictly differentiable. -/
def physlibA1PairMismatchDifferentiabilitySource
    {N : Nat} [NeZero N] (fixed : Lattice.PositiveMassConfig N)
    (site₁ site₂ observed : Lattice.Site N)
    (term : QuadraticPhaseTerm N) : Set (Real × Real) :=
  {pair |
    pair ∈ interior iidMassPairSupport ∧
    SimpleOrderedSpectrum
      (twoSiteHarmonicHermitian fixed site₁ site₂ pair) ∧
    ∀ r : Fin 3, 0 < orderedEigenvalue
      (twoSiteHarmonicHermitian fixed site₁ site₂ pair)
      (orderedIndexEquiv.symm (quadraticCollisionModes observed term r))}

private theorem exists_hasStrictFDerivAt_actualTwoMassModeFrequency
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

/-- Kernel-checked one-site eigenvalue-branch composition formula: the
vertical mismatch Jacobian is the signed sum of the three genuine ordered
mode vertical derivatives.  The existing actual simple-eigenvalue API
supplies each row; no abstract differentiability certificate is assumed. -/
theorem physlibA1PairMismatchVerticalJacobian_eq_signedSum
    {N : Nat} [NeZero N] (fixed : Lattice.PositiveMassConfig N)
    {site₁ site₂ : Lattice.Site N} (hsite : site₁ ≠ site₂)
    (observed : Lattice.Site N) (term : QuadraticPhaseTerm N)
    {pair : Real × Real}
    (hregular : pair ∈ physlibA1PairMismatchDifferentiabilitySource
      fixed site₁ site₂ observed term) :
    physlibA1PairMismatchVerticalJacobian
        fixed site₁ site₂ observed term pair =
      ∑ r : Fin 3, (quadraticCollisionSign term r).coefficient *
        actualTwoMassModeVerticalJacobian fixed site₁ site₂
          (quadraticCollisionModes observed term r) pair := by
  let modeFunction := fun r : Fin 3 => fun nearby : Real × Real =>
    modeFrequency (twoSiteMassConfig fixed site₁ site₂ nearby)
      (quadraticCollisionModes observed term r)
  have hmode : ∀ r, HasStrictFDerivAt (modeFunction r)
      (fderiv Real (modeFunction r) pair) pair := by
    intro r
    exact exists_hasStrictFDerivAt_actualTwoMassModeFrequency fixed hsite
      hregular.1 hregular.2.1 _ (hregular.2.2 r)
  have hsum : HasFDerivAt
      (fun nearby => ∑ r : Fin 3,
        (quadraticCollisionSign term r).coefficient * modeFunction r nearby)
      (∑ r : Fin 3, (quadraticCollisionSign term r).coefficient •
        fderiv Real (modeFunction r) pair) pair := by
    apply HasFDerivAt.fun_sum
    intro r _hr
    exact (hmode r).hasFDerivAt.const_mul _
  have hmismatch : HasFDerivAt
      (physlibA1PairMismatchChart fixed site₁ site₂ observed term)
      (∑ r : Fin 3, (quadraticCollisionSign term r).coefficient •
        fderiv Real (modeFunction r) pair) pair := by
    have hfun :
        physlibA1PairMismatchChart fixed site₁ site₂ observed term =
          fun nearby => ∑ r : Fin 3,
            (quadraticCollisionSign term r).coefficient *
              modeFunction r nearby := by
      funext nearby
      exact quadraticPhaseMismatch_eq_signedCollisionSum
        (modeFrequency (twoSiteMassConfig fixed site₁ site₂ nearby))
          observed term
    rw [hfun]
    exact hsum
  have hfderiv := hmismatch.fderiv
  simp only [physlibA1PairMismatchVerticalJacobian,
    actualTwoMassModeVerticalJacobian, hfderiv,
    ContinuousLinearMap.sum_apply, ContinuousLinearMap.smul_apply,
    smul_eq_mul]
  rfl

/-- Strict scalar derivative of the actual second-mass fiber at every point
of the displayed physical differentiability source. -/
theorem hasStrictDerivAt_physlibA1PairMismatchFiber
    {N : Nat} [NeZero N] (fixed : Lattice.PositiveMassConfig N)
    {site₁ site₂ : Lattice.Site N} (hsite : site₁ ≠ site₂)
    (observed : Lattice.Site N) (term : QuadraticPhaseTerm N)
    {pair : Real × Real}
    (hregular : pair ∈ physlibA1PairMismatchDifferentiabilitySource
      fixed site₁ site₂ observed term) :
    HasStrictDerivAt
      (fun second => physlibA1PairMismatchChart
        fixed site₁ site₂ observed term (pair.1, second))
      (physlibA1PairMismatchVerticalJacobian
        fixed site₁ site₂ observed term pair) pair.2 := by
  let modeFunction := fun r : Fin 3 => fun nearby : Real × Real =>
    modeFrequency (twoSiteMassConfig fixed site₁ site₂ nearby)
      (quadraticCollisionModes observed term r)
  have hmode : ∀ r, HasStrictFDerivAt (modeFunction r)
      (fderiv Real (modeFunction r) pair) pair := by
    intro r
    exact exists_hasStrictFDerivAt_actualTwoMassModeFrequency fixed hsite
      hregular.1 hregular.2.1 _ (hregular.2.2 r)
  have hsum : HasStrictFDerivAt
      (fun nearby => ∑ r : Fin 3,
        (quadraticCollisionSign term r).coefficient * modeFunction r nearby)
      (∑ r : Fin 3, (quadraticCollisionSign term r).coefficient •
        fderiv Real (modeFunction r) pair) pair := by
    apply HasStrictFDerivAt.fun_sum
    intro r _hr
    exact (hmode r).const_mul _
  have hmismatch : HasStrictFDerivAt
      (physlibA1PairMismatchChart fixed site₁ site₂ observed term)
      (∑ r : Fin 3, (quadraticCollisionSign term r).coefficient •
        fderiv Real (modeFunction r) pair) pair := by
    have hfun :
        physlibA1PairMismatchChart fixed site₁ site₂ observed term =
          fun nearby => ∑ r : Fin 3,
            (quadraticCollisionSign term r).coefficient *
              modeFunction r nearby := by
      funext nearby
      exact quadraticPhaseMismatch_eq_signedCollisionSum
        (modeFrequency (twoSiteMassConfig fixed site₁ site₂ nearby))
          observed term
    rw [hfun]
    exact hsum
  have hpairLine : HasStrictFDerivAt
      (fun second : Real => (pair.1, second))
      (ContinuousLinearMap.inr Real Real Real) pair.2 := by
    convert (hasStrictFDerivAt_const pair.1 pair.2).prodMk
      (hasStrictFDerivAt_id pair.2) using 1 <;>
      ext x <;> simp
  have hline := hmismatch.comp pair.2 hpairLine
  have hfderiv := hmismatch.hasFDerivAt.fderiv
  simpa [physlibA1PairMismatchVerticalJacobian, hfderiv,
    ContinuousLinearMap.comp_apply] using hline.hasStrictDerivAt

/-- Quantitative-good second-coordinate fiber at reciprocal-natural level
`1/(n+1)`. -/
def physlibA1PairFiberGoodLevel
    {N : Nat} [NeZero N] (fixed : Lattice.PositiveMassConfig N)
    (site₁ site₂ observed : Lattice.Site N)
    (term : QuadraticPhaseTerm N) (first : Real) (n : Nat) : Set Real :=
  {second |
    (first, second) ∈ physlibA1PairMismatchDifferentiabilitySource
      fixed site₁ site₂ observed term ∧
    1 / ((n : Real) + 1) ≤
      |physlibA1PairMismatchVerticalJacobian
        fixed site₁ site₂ observed term (first, second)|}

/-- The exact bad event retained by the one-site method.  It includes every
point outside the quantitative-good level but only inside the physical mass
support. -/
def physlibA1PairFiberBadLevel
    {N : Nat} [NeZero N] (fixed : Lattice.PositiveMassConfig N)
    (site₁ site₂ observed : Lattice.Site N)
    (term : QuadraticPhaseTerm N) (first : Real) (n : Nat) : Set Real :=
  massSupport \ physlibA1PairFiberGoodLevel
    fixed site₁ site₂ observed term first n

/-- Exact logical atlas of the bad event: boundary, nonsimple spectrum,
nonpositive participating eigenvalue, or a quantitatively small actual
vertical Jacobian.  These are the explicit sets requiring further
multivariable or analytic-zero-set control. -/
theorem mem_physlibA1PairFiberBadLevel_iff
    {N : Nat} [NeZero N] (fixed : Lattice.PositiveMassConfig N)
    (site₁ site₂ observed : Lattice.Site N)
    (term : QuadraticPhaseTerm N) (first second : Real) (n : Nat) :
    second ∈ physlibA1PairFiberBadLevel
        fixed site₁ site₂ observed term first n ↔
      second ∈ massSupport ∧
      ((first, second) ∉ interior iidMassPairSupport ∨
       ¬ SimpleOrderedSpectrum
          (twoSiteHarmonicHermitian fixed site₁ site₂ (first, second)) ∨
       (∃ r : Fin 3, orderedEigenvalue
          (twoSiteHarmonicHermitian fixed site₁ site₂ (first, second))
            (orderedIndexEquiv.symm
              (quadraticCollisionModes observed term r)) ≤ 0) ∨
       |physlibA1PairMismatchVerticalJacobian
          fixed site₁ site₂ observed term (first, second)| <
            1 / ((n : Real) + 1)) := by
  classical
  simp only [physlibA1PairFiberBadLevel, mem_diff,
    physlibA1PairFiberGoodLevel,
    physlibA1PairMismatchDifferentiabilitySource, mem_setOf_eq,
    not_and_or, not_forall, not_lt, not_le]
  tauto

/-- Every quantitatively noncritical actual fiber point produces a genuine
local open injective atlas patch.  Injectivity is thus a theorem locally; the
mass of points not covered at a chosen threshold remains the explicit bad
event above. -/
theorem exists_physlibA1PairFiber_localInjectivePatch
    {N : Nat} [NeZero N] (fixed : Lattice.PositiveMassConfig N)
    {site₁ site₂ : Lattice.Site N} (hsite : site₁ ≠ site₂)
    (observed : Lattice.Site N) (term : QuadraticPhaseTerm N)
    {pair : Real × Real}
    (hregular : pair ∈ physlibA1PairMismatchDifferentiabilitySource
      fixed site₁ site₂ observed term)
    (hjac : physlibA1PairMismatchVerticalJacobian
      fixed site₁ site₂ observed term pair ≠ 0) :
    ∃ patch : Set Real,
      pair.2 ∈ patch ∧ IsOpen patch ∧ MeasurableSet patch ∧
      patch ⊆ massSupport ∧
      InjOn
        (fun second => physlibA1PairMismatchChart
          fixed site₁ site₂ observed term (pair.1, second)) patch := by
  let jacobian := physlibA1PairMismatchVerticalJacobian
    fixed site₁ site₂ observed term pair
  let derivativeEquiv : Real ≃L[Real] Real :=
    ContinuousLinearEquiv.smulLeft (Units.mk0 jacobian hjac)
  have hequiv : (derivativeEquiv : Real →L[Real] Real) =
      ContinuousLinearMap.toSpanSingleton Real jacobian := by
    apply ContinuousLinearMap.ext
    intro x
    simp [derivativeEquiv, jacobian, mul_comm]
  have hstrict := hasStrictDerivAt_physlibA1PairMismatchFiber
    fixed hsite observed term hregular
  have hstrictEquiv : HasStrictFDerivAt
      (fun second => physlibA1PairMismatchChart
        fixed site₁ site₂ observed term (pair.1, second))
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

/-- The acoustic obstruction prevents injectivity on the nontrivial physical
mass support. -/
theorem not_injOn_physlibA1AcousticCopyTerm_pairFiber_massSupport
    {N : Nat} [NeZero N] (fixed : Lattice.PositiveMassConfig N)
    (site₁ site₂ observed : Lattice.Site N) (first : Real) :
    ¬ InjOn
      (fun second => physlibA1PairMismatchChart fixed site₁ site₂ observed
        (physlibA1AcousticCopyTerm observed) (first, second)) massSupport := by
  intro hinjective
  have hlower : massLower ∈ massSupport := by
    exact ⟨le_rfl, massLower_le_massUpper⟩
  have hupper : massUpper ∈ massSupport := by
    exact ⟨massLower_le_massUpper, le_rfl⟩
  have heq := hinjective hlower hupper (by
    simp [physlibA1AcousticCopyTerm_pairMismatch_eq_zero])
  have hne : massLower ≠ massUpper := by
    norm_num [massLower, massUpper]
  exact hne heq

/-- In particular, no positive vertical-Jacobian lower bound can hold for
all signed A1 terms on the full mass support. -/
theorem no_uniform_positive_A1_pairFiberJacobianLowerBound
    {N : Nat} [NeZero N] (fixed : Lattice.PositiveMassConfig N)
    (site₁ site₂ observed : Lattice.Site N) (first : Real)
    (j₀ : Real) (hj₀ : 0 < j₀) :
    ¬ (∀ (term : QuadraticPhaseTerm N) (second : Real),
      second ∈ massSupport →
      j₀ ≤ |physlibA1PairMismatchVerticalJacobian
        fixed site₁ site₂ observed term (first, second)|) := by
  intro hall
  have hlower : massLower ∈ massSupport :=
    ⟨le_rfl, massLower_le_massUpper⟩
  have hbound := hall (physlibA1AcousticCopyTerm observed) massLower hlower
  have hzero : physlibA1PairMismatchVerticalJacobian fixed site₁ site₂
      observed (physlibA1AcousticCopyTerm observed) (first, massLower) = 0 := by
    unfold physlibA1PairMismatchVerticalJacobian
    have hfun : physlibA1PairMismatchChart fixed site₁ site₂ observed
        (physlibA1AcousticCopyTerm observed) = fun _ => 0 := by
      funext pair
      exact physlibA1AcousticCopyTerm_pairMismatch_eq_zero
        fixed site₁ site₂ observed pair
    rw [hfun]
    simp
  rw [hzero, abs_zero] at hbound
  linarith

end

/-- Global measurability of the actual vertical Jacobian, including the
nonsimple and boundary loci where `fderiv` is totalized. -/
theorem measurable_physlibA1PairMismatchVerticalJacobian
    {N : Nat} [NeZero N] (fixed : Lattice.PositiveMassConfig N)
    (site₁ site₂ observed : Lattice.Site N)
    (term : QuadraticPhaseTerm N) :
    Measurable (physlibA1PairMismatchVerticalJacobian
      fixed site₁ site₂ observed term) := by
  unfold physlibA1PairMismatchVerticalJacobian
  exact (ContinuousLinearMap.apply Real Real (0, 1)).continuous.measurable.comp
    (measurable_fderiv Real
      (physlibA1PairMismatchChart fixed site₁ site₂ observed term))

/-- The exact simple-positive differentiability source is measurable. -/
theorem measurableSet_physlibA1PairMismatchDifferentiabilitySource
    {N : Nat} [NeZero N] (fixed : Lattice.PositiveMassConfig N)
    (site₁ site₂ observed : Lattice.Site N)
    (term : QuadraticPhaseTerm N) :
    MeasurableSet (physlibA1PairMismatchDifferentiabilitySource
      fixed site₁ site₂ observed term) := by
  have hsimpleOpen : IsOpen
      {pair : Real × Real | SimpleOrderedSpectrum
        (twoSiteHarmonicHermitian fixed site₁ site₂ pair)} := by
    rw [isOpen_iff_mem_nhds]
    intro pair hsimple
    exact eventually_simple_twoSiteHarmonicHermitian
      fixed site₁ site₂ pair hsimple
  have hpositive : MeasurableSet
      {pair : Real × Real | ∀ r : Fin 3, 0 < orderedEigenvalue
        (twoSiteHarmonicHermitian fixed site₁ site₂ pair)
        (orderedIndexEquiv.symm
          (quadraticCollisionModes observed term r))} := by
    rw [show {pair : Real × Real | ∀ r : Fin 3, 0 < orderedEigenvalue
        (twoSiteHarmonicHermitian fixed site₁ site₂ pair)
        (orderedIndexEquiv.symm
          (quadraticCollisionModes observed term r))} =
      ⋂ r : Fin 3, {pair : Real × Real | 0 < orderedEigenvalue
        (twoSiteHarmonicHermitian fixed site₁ site₂ pair)
        (orderedIndexEquiv.symm
          (quadraticCollisionModes observed term r))} by ext; simp]
    apply MeasurableSet.iInter
    intro r
    exact measurableSet_Ioi.preimage
      ((continuous_orderedEigenvalue
        (orderedIndexEquiv.symm
          (quadraticCollisionModes observed term r))).measurable.comp
        (continuous_twoSiteHarmonicHermitian
          fixed site₁ site₂).measurable)
  exact isOpen_interior.measurableSet.inter
    (hsimpleOpen.measurableSet.inter hpositive)

/-- Every reciprocal-natural quantitative-good fiber is measurable. -/
theorem measurableSet_physlibA1PairFiberGoodLevel
    {N : Nat} [NeZero N] (fixed : Lattice.PositiveMassConfig N)
    (site₁ site₂ observed : Lattice.Site N)
    (term : QuadraticPhaseTerm N) (first : Real) (n : Nat) :
    MeasurableSet (physlibA1PairFiberGoodLevel
      fixed site₁ site₂ observed term first n) := by
  let line : Real → Real × Real := fun second => (first, second)
  have hline : Measurable line := measurable_const.prodMk measurable_id
  have hsource :=
    (measurableSet_physlibA1PairMismatchDifferentiabilitySource
      fixed site₁ site₂ observed term).preimage hline
  have hjac : Measurable fun second =>
      |physlibA1PairMismatchVerticalJacobian
        fixed site₁ site₂ observed term (first, second)| :=
    (measurable_physlibA1PairMismatchVerticalJacobian
      fixed site₁ site₂ observed term).comp hline |>.abs
  exact hsource.inter (measurableSet_Ici.preimage hjac)

/-- The retained physical bad-Jacobian event is measurable. -/
theorem measurableSet_physlibA1PairFiberBadLevel
    {N : Nat} [NeZero N] (fixed : Lattice.PositiveMassConfig N)
    (site₁ site₂ observed : Lattice.Site N)
    (term : QuadraticPhaseTerm N) (first : Real) (n : Nat) :
    MeasurableSet (physlibA1PairFiberBadLevel
      fixed site₁ site₂ observed term first n) := by
  exact measurableSet_Icc.diff
    (measurableSet_physlibA1PairFiberGoodLevel
      fixed site₁ site₂ observed term first n)

/-- Reciprocal-natural levels cover precisely every regular noncritical
fiber point.  This supplies a transparent countable atlas but no quantitative
claim that its complementary mass is small. -/
theorem regularNoncriticalFiber_subset_iUnion_goodLevel
    {N : Nat} [NeZero N] (fixed : Lattice.PositiveMassConfig N)
    (site₁ site₂ observed : Lattice.Site N)
    (term : QuadraticPhaseTerm N) (first : Real) :
    {second |
      (first, second) ∈ physlibA1PairMismatchDifferentiabilitySource
        fixed site₁ site₂ observed term ∧
      physlibA1PairMismatchVerticalJacobian
        fixed site₁ site₂ observed term (first, second) ≠ 0} ⊆
      ⋃ n, physlibA1PairFiberGoodLevel
        fixed site₁ site₂ observed term first n := by
  intro second hsecond
  obtain ⟨n, hn⟩ := exists_nat_one_div_lt (abs_pos.mpr hsecond.2)
  exact mem_iUnion.mpr ⟨n, hsecond.1, hn.le⟩

/-- At any fixed order, the pair-fiber bad event is the finite union over
the actually enumerated cumulative denominators.  Exactly resonant or
charge-balanced denominators are not silently discarded: if their
coefficient has not separately been proved zero, their bad set remains in
this union. -/
def physlibFixedHistoryPairFiberBadEvent
    {J : Type*} [Fintype J]
    {N : Nat} [NeZero N] (fixed : Lattice.PositiveMassConfig N)
    (site₁ site₂ observed : Lattice.Site N)
    (term : J → QuadraticPhaseTerm N) (first : Real)
    (level : J → Nat) : Set Real :=
  ⋃ j, physlibA1PairFiberBadLevel
    fixed site₁ site₂ observed (term j) first (level j)

theorem measurableSet_physlibFixedHistoryPairFiberBadEvent
    {J : Type*} [Fintype J]
    {N : Nat} [NeZero N] (fixed : Lattice.PositiveMassConfig N)
    (site₁ site₂ observed : Lattice.Site N)
    (term : J → QuadraticPhaseTerm N) (first : Real)
    (level : J → Nat) :
    MeasurableSet (physlibFixedHistoryPairFiberBadEvent
      fixed site₁ site₂ observed term first level) := by
  classical
  exact MeasurableSet.iUnion fun j =>
    measurableSet_physlibA1PairFiberBadLevel
      fixed site₁ site₂ observed (term j) first (level j)

/-- Fixed-order union bound.  The loss is the exact finite sum over
cumulative denominators; it contains no probabilistic independence premise. -/
theorem measure_physlibFixedHistoryPairFiberBadEvent_le_sum
    {J : Type*} [Fintype J]
    {N : Nat} [NeZero N] (fixed : Lattice.PositiveMassConfig N)
    (site₁ site₂ observed : Lattice.Site N)
    (term : J → QuadraticPhaseTerm N) (first : Real)
    (level : J → Nat) :
    massCoordinateLaw (physlibFixedHistoryPairFiberBadEvent
        fixed site₁ site₂ observed term first level) ≤
      ∑ j, massCoordinateLaw
        (physlibA1PairFiberBadLevel fixed site₁ site₂ observed
          (term j) first (level j)) := by
  classical
  simpa [physlibFixedHistoryPairFiberBadEvent] using
    (measure_iUnion_le (μ := massCoordinateLaw) (fun j =>
      physlibA1PairFiberBadLevel fixed site₁ site₂ observed
        (term j) first (level j)))

/-- If each cumulative denominator has bad mass at most `budget`, a
fixed-order history costs exactly the number of enumerated denominators.
There is no order-independent conclusion here. -/
theorem measure_physlibFixedHistoryPairFiberBadEvent_le_card_mul
    {J : Type*} [Fintype J]
    {N : Nat} [NeZero N] (fixed : Lattice.PositiveMassConfig N)
    (site₁ site₂ observed : Lattice.Site N)
    (term : J → QuadraticPhaseTerm N) (first : Real)
    (level : J → Nat) (budget : ENNReal)
    (hbudget : ∀ j, massCoordinateLaw
      (physlibA1PairFiberBadLevel fixed site₁ site₂ observed
        (term j) first (level j)) ≤ budget) :
    massCoordinateLaw (physlibFixedHistoryPairFiberBadEvent
        fixed site₁ site₂ observed term first level) ≤
      (Fintype.card J : ENNReal) * budget := by
  calc
    massCoordinateLaw (physlibFixedHistoryPairFiberBadEvent
        fixed site₁ site₂ observed term first level) ≤
      ∑ j, massCoordinateLaw
        (physlibA1PairFiberBadLevel fixed site₁ site₂ observed
          (term j) first (level j)) :=
      measure_physlibFixedHistoryPairFiberBadEvent_le_sum
        fixed site₁ site₂ observed term first level
    _ ≤ ∑ _j : J, budget := Finset.sum_le_sum fun j _ => hbudget j
    _ = (Fintype.card J : ENNReal) * budget := by simp

end ArchonPhysics.PhyslibFPUTA1PairFiberTransversalityAtlas
