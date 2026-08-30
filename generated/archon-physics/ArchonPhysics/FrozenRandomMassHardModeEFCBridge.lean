import ArchonPhysics.BHOAnnealedEFCLocalizationBorelCantelli
import ArchonPhysics.FrozenAndersonOneSiteSpectralAveraging
import ArchonPhysics.GenericSpectrumResultant
import ArchonPhysics.RandomMassPhaseInitialData

/-!
# Actual finite-volume random-mass hard-mode EFC

This module identifies the abstract finite-volume eigenfunction correlator
used by the BHO probability argument with the ordered eigenvectors of the
actual iid random-mass harmonic matrix.  On the almost-sure simple-spectrum
event it also replaces the signed eigenvectors by the totalized ordered
spectral projectors.

Completeness of the ordered projectors and finite Cauchy--Schwarz give the
sharp model-independent annealed bound `E[EFC(x,y)] <= 1`.  This bound is
uniform in volume but contains no spatial decay.  The current one-site
spectral-averaging library supplies the sharp frozen diagonal-potential
small-ball constant `5 / (2 |lambda|)`, but not yet the off-diagonal
fractional-moment contraction needed to improve `1` to a stretched
exponential in `|x-y| / N^(2 alpha)`.
-/

namespace ArchonPhysics.FrozenRandomMassHardModeEFCBridge

open ArchonPhysics
open ArchonPhysics.BHOAnnealedEFCLocalizationBorelCantelli
open ArchonPhysics.BHORandomMassLocalizationSchedule
open ArchonPhysics.FrozenAndersonOneSiteSpectralAveraging
open ArchonPhysics.FrozenAndersonDiagonalPotentialDensity
open ArchonPhysics.GenericSpectrumResultant
open ArchonPhysics.HarmonicModes
open ArchonPhysics.MeasurableOrderedEigenframe
open ArchonPhysics.MeasurableOrderedModeCoupling.Harmonic
open ArchonPhysics.MeasurableOrderedSpectrum
open ArchonPhysics.OrderedSingleModeProjector
open ArchonPhysics.RandomMassMeasurableOrderedEigenframe
open ArchonPhysics.RandomMassOrderedProjectorBridge
open ArchonPhysics.RandomMassAndersonTransferBridge
open ArchonPhysics.RandomMassPhaseInitialData
open ArchonPhysics.RandomMassPositiveCollisionData
open MeasureTheory
open scoped ENNReal Matrix

noncomputable section

variable {Omega : Type*} [MeasurableSpace Omega]

/-- The actual BHO hard-mode predicate, transported to the natural
`Fin (n + 2)` indexing used by the probability argument. -/
def frozenRandomMassHardMode
    (ensemble : IIDMassPhaseEnsemble Omega) (alpha : Real)
    (n : Nat) (omega : Omega) (q : Fin (n + 2)) : Prop := by
  letI : NeZero (n + 2) := ⟨by omega⟩
  exact bhoHardFrequencyCutoff alpha (n + 2) <
    orderedModeFrequency
      (harmonicHermitianSample
        (ensemble.restrictPositiveMass (N := n + 2)) omega)
      ((orderedModeIndexEquivFin (n + 2)).symm q)

/-- A coordinate of the explicit measurable signed ordered eigenvector of
the actual finite-volume random-mass harmonic matrix. -/
def frozenRandomMassEigenvectorCoordinate
    (ensemble : IIDMassPhaseEnsemble Omega)
    (n : Nat) (omega : Omega) (q x : Fin (n + 2)) : Real := by
  letI : NeZero (n + 2) := ⟨by omega⟩
  exact orderedEigenvectorSample ensemble
    ((orderedModeIndexEquivFin (n + 2)).symm q) omega
    ((siteEquivFin (n + 2)).symm x)

/-- The actual finite-volume hard-mode eigenfunction correlator. -/
def frozenRandomMassHardModeEFC
    (ensemble : IIDMassPhaseEnsemble Omega) (alpha : Real)
    (n : Nat) (omega : Omega) (x y : Fin (n + 2)) : ENNReal := by
  classical
  exact ∑ q : Fin (n + 2),
    if frozenRandomMassHardMode ensemble alpha n omega q then
      ENNReal.ofReal
        |frozenRandomMassEigenvectorCoordinate ensemble n omega q x *
          frozenRandomMassEigenvectorCoordinate ensemble n omega q y|
    else 0

/-- Strict identification with the generic EFC consumed by the BHO
Markov/union-bound/Borel--Cantelli bridge. -/
theorem frozenRandomMassHardModeEFC_eq_hardEigenfunctionCorrelator
    (ensemble : IIDMassPhaseEnsemble Omega) (alpha : Real)
    (n : Nat) (omega : Omega) (x y : Fin (n + 2)) :
    frozenRandomMassHardModeEFC ensemble alpha n omega x y =
      hardEigenfunctionCorrelator
        (frozenRandomMassHardMode ensemble alpha)
        (frozenRandomMassEigenvectorCoordinate ensemble)
        n omega x y := by
  rfl

/-- The same actual EFC written entirely with ordered spectral-projector
entries.  Unlike a chosen eigenvector, this expression is globally
totalized through spectral collisions. -/
def frozenRandomMassHardModeProjectorEFC
    (ensemble : IIDMassPhaseEnsemble Omega) (alpha : Real)
    (n : Nat) (omega : Omega) (x y : Fin (n + 2)) : ENNReal := by
  classical
  letI : NeZero (n + 2) := ⟨by omega⟩
  let A := harmonicHermitianSample
    (ensemble.restrictPositiveMass (N := n + 2)) omega
  exact ∑ q : Fin (n + 2),
    if frozenRandomMassHardMode ensemble alpha n omega q then
      ENNReal.ofReal |orderedModeProjector A
        ((orderedModeIndexEquivFin (n + 2)).symm q)
        ((siteEquivFin (n + 2)).symm x)
        ((siteEquivFin (n + 2)).symm y)|
    else 0

/-- On simple spectrum, the actual signed-eigenvector EFC is exactly the
ordered-projector EFC. -/
theorem frozenRandomMassHardModeEFC_eq_projectorEFC_of_simple
    (ensemble : IIDMassPhaseEnsemble Omega) (alpha : Real)
    (n : Nat) (omega : Omega) (x y : Fin (n + 2))
    (hsimple : SimpleOrderedSpectrum
      (harmonicHermitianSample
        (ensemble.restrictPositiveMass (N := n + 2)) omega)) :
    frozenRandomMassHardModeEFC ensemble alpha n omega x y =
      frozenRandomMassHardModeProjectorEFC
        ensemble alpha n omega x y := by
  classical
  letI : NeZero (n + 2) := ⟨by omega⟩
  unfold frozenRandomMassHardModeEFC frozenRandomMassHardModeProjectorEFC
  apply Finset.sum_congr rfl
  intro q _hq
  by_cases hhard : frozenRandomMassHardMode ensemble alpha n omega q
  · simp only [if_pos hhard]
    have houter := signedOrderedEigenvector_outerProduct
      (harmonicHermitianSample
        (ensemble.restrictPositiveMass (N := n + 2)) omega)
      hsimple ((orderedModeIndexEquivFin (n + 2)).symm q)
    have hentry := congrArg (fun M : Matrix (Lattice.Site (n + 2))
        (Lattice.Site (n + 2)) Real =>
      M ((siteEquivFin (n + 2)).symm x)
        ((siteEquivFin (n + 2)).symm y)) houter
    simpa [frozenRandomMassEigenvectorCoordinate,
      orderedEigenvectorSample, Matrix.vecMulVec_apply] using
      congrArg (fun z : Real => ENNReal.ofReal |z|) hentry
  · simp [hhard]

/-- The squared coordinates of the measurable ordered frame resolve one at
every fixed lattice site whenever the spectrum is simple. -/
theorem sum_sq_frozenRandomMassEigenvectorCoordinate_eq_one_of_simple
    (ensemble : IIDMassPhaseEnsemble Omega) (n : Nat) (omega : Omega)
    (x : Fin (n + 2))
    (hsimple : SimpleOrderedSpectrum
      (harmonicHermitianSample
        (ensemble.restrictPositiveMass (N := n + 2)) omega)) :
    (∑ q : Fin (n + 2),
      |frozenRandomMassEigenvectorCoordinate ensemble n omega q x| ^ 2) = 1 := by
  classical
  letI : NeZero (n + 2) := ⟨by omega⟩
  let A := harmonicHermitianSample
    (ensemble.restrictPositiveMass (N := n + 2)) omega
  let site := (siteEquivFin (n + 2)).symm x
  calc
    (∑ q : Fin (n + 2),
        |frozenRandomMassEigenvectorCoordinate ensemble n omega q x| ^ 2) =
        ∑ k : OrderedModeIndex (n + 2),
          |signedOrderedEigenvector A k site| ^ 2 := by
      symm
      exact Fintype.sum_equiv (orderedModeIndexEquivFin (n + 2))
        (fun k : OrderedModeIndex (n + 2) =>
          |signedOrderedEigenvector A k site| ^ 2)
        (fun q : Fin (n + 2) =>
          |frozenRandomMassEigenvectorCoordinate ensemble n omega q x| ^ 2)
        (fun k => by
          simp [A, site, frozenRandomMassEigenvectorCoordinate,
            orderedEigenvectorSample])
    _ = ∑ k : OrderedModeIndex (n + 2),
        orderedModeProjector A k site site := by
      apply Finset.sum_congr rfl
      intro k _hk
      have houter := signedOrderedEigenvector_outerProduct A hsimple k
      have hentry := congrArg (fun M : Matrix (Lattice.Site (n + 2))
          (Lattice.Site (n + 2)) Real => M site site) houter
      simpa [Matrix.vecMulVec_apply, sq_abs, pow_two] using hentry
    _ = (∑ k : OrderedModeIndex (n + 2),
        orderedModeProjector A k) site site := by
      simp only [Matrix.sum_apply]
    _ = (1 : Matrix (Lattice.Site (n + 2))
        (Lattice.Site (n + 2)) Real) site site := by
      rw [orderedModeProjector_sum_eq_one A hsimple]
    _ = 1 := by simp

/-- Finite Cauchy--Schwarz and completeness give the sharp universal bound
`EFC(x,y) <= 1`, independently of the hard cutoff and the volume. -/
theorem frozenRandomMassHardModeEFC_le_one_of_simple
    (ensemble : IIDMassPhaseEnsemble Omega) (alpha : Real)
    (n : Nat) (omega : Omega) (x y : Fin (n + 2))
    (hsimple : SimpleOrderedSpectrum
      (harmonicHermitianSample
        (ensemble.restrictPositiveMass (N := n + 2)) omega)) :
    frozenRandomMassHardModeEFC ensemble alpha n omega x y <= 1 := by
  classical
  let vx : Fin (n + 2) -> Real := fun q =>
    |frozenRandomMassEigenvectorCoordinate ensemble n omega q x|
  let vy : Fin (n + 2) -> Real := fun q =>
    |frozenRandomMassEigenvectorCoordinate ensemble n omega q y|
  have hrestricted :
      (∑ q : Fin (n + 2),
        if frozenRandomMassHardMode ensemble alpha n omega q then
          vx q * vy q else 0) <= ∑ q : Fin (n + 2), vx q * vy q := by
    apply Finset.sum_le_sum
    intro q _hq
    by_cases hhard : frozenRandomMassHardMode ensemble alpha n omega q
    · simp [hhard]
    · simp [hhard, vx, vy, mul_nonneg]
  have hcauchy : (∑ q : Fin (n + 2), vx q * vy q) <= 1 := by
    calc
      (∑ q : Fin (n + 2), vx q * vy q) <=
          Real.sqrt (∑ q : Fin (n + 2), vx q ^ 2) *
            Real.sqrt (∑ q : Fin (n + 2), vy q ^ 2) :=
        Real.sum_mul_le_sqrt_mul_sqrt Finset.univ vx vy
      _ = 1 := by
        rw [show (∑ q : Fin (n + 2), vx q ^ 2) = 1 by
          simpa [vx] using
            sum_sq_frozenRandomMassEigenvectorCoordinate_eq_one_of_simple
              ensemble n omega x hsimple]
        rw [show (∑ q : Fin (n + 2), vy q ^ 2) = 1 by
          simpa [vy] using
            sum_sq_frozenRandomMassEigenvectorCoordinate_eq_one_of_simple
              ensemble n omega y hsimple]
        norm_num
  have hreal :
      (∑ q : Fin (n + 2),
        if frozenRandomMassHardMode ensemble alpha n omega q then
          |frozenRandomMassEigenvectorCoordinate ensemble n omega q x *
            frozenRandomMassEigenvectorCoordinate ensemble n omega q y|
        else 0) <= 1 := by
    simpa [vx, vy, abs_mul] using hrestricted.trans hcauchy
  unfold frozenRandomMassHardModeEFC
  have heq :
      (∑ q : Fin (n + 2),
        if frozenRandomMassHardMode ensemble alpha n omega q then
          ENNReal.ofReal
            |frozenRandomMassEigenvectorCoordinate ensemble n omega q x *
              frozenRandomMassEigenvectorCoordinate ensemble n omega q y|
        else 0) =
      ENNReal.ofReal
        (∑ q : Fin (n + 2),
          if frozenRandomMassHardMode ensemble alpha n omega q then
            |frozenRandomMassEigenvectorCoordinate ensemble n omega q x *
              frozenRandomMassEigenvectorCoordinate ensemble n omega q y|
          else 0) := by
    rw [ENNReal.ofReal_sum_of_nonneg]
    · apply Finset.sum_congr rfl
      intro q _hq
      by_cases hhard : frozenRandomMassHardMode ensemble alpha n omega q <;>
        simp [hhard]
    · intro q _hq
      split_ifs <;> positivity
  rw [heq]
  exact ENNReal.ofReal_le_one.mpr hreal

/-- Almost surely, every actual finite-volume hard-mode EFC is at most one. -/
theorem frozenRandomMassHardModeEFC_le_one_ae
    (ensemble : IIDMassPhaseEnsemble Omega) (alpha : Real) (n : Nat)
    (x y : Fin (n + 2)) :
    ∀ᵐ omega ∂ensemble.probability,
      frozenRandomMassHardModeEFC ensemble alpha n omega x y <= 1 := by
  have hN : 2 <= n + 2 := by omega
  filter_upwards [simpleOrderedSpectrum_ae ensemble hN] with omega hsimple
  exact frozenRandomMassHardModeEFC_le_one_of_simple
    ensemble alpha n omega x y hsimple

/-- The strongest unconditional annealed bound currently available for the
actual model: it is volume-uniform but has no off-diagonal decay. -/
theorem lintegral_frozenRandomMassHardModeEFC_le_one
    (ensemble : IIDMassPhaseEnsemble Omega) (alpha : Real) (n : Nat)
    (x y : Fin (n + 2)) :
    (∫⁻ omega, frozenRandomMassHardModeEFC
      ensemble alpha n omega x y ∂ensemble.probability) <= 1 := by
  let _ : IsProbabilityMeasure ensemble.probability :=
    ⟨ensemble.probability_univ⟩
  calc
    (∫⁻ omega, frozenRandomMassHardModeEFC
        ensemble alpha n omega x y ∂ensemble.probability) <=
        ∫⁻ _omega, (1 : ENNReal) ∂ensemble.probability := by
      apply lintegral_mono_ae
      exact frozenRandomMassHardModeEFC_le_one_ae ensemble alpha n x y
    _ = 1 := by simp

/-- Canonical iid `Uniform[4/5,6/5]` specialization of the unconditional
annealed bound. -/
theorem canonical_lintegral_frozenRandomMassHardModeEFC_le_one
    (alpha : Real) (n : Nat) (x y : Fin (n + 2)) :
    (∫⁻ omega, frozenRandomMassHardModeEFC
      canonicalIIDMassPhaseEnsemble alpha n omega x y
      ∂(RandomEnsemble.canonicalLaw)) <= 1 :=
  lintegral_frozenRandomMassHardModeEFC_le_one
    canonicalIIDMassPhaseEnsemble alpha n x y

/-- The exact sharp one-site small-ball input already proved for the frozen
Anderson diagonal potential.  It is an input to, but not a substitute for,
the missing off-diagonal fractional-moment contraction. -/
theorem frozenDiagonalPotentialSmallBall_le
    {lambda a b : Real} (hlambda : lambda ≠ 0) :
    andersonDiagonalPotentialLaw lambda (Set.Icc a b) <=
      ((5 / 2 : ENNReal) * ENNReal.ofReal |lambda|⁻¹) *
        ENNReal.ofReal (b - a) :=
  andersonDiagonalPotentialLaw_Icc_le_fiveHalves hlambda

/-- Reduction of the BHO model premise to the actual ordered-projector EFC.
The raw hypothesis below is the remaining model theorem: an off-diagonal
fractional-moment contraction for the frozen iid random-mass operator. -/
theorem lintegral_frozenRandomMassHardModeEFC_le_of_projectorContraction
    (ensemble : IIDMassPhaseEnsemble Omega) (alpha : Real) (n : Nat)
    (x y : Fin (n + 2)) (bound : ENNReal)
    (hcontraction :
      (∫⁻ omega, frozenRandomMassHardModeProjectorEFC
        ensemble alpha n omega x y ∂ensemble.probability) <= bound) :
    (∫⁻ omega, frozenRandomMassHardModeEFC
      ensemble alpha n omega x y ∂ensemble.probability) <= bound := by
  have heq : ∀ᵐ omega ∂ensemble.probability,
      frozenRandomMassHardModeEFC ensemble alpha n omega x y =
        frozenRandomMassHardModeProjectorEFC
          ensemble alpha n omega x y := by
    have hN : 2 <= n + 2 := by omega
    filter_upwards [simpleOrderedSpectrum_ae ensemble hN] with omega hsimple
    exact frozenRandomMassHardModeEFC_eq_projectorEFC_of_simple
      ensemble alpha n omega x y hsimple
  rw [lintegral_congr_ae heq]
  exact hcontraction

end

end ArchonPhysics.FrozenRandomMassHardModeEFCBridge
