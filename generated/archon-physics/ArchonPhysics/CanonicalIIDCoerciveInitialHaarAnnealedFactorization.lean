import ArchonPhysics.CanonicalIIDCoerciveInitialHaarBlockFactorization

/-!
# Annealed initial Haar factorization with the exact mass remainder

The canonical sample is the product of the iid mass sequence and the iid
Haar phase sequence.  This module uses that actual product law to evaluate
the time-zero signed block Bochner integral and then computes the exact
two-block factorization defect.

Phase separation alone removes every sector in which at least one block has
nonzero aggregate charge.  If both blocks are charge-balanced, however, the
defect is precisely the covariance of their mass-dependent ordered-frequency
radii.  Since random-mass normal modes are global functions of the common
mass configuration, this covariance is retained rather than assumed zero.
-/

namespace ArchonPhysics.CanonicalIIDCoerciveInitialHaarAnnealedFactorization

open scoped BigOperators Matrix

open ArchonPhysics
open ArchonPhysics.CanonicalIIDCoerciveContinuousMomentFrontier
open ArchonPhysics.CanonicalIIDCoerciveInitialHaarBlockFactorization
open ArchonPhysics.CanonicalIIDCoerciveSignedModalHierarchy
open ArchonPhysics.CanonicalIIDCoerciveSignedModalObservableBridge
open ArchonPhysics.FiniteEnsemblePhaseMoments
open ArchonPhysics.FinitePhaseMonomials
open ArchonPhysics.FreeFPUTInitialHaarDisjointClusterFactorization
open ArchonPhysics.MeasurableOrderedModeCoupling.Harmonic
open ArchonPhysics.MeasurableOrderedSpectrum
open ArchonPhysics.OrderedSingleModeProjector
open ArchonPhysics.OrderedTranslationLastMode
open ArchonPhysics.RandomMassOrderedProjectorBridge
open ArchonPhysics.RandomMassPositiveCollisionData
open MeasureTheory ProbabilityTheory

noncomputable section

variable {N : Nat} [NeZero N]
variable {I : Type*} [Fintype I] [DecidableEq I]

theorem canonicalInitialRadialBlockCoefficient_phase_irrelevant
    (a : Real) (entry : I → PhaseSign × OrderedModeIndex N)
    (block : Finset I) (raw : RandomEnsemble.RawMassSequence)
    (phase : RandomEnsemble.PhaseSequence) :
    canonicalInitialRadialBlockCoefficient (N := N)
        a entry block (raw, phase) =
      canonicalInitialRadialBlockCoefficient (N := N)
        a entry block (raw, 0) := by
  rfl

theorem canonicalInitialBlockPhaseCharacter_mass_irrelevant
    (entry : I → PhaseSign × OrderedModeIndex N)
    (block : Finset I) (raw : RandomEnsemble.RawMassSequence)
    (phase : RandomEnsemble.PhaseSequence) :
    canonicalInitialBlockPhaseCharacter (N := N)
        entry block (raw, phase) =
      canonicalInitialBlockPhaseCharacter (N := N)
        entry block (0, phase) := by
  rfl

/-- The radial coefficient and the Haar character are independent under the
actual canonical product law. -/
theorem indepFun_canonicalInitialRadialBlockCoefficient_phaseCharacter
    (a : Real) (entry : I → PhaseSign × OrderedModeIndex N)
    (block : Finset I) :
    IndepFun
      (canonicalInitialRadialBlockCoefficient (N := N) a entry block)
      (canonicalInitialBlockPhaseCharacter (N := N) entry block)
      canonicalIIDMassPhaseEnsemble.probability := by
  let radial : RandomEnsemble.RawMassSequence → Complex :=
    fun raw => canonicalInitialRadialBlockCoefficient (N := N)
      a entry block (raw, 0)
  let character : RandomEnsemble.PhaseSequence → Complex :=
    fun phase => canonicalInitialBlockPhaseCharacter (N := N)
      entry block (0, phase)
  have hradial : Measurable radial :=
    (measurable_canonicalInitialRadialBlockCoefficient
      (N := N) a entry block).comp
        (measurable_id.prodMk measurable_const)
  have hcharacter : Measurable character :=
    (measurable_canonicalInitialBlockPhaseCharacter
      (N := N) entry block).comp
        (measurable_const.prodMk measurable_id)
  have hindep :
      (fun omega : RandomEnsemble.SampleSpace => radial omega.1) ⟂ᵢ[
        RandomEnsemble.massSequenceLaw.prod RandomEnsemble.phaseSequenceLaw]
      (fun omega : RandomEnsemble.SampleSpace => character omega.2) :=
    ProbabilityTheory.indepFun_prod hradial hcharacter
  change IndepFun _ _
    (RandomEnsemble.massSequenceLaw.prod RandomEnsemble.phaseSequenceLaw)
  refine hindep.congr ?_ ?_
  · filter_upwards with omega
    exact (canonicalInitialRadialBlockCoefficient_phase_irrelevant
      (N := N) a entry block omega.1 omega.2).symm
  · filter_upwards with omega
    exact (canonicalInitialBlockPhaseCharacter_mass_irrelevant
      (N := N) entry block omega.1 omega.2).symm

/-- Exact all-mode Haar selector for the actual initial phase character. -/
theorem integral_canonicalInitialBlockPhaseCharacter_eq_selector
    (entry : I → PhaseSign × OrderedModeIndex N)
    (block : Finset I) :
    (∫ omega, canonicalInitialBlockPhaseCharacter (N := N)
        entry block omega
      ∂canonicalIIDMassPhaseEnsemble.probability) =
      if canonicalOrderedSignedBlockCharge (N := N) entry block = 0
        then 1 else 0 := by
  exact restrictPhase_mFourier_expectation canonicalIIDMassPhaseEnsemble
    (canonicalOrderedSignedBlockCharge (N := N) entry block)

/-- Exact arbitrary-finite-order initial moment of the actual canonical
signed modal block. -/
theorem canonicalSignedBlockBochnerIntegral_zero_eq_radialMean_mul_selector
    (hN : 3 ≤ N) {a : Real} (ha0 : 0 ≤ a) (ha1 : a ≤ 1 / 4)
    (kappa beta g : Real) (hbeta : 2 * kappa ^ 2 / 9 < beta)
    (entry : I → PhaseSign × OrderedModeIndex N)
    (hpositive : ∀ i, (entry i).2 ≠
      lastOrderedIndex (ι := Lattice.Site N))
    (block : Finset I) :
    canonicalSignedBlockBochnerIntegral (N := N)
        kappa beta g hbeta a entry block 0 =
      if canonicalOrderedSignedBlockCharge (N := N) entry block = 0 then
        canonicalInitialRadialBlockMean (N := N) a entry block else 0 := by
  have hproduct :
      (∫ omega, canonicalInitialRadialBlockCoefficient (N := N)
          a entry block omega *
        canonicalInitialBlockPhaseCharacter (N := N) entry block omega
        ∂canonicalIIDMassPhaseEnsemble.probability) =
      canonicalInitialRadialBlockMean (N := N) a entry block *
        (∫ omega, canonicalInitialBlockPhaseCharacter (N := N)
            entry block omega
          ∂canonicalIIDMassPhaseEnsemble.probability) := by
    simpa [canonicalInitialRadialBlockMean] using
      (indepFun_canonicalInitialRadialBlockCoefficient_phaseCharacter
        (N := N) a entry block).integral_mul_eq_mul_integral
          (measurable_canonicalInitialRadialBlockCoefficient
            (N := N) a entry block).aestronglyMeasurable
          (measurable_canonicalInitialBlockPhaseCharacter
            (N := N) entry block).aestronglyMeasurable
  rw [canonicalSignedBlockBochnerIntegral]
  calc
    (∫ omega, canonicalSignedBlockObservable (N := N)
        kappa beta g hbeta a entry block (omega, 0)
        ∂canonicalIIDMassPhaseEnsemble.probability) =
      ∫ omega, canonicalInitialRadialBlockCoefficient (N := N)
          a entry block omega *
        canonicalInitialBlockPhaseCharacter (N := N) entry block omega
        ∂canonicalIIDMassPhaseEnsemble.probability := by
      apply integral_congr_ae
      filter_upwards [
        simpleOrderedSpectrum_ae (N := N)
          canonicalIIDMassPhaseEnsemble (by omega)] with omega hsimple
      apply canonicalSignedBlockObservable_zero_of_simple
        hN ha0 ha1 kappa beta g hbeta entry hpositive block omega
      simpa [harmonicHermitianSample, harmonicHermitian, canonicalMass]
        using hsimple
    _ = canonicalInitialRadialBlockMean (N := N) a entry block *
        (∫ omega, canonicalInitialBlockPhaseCharacter (N := N)
            entry block omega
          ∂canonicalIIDMassPhaseEnsemble.probability) := hproduct
    _ = _ := by
      rw [integral_canonicalInitialBlockPhaseCharacter_eq_selector]
      split <;> simp_all

end

end ArchonPhysics.CanonicalIIDCoerciveInitialHaarAnnealedFactorization
