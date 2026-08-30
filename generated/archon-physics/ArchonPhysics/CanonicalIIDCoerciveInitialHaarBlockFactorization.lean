import ArchonPhysics.CanonicalIIDCoerciveInitialHaarBlockMoment

/-!
# Canonical initial Haar selector and the surviving mass covariance

This file evaluates the time-zero canonical signed block Bochner integral for
an arbitrary finite signed block of actual ordered modes.  The result is an
exact product of:

* the annealed expectation of the mass-dependent radial coefficient; and
* the product-Haar selector of the complete ordered-mode phase charge.

For two disjoint index blocks whose aggregate phase-charge supports are
disjoint, the factorization defect is exactly the two Haar selectors times
the covariance of their random radial coefficients.  Hence an unbalanced
block gives exact zero defect, while a balanced--balanced pair is not
silently declared independent: its common random-mass covariance remains.

All statements are at time zero.  They do not assert positive-time RPA,
decoherence, closure, or decay.
-/

namespace ArchonPhysics.CanonicalIIDCoerciveInitialHaarBlockFactorization

open scoped BigOperators Matrix

open ArchonPhysics
open ArchonPhysics.CanonicalIIDCoerciveActualExpectationCompleted
open ArchonPhysics.CanonicalIIDCoerciveContinuousMomentFrontier
open ArchonPhysics.CanonicalIIDCoerciveInitialHaarBlockMoment
open ArchonPhysics.CanonicalIIDCoerciveSignedModalHierarchy
open ArchonPhysics.CanonicalIIDCoerciveSignedModalObservableBridge
open ArchonPhysics.FiniteEnsemblePhaseMoments
open ArchonPhysics.FinitePhaseMonomials
open ArchonPhysics.FreeFPUTInitialHaarDisjointClusterFactorization
open ArchonPhysics.OrderedTranslationLastMode
open ArchonPhysics.MeasurableOrderedSpectrum
open ArchonPhysics.MeasurableOrderedModeCoupling.Harmonic
open ArchonPhysics.OrderedSingleModeProjector
open ArchonPhysics.PhaseEnergyModeCoordinates
open ArchonPhysics.PhyslibFPUTBinaryInteractionTreeCouples
open ArchonPhysics.RandomMassPhaseInitialData
open ArchonPhysics.RandomMassPositiveCollisionData
open MeasureTheory ProbabilityTheory UnitAddTorus

noncomputable section

variable {N : Nat} [NeZero N]
variable {I : Type*} [Fintype I] [DecidableEq I]

/-- The lattice phase coordinate assigned to one ordered-mode entry. -/
def canonicalOrderedSignedMode
    (entry : PhaseSign × OrderedModeIndex N) :
    SignedMode (Lattice.Site N) :=
  ⟨ZMod.finEquiv N (orderedModeIndexEquivFin N entry.2), entry.1⟩

/-- Complete all-mode phase charge of a finite ordered signed block. -/
def canonicalOrderedSignedBlockCharge
    (entry : I → PhaseSign × OrderedModeIndex N)
    (block : Finset I) : Lattice.Site N → Int :=
  ∑ i ∈ block, (canonicalOrderedSignedMode (N := N) (entry i)).charge

/-- Mass-dependent real radial coefficient of a finite signed block.  The
sign does not alter it because the radius is real. -/
def canonicalInitialRadialBlockCoefficient
    (a : Real) (entry : I → PhaseSign × OrderedModeIndex N)
    (block : Finset I) (omega : CanonicalSample) : Complex :=
  ∏ i ∈ block,
    (canonicalInitialOrderedRadius (N := N) a (entry i).2 omega : Complex)

/-- The exact finite Fourier character carried by the block's initial Haar
phases. -/
def canonicalInitialBlockPhaseCharacter
    (entry : I → PhaseSign × OrderedModeIndex N)
    (block : Finset I) (omega : CanonicalSample) : Complex :=
  mFourier (canonicalOrderedSignedBlockCharge (N := N) entry block)
    (canonicalIIDMassPhaseEnsemble.restrictPhase omega)

/-- Annealed mean of the mass-dependent block radius. -/
def canonicalInitialRadialBlockMean
    (a : Real) (entry : I → PhaseSign × OrderedModeIndex N)
    (block : Finset I) : Complex :=
  ∫ omega, canonicalInitialRadialBlockCoefficient (N := N)
      a entry block omega
    ∂canonicalIIDMassPhaseEnsemble.probability

omit [Fintype I] [DecidableEq I] in
theorem canonical_finEquiv_val (i : Fin N) :
    (ZMod.finEquiv N i).val = i.val := by
  cases N with
  | zero => exact (NeZero.ne 0 rfl).elim
  | succ n => rfl

omit [Fintype I] [DecidableEq I] in
theorem orderedPhaseSample_eq_restrictPhase
    (omega : CanonicalSample) (k : OrderedModeIndex N) :
    orderedPhaseSample canonicalIIDMassPhaseEnsemble omega k =
      canonicalIIDMassPhaseEnsemble.restrictPhase omega
        (ZMod.finEquiv N (orderedModeIndexEquivFin N k)) := by
  simp [orderedPhaseSample, IIDMassPhaseEnsemble.restrictPhase,
    canonicalIIDMassPhaseEnsemble, RandomEnsemble.phaseAt,
    canonical_finEquiv_val]

omit [Fintype I] [DecidableEq I] in
theorem phaseSignActComplex_unitPhase_eq_orderedCharacter
    (omega : CanonicalSample)
    (entry : PhaseSign × OrderedModeIndex N) :
    phaseSignActComplex entry.1
        (unitPhase
          (orderedPhaseSample canonicalIIDMassPhaseEnsemble omega entry.2)) =
      mFourier (canonicalOrderedSignedMode (N := N) entry).charge
        (canonicalIIDMassPhaseEnsemble.restrictPhase omega) := by
  rw [orderedPhaseSample_eq_restrictPhase]
  exact SignedMode.phaseFactor_eq_mFourier
    (canonicalOrderedSignedMode (N := N) entry)
    (canonicalIIDMassPhaseEnsemble.restrictPhase omega)

omit [Fintype I] [DecidableEq I] in
theorem canonicalSignedInteractionAmplitude_zero_of_simple
    (hN : 3 ≤ N) {a : Real} (ha0 : 0 ≤ a) (ha1 : a ≤ 1 / 4)
    (kappa beta g : Real) (hbeta : 2 * kappa ^ 2 / 9 < beta)
    (omega : CanonicalSample)
    (hsimple : SimpleOrderedSpectrum
      (harmonicHermitian (canonicalMass (N := N) omega)))
    (entry : PhaseSign × OrderedModeIndex N)
    (hentry : entry.2 ≠ lastOrderedIndex (ι := Lattice.Site N)) :
    canonicalSignedInteractionAmplitude (N := N)
        kappa beta g hbeta a entry (omega, 0) =
      (canonicalInitialOrderedRadius (N := N) a entry.2 omega : Complex) *
        mFourier (canonicalOrderedSignedMode (N := N) entry).charge
          (canonicalIIDMassPhaseEnsemble.restrictPhase omega) := by
  unfold canonicalSignedInteractionAmplitude
  rw [
    canonicalInteractionAmplitude_zero_of_simple
      hN ha0 ha1 kappa beta g hbeta omega hsimple entry.2 hentry]
  have hphase := phaseSignActComplex_unitPhase_eq_orderedCharacter
    (N := N) omega entry
  have hreal :
      phaseSignActComplex entry.1
          ((canonicalInitialOrderedRadius (N := N) a entry.2 omega : Complex) *
            unitPhase (orderedPhaseSample canonicalIIDMassPhaseEnsemble omega entry.2)) =
        (canonicalInitialOrderedRadius (N := N) a entry.2 omega : Complex) *
          phaseSignActComplex entry.1
            (unitPhase (orderedPhaseSample canonicalIIDMassPhaseEnsemble omega entry.2)) := by
    cases entry.1 <;> simp [phaseSignActComplex]
  rw [hreal, hphase]

theorem canonicalSignedBlockObservable_zero_of_simple
    (hN : 3 ≤ N) {a : Real} (ha0 : 0 ≤ a) (ha1 : a ≤ 1 / 4)
    (kappa beta g : Real) (hbeta : 2 * kappa ^ 2 / 9 < beta)
    (entry : I → PhaseSign × OrderedModeIndex N)
    (hpositive : ∀ i, (entry i).2 ≠
      lastOrderedIndex (ι := Lattice.Site N))
    (block : Finset I) (omega : CanonicalSample)
    (hsimple : SimpleOrderedSpectrum
      (harmonicHermitian (canonicalMass (N := N) omega))) :
    canonicalSignedBlockObservable (N := N)
        kappa beta g hbeta a entry block (omega, 0) =
      canonicalInitialRadialBlockCoefficient (N := N) a entry block omega *
        canonicalInitialBlockPhaseCharacter (N := N) entry block omega := by
  classical
  induction block using Finset.induction with
  | empty =>
      simp [canonicalSignedBlockObservable,
        canonicalInitialRadialBlockCoefficient,
        canonicalInitialBlockPhaseCharacter,
        canonicalOrderedSignedBlockCharge, mFourier_zero]
  | @insert i block hi ih =>
      rw [show canonicalSignedBlockObservable (N := N)
          kappa beta g hbeta a entry (insert i block) (omega, 0) =
          canonicalSignedInteractionAmplitude (N := N)
              kappa beta g hbeta a (entry i) (omega, 0) *
            canonicalSignedBlockObservable (N := N)
              kappa beta g hbeta a entry block (omega, 0) by
        simp [canonicalSignedBlockObservable, hi]]
      rw [canonicalSignedInteractionAmplitude_zero_of_simple
        hN ha0 ha1 kappa beta g hbeta omega hsimple (entry i) (hpositive i),
        ih]
      unfold canonicalInitialRadialBlockCoefficient
        canonicalInitialBlockPhaseCharacter
        canonicalOrderedSignedBlockCharge
      rw [Finset.prod_insert hi]
      simp only [Finset.mem_insert, true_or, Finset.sum_insert hi]
      rw [mFourier_add]
      ring

theorem measurable_canonicalInitialOrderedRadius
    (a : Real) (k : OrderedModeIndex N) :
    Measurable (canonicalInitialOrderedRadius (N := N) a k) := by
  unfold canonicalInitialOrderedRadius
  exact Measurable.sqrt (measurable_const.div
    (measurable_canonicalOrderedFrequency (N := N) k))

theorem measurable_canonicalInitialRadialBlockCoefficient
    (a : Real) (entry : I → PhaseSign × OrderedModeIndex N)
    (block : Finset I) :
    Measurable (canonicalInitialRadialBlockCoefficient (N := N)
      a entry block) := by
  unfold canonicalInitialRadialBlockCoefficient
  apply Finset.measurable_prod
  intro i _hi
  exact Complex.measurable_ofReal.comp
    (measurable_canonicalInitialOrderedRadius (N := N) a (entry i).2)

theorem measurable_canonicalInitialBlockPhaseCharacter
    (entry : I → PhaseSign × OrderedModeIndex N)
    (block : Finset I) :
    Measurable (canonicalInitialBlockPhaseCharacter (N := N)
      entry block) := by
  exact (mFourier
    (canonicalOrderedSignedBlockCharge (N := N) entry block)).continuous.measurable.comp
      canonicalIIDMassPhaseEnsemble.measurable_restrictPhase

end

end ArchonPhysics.CanonicalIIDCoerciveInitialHaarBlockFactorization
