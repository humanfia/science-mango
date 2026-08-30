import ArchonPhysics.CanonicalIIDCoerciveInitialHaarFactorizationDefect

/-!
# Quenched initial Haar factorization at fixed mass

This module conditions on one raw mass sequence and integrates only over the
iid Haar phase sequence.  At time zero every finite signed ordered-mode block
therefore has quenched moment

    fixed radial coefficient * complete Haar charge selector.

For two disjoint index blocks with disjoint aggregate charge supports, the
selector factorizes exactly.  The radial coefficient is deterministic after
conditioning on the mass and factorizes over the disjoint union, so the
quenched factorization defect is exactly zero in every charge sector,
including balanced--balanced.

This statement does not identify the corresponding annealed defect with zero:
averaging over the shared random mass can leave the radial covariance proved
in `CanonicalIIDCoerciveInitialHaarFactorizationDefect`.
-/

namespace ArchonPhysics.CanonicalIIDCoerciveInitialHaarQuenchedFactorization

open scoped BigOperators Matrix

open ArchonPhysics
open ArchonPhysics.CanonicalIIDCoerciveContinuousMomentFrontier
open ArchonPhysics.CanonicalIIDCoerciveInitialHaarBlockFactorization
open ArchonPhysics.CanonicalIIDCoerciveInitialHaarFactorizationDefect
open ArchonPhysics.CanonicalIIDCoerciveSignedModalHierarchy
open ArchonPhysics.CanonicalIIDCoerciveSignedModalObservableBridge
open ArchonPhysics.FiniteEnsemblePhaseMoments
open ArchonPhysics.FinitePhaseMonomials
open ArchonPhysics.FreeFPUTInitialHaarDisjointClusterFactorization
open ArchonPhysics.MeasurableOrderedModeCoupling.Harmonic
open ArchonPhysics.MeasurableOrderedSpectrum
open ArchonPhysics.OrderedSingleModeProjector
open ArchonPhysics.OrderedTranslationLastMode
open ArchonPhysics.PhyslibFPUTHigherOrderClusterFactorizationPropagation
open ArchonPhysics.RandomMassPositiveCollisionData
open ArchonPhysics.RandomPhaseMoments
open MeasureTheory ProbabilityTheory UnitAddTorus

noncomputable section

variable {N : Nat} [NeZero N]
variable {I : Type*} [Fintype I] [DecidableEq I]

/-- Restriction of the infinite iid phase sequence to the periodic chain. -/
def canonicalQuenchedPhaseRestriction
    (phase : RandomEnsemble.PhaseSequence) : UnitAddTorus (Lattice.Site N) :=
  fun i => phase i.val

theorem measurable_canonicalQuenchedPhaseRestriction :
    Measurable (canonicalQuenchedPhaseRestriction (N := N)) := by
  exact measurable_pi_lambda _ fun i => measurable_pi_apply i.val

omit [Fintype I] [DecidableEq I] in
theorem quenchedPhaseCoordinate_hasLaw (i : Lattice.Site N) :
    HasLaw (fun phase : RandomEnsemble.PhaseSequence => phase i.val)
      RandomEnsemble.phaseCoordinateLaw RandomEnsemble.phaseSequenceLaw := by
  exact (measurePreserving_eval_infinitePi
    (fun _ : Nat => RandomEnsemble.phaseCoordinateLaw) i.val).hasLaw

omit [Fintype I] [DecidableEq I] in
theorem quenchedPhaseCoordinates_iIndep :
    iIndepFun
      (fun (i : Lattice.Site N) (phase : RandomEnsemble.PhaseSequence) =>
        phase i.val)
      RandomEnsemble.phaseSequenceLaw := by
  unfold RandomEnsemble.phaseSequenceLaw
  exact (iIndepFun_infinitePi
    (fun _ : Nat => measurable_id)).precomp (ZMod.val_injective N)

omit [Fintype I] [DecidableEq I] in
/-- The finite phase restriction at fixed mass has normalized product Haar
law. -/
theorem canonicalQuenchedPhaseRestriction_hasLaw_finitePhaseHaarLaw :
    HasLaw (canonicalQuenchedPhaseRestriction (N := N))
      (finitePhaseHaarLaw (Lattice.Site N))
      RandomEnsemble.phaseSequenceLaw := by
  have hJoint :
      HasLaw (canonicalQuenchedPhaseRestriction (N := N))
        (Measure.infinitePi
          (fun _ : Lattice.Site N => RandomEnsemble.phaseCoordinateLaw))
        RandomEnsemble.phaseSequenceLaw := by
    apply quenchedPhaseCoordinates_iIndep (N := N) |>.hasLaw_infinitePi
    · exact quenchedPhaseCoordinate_hasLaw (N := N)
    · exact measurable_canonicalQuenchedPhaseRestriction
        (N := N) |>.aemeasurable
  rw [finitePhaseProductLaw_eq_finitePhaseHaarLaw] at hJoint
  exact hJoint

omit [Fintype I] [DecidableEq I] in
/-- Exact charge selector under the phase law with the mass frozen. -/
theorem integral_mFourier_canonicalQuenchedPhaseRestriction_eq_selector
    (charge : Lattice.Site N -> Int) :
    (integral RandomEnsemble.phaseSequenceLaw
      (fun phase : RandomEnsemble.PhaseSequence =>
        mFourier charge
          (canonicalQuenchedPhaseRestriction (N := N) phase))) =
      if charge = 0 then 1 else 0 := by
  calc
    (integral RandomEnsemble.phaseSequenceLaw
        (fun phase : RandomEnsemble.PhaseSequence =>
          mFourier charge
            (canonicalQuenchedPhaseRestriction (N := N) phase))) =
      integral (finitePhaseHaarLaw (Lattice.Site N)) (mFourier charge) := by
        simpa [Function.comp_def] using
          (canonicalQuenchedPhaseRestriction_hasLaw_finitePhaseHaarLaw
            (N := N)).integral_comp
              (mFourier charge).continuous.aestronglyMeasurable
    _ = if charge = 0 then 1 else 0 := integral_mFourier_eq_ite charge

/-- The time-zero signed block moment conditioned on one raw mass sequence. -/
def canonicalQuenchedSignedBlockMoment
    (raw : RandomEnsemble.RawMassSequence)
    (kappa beta g : Real) (hbeta : 2 * kappa ^ 2 / 9 < beta)
    (a : Real) (entry : I -> PhaseSign × OrderedModeIndex N)
    (block : Finset I) : Complex :=
  integral RandomEnsemble.phaseSequenceLaw
    (fun phase : RandomEnsemble.PhaseSequence =>
      canonicalSignedBlockObservable (N := N)
        kappa beta g hbeta a entry block ((raw, phase), 0))

/-- At fixed raw mass, the radial block coefficient is independent of the
phase sequence. -/
theorem canonicalInitialRadialBlockCoefficient_fixedRaw
    (a : Real) (entry : I -> PhaseSign × OrderedModeIndex N)
    (block : Finset I) (raw : RandomEnsemble.RawMassSequence)
    (phase : RandomEnsemble.PhaseSequence) :
    canonicalInitialRadialBlockCoefficient (N := N)
        a entry block (raw, phase) =
      canonicalInitialRadialBlockCoefficient (N := N)
        a entry block (raw, 0) := by
  rfl

/-- At fixed raw mass, the initial phase character is the Fourier character
of the finite restriction of the supplied phase sequence. -/
theorem canonicalInitialBlockPhaseCharacter_fixedRaw
    (entry : I -> PhaseSign × OrderedModeIndex N)
    (block : Finset I) (raw : RandomEnsemble.RawMassSequence)
    (phase : RandomEnsemble.PhaseSequence) :
    canonicalInitialBlockPhaseCharacter (N := N)
        entry block (raw, phase) =
      mFourier (canonicalOrderedSignedBlockCharge (N := N) entry block)
        (canonicalQuenchedPhaseRestriction (N := N) phase) := by
  rfl

/-- Exact arbitrary-order quenched time-zero block moment: one fixed radial
coefficient times the complete Haar charge selector. -/
theorem canonicalQuenchedSignedBlockMoment_eq_radial_mul_selector
    (hN : 3 <= N) {a : Real} (ha0 : 0 <= a) (ha1 : a <= 1 / 4)
    (raw : RandomEnsemble.RawMassSequence)
    (hsimple : SimpleOrderedSpectrum
      (harmonicHermitian (canonicalMass (N := N) (raw, 0))))
    (kappa beta g : Real) (hbeta : 2 * kappa ^ 2 / 9 < beta)
    (entry : I -> PhaseSign × OrderedModeIndex N)
    (hpositive : forall i, (entry i).2 ≠
      lastOrderedIndex (ι := Lattice.Site N))
    (block : Finset I) :
    canonicalQuenchedSignedBlockMoment (N := N)
        raw kappa beta g hbeta a entry block =
      canonicalInitialRadialBlockCoefficient (N := N)
          a entry block (raw, 0) *
        (if canonicalOrderedSignedBlockCharge (N := N) entry block = 0
          then 1 else 0) := by
  unfold canonicalQuenchedSignedBlockMoment
  calc
    (integral RandomEnsemble.phaseSequenceLaw
        (fun phase : RandomEnsemble.PhaseSequence =>
          canonicalSignedBlockObservable (N := N)
            kappa beta g hbeta a entry block ((raw, phase), 0))) =
      integral RandomEnsemble.phaseSequenceLaw
        (fun phase : RandomEnsemble.PhaseSequence =>
          canonicalInitialRadialBlockCoefficient (N := N)
              a entry block (raw, phase) *
            canonicalInitialBlockPhaseCharacter (N := N)
              entry block (raw, phase)) := by
          apply integral_congr_ae
          filter_upwards with phase
          apply canonicalSignedBlockObservable_zero_of_simple
            hN ha0 ha1 kappa beta g hbeta entry hpositive block (raw, phase)
          have hmass : canonicalMass (N := N) (raw, phase) =
              canonicalMass (N := N) (raw, 0) := by rfl
          rw [hmass]
          exact hsimple
    _ = integral RandomEnsemble.phaseSequenceLaw
        (fun phase : RandomEnsemble.PhaseSequence =>
          canonicalInitialRadialBlockCoefficient (N := N)
              a entry block (raw, 0) *
            mFourier
              (canonicalOrderedSignedBlockCharge (N := N) entry block)
              (canonicalQuenchedPhaseRestriction (N := N) phase)) := by
          apply integral_congr_ae
          filter_upwards with phase
          rw [canonicalInitialRadialBlockCoefficient_fixedRaw,
            canonicalInitialBlockPhaseCharacter_fixedRaw]
    _ = canonicalInitialRadialBlockCoefficient (N := N)
          a entry block (raw, 0) *
        integral RandomEnsemble.phaseSequenceLaw
          (fun phase : RandomEnsemble.PhaseSequence =>
            mFourier
              (canonicalOrderedSignedBlockCharge (N := N) entry block)
              (canonicalQuenchedPhaseRestriction (N := N) phase)) := by
            rw [integral_const_mul]
    _ = canonicalInitialRadialBlockCoefficient (N := N)
          a entry block (raw, 0) *
        (if canonicalOrderedSignedBlockCharge (N := N) entry block = 0
          then 1 else 0) := by
            rw [integral_mFourier_canonicalQuenchedPhaseRestriction_eq_selector]

/-- Quenched two-block factorization defect at time zero. -/
def canonicalQuenchedClusterFactorizationDefect
    (raw : RandomEnsemble.RawMassSequence)
    (kappa beta g : Real) (hbeta : 2 * kappa ^ 2 / 9 < beta)
    (a : Real) (entry : I -> PhaseSign × OrderedModeIndex N)
    (left right : Finset I) : Complex :=
  canonicalQuenchedSignedBlockMoment (N := N)
      raw kappa beta g hbeta a entry (left ∪ right) -
    canonicalQuenchedSignedBlockMoment (N := N)
        raw kappa beta g hbeta a entry left *
      canonicalQuenchedSignedBlockMoment (N := N)
        raw kappa beta g hbeta a entry right

/-- Radial coefficients multiply over disjoint index blocks once the mass is
fixed. -/
theorem canonicalInitialRadialBlockCoefficient_union
    (a : Real) (entry : I -> PhaseSign × OrderedModeIndex N)
    {left right : Finset I} (hindex : Disjoint left right)
    (omega : CanonicalSample) :
    canonicalInitialRadialBlockCoefficient (N := N)
        a entry (left ∪ right) omega =
      canonicalInitialRadialBlockCoefficient (N := N) a entry left omega *
        canonicalInitialRadialBlockCoefficient (N := N)
          a entry right omega := by
  unfold canonicalInitialRadialBlockCoefficient
  rw [Finset.prod_union hindex]

/-- Exact quenched factorization for phase-separated blocks.  Unlike the
annealed statement, balanced--balanced blocks also factorize because the
shared mass has been conditioned on and is no longer random. -/
theorem canonicalQuenchedClusterFactorizationDefect_eq_zero
    (hN : 3 <= N) {a : Real} (ha0 : 0 <= a) (ha1 : a <= 1 / 4)
    (raw : RandomEnsemble.RawMassSequence)
    (hsimple : SimpleOrderedSpectrum
      (harmonicHermitian (canonicalMass (N := N) (raw, 0))))
    (kappa beta g : Real) (hbeta : 2 * kappa ^ 2 / 9 < beta)
    (entry : I -> PhaseSign × OrderedModeIndex N)
    (hpositive : forall i, (entry i).2 ≠
      lastOrderedIndex (ι := Lattice.Site N))
    {left right : Finset I} (hindex : Disjoint left right)
    (hcharge : Disjoint
      (Function.support
        (canonicalOrderedSignedBlockCharge (N := N) entry left))
      (Function.support
        (canonicalOrderedSignedBlockCharge (N := N) entry right))) :
    canonicalQuenchedClusterFactorizationDefect (N := N)
        raw kappa beta g hbeta a entry left right = 0 := by
  let leftCharge :=
    canonicalOrderedSignedBlockCharge (N := N) entry left
  let rightCharge :=
    canonicalOrderedSignedBlockCharge (N := N) entry right
  have hunion :
      canonicalOrderedSignedBlockCharge (N := N) entry (left ∪ right) =
        leftCharge + rightCharge :=
    canonicalOrderedSignedBlockCharge_union entry hindex
  have hradial := canonicalInitialRadialBlockCoefficient_union
    (N := N) a entry hindex (raw, 0)
  unfold canonicalQuenchedClusterFactorizationDefect
  rw [
    canonicalQuenchedSignedBlockMoment_eq_radial_mul_selector
      hN ha0 ha1 raw hsimple kappa beta g hbeta entry hpositive (left ∪ right),
    canonicalQuenchedSignedBlockMoment_eq_radial_mul_selector
      hN ha0 ha1 raw hsimple kappa beta g hbeta entry hpositive left,
    canonicalQuenchedSignedBlockMoment_eq_radial_mul_selector
      hN ha0 ha1 raw hsimple kappa beta g hbeta entry hpositive right,
    hunion, hradial]
  rw [haarChargeSelector_add_eq_mul_of_disjoint_support
    leftCharge rightCharge hcharge]
  simp only [leftCharge, rightCharge]
  ring

end

end ArchonPhysics.CanonicalIIDCoerciveInitialHaarQuenchedFactorization
