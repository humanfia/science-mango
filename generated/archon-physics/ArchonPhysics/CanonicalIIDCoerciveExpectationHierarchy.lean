import ArchonPhysics.CanonicalIIDCoerciveContinuousMomentFrontier
import ArchonPhysics.FreeFPUTObservedChildAcousticMomentLinearVolumeBound
import Mathlib.Analysis.Calculus.ParametricIntegral

/-!
# Continuous canonical iid expectation hierarchy

This module isolates the analytic step which moves the time derivative through
the canonical iid Bochner integral.  It is specialized throughout to the
actual coercive alpha--beta canonical flow and its measurable signed ordered
modal blocks.

Two concrete controls are proved here.

* Almost surely, the complete canonical trajectory stays in the one common
  coercive energy shell at every real time.  In particular its physical
  position and momentum are bounded by the shell cutoff radius.
* Every fixed ordered mode different from the translation label has the
  deterministic frozen-support infrared bound `omega⁻¹ <= N`.

The final differentiation theorem uses a deliberately transparent remaining
predicate: the *actual* block insertion must have one nonnegative constant
bound, almost surely and uniformly on the chosen time neighborhood.  This is
strictly weaker and more concrete than postulating a generic dominated
parametric integral theorem, but it is not hidden: proving this predicate from
the displayed shell and infrared bounds still requires the finite-dimensional
polynomial norm estimate for the full quadratic-plus-cubic source.

No RPA, Markov, independence, closure, decay, or kinetic conclusion is used.
The translation zero mode is explicitly excluded.
-/

namespace ArchonPhysics.CanonicalIIDCoerciveExpectationHierarchy

open scoped BigOperators Matrix Topology

open ArchonPhysics
open ArchonPhysics.CanonicalIIDCoerciveContinuousMomentFrontier
open ArchonPhysics.CanonicalIIDCoerciveSignedModalBlockHierarchy
open ArchonPhysics.CanonicalIIDCoerciveSignedModalHierarchy
open ArchonPhysics.CanonicalIIDCoerciveSignedModalObservableBridge
open ArchonPhysics.CanonicalRandomMassGlobalFlow
open ArchonPhysics.CanonicalRandomMassPhaseGlobalFlow
open ArchonPhysics.CoerciveHamiltonianContinuation
open ArchonPhysics.FreeFPUTObservedChildAcousticMomentLinearVolumeBound
open ArchonPhysics.GlobalReducedParametricFlowAdapter
open ArchonPhysics.MeasurableOrderedModeCoupling.Harmonic
open ArchonPhysics.MeasurableOrderedSpectrum
open ArchonPhysics.OrderedSingleModeProjector
open ArchonPhysics.OrderedTranslationLastMode
open ArchonPhysics.ParametricLocalHamiltonianFlow
open ArchonPhysics.RandomMassInitialEnergyBound
open ArchonPhysics.RandomMassOrderedProjectorBridge
open ArchonPhysics.RandomMassPositiveCollisionData
open ArchonPhysics.RandomMassReducedPhaseInitialData
open MeasureTheory
open Metric

noncomputable section

variable {N : Nat} [NeZero N]

/-- On a simple sample, the actual canonical trajectory stays in the common
coercive shell at every real time. -/
theorem norm_canonicalRandomMassPhaseTrajectory_le_cutoffRadius_of_simple
    (hN : 3 ≤ N) {a : Real} (ha0 : 0 ≤ a) (ha1 : a ≤ 1 / 4)
    (kappa beta g : Real) (hbeta : 2 * kappa ^ 2 / 9 < beta)
    (omega : CanonicalSample)
    (hsimple : SimpleOrderedSpectrum
      (harmonicHermitian (canonicalMass (N := N) omega)))
    (time : Real) :
    ‖canonicalRandomMassPhaseTrajectory (N := N)
        canonicalIIDMassPhaseEnsemble kappa beta g hbeta a (omega, time)‖ ≤
      (canonicalRandomMassPhaseEnergyShell N kappa beta g hbeta).cutoffRadius := by
  let shell := canonicalRandomMassPhaseEnergyShell N kappa beta g hbeta
  have henergy : reducedHamiltonian (canonicalMass (N := N) omega)
      kappa beta g
      (reducedInitialStateOfSimple canonicalIIDMassPhaseEnsemble a omega hsimple) ≤
        initialEnergyUpperBound kappa beta g :=
    reducedHamiltonian_reducedInitialStateOfSimple_le
      canonicalIIDMassPhaseEnsemble hN ha0 ha1 hbeta g omega hsimple
  obtain ⟨z, _hz0, _hz, hmatch, hbound, _hderiv, _henergy, _hjoint⟩ :=
    canonicalRandomMassGlobalFlow_matches_reduced shell
      (canonicalMass (N := N) omega)
      (massAdmissible_canonicalIIDUniformEnergyShell
        canonicalIIDMassPhaseEnsemble kappa beta g
          (initialEnergyUpperBound kappa beta g) hbeta omega)
      (reducedInitialStateOfSimple canonicalIIDMassPhaseEnsemble a omega hsimple)
      henergy
  have hinitial :
      parametricInitialSample canonicalIIDMassPhaseEnsemble (N := N)
          kappa beta g a omega =
        embedReducedPoint (canonicalMass (N := N) omega)
          kappa beta g
          (reducedInitialStateOfSimple canonicalIIDMassPhaseEnsemble a omega hsimple) :=
    parametricInitialSample_eq_embedReducedPoint
      canonicalIIDMassPhaseEnsemble kappa beta g a omega hsimple
  change ‖canonicalRandomMassGlobalFlow shell
      (parametricInitialSample canonicalIIDMassPhaseEnsemble (N := N)
        kappa beta g a omega, time)‖ ≤ shell.cutoffRadius
  rw [hinitial]
  simpa [shell, canonicalRandomMassPhaseEnergyShell,
    canonicalIIDUniformEnergyShell] using hbound time

/-- A single full-measure set carries the common shell bound for every time. -/
theorem norm_canonicalRandomMassPhaseTrajectory_le_cutoffRadius_ae_allTime
    (hN : 3 ≤ N) {a : Real} (ha0 : 0 ≤ a) (ha1 : a ≤ 1 / 4)
    (kappa beta g : Real) (hbeta : 2 * kappa ^ 2 / 9 < beta) :
    ∀ᵐ omega ∂canonicalIIDMassPhaseEnsemble.probability,
      ∀ time : Real,
        ‖canonicalRandomMassPhaseTrajectory (N := N)
            canonicalIIDMassPhaseEnsemble kappa beta g hbeta a (omega, time)‖ ≤
          (canonicalRandomMassPhaseEnergyShell N kappa beta g hbeta).cutoffRadius := by
  filter_upwards [RandomMassOrderedProjectorBridge.simpleOrderedSpectrum_ae
    (N := N) canonicalIIDMassPhaseEnsemble (show 2 ≤ N by omega)]
      with omega hsimpleSample
  have hsimple : SimpleOrderedSpectrum
      (harmonicHermitian (canonicalMass (N := N) omega)) := by
    simpa [canonicalMass, harmonicHermitianSample, harmonicHermitian] using
      hsimpleSample
  intro time
  exact norm_canonicalRandomMassPhaseTrajectory_le_cutoffRadius_of_simple
    hN ha0 ha1 kappa beta g hbeta omega hsimple time

/-- The position coordinate inherits the same almost-sure all-time shell
bound. -/
theorem norm_canonicalFlowPosition_le_cutoffRadius_ae_allTime
    (hN : 3 ≤ N) {a : Real} (ha0 : 0 ≤ a) (ha1 : a ≤ 1 / 4)
    (kappa beta g : Real) (hbeta : 2 * kappa ^ 2 / 9 < beta) :
    ∀ᵐ omega ∂canonicalIIDMassPhaseEnsemble.probability,
      ∀ time : Real,
        ‖canonicalFlowPosition (N := N)
            kappa beta g hbeta a (omega, time)‖ ≤
          (canonicalRandomMassPhaseEnergyShell N kappa beta g hbeta).cutoffRadius := by
  filter_upwards [norm_canonicalRandomMassPhaseTrajectory_le_cutoffRadius_ae_allTime
    hN ha0 ha1 kappa beta g hbeta] with omega hbound
  intro time
  have hphase :
      ‖(canonicalRandomMassPhaseTrajectory (N := N)
          canonicalIIDMassPhaseEnsemble kappa beta g hbeta a
            (omega, time)).2‖ ≤
        ‖canonicalRandomMassPhaseTrajectory (N := N)
          canonicalIIDMassPhaseEnsemble kappa beta g hbeta a
            (omega, time)‖ := by
    rw [Prod.norm_def]
    exact le_max_right _ _
  have hposition :
      ‖(canonicalRandomMassPhaseTrajectory (N := N)
          canonicalIIDMassPhaseEnsemble kappa beta g hbeta a
            (omega, time)).2.1‖ ≤
        ‖(canonicalRandomMassPhaseTrajectory (N := N)
          canonicalIIDMassPhaseEnsemble kappa beta g hbeta a
            (omega, time)).2‖ := by
    rw [Prod.norm_def]
    exact le_max_left _ _
  exact (show ‖canonicalFlowPosition (N := N)
      kappa beta g hbeta a (omega, time)‖ ≤ _ by
    simpa [canonicalFlowPosition] using hposition.trans (hphase.trans (hbound time)))

/-- The canonical momentum coordinate inherits the same almost-sure all-time
shell bound. -/
theorem norm_canonicalFlowMomentum_le_cutoffRadius_ae_allTime
    (hN : 3 ≤ N) {a : Real} (ha0 : 0 ≤ a) (ha1 : a ≤ 1 / 4)
    (kappa beta g : Real) (hbeta : 2 * kappa ^ 2 / 9 < beta) :
    ∀ᵐ omega ∂canonicalIIDMassPhaseEnsemble.probability,
      ∀ time : Real,
        ‖canonicalFlowMomentum (N := N)
            kappa beta g hbeta a (omega, time)‖ ≤
          (canonicalRandomMassPhaseEnergyShell N kappa beta g hbeta).cutoffRadius := by
  filter_upwards [norm_canonicalRandomMassPhaseTrajectory_le_cutoffRadius_ae_allTime
    hN ha0 ha1 kappa beta g hbeta] with omega hbound
  intro time
  have hphase :
      ‖(canonicalRandomMassPhaseTrajectory (N := N)
          canonicalIIDMassPhaseEnsemble kappa beta g hbeta a
            (omega, time)).2‖ ≤
        ‖canonicalRandomMassPhaseTrajectory (N := N)
          canonicalIIDMassPhaseEnsemble kappa beta g hbeta a
            (omega, time)‖ := by
    rw [Prod.norm_def]
    exact le_max_right _ _
  have hmomentum :
      ‖(canonicalRandomMassPhaseTrajectory (N := N)
          canonicalIIDMassPhaseEnsemble kappa beta g hbeta a
            (omega, time)).2.2‖ ≤
        ‖(canonicalRandomMassPhaseTrajectory (N := N)
          canonicalIIDMassPhaseEnsemble kappa beta g hbeta a
            (omega, time)).2‖ := by
    rw [Prod.norm_def]
    exact le_max_right _ _
  exact (show ‖canonicalFlowMomentum (N := N)
      kappa beta g hbeta a (omega, time)‖ ≤ _ by
    simpa [canonicalFlowMomentum] using hmomentum.trans (hphase.trans (hbound time)))

/-- Deterministic finite-volume infrared control for every selected ordered
mode other than the translation label. -/
theorem inv_canonicalOrderedFrequency_le_volume
    (k : OrderedModeIndex N)
    (hk : k ≠ lastOrderedIndex (ι := Lattice.Site N))
    (omega : CanonicalSample) :
    (canonicalOrderedFrequency (N := N) k omega)⁻¹ ≤ (N : Real) := by
  let m := canonicalMass (N := N) omega
  have hlower : ∀ i, (4 / 5 : Real) ≤ m.mass i := by
    intro i
    simpa [m, canonicalMass, RandomEnsemble.massLower] using
      (canonicalIIDMassPhaseEnsemble.mass_mem_support i.val omega).1
  have hupper : ∀ i, m.mass i ≤ (6 / 5 : Real) := by
    intro i
    simpa [m, canonicalMass, RandomEnsemble.massUpper] using
      (canonicalIIDMassPhaseEnsemble.mass_mem_support i.val omega).2
  have hfrequency : 0 < orderedModeFrequency (harmonicHermitian m) k :=
    (CanonicalCollisionSoftLegBound.orderedModeFrequency_pos_iff_ne_last_unconditional
      m k).2 hk
  have hphysical : 0 < ModalPhaseMismatch.modeFrequency m (orderedIndexEquiv k) := by
    simpa [MeasurableOrderedModeCoupling.Harmonic.orderedModeFrequency_harmonicHermitian_eq]
      using hfrequency
  have hbound := frozenSupport_inv_modeFrequency_le_volume
    m hlower hupper (orderedIndexEquiv k) hphysical
  simpa [canonicalOrderedFrequency, m,
    MeasurableOrderedModeCoupling.Harmonic.orderedModeFrequency_harmonicHermitian_eq]
    using hbound

variable {I : Type*} [Fintype I] [DecidableEq I]

/-- A transparent local derivative envelope for the actual canonical signed
block source.  The bound is a scalar constant because the canonical law is a
probability measure. -/
def HasCanonicalSignedBlockLocalDerivativeEnvelope
    (kappa beta g : Real) (hbeta : 2 * kappa ^ 2 / 9 < beta)
    (a : Real) (entry : I → FinitePhaseMonomials.PhaseSign × OrderedModeIndex N)
    (block : Finset I) (time radius bound : Real) : Prop :=
  0 < radius ∧ 0 ≤ bound ∧
    ∀ᵐ omega ∂canonicalIIDMassPhaseEnsemble.probability,
      ∀ s ∈ ball time radius,
        ‖canonicalSignedBlockInsertion (N := N)
            kappa beta g hbeta a entry block (omega, s)‖ ≤ bound

/-- The constant function supplied by a nonnegative local envelope is
integrable for the canonical probability law. -/
theorem integrable_const_of_hasCanonicalSignedBlockLocalDerivativeEnvelope
    {kappa beta g : Real} {hbeta : 2 * kappa ^ 2 / 9 < beta}
    {a : Real}
    {entry : I → FinitePhaseMonomials.PhaseSign × OrderedModeIndex N}
    {block : Finset I} {time radius bound : Real}
    (henvelope : HasCanonicalSignedBlockLocalDerivativeEnvelope (N := N)
      kappa beta g hbeta a entry block time radius bound) :
    Integrable (fun _ : CanonicalSample => bound)
      canonicalIIDMassPhaseEnsemble.probability := by
  let _ : IsFiniteMeasure canonicalIIDMassPhaseEnsemble.probability :=
    ⟨by rw [canonicalIIDMassPhaseEnsemble.probability_univ]; norm_num⟩
  exact integrable_const bound

/-- Under the explicit local envelope, the continuous canonical block
expectation differentiates to the Bochner expectation of the exact full
one-slot source. -/
theorem hasDerivAt_canonicalSignedBlockBochnerIntegral
    (hN : 3 ≤ N) {a : Real} (ha0 : 0 ≤ a) (ha1 : a ≤ 1 / 4)
    (kappa beta g : Real) (hbeta : 2 * kappa ^ 2 / 9 < beta)
    (entry : I → FinitePhaseMonomials.PhaseSign × OrderedModeIndex N)
    (hpositive : ∀ i, (entry i).2 ≠
      lastOrderedIndex (ι := Lattice.Site N))
    (block : Finset I) (time radius bound : Real)
    (henvelope : HasCanonicalSignedBlockLocalDerivativeEnvelope (N := N)
      kappa beta g hbeta a entry block time radius bound)
    (hintegrable : Integrable
      (fun omega : CanonicalSample =>
        canonicalSignedBlockObservable (N := N)
          kappa beta g hbeta a entry block (omega, time))
      canonicalIIDMassPhaseEnsemble.probability) :
    HasDerivAt
      (canonicalSignedBlockBochnerIntegral (N := N)
        kappa beta g hbeta a entry block)
      (canonicalSignedBlockInsertionBochnerIntegral (N := N)
        kappa beta g hbeta a entry block time) time := by
  let mu := canonicalIIDMassPhaseEnsemble.probability
  let F : Real → CanonicalSample → Complex := fun s omega =>
    canonicalSignedBlockObservable (N := N)
      kappa beta g hbeta a entry block (omega, s)
  let F' : Real → CanonicalSample → Complex := fun s omega =>
    canonicalSignedBlockInsertion (N := N)
      kappa beta g hbeta a entry block (omega, s)
  have hmeas : ∀ᶠ s in 𝓝 time, AEStronglyMeasurable (F s) mu := by
    exact Filter.Eventually.of_forall fun s =>
      aestronglyMeasurable_canonicalSignedBlock_fixedTime
        (N := N) kappa beta g hbeta a entry block s
  have hsourceMeas : AEStronglyMeasurable (F' time) mu :=
    aestronglyMeasurable_canonicalSignedBlockInsertion_fixedTime
      (N := N) kappa beta g hbeta a entry block time
  have hdiff : ∀ᵐ omega ∂mu, ∀ s ∈ ball time radius,
      HasDerivAt (fun u => F u omega) (F' s omega) s := by
    filter_upwards [canonicalSignedBlockHierarchy_ae_allTime
      hN ha0 ha1 kappa beta g hbeta entry hpositive] with omega homega
    intro s _hs
    exact homega block s
  have hbound : ∀ᵐ omega ∂mu, ∀ s ∈ ball time radius,
      ‖F' s omega‖ ≤ (fun _ : CanonicalSample => bound) omega := by
    simpa [HasCanonicalSignedBlockLocalDerivativeEnvelope, mu, F'] using
      henvelope.2.2
  have hresult := hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (F := F) (F' := F') (bound := fun _ : CanonicalSample => bound)
    (μ := mu) (ball_mem_nhds time henvelope.1)
    hmeas hintegrable hsourceMeas hbound
    (integrable_const_of_hasCanonicalSignedBlockLocalDerivativeEnvelope
      (N := N) henvelope) hdiff
  change HasDerivAt
    (fun s => ∫ omega : CanonicalSample,
      canonicalSignedBlockObservable (N := N)
        kappa beta g hbeta a entry block (omega, s)
      ∂canonicalIIDMassPhaseEnsemble.probability)
    (∫ omega : CanonicalSample,
      canonicalSignedBlockInsertion (N := N)
        kappa beta g hbeta a entry block (omega, time)
      ∂canonicalIIDMassPhaseEnsemble.probability) time
  simpa [F, F', mu] using hresult.2

end

end ArchonPhysics.CanonicalIIDCoerciveExpectationHierarchy
