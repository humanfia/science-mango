import ArchonPhysics.CanonicalIIDCoerciveSignedModalObservableBridge

/-!
# Almost-sure finite-block hierarchy on the canonical iid coercive flow

This module instantiates the measurable signed-frame derivative bridge on the
single canonical iid mass--phase global flow.  The canonical flow agrees,
almost surely and for every real time at once, with a genuine untruncated
coercive alpha--beta Hamilton orbit.  Therefore every arbitrary fixed finite
signed modal block satisfies the exact one-slot full-source hierarchy almost
surely.

The conclusion is pointwise in time but its almost-sure set is uniform in
time.  It is not yet a derivative-under-expectation theorem: a uniform
integrable bound for the complete source is still required for that analytic
interchange.  In particular this file does not assume or prove RPA, Markov
closure, cumulant decay, or thermalization.
-/

namespace ArchonPhysics.CanonicalIIDCoerciveSignedModalBlockHierarchy

open scoped BigOperators Matrix

open ArchonPhysics
open ArchonPhysics.CanonicalIIDCoerciveSignedModalHierarchy
open ArchonPhysics.CanonicalIIDCoerciveSignedModalObservableBridge
open ArchonPhysics.CanonicalRandomMassPhaseGlobalFlow
open ArchonPhysics.CoerciveHamiltonianContinuation
open ArchonPhysics.ComplexModeAmplitude
open ArchonPhysics.CoerciveHamiltonianPhyslib
open ArchonPhysics.FinitePhaseMonomials
open ArchonPhysics.GlobalReducedParametricFlowAdapter
open ArchonPhysics.PhaseRenormalization
open ArchonPhysics.RandomMassOrderedProjectorBridge
open ArchonPhysics.MassWeightedHamiltonianDynamics
open ArchonPhysics.MeasurableOrderedModeCoupling.Harmonic
open ArchonPhysics.MeasurableOrderedSpectrum
open ArchonPhysics.OrderedSingleModeProjector
open ArchonPhysics.PhyslibFPUTBinaryInteractionTreeCouples
open ArchonPhysics.PhyslibFPUTPositiveTimeCumulantHierarchy
open ArchonPhysics.RandomMassMeasurableHarmonicEnergy
open ArchonPhysics.RandomMassMeasurableOrderedEigenframe
open ArchonPhysics.RandomMassPositiveCollisionData
open ArchonPhysics.RandomMassReducedPhaseInitialData
open ArchonPhysics.ReducedGlobalTrajectoryPhyslibAdapter
open MeasureTheory

noncomputable section

variable {N : Nat} [NeZero N]

/-- Full coercive source of one measurable ordered mode along the canonical
random trajectory. -/
def canonicalOrderedRotatedSource
    (kappa beta g : Real) (hbeta : 2 * kappa ^ 2 / 9 < beta)
    (a : Real) (k : OrderedModeIndex N)
    (st : CanonicalSample × Real) : Complex :=
  orderedSignedRotatedSource (canonicalMass (N := N) st.1)
    kappa beta g k
    (fun time => canonicalFlowPosition (N := N)
      kappa beta g hbeta a (st.1, time)) st.2

/-- Signed phase/conjugate branch of the complete canonical source. -/
def canonicalSignedRotatedSource
    (kappa beta g : Real) (hbeta : 2 * kappa ^ 2 / 9 < beta)
    (a : Real) (entry : PhaseSign × OrderedModeIndex N)
    (st : CanonicalSample × Real) : Complex :=
  phaseSignActComplex entry.1
    (canonicalOrderedRotatedSource (N := N)
      kappa beta g hbeta a entry.2 st)

theorem canonicalInteractionAmplitude_eq_orderedPath_of_match
    (kappa beta g : Real) (hbeta : 2 * kappa ^ 2 / 9 < beta)
    (a : Real) (omega : CanonicalSample)
    (z : Real → ReducedPhaseSpace (canonicalMass (N := N) omega))
    (hmatch : ∀ time,
      canonicalRandomMassPhaseTrajectory (N := N)
          canonicalIIDMassPhaseEnsemble kappa beta g hbeta a (omega, time) =
        embedReducedPoint (canonicalMass (N := N) omega)
          kappa beta g (z time))
    (k : OrderedModeIndex N) (time : Real) :
    canonicalInteractionAmplitude (N := N)
        kappa beta g hbeta a k (omega, time) =
      phaseRenormalize
        (orderedModeFrequency
          (harmonicHermitian (canonicalMass (N := N) omega)) k * time)
        (complexModeAmplitude
          (orderedModeFrequency
            (harmonicHermitian (canonicalMass (N := N) omega)) k)
          (orderedSignedPositionPath (canonicalMass (N := N) omega) k
            (fun s => ((z s).1 : HilbertConfiguration N)) time)
          (orderedSignedMomentumPath (canonicalMass (N := N) omega) k
            (fun s => ((z s).2 : HilbertConfiguration N)) time)) := by
  have hq : canonicalFlowPosition (N := N) kappa beta g hbeta a
      (omega, time) = ((z time).1 : HilbertConfiguration N) := by
    simpa [canonicalFlowPosition, embedReducedPoint] using
      congrArg (fun x => x.2.1) (hmatch time)
  have hp : canonicalFlowMomentum (N := N) kappa beta g hbeta a
      (omega, time) = ((z time).2 : HilbertConfiguration N) := by
    simpa [canonicalFlowMomentum, embedReducedPoint] using
      congrArg (fun x => x.2.2) (hmatch time)
  unfold canonicalInteractionAmplitude canonicalOrderedFrequency
    canonicalOrderedModalPosition canonicalOrderedModalMomentum
    orderedSignedPositionPath orderedSignedMomentumPath
    massWeightedPositionSample massWeightedMomentumSample
    massWeightedPosition massWeightedMomentum orderedEigenvectorSample
  rw [hq, hp]
  rfl

theorem canonicalOrderedRotatedSource_eq_orderedSource_of_match
    (kappa beta g : Real) (hbeta : 2 * kappa ^ 2 / 9 < beta)
    (a : Real) (omega : CanonicalSample)
    (z : Real → ReducedPhaseSpace (canonicalMass (N := N) omega))
    (hmatch : ∀ time,
      canonicalRandomMassPhaseTrajectory (N := N)
          canonicalIIDMassPhaseEnsemble kappa beta g hbeta a (omega, time) =
        embedReducedPoint (canonicalMass (N := N) omega)
          kappa beta g (z time))
    (k : OrderedModeIndex N) (time : Real) :
    canonicalOrderedRotatedSource (N := N)
        kappa beta g hbeta a k (omega, time) =
      orderedSignedRotatedSource (canonicalMass (N := N) omega) kappa beta g k
        (fun s => ((z s).1 : HilbertConfiguration N)) time := by
  unfold canonicalOrderedRotatedSource
  congr 1
  funext s
  simpa [canonicalFlowPosition, embedReducedPoint] using
    congrArg (fun x => x.2.1) (hmatch s)

/-- On each simple sample, the actual canonical amplitude has the exact full
coercive source derivative at every real time. -/
theorem hasDerivAt_canonicalInteractionAmplitude_of_simple
    (hN : 3 ≤ N) {a : Real} (ha0 : 0 ≤ a) (ha1 : a ≤ 1 / 4)
    (kappa beta g : Real) (hbeta : 2 * kappa ^ 2 / 9 < beta)
    (omega : CanonicalSample)
    (hsimple : SimpleOrderedSpectrum
      (harmonicHermitian (canonicalMass (N := N) omega)))
    (k : OrderedModeIndex N)
    (homega : 0 < orderedModeFrequency
      (harmonicHermitian (canonicalMass (N := N) omega)) k)
    (time : Real) :
    HasDerivAt
      (fun s => canonicalInteractionAmplitude (N := N)
        kappa beta g hbeta a k (omega, s))
      (canonicalOrderedRotatedSource (N := N)
        kappa beta g hbeta a k (omega, time)) time := by
  obtain ⟨z, _hz0, hz, hmatch, _henergy⟩ :=
    canonicalRandomMassPhaseTrajectory_matches_reduced_of_simple
      canonicalIIDMassPhaseEnsemble hN ha0 ha1
      kappa beta g hbeta omega hsimple
  let p : Real → HilbertConfiguration N :=
    fun s => ((z s).2 : HilbertConfiguration N)
  let q : Real → HilbertConfiguration N :=
    fun s => ((z s).1 : HilbertConfiguration N)
  have hDynamics : HasExplicitHamiltonDerivatives
      (canonicalMass (N := N) omega) kappa beta g p q := by
    intro s
    constructor
    · simpa [p, q, reducedVelocity_coe] using
        hasDerivAt_reducedPosition_coe
          (canonicalMass (N := N) omega) kappa beta g (hz s)
    · simpa [p, q, reducedPotentialGradient_coe] using
        hasDerivAt_reducedMomentum_coe
          (canonicalMass (N := N) omega) kappa beta g (hz s)
  have hactual := hasDerivAt_orderedSignedInteractionPath
    (canonicalMass (N := N) omega) kappa beta g hsimple k
    hDynamics homega time
  rw [canonicalOrderedRotatedSource_eq_orderedSource_of_match
    kappa beta g hbeta a omega
    z hmatch k time]
  apply hactual.congr_of_eventuallyEq
  exact Filter.Eventually.of_forall fun s => by
    simpa only [orderedSignedInteractionPath] using
      canonicalInteractionAmplitude_eq_orderedPath_of_match
        kappa beta g hbeta a omega
        z hmatch k s

theorem hasDerivAt_canonicalSignedInteractionAmplitude_of_simple
    (hN : 3 ≤ N) {a : Real} (ha0 : 0 ≤ a) (ha1 : a ≤ 1 / 4)
    (kappa beta g : Real) (hbeta : 2 * kappa ^ 2 / 9 < beta)
    (omega : CanonicalSample)
    (hsimple : SimpleOrderedSpectrum
      (harmonicHermitian (canonicalMass (N := N) omega)))
    (entry : PhaseSign × OrderedModeIndex N)
    (homega : 0 < orderedModeFrequency
      (harmonicHermitian (canonicalMass (N := N) omega)) entry.2)
    (time : Real) :
    HasDerivAt
      (fun s => canonicalSignedInteractionAmplitude (N := N)
        kappa beta g hbeta a entry (omega, s))
      (canonicalSignedRotatedSource (N := N)
        kappa beta g hbeta a entry (omega, time)) time := by
  rcases entry with ⟨sign, k⟩
  have h := hasDerivAt_canonicalInteractionAmplitude_of_simple
    hN ha0 ha1 kappa beta g hbeta omega hsimple k homega time
  cases sign with
  | phase =>
      change HasDerivAt
        (fun s => canonicalInteractionAmplitude (N := N)
          kappa beta g hbeta a k (omega, s))
        (canonicalOrderedRotatedSource (N := N)
          kappa beta g hbeta a k (omega, time)) time
      exact h
  | conjugate =>
      change HasDerivAt
        (fun s => star (canonicalInteractionAmplitude (N := N)
          kappa beta g hbeta a k (omega, s)))
        (star (canonicalOrderedRotatedSource (N := N)
          kappa beta g hbeta a k (omega, time))) time
      exact h.star

variable {I : Type*} [Fintype I] [DecidableEq I]

/-- One-slot insertion of the complete canonical source into a fixed block. -/
def canonicalSignedBlockInsertion
    (kappa beta g : Real) (hbeta : 2 * kappa ^ 2 / 9 < beta)
    (a : Real) (entry : I → PhaseSign × OrderedModeIndex N)
    (block : Finset I) (st : CanonicalSample × Real) : Complex :=
  ∑ i ∈ block,
    (∏ j ∈ block.erase i,
      canonicalSignedInteractionAmplitude (N := N)
        kappa beta g hbeta a (entry j) st) *
      canonicalSignedRotatedSource (N := N)
        kappa beta g hbeta a (entry i) st

/-- Arbitrary fixed-order exact Leibniz hierarchy on one simple sample. -/
theorem hasDerivAt_canonicalSignedBlockObservable_of_simple
    (hN : 3 ≤ N) {a : Real} (ha0 : 0 ≤ a) (ha1 : a ≤ 1 / 4)
    (kappa beta g : Real) (hbeta : 2 * kappa ^ 2 / 9 < beta)
    (omega : CanonicalSample)
    (hsimple : SimpleOrderedSpectrum
      (harmonicHermitian (canonicalMass (N := N) omega)))
    (entry : I → PhaseSign × OrderedModeIndex N)
    (homega : ∀ i, 0 < orderedModeFrequency
      (harmonicHermitian (canonicalMass (N := N) omega)) (entry i).2)
    (block : Finset I) (time : Real) :
    HasDerivAt
      (fun s => canonicalSignedBlockObservable (N := N)
        kappa beta g hbeta a entry block (omega, s))
      (canonicalSignedBlockInsertion (N := N)
        kappa beta g hbeta a entry block (omega, time)) time := by
  simpa only [canonicalSignedBlockObservable,
    canonicalSignedBlockInsertion, signedBlockMonomial,
    signedBlockSlotInsertion, smul_eq_mul] using
    (HasDerivAt.fun_finsetProd fun i hi =>
      hasDerivAt_canonicalSignedInteractionAmplitude_of_simple
        hN ha0 ha1 kappa beta g hbeta omega hsimple
        (entry i) (homega i) time)

/-- The almost-sure set is uniform in real time and works for every fixed
finite block simultaneously. -/
theorem canonicalSignedBlockHierarchy_ae_allTime
    (hN : 3 ≤ N) {a : Real} (ha0 : 0 ≤ a) (ha1 : a ≤ 1 / 4)
    (kappa beta g : Real) (hbeta : 2 * kappa ^ 2 / 9 < beta)
    (entry : I → PhaseSign × OrderedModeIndex N)
    (hpositive : ∀ i, (entry i).2 ≠
      OrderedTranslationLastMode.lastOrderedIndex (ι := Lattice.Site N)) :
    ∀ᵐ omega ∂canonicalIIDMassPhaseEnsemble.probability,
      ∀ block : Finset I, ∀ time : Real,
        HasDerivAt
          (fun s => canonicalSignedBlockObservable (N := N)
            kappa beta g hbeta a entry block (omega, s))
          (canonicalSignedBlockInsertion (N := N)
            kappa beta g hbeta a entry block (omega, time)) time := by
  filter_upwards [RandomMassOrderedProjectorBridge.simpleOrderedSpectrum_ae
    (N := N) canonicalIIDMassPhaseEnsemble (show 2 ≤ N by omega)]
      with omega hsimpleSample
  have hsimple : SimpleOrderedSpectrum
      (harmonicHermitian (canonicalMass (N := N) omega)) := by
    simpa [canonicalMass, harmonicHermitianSample, harmonicHermitian] using
      hsimpleSample
  have homega : ∀ i, 0 < orderedModeFrequency
      (harmonicHermitian (canonicalMass (N := N) omega)) (entry i).2 := by
    intro i
    exact (OrderedTranslationLastMode.orderedModeFrequency_pos_iff_ne_last
      (canonicalMass (N := N) omega) hsimple (entry i).2).2 (hpositive i)
  intro block time
  exact hasDerivAt_canonicalSignedBlockObservable_of_simple
    hN ha0 ha1 kappa beta g hbeta omega hsimple entry homega block time

end

end ArchonPhysics.CanonicalIIDCoerciveSignedModalBlockHierarchy
