import ArchonPhysics.CanonicalIIDCoerciveSignedModalBlockHierarchy

/-!
# Continuous canonical iid moment/cumulant frontier

This module constructs the actual continuous canonical iid Bochner-integral expressions
associated with the measurable signed ordered-mode blocks.  It also proves
measurability of the complete coercive alpha--beta source and of every finite
one-slot insertion.  Thus both sides of the desired expectation hierarchy
are now concrete functions of the same canonical flow and probability law.

What is intentionally absent is a theorem differentiating the first integral
into the second.  The existing parameterized-integral theorem requires an
integrable bound, uniform in a time neighborhood, for the block derivative.
For these normalized complex amplitudes that bound must simultaneously use

* a uniform positive lower bound for every selected nontranslation frequency;
* the canonical coercive shell bound on position and momentum; and
* a uniform bound for the full quadratic-plus-cubic nonlinear force.

The pointwise almost-sure derivative proved in the imported block hierarchy
does not itself supply those bounds.  No abstract `dominated` premise is
inserted here as a substitute.  Consequently the definitions below are the
exact continuous-expectation frontier, not a claimed closed hierarchy.

At time zero, FreeFPUTInitialHaarDisjointClusterFactorization and
PhyslibFPUTArbitraryClusterDecoherencePropagation already provide the
kernel-checked arbitrary-order Haar many-cluster factorization and its exact
finite-ensemble propagation telescope.  This file does not yet identify the
canonical continuous-law Bochner expressions below with that initial-Haar
interface.  In particular, total charge balance alone is not used as a
surrogate for factorization of two or more disjoint mode clusters.

Deng--Hani, *Propagation of chaos and higher order statistics in wave
kinetic theory* (arXiv:2110.04565), is a blueprint for why arbitrary higher
moments and cumulants are the correct objects.  No result from that NLS
paper is imported as a theorem about the random-mass FPUT Hamiltonian.

Resonant, charge-balanced, and recollision connected sectors remain present.
-/

namespace ArchonPhysics.CanonicalIIDCoerciveContinuousMomentFrontier

open scoped BigOperators Matrix

open ArchonPhysics
open ArchonPhysics.CanonicalIIDCoerciveSignedModalBlockHierarchy
open ArchonPhysics.CanonicalIIDCoerciveSignedModalHierarchy
open ArchonPhysics.CanonicalIIDCoerciveSignedModalObservableBridge
open ArchonPhysics.CoerciveHamiltonianPhyslib
open ArchonPhysics.FinitePhaseMonomials
open ArchonPhysics.ForcedComplexModeDuhamel
open ArchonPhysics.MassWeightedHamiltonianDynamics
open ArchonPhysics.MeasurableOrderedModeCoupling.Harmonic
open ArchonPhysics.PhaseRenormalization
open ArchonPhysics.PhyslibFPUTPositiveTimeCumulantHierarchy
open ArchonPhysics.PhyslibFPUTBinaryInteractionTreeCouples
open ArchonPhysics.RandomMassMeasurableOrderedEigenframe
open ArchonPhysics.RandomMassPositiveCollisionData
open MeasureTheory

noncomputable section

variable {N : Nat} [NeZero N]

theorem measurable_canonicalOrderedNonlinearForce
    (kappa beta g : Real) (hbeta : 2 * kappa ^ 2 / 9 < beta)
    (a : Real) (k : OrderedModeIndex N) :
    Measurable fun st : CanonicalSample × Real =>
      orderedSignedNonlinearForce (canonicalMass (N := N) st.1)
        kappa beta g k
        (canonicalFlowPosition (N := N) kappa beta g hbeta a st) := by
  have hq := measurable_canonicalFlowPosition
    (N := N) kappa beta g hbeta a
  have hv (i : Lattice.Site N) : Measurable fun st : CanonicalSample × Real =>
      orderedEigenvectorSample canonicalIIDMassPhaseEnsemble k st.1 i :=
    (measurable_pi_apply i).comp
      ((measurable_orderedEigenvectorSample
        canonicalIIDMassPhaseEnsemble k).comp measurable_fst)
  have hm (i : Lattice.Site N) : Measurable fun st : CanonicalSample × Real =>
      (canonicalMass (N := N) st.1).mass i :=
    (measurable_canonicalMass_coordinate (N := N) i).comp measurable_fst
  have hqcoord (i : Lattice.Site N) : Measurable fun st : CanonicalSample × Real =>
      canonicalFlowPosition (N := N) kappa beta g hbeta a st i :=
    (measurable_pi_apply i).comp
      ((WithLp.measurable_ofLp 2 _).comp hq)
  have hgradient (i : Lattice.Site N) : Measurable fun st : CanonicalSample × Real =>
      nonlinearPotentialGradient kappa beta g
        (canonicalFlowPosition (N := N) kappa beta g hbeta a st) i := by
    unfold nonlinearPotentialGradient
    simp only [WithLp.ofLp_sum, WithLp.ofLp_smul, Finset.sum_apply,
      Pi.smul_apply, smul_eq_mul]
    apply Finset.measurable_sum
    intro j _hj
    have hforward : Measurable fun st : CanonicalSample × Real =>
        Lattice.forwardDifference
          (asConfiguration
            (canonicalFlowPosition (N := N) kappa beta g hbeta a st)) j := by
      unfold Lattice.forwardDifference asConfiguration
      exact (hqcoord (j + 1)).sub (hqcoord j)
    have hnonlinear : Measurable fun st : CanonicalSample × Real =>
        nonlinearPotentialDerivative kappa beta g
          (Lattice.forwardDifference
            (asConfiguration
              (canonicalFlowPosition (N := N) kappa beta g hbeta a st)) j) := by
      unfold nonlinearPotentialDerivative
      fun_prop
    exact hnonlinear.mul measurable_const
  unfold orderedSignedNonlinearForce orderedSignedCoordinate
    transformedNonlinearForce dotProduct
  apply Finset.measurable_sum
  intro i _hi
  have hforce : Measurable fun st : CanonicalSample × Real =>
      (-inverseSqrtMassTransform (canonicalMass (N := N) st.1)
        (nonlinearPotentialGradient kappa beta g
          (canonicalFlowPosition (N := N) kappa beta g hbeta a st))) i := by
    simp only [PiLp.neg_apply, inverseSqrtMassTransform_apply]
    exact ((hm i).sqrt.inv.mul (hgradient i)).neg
  exact (hv i).mul hforce

theorem measurable_canonicalOrderedRotatedSource
    (kappa beta g : Real) (hbeta : 2 * kappa ^ 2 / 9 < beta)
    (a : Real) (k : OrderedModeIndex N) :
    Measurable (canonicalOrderedRotatedSource (N := N)
      kappa beta g hbeta a k) := by
  have hfrequency : Measurable fun st : CanonicalSample × Real =>
      canonicalOrderedFrequency (N := N) k st.1 :=
    (measurable_canonicalOrderedFrequency (N := N) k).comp measurable_fst
  have hforce := measurable_canonicalOrderedNonlinearForce
    (N := N) kappa beta g hbeta a k
  change Measurable fun st : CanonicalSample × Real =>
    phaseFactor (canonicalOrderedFrequency (N := N) k st.1 * st.2) *
      forcedModeSource (canonicalOrderedFrequency (N := N) k st.1)
        (orderedSignedNonlinearForce (canonicalMass (N := N) st.1)
          kappa beta g k
          (canonicalFlowPosition (N := N) kappa beta g hbeta a st))
  apply Measurable.mul
  · unfold phaseFactor
    fun_prop
  · unfold forcedModeSource
    fun_prop

theorem measurable_canonicalSignedRotatedSource
    (kappa beta g : Real) (hbeta : 2 * kappa ^ 2 / 9 < beta)
    (a : Real) (entry : PhaseSign × OrderedModeIndex N) :
    Measurable (canonicalSignedRotatedSource (N := N)
      kappa beta g hbeta a entry) := by
  rcases entry with ⟨sign, k⟩
  have h := measurable_canonicalOrderedRotatedSource
    (N := N) kappa beta g hbeta a k
  cases sign with
  | phase =>
      change Measurable (canonicalOrderedRotatedSource (N := N)
        kappa beta g hbeta a k)
      exact h
  | conjugate =>
      change Measurable fun st => star
        (canonicalOrderedRotatedSource (N := N) kappa beta g hbeta a k st)
      exact Complex.continuous_conj.measurable.comp h

variable {I : Type*} [Fintype I] [DecidableEq I]

theorem measurable_canonicalSignedBlockInsertion
    (kappa beta g : Real) (hbeta : 2 * kappa ^ 2 / 9 < beta)
    (a : Real) (entry : I → PhaseSign × OrderedModeIndex N)
    (block : Finset I) :
    Measurable (canonicalSignedBlockInsertion (N := N)
      kappa beta g hbeta a entry block) := by
  unfold canonicalSignedBlockInsertion
  apply Finset.measurable_sum
  intro i _hi
  apply Measurable.mul
  · apply Finset.measurable_prod
    intro j _hj
    exact measurable_canonicalSignedInteractionAmplitude
      (N := N) kappa beta g hbeta a (entry j)
  · exact measurable_canonicalSignedRotatedSource
      (N := N) kappa beta g hbeta a (entry i)

/-- Continuous canonical iid block integral.  It is a genuine Bochner
integral expression; integrability is not asserted in this module. -/
def canonicalSignedBlockBochnerIntegral
    (kappa beta g : Real) (hbeta : 2 * kappa ^ 2 / 9 < beta)
    (a : Real) (entry : I → PhaseSign × OrderedModeIndex N)
    (block : Finset I) (time : Real) : Complex :=
  ∫ omega, canonicalSignedBlockObservable (N := N)
      kappa beta g hbeta a entry block (omega, time)
    ∂canonicalIIDMassPhaseEnsemble.probability

/-- Continuous canonical iid expectation of the exact one-slot source. -/
def canonicalSignedBlockInsertionBochnerIntegral
    (kappa beta g : Real) (hbeta : 2 * kappa ^ 2 / 9 < beta)
    (a : Real) (entry : I → PhaseSign × OrderedModeIndex N)
    (block : Finset I) (time : Real) : Complex :=
  ∫ omega, canonicalSignedBlockInsertion (N := N)
      kappa beta g hbeta a entry block (omega, time)
    ∂canonicalIIDMassPhaseEnsemble.probability

theorem aestronglyMeasurable_canonicalSignedBlock_fixedTime
    (kappa beta g : Real) (hbeta : 2 * kappa ^ 2 / 9 < beta)
    (a : Real) (entry : I → PhaseSign × OrderedModeIndex N)
    (block : Finset I) (time : Real) :
    AEStronglyMeasurable
      (fun omega : CanonicalSample =>
        canonicalSignedBlockObservable (N := N)
          kappa beta g hbeta a entry block (omega, time))
      canonicalIIDMassPhaseEnsemble.probability :=
  (measurable_canonicalSignedBlockObservable_fixedTime
    (N := N) kappa beta g hbeta a entry block time).aestronglyMeasurable

theorem aestronglyMeasurable_canonicalSignedBlockInsertion_fixedTime
    (kappa beta g : Real) (hbeta : 2 * kappa ^ 2 / 9 < beta)
    (a : Real) (entry : I → PhaseSign × OrderedModeIndex N)
    (block : Finset I) (time : Real) :
    AEStronglyMeasurable
      (fun omega : CanonicalSample =>
        canonicalSignedBlockInsertion (N := N)
          kappa beta g hbeta a entry block (omega, time))
      canonicalIIDMassPhaseEnsemble.probability := by
  exact (measurable_canonicalSignedBlockInsertion
    (N := N) kappa beta g hbeta a entry block).comp
      (measurable_id.prodMk measurable_const) |>.aestronglyMeasurable

/-- Continuous-law connected cumulant built from all finite block integrals. -/
def canonicalSignedConnectedCumulant
    [Nonempty I]
    (kappa beta g : Real) (hbeta : 2 * kappa ^ 2 / 9 < beta)
    (a : Real) (entry : I → PhaseSign × OrderedModeIndex N)
    (time : Real) : Complex :=
  suppliedConnectedCumulantPath
    (canonicalSignedBlockBochnerIntegral (N := N)
      kappa beta g hbeta a entry) time

/-- Formal partition/Mobius source assembled from the concrete continuous
block integrals and concrete source-insertion integrals. -/
def canonicalSignedConnectedCumulantHierarchySource
    [Nonempty I]
    (kappa beta g : Real) (hbeta : 2 * kappa ^ 2 / 9 < beta)
    (a : Real) (entry : I → PhaseSign × OrderedModeIndex N)
    (time : Real) : Complex :=
  suppliedConnectedCumulantHierarchySource
    (canonicalSignedBlockBochnerIntegral (N := N)
      kappa beta g hbeta a entry)
    (canonicalSignedBlockInsertionBochnerIntegral (N := N)
      kappa beta g hbeta a entry) time

end

end ArchonPhysics.CanonicalIIDCoerciveContinuousMomentFrontier
