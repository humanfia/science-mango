import ArchonPhysics.CanonicalIIDCoerciveClusterExpectationClosure
import ArchonPhysics.PhyslibFPUTUniformMomentDecoherencePropagation

/-!
# Uniform canonical iid coercive block-moment bounds

This module turns a system-uniform bound on the deterministic canonical
signed-amplitude envelope into a system-uniform bound on every fixed
continuous-law Bochner block moment.  For a block `block`, the explicit
witness is

`canonicalSignedBlockEnvelope A block = (1 + A) ^ block.card`.

The resulting family theorem has exactly the `hmoment` shape required by
`tendsto_orderedClusterFactorizationDefect_zero_of_uniformMomentBound`; the
last theorem applies that convergence result directly.

The current shell API defines `cutoffRadius` by classical choice and provides
no continuity or local boundedness theorem for that choice as the coupling
varies.  Consequently, convergence of a coupling sequence alone does not
currently imply boundedness of `canonicalSignedAmplitudeEnvelope`.  The
pointwise premise `forall scale, envelope (g scale) <= A` is therefore kept
explicit.  No RPA closure, decay, or kinetic conclusion is asserted here.
-/

namespace ArchonPhysics.CanonicalIIDCoerciveUniformBlockMomentBound

open scoped BigOperators Topology

open Filter
open ArchonPhysics
open ArchonPhysics.CanonicalIIDCoerciveActualExpectationAdapter
open ArchonPhysics.CanonicalIIDCoerciveActualExpectationCompleted
open ArchonPhysics.CanonicalIIDCoerciveClusterExpectationClosure
open ArchonPhysics.CanonicalIIDCoerciveContinuousMomentFrontier
open ArchonPhysics.CanonicalIIDCoerciveSignedModalObservableBridge
open ArchonPhysics.FinitePhaseMonomials
open ArchonPhysics.OrderedTranslationLastMode
open ArchonPhysics.PhyslibFPUTArbitraryClusterDecoherencePropagation
open ArchonPhysics.PhyslibFPUTHigherOrderClusterFactorizationPropagation
open ArchonPhysics.PhyslibFPUTUniformMomentDecoherencePropagation
open ArchonPhysics.RandomMassPositiveCollisionData

noncomputable section

variable {N : Nat} [NeZero N]
variable {I : Type*} [Fintype I] [DecidableEq I]

omit [Fintype I] [DecidableEq I] in
/-- The deterministic block envelope is monotone in a nonnegative amplitude
envelope. -/
theorem canonicalSignedBlockEnvelope_mono_of_nonneg
    (block : Finset I) {A B : Real} (hA : 0 <= A) (hAB : A <= B) :
    canonicalSignedBlockEnvelope A block <=
      canonicalSignedBlockEnvelope B block := by
  unfold canonicalSignedBlockEnvelope
  exact pow_le_pow_left₀ (by linarith) (by linarith) block.card

/-- A common upper bound for the one-slot canonical envelope bounds the
Bochner moment at every system index by one fixed block envelope. -/
theorem norm_canonicalSignedBlockBochnerIntegral_le_uniformEnvelope
    (hN : 3 <= N) {a : Real} (ha0 : 0 <= a) (ha1 : a <= 1 / 4)
    (kappa beta : Real) (g : Nat -> Real)
    (hbeta : 2 * kappa ^ 2 / 9 < beta)
    (entry : I -> PhaseSign × OrderedModeIndex N)
    (hpositive : forall i, (entry i).2 ≠
      lastOrderedIndex (ι := Lattice.Site N))
    (block : Finset I) (time : Nat -> Real) (A : Real)
    (henvelope : forall scale,
      canonicalSignedAmplitudeEnvelope N kappa beta (g scale) hbeta <= A)
    (scale : Nat) :
    ‖canonicalSignedBlockBochnerIntegral (N := N)
        kappa beta (g scale) hbeta a entry block (time scale)‖ <=
      canonicalSignedBlockEnvelope A block := by
  calc
    ‖canonicalSignedBlockBochnerIntegral (N := N)
        kappa beta (g scale) hbeta a entry block (time scale)‖ <=
        canonicalSignedBlockEnvelope
          (canonicalSignedAmplitudeEnvelope N kappa beta (g scale) hbeta)
          block :=
      norm_canonicalSignedBlockBochnerIntegral_le_envelope
        hN ha0 ha1 kappa beta (g scale) hbeta entry hpositive block
          (time scale)
    _ <= canonicalSignedBlockEnvelope A block :=
      canonicalSignedBlockEnvelope_mono_of_nonneg block
        (canonicalSignedAmplitudeEnvelope_nonneg
          (N := N) kappa beta (g scale) hbeta)
        (henvelope scale)

/-- For a fixed cluster, the explicit witness `(1 + A) ^ cluster.card`
uniformly bounds all system-indexed canonical Bochner moments. -/
theorem exists_systemUniform_canonicalSignedBlockBochnerIntegral_bound
    (hN : 3 <= N) {a : Real} (ha0 : 0 <= a) (ha1 : a <= 1 / 4)
    (kappa beta : Real) (g : Nat -> Real)
    (hbeta : 2 * kappa ^ 2 / 9 < beta)
    (entry : I -> PhaseSign × OrderedModeIndex N)
    (hpositive : forall i, (entry i).2 ≠
      lastOrderedIndex (ι := Lattice.Site N))
    (cluster : Finset I) (time : Nat -> Real) (A : Real)
    (henvelope : forall scale,
      canonicalSignedAmplitudeEnvelope N kappa beta (g scale) hbeta <= A) :
    exists bound : Real, 0 <= bound ∧ forall scale,
      ‖canonicalSignedBlockBochnerIntegral (N := N)
          kappa beta (g scale) hbeta a entry cluster (time scale)‖ <= bound := by
  have hA : 0 <= A :=
    (canonicalSignedAmplitudeEnvelope_nonneg
      (N := N) kappa beta (g 0) hbeta).trans (henvelope 0)
  refine ⟨canonicalSignedBlockEnvelope A cluster, ?_, ?_⟩
  · unfold canonicalSignedBlockEnvelope
    exact pow_nonneg (by linarith) cluster.card
  · intro scale
    exact norm_canonicalSignedBlockBochnerIntegral_le_uniformEnvelope
      hN ha0 ha1 kappa beta g hbeta entry hpositive cluster time A
        henvelope scale

/-- Exact `hmoment` adapter for an ordered family of fixed finite clusters.
The bound may depend on the cluster level but not on the scaling index. -/
theorem canonicalSignedBlockBochnerIntegral_hmoment_of_uniformEnvelope
    (hN : 3 <= N) {a : Real} (ha0 : 0 <= a) (ha1 : a <= 1 / 4)
    (kappa beta : Real) (g : Nat -> Real)
    (hbeta : 2 * kappa ^ 2 / 9 < beta)
    (entry : I -> PhaseSign × OrderedModeIndex N)
    (hpositive : forall i, (entry i).2 ≠
      lastOrderedIndex (ι := Lattice.Site N))
    (cluster : Nat -> Finset I) (time : Nat -> Real)
    (A : Real)
    (henvelope : forall scale,
      canonicalSignedAmplitudeEnvelope N kappa beta (g scale) hbeta <= A) :
    forall level, exists bound : Real, forall scale,
      ‖canonicalSignedBlockBochnerIntegral (N := N)
          kappa beta (g scale) hbeta a entry (cluster level) (time scale)‖ <=
        bound := by
  intro level
  rcases exists_systemUniform_canonicalSignedBlockBochnerIntegral_bound
      hN ha0 ha1 kappa beta g hbeta entry hpositive (cluster level) time A
        henvelope with
    ⟨bound, _hboundNonneg, hbound⟩
  exact ⟨bound, hbound⟩

omit [Fintype I] [DecidableEq I] in
/-- The empty canonical Bochner block moment is exactly one because the
canonical iid ensemble is a probability measure. -/
theorem canonicalSignedBlockBochnerIntegral_empty
    (kappa beta g : Real) (hbeta : 2 * kappa ^ 2 / 9 < beta)
    (a : Real) (entry : I -> PhaseSign × OrderedModeIndex N) (time : Real) :
    canonicalSignedBlockBochnerIntegral (N := N)
      kappa beta g hbeta a entry (∅ : Finset I) time = 1 := by
  let _ : MeasureTheory.IsFiniteMeasure canonicalIIDMassPhaseEnsemble.probability :=
    ⟨by rw [canonicalIIDMassPhaseEnsemble.probability_univ]; norm_num⟩
  change (∫ _omega : RandomEnsemble.SampleSpace, (1 : Complex)
    ∂canonicalIIDMassPhaseEnsemble.probability) = 1
  rw [MeasureTheory.integral_const]
  rw [MeasureTheory.Measure.real, canonicalIIDMassPhaseEnsemble.probability_univ]
  norm_num

/-- Direct continuous-law specialization of the generic ordered-cluster
convergence theorem.  Uniform envelope control supplies precisely its
`hmoment` premise; binary factorization decay remains the sole asymptotic
input. -/
theorem tendsto_orderedCanonicalSignedClusterFactorizationDefect_zero_of_uniformEnvelope
    (hN : 3 <= N) {a : Real} (ha0 : 0 <= a) (ha1 : a <= 1 / 4)
    (kappa beta : Real) (g : Nat -> Real)
    (hbeta : 2 * kappa ^ 2 / 9 < beta)
    (entry : I -> PhaseSign × OrderedModeIndex N)
    (hpositive : forall i, (entry i).2 ≠
      lastOrderedIndex (ι := Lattice.Site N))
    (cluster : Nat -> Finset I) (time : Nat -> Real)
    (A : Real)
    (henvelope : forall scale,
      canonicalSignedAmplitudeEnvelope N kappa beta (g scale) hbeta <= A)
    (hbinary : forall level, Tendsto
      (fun scale => blockFactorizationDefect
        (canonicalSignedBlockBochnerIntegral (N := N)
          kappa beta (g scale) hbeta a entry)
        (orderedClusterUnion cluster level) (cluster level) (time scale))
      atTop (nhds 0))
    (count : Nat) :
    Tendsto
      (fun scale => orderedClusterFactorizationDefect
        (canonicalSignedBlockBochnerIntegral (N := N)
          kappa beta (g scale) hbeta a entry)
        cluster count (time scale))
      atTop (nhds 0) := by
  exact tendsto_orderedClusterFactorizationDefect_zero_of_uniformMomentBound
    (fun scale => canonicalSignedBlockBochnerIntegral (N := N)
      kappa beta (g scale) hbeta a entry)
    cluster time
    (fun scale => canonicalSignedBlockBochnerIntegral_empty
      kappa beta (g scale) hbeta a entry (time scale))
    hbinary
    (canonicalSignedBlockBochnerIntegral_hmoment_of_uniformEnvelope
      hN ha0 ha1 kappa beta g hbeta entry hpositive cluster time A henvelope)
    count

end

end ArchonPhysics.CanonicalIIDCoerciveUniformBlockMomentBound
