import ArchonPhysics.CanonicalIIDCoerciveExpectationHierarchy
import ArchonPhysics.UniformRandomMassHarmonicSpectrumBound

/-!
# Actual canonical iid envelope and expectation adapter

This module discharges the last analytic premises in
`CanonicalIIDCoerciveExpectationHierarchy` for the genuine coercive
alpha--beta canonical flow.  On the common energy shell, frozen masses in
`[4/5,6/5]` give coarse explicit bounds for the mass transforms.  The full
quadratic-plus-cubic bond force is then bounded directly, while the
nontranslation infrared estimate `omega⁻¹ <= N` controls the complex-mode
normalization.  Finite products and one-slot insertions consequently have
uniform deterministic bounds and are Bochner integrable.

The final theorem differentiates the actual canonical signed-block
expectation without an abstract envelope or base-integrability premise.
Only finite volume, the coercive shell assumptions, and exclusion of the
translation zero mode remain.  These are domination estimates for the exact
finite-dimensional hierarchy; they assert no RPA, Markov closure, cumulant
decay, propagation of chaos, or kinetic limit.
-/

namespace ArchonPhysics.CanonicalIIDCoerciveActualExpectationAdapter

open scoped BigOperators Matrix Topology

open ArchonPhysics
open ArchonPhysics.CanonicalIIDCoerciveExpectationHierarchy
open ArchonPhysics.CanonicalIIDCoerciveSignedModalBlockHierarchy
open ArchonPhysics.CanonicalIIDCoerciveSignedModalHierarchy
open ArchonPhysics.CanonicalIIDCoerciveSignedModalObservableBridge
open ArchonPhysics.CanonicalRandomMassPhaseGlobalFlow
open ArchonPhysics.ComplexModeAmplitude
open ArchonPhysics.CoerciveHamiltonianPhyslib
open ArchonPhysics.ConcreteHamiltonGradients
open ArchonPhysics.FinitePhaseMonomials
open ArchonPhysics.ForcedComplexModeDuhamel
open ArchonPhysics.GlobalRandomMassModalObservable
open ArchonPhysics.MassWeightedHamiltonianDynamics
open ArchonPhysics.MeasurableOrderedEigenframe
open ArchonPhysics.MeasurableOrderedModeCoupling.Harmonic
open ArchonPhysics.MeasurableOrderedSpectrum
open ArchonPhysics.OrderedSingleModeProjector
open ArchonPhysics.OrderedTranslationLastMode
open ArchonPhysics.PhaseRenormalization
open ArchonPhysics.PhyslibFPUTBinaryInteractionTreeCouples
open ArchonPhysics.RandomMassMeasurableHarmonicEnergy
open ArchonPhysics.RandomMassOrderedProjectorBridge
open ArchonPhysics.RandomMassPositiveCollisionData
open ArchonPhysics.ReducedModeTransform
open ArchonPhysics.UniformRandomMassHarmonicSpectrumBound
open MeasureTheory
open Metric

noncomputable section

variable {N : Nat} [NeZero N]

/-- A nonnegative version of the common physical shell radius. -/
def canonicalNonnegativeShellRadius
    (N : Nat) [NeZero N] (kappa beta g : Real)
    (hbeta : 2 * kappa ^ 2 / 9 < beta) : Real :=
  max (canonicalRandomMassPhaseEnergyShell N kappa beta g hbeta).cutoffRadius 0

/-- Coarse common bound for either mass-weighted position or momentum. -/
def canonicalWeightedCoordinateEnvelope
    (N : Nat) [NeZero N] (kappa beta g : Real)
    (hbeta : 2 * kappa ^ 2 / 9 < beta) : Real :=
  2 * canonicalNonnegativeShellRadius N kappa beta g hbeta

/-- Deterministic upper bound for `1 / sqrt (2 omega)` on every selected
nontranslation ordered mode. -/
def canonicalPositiveFrequencyNormalizationEnvelope (N : Nat) : Real :=
  (Real.sqrt (2 * (N : Real)⁻¹))⁻¹

/-- Pointwise envelope for the quadratic-plus-cubic residual derivative at a
bond whose difference is bounded by `B`. -/
def canonicalNonlinearBondDerivativeEnvelope
    (kappa beta g B : Real) : Real :=
  |kappa * g| * B ^ 2 + |beta * g ^ 2| * B ^ 3

/-- Coarse norm bound for the full transformed nonlinear force. -/
def canonicalTransformedNonlinearForceEnvelope
    (N : Nat) (kappa beta g B : Real) : Real :=
  4 * (N : Real) * canonicalNonlinearBondDerivativeEnvelope kappa beta g B

/-- Uniform norm bound for one signed interaction-picture amplitude. -/
def canonicalSignedAmplitudeEnvelope
    (N : Nat) [NeZero N] (kappa beta g : Real)
    (hbeta : 2 * kappa ^ 2 / 9 < beta) : Real :=
  let B := canonicalWeightedCoordinateEnvelope N kappa beta g hbeta
  (Real.sqrt 5 * B + B) * canonicalPositiveFrequencyNormalizationEnvelope N

/-- Uniform norm bound for one signed full alpha--beta rotated source. -/
def canonicalSignedSourceEnvelope
    (N : Nat) [NeZero N] (kappa beta g : Real)
    (hbeta : 2 * kappa ^ 2 / 9 < beta) : Real :=
  let B := canonicalWeightedCoordinateEnvelope N kappa beta g hbeta
  canonicalTransformedNonlinearForceEnvelope N kappa beta g B *
    canonicalPositiveFrequencyNormalizationEnvelope N

/-- Uniform norm bound for an arbitrary fixed finite signed block. -/
def canonicalSignedBlockEnvelope {I : Type*}
    (A : Real) (block : Finset I) : Real :=
  (1 + A) ^ block.card

/-- Uniform norm bound for the exact one-slot source insertion. -/
def canonicalSignedBlockInsertionEnvelope {I : Type*}
    (A S : Real) (block : Finset I) : Real :=
  (block.card : Real) * canonicalSignedBlockEnvelope A block * S

theorem canonicalNonnegativeShellRadius_nonneg
    (kappa beta g : Real) (hbeta : 2 * kappa ^ 2 / 9 < beta) :
    0 ≤ canonicalNonnegativeShellRadius N kappa beta g hbeta := by
  simp [canonicalNonnegativeShellRadius]

theorem canonicalWeightedCoordinateEnvelope_nonneg
    (kappa beta g : Real) (hbeta : 2 * kappa ^ 2 / 9 < beta) :
    0 ≤ canonicalWeightedCoordinateEnvelope N kappa beta g hbeta := by
  unfold canonicalWeightedCoordinateEnvelope
  exact mul_nonneg (by norm_num)
    (canonicalNonnegativeShellRadius_nonneg kappa beta g hbeta)

theorem canonicalNonlinearBondDerivativeEnvelope_nonneg
    (kappa beta g B : Real) (hB : 0 ≤ B) :
    0 ≤ canonicalNonlinearBondDerivativeEnvelope kappa beta g B := by
  unfold canonicalNonlinearBondDerivativeEnvelope
  positivity

theorem canonicalTransformedNonlinearForceEnvelope_nonneg
    (kappa beta g B : Real) (hB : 0 ≤ B) :
    0 ≤ canonicalTransformedNonlinearForceEnvelope N kappa beta g B := by
  unfold canonicalTransformedNonlinearForceEnvelope
  exact mul_nonneg
    (mul_nonneg (by norm_num) (Nat.cast_nonneg N))
    (canonicalNonlinearBondDerivativeEnvelope_nonneg kappa beta g B hB)

theorem norm_sqrtMassTransform_le_two_mul
    (m : Lattice.PositiveMassConfig N)
    (hmass : ∀ i, m.mass i ≤ (6 / 5 : Real))
    (q : HilbertConfiguration N) :
    ‖sqrtMassTransform m q‖ ≤ 2 * ‖q‖ := by
  have hsq : ‖sqrtMassTransform m q‖ ^ 2 ≤ 4 * ‖q‖ ^ 2 := by
    rw [EuclideanSpace.real_norm_sq_eq, EuclideanSpace.real_norm_sq_eq]
    simp only [sqrtMassTransform_apply, mul_pow]
    calc
      (∑ i, Real.sqrt (m.mass i) ^ 2 * q i ^ 2) =
          ∑ i, m.mass i * q i ^ 2 := by
        apply Finset.sum_congr rfl
        intro i _hi
        rw [Real.sq_sqrt (m.mass_pos i).le]
      _ ≤ ∑ i, 4 * q i ^ 2 := by
        apply Finset.sum_le_sum
        intro i _hi
        exact mul_le_mul_of_nonneg_right
          ((hmass i).trans (by norm_num)) (sq_nonneg (q i))
      _ = 4 * ∑ i, q i ^ 2 := by rw [Finset.mul_sum]
  nlinarith [norm_nonneg (sqrtMassTransform m q), norm_nonneg q]

theorem norm_inverseSqrtMassTransform_le_two_mul
    (m : Lattice.PositiveMassConfig N)
    (hmass : ∀ i, (4 / 5 : Real) ≤ m.mass i)
    (p : HilbertConfiguration N) :
    ‖inverseSqrtMassTransform m p‖ ≤ 2 * ‖p‖ := by
  have hbase := sum_sq_inverseSqrtMassAction_le_inv_mul_sum_sq
    m (4 / 5 : Real) (by norm_num) hmass (asConfiguration p)
  have hsq : ‖inverseSqrtMassTransform m p‖ ^ 2 ≤ 4 * ‖p‖ ^ 2 := by
    rw [inverseSqrtMassTransform_eq_latticeAction,
      EuclideanSpace.real_norm_sq_eq, EuclideanSpace.real_norm_sq_eq]
    change (∑ i, Lattice.inverseSqrtMassAction m (asConfiguration p) i ^ 2) ≤
      4 * ∑ i, p i ^ 2
    calc
      (∑ i, Lattice.inverseSqrtMassAction m (asConfiguration p) i ^ 2) ≤
          (4 / 5 : Real)⁻¹ * ∑ i, asConfiguration p i ^ 2 := hbase
      _ ≤ 4 * ∑ i, p i ^ 2 := by
        exact mul_le_mul_of_nonneg_right (by norm_num)
          (Finset.sum_nonneg fun i _hi => sq_nonneg (p i))
  nlinarith [norm_nonneg (inverseSqrtMassTransform m p), norm_nonneg p]

theorem abs_orderedSignedCoordinate_le_norm
    (m : Lattice.PositiveMassConfig N)
    (hsimple : SimpleOrderedSpectrum (harmonicHermitian m))
    (k : OrderedModeIndex N) (x : WeightedConfiguration N) :
    |orderedSignedCoordinate m k x| ≤ ‖x‖ := by
  have hinner := abs_real_inner_le_norm x
    (signedOrderedEigenvectorLp (harmonicHermitian m) k)
  rw [signedOrderedEigenvectorLp_norm (harmonicHermitian m) hsimple k,
    mul_one] at hinner
  simpa only [orderedSignedCoordinate, signedOrderedEigenvectorLp,
    EuclideanSpace.inner_eq_star_dotProduct, star_trivial] using hinner

theorem norm_bondDirection_le_two (i : Lattice.Site N) :
    ‖bondDirection i‖ ≤ 2 := by
  calc
    ‖bondDirection i‖ =
        ‖EuclideanSpace.single (i + 1) 1 - EuclideanSpace.single i 1‖ := rfl
    _ ≤ ‖EuclideanSpace.single (i + 1) (1 : Real)‖ +
        ‖EuclideanSpace.single i (1 : Real)‖ := norm_sub_le _ _
    _ = 2 := by simp only [EuclideanSpace.norm_single, norm_one]; norm_num

end

end ArchonPhysics.CanonicalIIDCoerciveActualExpectationAdapter
