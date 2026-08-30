import ArchonPhysics.CanonicalIIDCoerciveActualExpectationClosure

/-!
# Actual canonical signed-block expectation theorem

This module completes the concrete nonlinear-force, amplitude, finite-product,
and Bochner-integrability estimates and feeds them into the parametric
integral theorem.  The result has no abstract domination or base-time
integrability arguments: those are derived from the actual coercive shell and
the frozen-support nontranslation frequency bound.
-/

namespace ArchonPhysics.CanonicalIIDCoerciveActualExpectationTheorem

open scoped BigOperators Matrix Topology

open ArchonPhysics
open ArchonPhysics.CanonicalIIDCoerciveActualExpectationAdapter
open ArchonPhysics.CanonicalIIDCoerciveActualExpectationClosure
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
open ArchonPhysics.RandomMassMeasurableOrderedEigenframe
open ArchonPhysics.RandomMassOrderedProjectorBridge
open ArchonPhysics.RandomMassPositiveCollisionData
open ArchonPhysics.ReducedModeTransform
open MeasureTheory
open Metric

noncomputable section

variable {N : Nat} [NeZero N]

theorem norm_nonlinearPotentialGradient_le
    (kappa beta g B : Real) (hB : 0 ≤ B)
    (q : HilbertConfiguration N)
    (hq : ∀ i : Lattice.Site N,
      |Lattice.forwardDifference (asConfiguration q) i| ≤ B) :
    ‖nonlinearPotentialGradient kappa beta g q‖ ≤
      2 * (N : Real) *
        canonicalNonlinearBondDerivativeEnvelope kappa beta g B := by
  classical
  let D := canonicalNonlinearBondDerivativeEnvelope kappa beta g B
  have hD : 0 ≤ D :=
    canonicalNonlinearBondDerivativeEnvelope_nonneg kappa beta g B hB
  calc
    ‖nonlinearPotentialGradient kappa beta g q‖ =
        ‖∑ i : Lattice.Site N,
          nonlinearPotentialDerivative kappa beta g
              (Lattice.forwardDifference (asConfiguration q) i) •
            bondDirection i‖ := rfl
    _ ≤ ∑ i : Lattice.Site N,
        ‖nonlinearPotentialDerivative kappa beta g
              (Lattice.forwardDifference (asConfiguration q) i) •
            bondDirection i‖ := norm_sum_le _ _
    _ ≤ ∑ _i : Lattice.Site N, D * 2 := by
      apply Finset.sum_le_sum
      intro i _hi
      rw [norm_smul, Real.norm_eq_abs]
      exact mul_le_mul
        (abs_nonlinearPotentialDerivative_le_envelope
          kappa beta g _ B (hq i))
        (norm_bondDirection_le_two i) (norm_nonneg _) hD
    _ = 2 * (N : Real) * D := by
      simp [ZMod.card]
      ring

theorem norm_transformedNonlinearForce_le_envelope
    (m : Lattice.PositiveMassConfig N)
    (hmass : ∀ i, (4 / 5 : Real) ≤ m.mass i)
    (kappa beta g B : Real) (hB : 0 ≤ B)
    (q : HilbertConfiguration N)
    (hq : ∀ i : Lattice.Site N,
      |Lattice.forwardDifference (asConfiguration q) i| ≤ B) :
    ‖transformedNonlinearForce m kappa beta g q‖ ≤
      canonicalTransformedNonlinearForceEnvelope N kappa beta g B := by
  calc
    ‖transformedNonlinearForce m kappa beta g q‖ =
        ‖inverseSqrtMassTransform m
          (nonlinearPotentialGradient kappa beta g q)‖ := by
      simp only [transformedNonlinearForce, norm_neg]
    _ ≤ 2 * ‖nonlinearPotentialGradient kappa beta g q‖ :=
      norm_inverseSqrtMassTransform_le_two_mul m hmass _
    _ ≤ 2 * (2 * (N : Real) *
        canonicalNonlinearBondDerivativeEnvelope kappa beta g B) := by
      gcongr
      exact norm_nonlinearPotentialGradient_le kappa beta g B hB q hq
    _ = canonicalTransformedNonlinearForceEnvelope N kappa beta g B := by
      unfold canonicalTransformedNonlinearForceEnvelope
      ring

theorem norm_phaseSignActComplex (sign : PhaseSign) (z : Complex) :
    ‖phaseSignActComplex sign z‖ = ‖z‖ := by
  cases sign <;> simp [phaseSignActComplex]

theorem norm_complexModeAmplitude_le
    {omega Q P W B D : Real}
    (homega : 0 < omega) (homegaW : omega ≤ W)
    (hW : 0 ≤ W) (hQ : |Q| ≤ B) (hP : |P| ≤ B)
    (hB : 0 ≤ B)
    (hD : (Real.sqrt (2 * omega))⁻¹ ≤ D) (hD0 : 0 ≤ D) :
    ‖complexModeAmplitude omega Q P‖ ≤ (W * B + B) * D := by
  have hnum :
      ‖((omega * Q : Real) : Complex) + (P : Complex) * Complex.I‖ ≤
        W * B + B := by
    calc
      ‖((omega * Q : Real) : Complex) + (P : Complex) * Complex.I‖ ≤
          ‖((omega * Q : Real) : Complex)‖ +
            ‖(P : Complex) * Complex.I‖ := norm_add_le _ _
      _ = |omega| * |Q| + |P| := by
        simp [abs_mul]
      _ ≤ W * B + B := by
        rw [abs_of_pos homega]
        exact add_le_add
          (mul_le_mul homegaW hQ (abs_nonneg Q) hW) hP
  unfold complexModeAmplitude
  rw [norm_div, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg (Real.sqrt_nonneg _), div_eq_mul_inv]
  exact mul_le_mul hnum hD (inv_nonneg.mpr (Real.sqrt_nonneg _))
    (add_nonneg (mul_nonneg hW hB) hB)

theorem norm_forcedModeSource_le
    {omega force D : Real} (homega : 0 < omega)
    (hD : (Real.sqrt (2 * omega))⁻¹ ≤ D) (hD0 : 0 ≤ D) :
    ‖forcedModeSource omega force‖ ≤ |force| * D := by
  unfold forcedModeSource
  rw [norm_div, norm_mul, Complex.norm_I, one_mul]
  simp only [Complex.norm_real, Real.norm_eq_abs]
  rw [abs_of_nonneg (Real.sqrt_nonneg _), div_eq_mul_inv]
  exact mul_le_mul_of_nonneg_left hD (abs_nonneg force)

theorem abs_canonicalOrderedModalPosition_le_envelope_of_simple
    (kappa beta g : Real) (hbeta : 2 * kappa ^ 2 / 9 < beta)
    (a : Real) (omega : CanonicalSample)
    (hsimple : SimpleOrderedSpectrum
      (harmonicHermitian (canonicalMass (N := N) omega)))
    (k : OrderedModeIndex N) (time : Real)
    (hq : ‖canonicalFlowPosition (N := N)
        kappa beta g hbeta a (omega, time)‖ ≤
      (canonicalRandomMassPhaseEnergyShell N kappa beta g hbeta).cutoffRadius) :
    |canonicalOrderedModalPosition (N := N)
        kappa beta g hbeta a k (omega, time)| ≤
      canonicalWeightedCoordinateEnvelope N kappa beta g hbeta := by
  have hproject := abs_orderedSignedCoordinate_le_norm
    (canonicalMass (N := N) omega) hsimple k
    (sqrtMassTransform (canonicalMass (N := N) omega)
      (canonicalFlowPosition (N := N)
        kappa beta g hbeta a (omega, time)))
  have hweight := norm_sqrtMassTransform_canonical_le_envelope
    kappa beta g hbeta omega
      (canonicalFlowPosition (N := N)
        kappa beta g hbeta a (omega, time)) hq
  exact (show
    |canonicalOrderedModalPosition (N := N)
        kappa beta g hbeta a k (omega, time)| ≤ _ by
      simpa [canonicalOrderedModalPosition, orderedSignedCoordinate,
        orderedEigenvectorSample, harmonicHermitianSample, harmonicHermitian,
        canonicalMass, massWeightedPositionSample] using hproject.trans hweight)

theorem abs_canonicalOrderedModalMomentum_le_envelope_of_simple
    (kappa beta g : Real) (hbeta : 2 * kappa ^ 2 / 9 < beta)
    (a : Real) (omega : CanonicalSample)
    (hsimple : SimpleOrderedSpectrum
      (harmonicHermitian (canonicalMass (N := N) omega)))
    (k : OrderedModeIndex N) (time : Real)
    (hp : ‖canonicalFlowMomentum (N := N)
        kappa beta g hbeta a (omega, time)‖ ≤
      (canonicalRandomMassPhaseEnergyShell N kappa beta g hbeta).cutoffRadius) :
    |canonicalOrderedModalMomentum (N := N)
        kappa beta g hbeta a k (omega, time)| ≤
      canonicalWeightedCoordinateEnvelope N kappa beta g hbeta := by
  have hproject := abs_orderedSignedCoordinate_le_norm
    (canonicalMass (N := N) omega) hsimple k
    (inverseSqrtMassTransform (canonicalMass (N := N) omega)
      (canonicalFlowMomentum (N := N)
        kappa beta g hbeta a (omega, time)))
  have hweight := norm_inverseSqrtMassTransform_canonical_le_envelope
    kappa beta g hbeta omega
      (canonicalFlowMomentum (N := N)
        kappa beta g hbeta a (omega, time)) hp
  exact (show
    |canonicalOrderedModalMomentum (N := N)
        kappa beta g hbeta a k (omega, time)| ≤ _ by
      simpa [canonicalOrderedModalMomentum, orderedSignedCoordinate,
        orderedEigenvectorSample, harmonicHermitianSample, harmonicHermitian,
        canonicalMass, massWeightedMomentumSample] using hproject.trans hweight)

end

end ArchonPhysics.CanonicalIIDCoerciveActualExpectationTheorem
