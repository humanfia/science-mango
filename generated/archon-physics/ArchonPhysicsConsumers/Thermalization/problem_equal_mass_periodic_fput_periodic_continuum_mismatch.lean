import ArchonPhysics.EqualMassPeriodicFPUTPeriodicContinuumMismatch

/-!
# Consumer: global periodic equal-mass FPUT collision mismatch
-/

namespace ArchonPhysicsConsumers.Thermalization

open ArchonPhysics.EqualMassPeriodicFPUTDiscreteContinuumShellBridge
open ArchonPhysics.EqualMassPeriodicFPUTPeriodicContinuumMismatch
open ArchonPhysics.EqualMassPeriodicFPUTTwoToTwoMomentumShell
open ArchonPhysics.FPUTFiniteTimeCollisionQuadrature
open ArchonPhysics.Lattice
open ArchonPhysics.NormalizedResonancePeakKernel
open Set
open scoped BigOperators

noncomputable section

theorem periodic_FPUT_mismatch_grid_identity_consumer
    {N : Nat} [NeZero N] (k₀ k₁ k₂ : Site N) :
    periodicReducedFourWaveMismatch
        (gridWaveNumber N k₀) (gridWaveNumber N k₁)
          (gridWaveNumber N k₂) =
      reducedTwoToTwoMismatch k₀ k₁ k₂ :=
  periodicReducedFourWaveMismatch_grid_eq k₀ k₁ k₂

theorem actual_FPUT_collision_slice_quadrature_consumer
    (N : Nat) [NeZero N] (k₀ k₁ : Site N)
    (mark : Real → Real) {T markBound markSlope : Real}
    (hT : 0 < T) (hmarkBound : 0 ≤ markBound)
    (hmarkSlope : 0 ≤ markSlope)
    (hmarkContinuous : Continuous mark)
    (hmarkEndpoint : mark 0 = mark (2 * Real.pi))
    (hmarkBoundOn : ∀ x ∈ Icc (0 : Real) (2 * Real.pi),
      |mark x| ≤ markBound)
    (hmarkLipOn : ∀ x ∈ Icc (0 : Real) (2 * Real.pi),
      ∀ y ∈ Icc (0 : Real) (2 * Real.pi),
        |mark x - mark y| ≤ markSlope * |x - y|) :
    |(2 * Real.pi / (N : Real)) *
        ∑ k₂ : Site N, mark (gridWaveNumber N k₂) *
          normalizedFiniteTimeResonanceKernel
            (reducedTwoToTwoMismatch k₀ k₁ k₂) T -
      ∫ x in (0 : Real)..(2 * Real.pi),
        finiteTimeMarkedCollisionIntegrand
          (periodicReducedFourWaveMismatch
            (gridWaveNumber N k₀) (gridWaveNumber N k₁)) mark T x| ≤
      finiteTimeMarkedCollisionLipschitzConstant
          T markBound markSlope 2 *
        (2 * Real.pi) ^ 2 / (N : Real) :=
  abs_actualFPUTCollisionSlice_sub_continuum_le
    N k₀ k₁ mark hT hmarkBound hmarkSlope hmarkContinuous
      hmarkEndpoint hmarkBoundOn hmarkLipOn

#print axioms periodic_FPUT_mismatch_grid_identity_consumer
#print axioms actual_FPUT_collision_slice_quadrature_consumer

end

end ArchonPhysicsConsumers.Thermalization
