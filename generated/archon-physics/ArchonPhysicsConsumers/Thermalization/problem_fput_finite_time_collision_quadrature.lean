import ArchonPhysics.FPUTFiniteTimeCollisionQuadrature

/-!
# Consumer: finite-time FPUT collision quadrature
-/

namespace ArchonPhysicsConsumers.Thermalization

open ArchonPhysics.EqualMassPeriodicFPUTDiscreteContinuumShellBridge
open ArchonPhysics.FPUTFiniteTimeCollisionQuadrature
open ArchonPhysics.Lattice
open Set
open scoped BigOperators

noncomputable section

theorem FPUT_finiteTime_collision_slice_quadrature_consumer
    (N : Nat) [NeZero N]
    (mismatch mark : Real → Real)
    {T markBound markSlope mismatchSlope : Real}
    (hT : 0 < T) (hmarkBound : 0 ≤ markBound)
    (hmarkSlope : 0 ≤ markSlope) (hmismatchSlope : 0 ≤ mismatchSlope)
    (hmarkContinuous : Continuous mark)
    (hmismatchContinuous : Continuous mismatch)
    (hmarkEndpoint : mark 0 = mark (2 * Real.pi))
    (hmismatchEndpoint : mismatch 0 = mismatch (2 * Real.pi))
    (hmarkBoundOn : ∀ x ∈ Icc (0 : Real) (2 * Real.pi),
      |mark x| ≤ markBound)
    (hmarkLipOn : ∀ x ∈ Icc (0 : Real) (2 * Real.pi),
      ∀ y ∈ Icc (0 : Real) (2 * Real.pi),
        |mark x - mark y| ≤ markSlope * |x - y|)
    (hmismatchLipOn : ∀ x ∈ Icc (0 : Real) (2 * Real.pi),
      ∀ y ∈ Icc (0 : Real) (2 * Real.pi),
        |mismatch x - mismatch y| ≤ mismatchSlope * |x - y|) :
    |(2 * Real.pi / (N : Real)) *
        ∑ k : Site N,
          finiteTimeMarkedCollisionIntegrand mismatch mark T
            (gridWaveNumber N k) -
      ∫ x in (0 : Real)..(2 * Real.pi),
        finiteTimeMarkedCollisionIntegrand mismatch mark T x| ≤
      finiteTimeMarkedCollisionLipschitzConstant
          T markBound markSlope mismatchSlope *
        (2 * Real.pi) ^ 2 / (N : Real) :=
  abs_finiteTimeMarkedCollision_fourierGrid_sub_integral_le
    N mismatch mark hT hmarkBound hmarkSlope hmismatchSlope
    hmarkContinuous hmismatchContinuous hmarkEndpoint hmismatchEndpoint
    hmarkBoundOn hmarkLipOn hmismatchLipOn

#print axioms FPUT_finiteTime_collision_slice_quadrature_consumer

end

end ArchonPhysicsConsumers.Thermalization
