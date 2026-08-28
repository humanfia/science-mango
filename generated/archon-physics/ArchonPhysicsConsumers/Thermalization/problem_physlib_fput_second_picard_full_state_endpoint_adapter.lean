import ArchonPhysics.PhyslibFPUTSecondPicardFullStateEndpointAdapter

/-!
# Consumer: full-state FPUT second-Picard endpoint propagation

This consumer exposes the type-correct block triangle and the direct
Hamiltonian-to-cubic endpoint theorem.  The initial state lives in a full
seminormed state space; only the observed endpoint amplitude is complex.
-/

namespace ArchonPhysicsConsumers.Thermalization.PhyslibFPUTSecondPicardFullStateEndpointAdapter

open ArchonPhysics
open ArchonPhysics.Lattice
open ArchonPhysics.PhyslibFPUTSecondPicardDeterministicCoupling
open ArchonPhysics.PhyslibFPUTSecondPicardFullStateEndpointAdapter

noncomputable section

/-- Consumer-facing full-state deterministic triangle. -/
theorem problem_full_state_endpoint_triangle
    {E : Type*} [SeminormedAddCommGroup E]
    (actualBlock referenceBlock : E → Complex) (x y : E)
    {initialDelta flowAmplification picardDelta : Real}
    (hA : 0 ≤ flowAmplification)
    (hxy : ‖x - y‖ ≤ initialDelta)
    (hflow : ‖actualBlock x - actualBlock y‖ ≤
      flowAmplification * ‖x - y‖)
    (hpicard : ‖actualBlock y - referenceBlock y‖ ≤ picardDelta) :
    ‖actualBlock x - referenceBlock y‖ ≤
      flowAmplification * initialDelta + picardDelta :=
  norm_fullStateBlock_sub_referenceBlock_le
    actualBlock referenceBlock x y hA hxy hflow hpicard

/-- Consumer-facing statement that the physical second-Picard radius has
the exact cubic form needed by blockwise endpoint propagation. -/
theorem problem_physlib_second_picard_delta_is_cubic
    {N : Nat} [NeZero N]
    (m : PositiveMassConfig N) (mUpper kappa beta g H : Real)
    (radius : Site N → Real) (T : Real) (observed : Site N) :
    physlibSecondPicardCouplingDelta
        m mUpper kappa beta g H radius T observed ≤
      ArchonPhysics.PhyslibFPUTCubicHistoryLipschitzRemainder.cubicLipschitzAfterSecondPicardCoefficientUnitEnergyWindowEnvelope
          m mUpper kappa beta g H radius T observed * |g| ^ 3 :=
  physlibSecondPicardCouplingDelta_le_unit_mul_abs_cube
    m mUpper kappa beta g H radius T observed

#print axioms problem_full_state_endpoint_triangle
#print axioms problem_physlib_second_picard_delta_is_cubic
#print axioms physlibSecondPicard_fullState_reference_consistent
#print axioms physlibSecondPicard_fullState_final_near_abs_cube

end

end ArchonPhysicsConsumers.Thermalization.PhyslibFPUTSecondPicardFullStateEndpointAdapter
