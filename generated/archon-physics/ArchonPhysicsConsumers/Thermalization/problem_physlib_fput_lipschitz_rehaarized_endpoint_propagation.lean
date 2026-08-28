import ArchonPhysics.PhyslibFPUTLipschitzReHaarizedEndpointPropagation

/-!
# Consumer: Lipschitz propagation of a multimode FPUT endpoint

The consumer keeps the block state in an arbitrary metric space `X` and
maps it to a complex modal amplitude.  Thus the theorem applies directly to
a full finite FPUT state rather than only to a scalar surrogate.
-/

namespace ArchonPhysicsConsumers.Thermalization.PhyslibFPUTLipschitzReHaarizedEndpointPropagation

open ArchonPhysics.PhyslibFPUTLipschitzReHaarizedEndpointPropagation

/-- A Mathlib `LipschitzWith` witness closes the exact endpoint triangle for
a multimode state and a complex observable. -/
theorem problem_lipschitz_rehaarized_endpoint_propagation
    {X : Type*} [PseudoMetricSpace X]
    (actualBlock referenceBlock : X → Complex) (x y : X)
    (A : NNReal) {initialDelta picardDelta : Real}
    (hactualBlock : LipschitzWith A actualBlock)
    (hinitial : dist x y ≤ initialDelta)
    (hpicard : ‖actualBlock y - referenceBlock y‖ ≤ picardDelta) :
    ‖actualBlock x - referenceBlock y‖ ≤
      (A : Real) * initialDelta + picardDelta :=
  norm_actualBlock_sub_referenceBlock_le_of_lipschitzWith
    actualBlock referenceBlock x y A hactualBlock hinitial hpicard

/-- Cubic input errors remain cubic after a Lipschitz block observable. -/
theorem problem_lipschitz_rehaarized_endpoint_abs_cube
    {X : Type*} [PseudoMetricSpace X]
    (actualBlock referenceBlock : X → Complex) (x y : X)
    (A : NNReal)
    {g initialDelta picardDelta Cinitial Cpicard : Real}
    (hactualBlock : LipschitzWith A actualBlock)
    (hinitial : dist x y ≤ initialDelta)
    (hpicard : ‖actualBlock y - referenceBlock y‖ ≤ picardDelta)
    (hinitialCubic : initialDelta ≤ Cinitial * |g| ^ 3)
    (hpicardCubic : picardDelta ≤ Cpicard * |g| ^ 3) :
    ‖actualBlock x - referenceBlock y‖ ≤
      ((A : Real) * Cinitial + Cpicard) * |g| ^ 3 :=
  norm_actualBlock_sub_referenceBlock_le_abs_cube_of_lipschitzWith
    actualBlock referenceBlock x y A hactualBlock hinitial hpicard
      hinitialCubic hpicardCubic

#print axioms problem_lipschitz_rehaarized_endpoint_propagation
#print axioms problem_lipschitz_rehaarized_endpoint_abs_cube
#print axioms LipschitzReHaarizedEndpointPropagationData.actualBlock_stable
#print axioms LipschitzReHaarizedEndpointPropagationData.final_near_abs_cube

end ArchonPhysicsConsumers.Thermalization.PhyslibFPUTLipschitzReHaarizedEndpointPropagation
