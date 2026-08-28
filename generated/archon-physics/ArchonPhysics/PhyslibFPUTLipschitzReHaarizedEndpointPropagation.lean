import ArchonPhysics.PhyslibFPUTReHaarizedEndpointPropagation

/-!
# Lipschitz adapter for one-block FPUT re-Haarization

The FPUT block state is generally multimode, so this module keeps its state
space `X` independent from the scalar modal observable.  A standard Mathlib
`LipschitzWith` estimate for the actual block observable replaces the custom
pair-specific stability edge.  It gives the exact endpoint radius

`A * initialDelta + picardDelta`

and its cubic specialization.  For FPUT amplitudes the target space is
`Complex`; the deterministic triangle itself is stated for any seminormed
additive target.
-/

namespace ArchonPhysics.PhyslibFPUTLipschitzReHaarizedEndpointPropagation

noncomputable section

/-! ## The Mathlib-grounded endpoint triangle -/

/-- A standard Mathlib Lipschitz estimate supplies the flow-stability edge
in the one-block endpoint triangle.  The block state `X` and observable
target `Y` are deliberately distinct. -/
theorem norm_actualBlock_sub_referenceBlock_le_of_lipschitzWith
    {X Y : Type*} [PseudoMetricSpace X] [SeminormedAddCommGroup Y]
    (actualBlock referenceBlock : X → Y) (x y : X)
    (A : NNReal) {initialDelta picardDelta : Real}
    (hactualBlock : LipschitzWith A actualBlock)
    (hinitial : dist x y ≤ initialDelta)
    (hpicard : ‖actualBlock y - referenceBlock y‖ ≤ picardDelta) :
    ‖actualBlock x - referenceBlock y‖ ≤
      (A : Real) * initialDelta + picardDelta := by
  have hflow : ‖actualBlock x - actualBlock y‖ ≤
      (A : Real) * initialDelta := by
    simpa only [dist_eq_norm] using
      hactualBlock.dist_le_mul_of_le hinitial
  calc
    ‖actualBlock x - referenceBlock y‖ =
        ‖(actualBlock x - actualBlock y) +
          (actualBlock y - referenceBlock y)‖ := by
      congr 1
      abel
    _ ≤ ‖actualBlock x - actualBlock y‖ +
        ‖actualBlock y - referenceBlock y‖ := norm_add_le _ _
    _ ≤ (A : Real) * initialDelta + picardDelta :=
      add_le_add hflow hpicard

/-- If initial re-Haarization and second-Picard consistency are cubic, a
Lipschitz block observable propagates a cubic endpoint error with explicit
coefficient `A * Cinitial + Cpicard`. -/
theorem norm_actualBlock_sub_referenceBlock_le_abs_cube_of_lipschitzWith
    {X Y : Type*} [PseudoMetricSpace X] [SeminormedAddCommGroup Y]
    (actualBlock referenceBlock : X → Y) (x y : X)
    (A : NNReal)
    {g initialDelta picardDelta Cinitial Cpicard : Real}
    (hactualBlock : LipschitzWith A actualBlock)
    (hinitial : dist x y ≤ initialDelta)
    (hpicard : ‖actualBlock y - referenceBlock y‖ ≤ picardDelta)
    (hinitialCubic : initialDelta ≤ Cinitial * |g| ^ 3)
    (hpicardCubic : picardDelta ≤ Cpicard * |g| ^ 3) :
    ‖actualBlock x - referenceBlock y‖ ≤
      ((A : Real) * Cinitial + Cpicard) * |g| ^ 3 := by
  calc
    ‖actualBlock x - referenceBlock y‖ ≤
        (A : Real) * initialDelta + picardDelta :=
      norm_actualBlock_sub_referenceBlock_le_of_lipschitzWith
        actualBlock referenceBlock x y A hactualBlock hinitial hpicard
    _ ≤ (A : Real) * (Cinitial * |g| ^ 3) +
          Cpicard * |g| ^ 3 :=
      add_le_add
        (mul_le_mul_of_nonneg_left hinitialCubic A.coe_nonneg)
        hpicardCubic
    _ = ((A : Real) * Cinitial + Cpicard) * |g| ^ 3 := by ring

/-! ## A reusable multimode-state record -/

/-- Minimal one-block propagation input for a multimode state `X` and a
complex modal observable.  In contrast with the older scalar record, neither
the actual nor reference block is incorrectly typed as `Complex → Complex`.
-/
structure LipschitzReHaarizedEndpointPropagationData
    (Omega X : Type*) [PseudoMetricSpace X] where
  actualInitial : Omega → X
  referenceInitial : Omega → X
  actualBlock : X → Complex
  referenceBlock : X → Complex
  initialDelta : Real
  flowAmplification : NNReal
  picardDelta : Real
  initialDelta_nonneg : 0 ≤ initialDelta
  picardDelta_nonneg : 0 ≤ picardDelta
  initial_near : ∀ omega,
    dist (actualInitial omega) (referenceInitial omega) ≤ initialDelta
  actualBlock_lipschitz : LipschitzWith flowAmplification actualBlock
  reference_consistent : ∀ omega,
    ‖actualBlock (referenceInitial omega) -
        referenceBlock (referenceInitial omega)‖ ≤ picardDelta

namespace LipschitzReHaarizedEndpointPropagationData

variable {Omega X : Type*} [PseudoMetricSpace X]

/-- The exact radius propagated to the scalar endpoint observable. -/
def finalDelta
    (data : LipschitzReHaarizedEndpointPropagationData Omega X) : Real :=
  (data.flowAmplification : Real) * data.initialDelta + data.picardDelta

theorem finalDelta_nonneg
    (data : LipschitzReHaarizedEndpointPropagationData Omega X) :
    0 ≤ data.finalDelta := by
  exact add_nonneg
    (mul_nonneg data.flowAmplification.coe_nonneg data.initialDelta_nonneg)
    data.picardDelta_nonneg

/-- The global Lipschitz premise implies the pairwise stability estimate
formerly carried as a custom hypothesis. -/
theorem actualBlock_stable
    (data : LipschitzReHaarizedEndpointPropagationData Omega X)
    (omega : Omega) :
    ‖data.actualBlock (data.actualInitial omega) -
        data.actualBlock (data.referenceInitial omega)‖ ≤
      (data.flowAmplification : Real) *
        dist (data.actualInitial omega) (data.referenceInitial omega) := by
  simpa only [dist_eq_norm] using
    data.actualBlock_lipschitz.dist_le_mul
      (data.actualInitial omega) (data.referenceInitial omega)

/-- The exact endpoint triangle derived from the global Lipschitz witness. -/
theorem final_near
    (data : LipschitzReHaarizedEndpointPropagationData Omega X)
    (omega : Omega) :
    ‖data.actualBlock (data.actualInitial omega) -
        data.referenceBlock (data.referenceInitial omega)‖ ≤
      data.finalDelta := by
  exact norm_actualBlock_sub_referenceBlock_le_of_lipschitzWith
    data.actualBlock data.referenceBlock
    (data.actualInitial omega) (data.referenceInitial omega)
    data.flowAmplification data.actualBlock_lipschitz
    (data.initial_near omega) (data.reference_consistent omega)

/-- Cubic initial and Picard radii give the exact cubic endpoint radius. -/
theorem finalDelta_le_abs_cube
    (data : LipschitzReHaarizedEndpointPropagationData Omega X)
    {g Cinitial Cpicard : Real}
    (hinitialCubic : data.initialDelta ≤ Cinitial * |g| ^ 3)
    (hpicardCubic : data.picardDelta ≤ Cpicard * |g| ^ 3) :
    data.finalDelta ≤
      ((data.flowAmplification : Real) * Cinitial + Cpicard) * |g| ^ 3 := by
  unfold finalDelta
  calc
    (data.flowAmplification : Real) * data.initialDelta +
        data.picardDelta ≤
      (data.flowAmplification : Real) * (Cinitial * |g| ^ 3) +
        Cpicard * |g| ^ 3 :=
      add_le_add
        (mul_le_mul_of_nonneg_left hinitialCubic
          data.flowAmplification.coe_nonneg)
        hpicardCubic
    _ = ((data.flowAmplification : Real) * Cinitial + Cpicard) *
        |g| ^ 3 := by ring

/-- Pointwise cubic endpoint coupling obtained without a pair-specific flow
stability assumption. -/
theorem final_near_abs_cube
    (data : LipschitzReHaarizedEndpointPropagationData Omega X)
    {g Cinitial Cpicard : Real}
    (hinitialCubic : data.initialDelta ≤ Cinitial * |g| ^ 3)
    (hpicardCubic : data.picardDelta ≤ Cpicard * |g| ^ 3)
    (omega : Omega) :
    ‖data.actualBlock (data.actualInitial omega) -
        data.referenceBlock (data.referenceInitial omega)‖ ≤
      ((data.flowAmplification : Real) * Cinitial + Cpicard) * |g| ^ 3 :=
  (data.final_near omega).trans
    (data.finalDelta_le_abs_cube hinitialCubic hpicardCubic)

end LipschitzReHaarizedEndpointPropagationData

end

end ArchonPhysics.PhyslibFPUTLipschitzReHaarizedEndpointPropagation
