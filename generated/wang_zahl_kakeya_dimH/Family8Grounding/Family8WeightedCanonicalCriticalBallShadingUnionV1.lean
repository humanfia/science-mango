import Family8Grounding.Family8WeightedCanonicalCriticalScaleProxyAverageV2

/-!
# Literal critical-ball shading union containment

Restricting a shading to the weighted canonical critical-ball subtype cannot
enlarge its shaded union.  This is the denominator-side inclusion needed by
average-multiplicity retention arguments; it is definitional and carries no
mass hypothesis.
-/

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 1000000

open Set MeasureTheory
open scoped NNReal

namespace Family8WeightedCanonicalCriticalBallShadingUnionV1

open Submission.Kakeya.ConvexGeometry
open Family8Family7NativeHighWeightedCriticalBallV1
open Family8WeightedCanonicalCriticalScaleProxyAverageV2
open FamilyStickyCinematicL32WZL3UniformTubeSourceV1

noncomputable section

universe u

/-- The literal critical-ball restriction uses unchanged carriers, so its
union is contained in the source shading union. -/
theorem weightedCanonicalCriticalBallShading_shadedUnion_subset
    {radius : NNReal} {iota : Type u} [Fintype iota] [DecidableEq iota]
    (S : WZL3UniformTubeSource radius iota)
    (W : WeightedCanonicalNormBallData iota)
    (Y : Shading S.family.bodyFamily) :
    (weightedCanonicalCriticalBallShading S W Y).shadedUnion ⊆
      Y.shadedUnion := by
  intro x hx
  obtain ⟨i, hi⟩ := Set.mem_iUnion.mp hx
  exact Set.mem_iUnion.mpr ⟨i.1, hi⟩

#print axioms weightedCanonicalCriticalBallShading_shadedUnion_subset

end
end Family8WeightedCanonicalCriticalBallShadingUnionV1
