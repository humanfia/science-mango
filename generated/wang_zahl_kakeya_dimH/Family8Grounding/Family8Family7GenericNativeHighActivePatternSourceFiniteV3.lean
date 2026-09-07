import Family8Grounding.Family8Family7GenericNativeHighActivePatternSourceSubsetV3
import Mathlib.Tactic

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 1200000

open Set MeasureTheory
open scoped BigOperators ENNReal NNReal

namespace Family8Family7GenericNativeHighActivePatternSourceFiniteV3

open Family8Family7GenericNativeHighActivePatternSourceSubsetV3
open Family8Family7GenericNativeHighGeometryV1
open Family8Family7GenericNativeHighOccurrenceDefinitionsV1
open Family8ShadingAwareGenericNativeBranchCoreV2
open FamilyStickyCinematicL32FiniteProjectedShadingMultiplicitySliceV1
open FamilyStickyCinematicL32WZL3UniformTubeSourceV1

noncomputable section

universe u

/-- Finiteness of the generic source mass controls the literal active-pattern
source at every high centre. -/
theorem genericNativeHighActivePatternSource_ne_top_of_sourceMass_ne_top
    {radius : NNReal} {iota : Type u}
    [Fintype iota] [DecidableEq iota]
    {S : WZL3UniformTubeSource radius iota}
    {physical : FiniteProjectedShading (Real × Real) iota}
    {f : Real → Real} {hfContinuous : Continuous f}
    (D : GenericNativeBranchCore radius iota S physical f hfContinuous)
    (G : GenericNativeHighGeometry D) (c : D.HighCenter)
    (hsourceMass : D.sourceMass ≠ ∞) :
    volume (genericNativeHighActivePatternSource D G c) ≠ ∞ := by
  have hpatternBase :
      volume (genericNativeHighActivePatternSource D G c) ≤
        volume (D.highBase c) :=
    measure_mono (genericNativeHighActivePatternSource_subset_highBase D G c)
  have hbaseSource : volume (D.highBase c) ≤ D.sourceMass := by
    rw [D.sourceMass_eq_sum_cells]
    exact Finset.single_le_sum
      (s := D.centers)
      (f := fun center => volume (D.cell center))
      (fun _ _ => by exact zero_le)
      ((Finset.mem_filter.mp c.1.2).1)
  exact ne_top_of_le_ne_top hsourceMass (hpatternBase.trans hbaseSource)

#print axioms genericNativeHighActivePatternSource_ne_top_of_sourceMass_ne_top

end
end Family8Family7GenericNativeHighActivePatternSourceFiniteV3
