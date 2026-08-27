import FamilyStickyGrounding.Cinematic.FamilyStickyCinematicL32Prop41SampledLensCardinalityAssemblyV1
import Mathlib.Tactic

set_option autoImplicit false
set_option warningAsError true

namespace FamilyStickyCinematicL32Prop41SampledLensPaperShapeNumericsV1

open FamilyStickyCinematicL32Prop41SampledLensCardinalityAssemblyV1

/-- For a nonempty sampled curve family, the explicit lens expression has
the paper-shaped `load * sqrt load` growth. -/
theorem sampledLensBound_le_paperShape
    {depth load : Real} (hload : 1 <= load) :
    sampledLensBound depth load <=
      (316 + 48 * depth) * load * Real.sqrt load := by
  have hloadNonneg : 0 <= load := by linarith
  have hsqrtOne : 1 <= Real.sqrt load := Real.one_le_sqrt.mpr hload
  have hlinear : load <= load * Real.sqrt load := by
    have hmul := mul_le_mul_of_nonneg_left hsqrtOne hloadNonneg
    simpa using hmul
  unfold sampledLensBound
  calc
    load + 3 *
        (16 * depth * load * Real.sqrt load +
          105 * load * Real.sqrt load) =
        load + (48 * depth + 315) *
          (load * Real.sqrt load) := by ring
    _ <= load * Real.sqrt load +
        (48 * depth + 315) * (load * Real.sqrt load) := by
      exact add_le_add hlinear (le_refl _)
    _ = (316 + 48 * depth) * load * Real.sqrt load := by ring

/-- Final paper-shaped natural-cardinality endpoint. -/
theorem rectangleCard_le_sampledLensPaperShape
    (rectangleCard itemCard curveCard depth : Nat) (load : Real)
    (hsurvival : (rectangleCard : Real) / 8 <= (itemCard : Real))
    (hlens : (itemCard : Real) <=
      (curveCard : Real) + 3 *
        (16 * (depth : Real) * (curveCard : Real) *
            Real.sqrt (curveCard : Real) +
          105 * (curveCard : Real) * Real.sqrt (curveCard : Real)))
    (hcurveLoad : (curveCard : Real) <= load)
    (hload : 1 <= load) :
    (rectangleCard : Real) <=
      8 * (316 + 48 * (depth : Real)) * load * Real.sqrt load := by
  have hbase := rectangleCard_le_eight_mul_sampledLensBound
    rectangleCard itemCard curveCard depth load
      hsurvival hlens hcurveLoad
  have hshape := sampledLensBound_le_paperShape
    (depth := (depth : Real)) (load := load) hload
  calc
    (rectangleCard : Real) <=
        8 * sampledLensBound (depth : Real) load := hbase
    _ <= 8 * ((316 + 48 * (depth : Real)) *
        load * Real.sqrt load) :=
      mul_le_mul_of_nonneg_left hshape (by norm_num)
    _ = 8 * (316 + 48 * (depth : Real)) *
        load * Real.sqrt load := by ring

#print axioms sampledLensBound_le_paperShape
#print axioms rectangleCard_le_sampledLensPaperShape

end FamilyStickyCinematicL32Prop41SampledLensPaperShapeNumericsV1
