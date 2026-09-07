import Family8Grounding.Family8FiniteRandomRigidMotionPaperFixedJohnDensityNondegeneracyV3
import Mathlib.Tactic

open scoped ENNReal NNReal

namespace Family8FiniteRandomRigidMotionPaperFixedJohnDensityNondegeneracyV4

open Family8KatzTaoFrostmanPropertiesV1
open Family8FiniteRandomRigidMotionPaperFixedJohnAutomaticConflictCapV2
open Family8FiniteRandomRigidMotionPaperFixedJohnCapVsLongMeanV2
open Family8FiniteRandomRigidMotionPaperFixedJohnAutomaticDensityRepetitionsV2
open Family8FiniteRandomRigidMotionPaperFixedJohnDensityNondegeneracyV3

noncomputable section

set_option autoImplicit false
set_option warningAsError true

/-! Direct lower bound for the automatic repetition count.  This is the
nonempty-family consequence that downstream code can use without first
choosing an integer target or restating a scalar budget. -/

theorem densityUnitCost_inv_sub_one_lt_automaticRepetitions
    {delta : NNReal} {iota : Type}
    [Fintype iota] [DecidableEq iota]
    (D : ActualTubeDatum delta iota) (hD : D.IsAdmissible)
    (hcard : Fintype.card iota ≠ 0) :
    1 / fixedJohnDensityUnitCost delta iota - 1 <
      (fixedJohnAutomaticDensityRepetitions D hD : Real) := by
  have hcost : 0 < fixedJohnDensityUnitCost delta iota :=
    fixedJohnDensityUnitCost_pos hD.delta_pos hcard
  have hmass : (1 : Real) ≤
      (fixedJohnPackingMaximalConcentration D hD).toReal :=
    one_le_fixedJohnPackingMaximalConcentration_toReal D hD hcard
  have hratio : 1 / fixedJohnDensityUnitCost delta iota ≤
      fixedJohnDensityRatio D hD := by
    rw [fixedJohnDensityRatio]
    exact (div_le_div_iff_of_pos_right hcost).2 hmass
  exact (sub_le_sub_right hratio 1).trans_lt
    (fixedJohnDensityRatio_sub_one_lt_repetitions D hD)

#print axioms densityUnitCost_inv_sub_one_lt_automaticRepetitions

end
end Family8FiniteRandomRigidMotionPaperFixedJohnDensityNondegeneracyV4
