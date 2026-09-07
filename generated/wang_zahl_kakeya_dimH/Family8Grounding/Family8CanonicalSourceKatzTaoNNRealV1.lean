import Family8Grounding.Family8KatzTaoFrostmanPropertiesV1
import Mathlib.Tactic

/-!
# Finite canonical source Katz--Tao constant

The paper hypotheses expose the source Katz--Tao coefficient as the finite
`ENNReal` power `delta ^ (-etaKT)`, while the shading-aware logarithmic
partition takes an `NNReal`.  This file records the canonical finite
representative and its exact coercion, so later same-object adapters do not
carry an arbitrary scalar choice.
-/

set_option autoImplicit false
set_option warningAsError true

open scoped ENNReal NNReal

namespace Family8CanonicalSourceKatzTaoNNRealV1

open LeanEval.Analysis.WangZahlKakeya
open Submission.Kakeya.ConvexGeometry
open Submission.Kakeya.ConvexFactoring
open Submission.Kakeya.Uniformity
open Family8KatzTaoFrostmanPropertiesV1

noncomputable section

/-- The canonical finite representative of the source Katz--Tao power. -/
def canonicalSourceKatzTaoNNReal
    (delta : NNReal) (etaKT : Real) : NNReal :=
  ((delta : ENNReal) ^ (-etaKT)).toNNReal

/-- Its coercion is definitionally the paper's source Katz--Tao power. -/
@[simp] theorem coe_canonicalSourceKatzTaoNNReal
    {delta : NNReal} (hdelta : 0 < delta) (etaKT : Real) :
    (canonicalSourceKatzTaoNNReal delta etaKT : ENNReal) =
      (delta : ENNReal) ^ (-etaKT) := by
  unfold canonicalSourceKatzTaoNNReal
  exact ENNReal.coe_toNNReal
    (ENNReal.rpow_ne_top_of_ne_zero
      (ENNReal.coe_ne_zero.mpr hdelta.ne') ENNReal.coe_ne_top)

/-- The canonical finite representative is strictly positive at every
positive physical scale. -/
theorem canonicalSourceKatzTaoNNReal_pos
    {delta : NNReal} (hdelta : 0 < delta) (etaKT : Real) :
    0 < canonicalSourceKatzTaoNNReal delta etaKT := by
  apply ENNReal.coe_pos.mp
  rw [coe_canonicalSourceKatzTaoNNReal hdelta etaKT]
  exact ENNReal.rpow_pos (ENNReal.coe_pos.mpr hdelta) ENNReal.coe_ne_top

/-- The source component of the paper hypotheses can be reused verbatim
with the finite canonical representative. -/
theorem isKatzTao_canonicalSourceKatzTaoNNReal
    {delta : NNReal} {index : Type} [Fintype index] [DecidableEq index]
    (D : ActualTubeDatum delta index) (hD : D.IsAdmissible)
    {etaKT : Real} (hKT : KatzTaoHypotheses D etaKT) :
    IsKatzTao (canonicalSourceKatzTaoNNReal delta etaKT : ENNReal)
      D.family.bodyFamily := by
  rw [coe_canonicalSourceKatzTaoNNReal hD.delta_pos etaKT]
  exact
    ((Family8KatzTaoFrostmanPropertiesV1.katzTaoHypotheses_iff_density_and_isKatzTao
      D etaKT).mp hKT).2

#print axioms canonicalSourceKatzTaoNNReal
#print axioms coe_canonicalSourceKatzTaoNNReal
#print axioms canonicalSourceKatzTaoNNReal_pos
#print axioms isKatzTao_canonicalSourceKatzTaoNNReal

end
end Family8CanonicalSourceKatzTaoNNRealV1
