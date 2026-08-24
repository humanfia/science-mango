import FamilyStickyGrounding.Cinematic.FamilyStickyCinematicL32LocalTangencyV1
import FamilyStickyGrounding.Cinematic.FamilyStickyCinematicL32TraceTangencyMinimizerV1
import Submission.Kakeya.ConvexGeometry.Tube

set_option autoImplicit false

open Set

namespace FamilyStickyCinematicL32ActualTubeCoefficientDistancesV1

open Submission.Kakeya.ConvexGeometry
open FamilyStickyCinematicL32LocalTangencyV1
open FamilyStickyCinematicL32TraceTangencyMinimizerV1

noncomputable section

/-!
# Clean coefficient distances for actual project tubes

Only the literal tube axis and the proved compact trace minimizer enter this
module.  In particular, it avoids every projected-shading and obsolete
finite-good-pairs dependency.
-/

def projectedTubeGraphC {delta : NNReal} (T : Tube delta) : Real :=
  T.axis.direction 0 / T.axis.direction 2

def projectedTubeGraphD {delta : NNReal} (T : Tube delta) : Real :=
  T.axis.direction 1 / T.axis.direction 2

def projectedTubeGraphA {delta : NNReal} (T : Tube delta) : Real :=
  T.axis.base 0 - projectedTubeGraphC T * T.axis.base 2

def projectedTubeGraphB {delta : NNReal} (T : Tube delta) : Real :=
  T.axis.base 1 - projectedTubeGraphD T * T.axis.base 2

def projectedTubePairDeltaA {delta : NNReal}
    (T U : Tube delta) : Real :=
  projectedTubeGraphA T - projectedTubeGraphA U

def projectedTubePairDeltaB {delta : NNReal}
    (T U : Tube delta) : Real :=
  projectedTubeGraphB T - projectedTubeGraphB U

def projectedTubePairDeltaD {delta : NNReal}
    (T U : Tube delta) : Real :=
  projectedTubeGraphD T - projectedTubeGraphD U

def projectedTubePairCoefficientDistance {delta : NNReal}
    (T U : Tube delta) : Real :=
  coefficientDistance
    (projectedTubePairDeltaA T U)
    (projectedTubePairDeltaB T U)
    (projectedTubePairDeltaD T U)

/-- The scalar value of the proved compact value--first-jet minimum. -/
noncomputable def projectedTubePairTangencyDistance
    {delta : NNReal} (T U : Tube delta)
    (f f1 f2 : Real → Real) (A B : Real) (hAB : A ≤ B)
    (hfDeriv : ∀ z, z ∈ Icc A B → HasDerivAt f (f1 z) z)
    (hf1Deriv : ∀ z, z ∈ Icc A B → HasDerivAt f1 (f2 z) z) : Real :=
  Classical.choose
    (exists_trace_tangencyParameter_with_minimizer
      f f1 f2
      (projectedTubePairDeltaA T U)
      (projectedTubePairDeltaB T U)
      (projectedTubePairDeltaD T U)
      hAB hfDeriv hf1Deriv)

theorem projectedTubePairCoefficientDistance_comm
    {delta : NNReal} (T U : Tube delta) :
    projectedTubePairCoefficientDistance T U =
      projectedTubePairCoefficientDistance U T := by
  simp only [projectedTubePairCoefficientDistance, coefficientDistance,
    projectedTubePairDeltaA, projectedTubePairDeltaB,
    projectedTubePairDeltaD]
  rw [abs_sub_comm (projectedTubeGraphA T),
    abs_sub_comm (projectedTubeGraphB T),
    abs_sub_comm (projectedTubeGraphD T)]

#print axioms projectedTubeGraphC
#print axioms projectedTubeGraphD
#print axioms projectedTubeGraphA
#print axioms projectedTubeGraphB
#print axioms projectedTubePairCoefficientDistance
#print axioms projectedTubePairTangencyDistance

end

end FamilyStickyCinematicL32ActualTubeCoefficientDistancesV1
