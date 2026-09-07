import Family8Grounding.Family8ActiveCoarseCanonicalFrostmanXLowerV3
import Family8Grounding.Family8ActiveCoarseFrostmanCardScaleMassSmallDeltaV4

set_option autoImplicit false
set_option warningAsError true
set_option linter.unusedSectionVars false
set_option maxHeartbeats 3000000

open Set MeasureTheory
open scoped ENNReal NNReal

namespace Family8ActiveCoarseCanonicalFrostmanXLowerParameterLadderV8

open LeanEval.Analysis.WangZahlKakeya
open Submission.Kakeya.ConvexGeometry
open Submission.Kakeya.ConvexFactoring
open Submission.Kakeya.Uniformity
open Family6CanonicalFrostmanConstantCoreV1
open Family8KatzTaoFrostmanPropertiesV1
open Family8ParameterLadderV1
open Family8StickyParentHullVolumeBoundV1
open FamilyStickyAtEveryScaleCoreV1
open Family8ParentAggregatedShadingActiveCoarseXUpperV3.StickyScaleCover

noncomputable section

namespace StickyScaleCover

/-! Fully pinned successor of the abandoned V1--V7 wrappers.  Every large
family/scale implicit passed across the two imported endpoints is explicit,
so elaboration does not search through the expanded sticky-cover types. -/

/-- The canonical long-interval `X` lower bound at the exact first-long
parameter-ladder exponent. -/
theorem parameterLadder_global_rpow_le_activeCoarseCardScaleMass_of_canonical
    {delta rho : NNReal} {iota : Type}
    [Fintype iota] [DecidableEq iota]
    (D : ActualTubeDatum delta iota) (hD : D.IsAdmissible)
    (S : StickyScaleCover D.family rho)
    {globalDelta : NNReal} {epsilon0 beta gamma : Real}
    (P : ParameterLadder epsilon0 beta gamma) (j : Nat)
    (hbeta : 0 < beta)
    (hglobal : 0 < globalDelta)
    (hrho : 0 < rho) (hrhoHalf : rho <= (2 : NNReal)⁻¹)
    (hcoarse : S.activeCoarse.Nonempty)
    (hC : canonicalFrostmanConstant
        S.activeCoarseFamily closedBallFourBody <=
      (globalDelta : ENNReal) ^
        (-Family8ActiveCoarseFrostmanCardScaleMassSmallDeltaV4.firstLongFrostmanBaseExponent
          P j))
    (hdelta : globalDelta <=
      Family8ActiveCoarseFrostmanCardScaleMassSmallDeltaV4.firstLongFrostmanEightSmallDeltaThreshold
        P j) :
    globalDelta ^ (10 * P.eta j / (P.epsilon * beta)) <=
      activeCoarseCardScaleMass S := by
  have hrough : (globalDelta : ENNReal) ^
        Family8ActiveCoarseFrostmanCardScaleMassSmallDeltaV4.firstLongFrostmanBaseExponent
          P j <=
      8 * (activeCoarseCardScaleMass S : ENNReal) :=
    Family8ActiveCoarseCanonicalFrostmanXLowerV3.StickyScaleCover.global_rpow_le_eight_mul_activeCoarseCardScaleMass_of_canonical
      (delta := delta) (rho := rho) (iota := iota)
      (globalDelta := globalDelta)
      (etaPrime :=
        Family8ActiveCoarseFrostmanCardScaleMassSmallDeltaV4.firstLongFrostmanBaseExponent
          P j)
      D hD S hglobal hrho hrhoHalf hcoarse hC
  have hcore : (globalDelta : ENNReal) ^
        (Family8ActiveCoarseFrostmanCardScaleMassSmallDeltaV4.firstLongFrostmanBaseExponent
            P j +
          Family8ActiveCoarseFrostmanCardScaleMassSmallDeltaV4.firstLongFrostmanAbsorbExponent
            P j) <=
      (activeCoarseCardScaleMass S : ENNReal) :=
    Family8ActiveCoarseFrostmanCardScaleMassSmallDeltaV4.global_rpow_add_absorb_le_of_le_eight_mul
      (globalDelta := globalDelta)
      (X := (activeCoarseCardScaleMass S : ENNReal))
      (e :=
        Family8ActiveCoarseFrostmanCardScaleMassSmallDeltaV4.firstLongFrostmanBaseExponent
          P j)
      (a :=
        Family8ActiveCoarseFrostmanCardScaleMassSmallDeltaV4.firstLongFrostmanAbsorbExponent
          P j)
      hglobal
      (Family8ActiveCoarseFrostmanCardScaleMassSmallDeltaV4.firstLongFrostmanAbsorbExponent_pos
        (epsilon0 := epsilon0) (beta := beta) (gamma := gamma) P j hbeta)
      hdelta hrough
  apply ENNReal.coe_le_coe.mp
  rw [ENNReal.coe_rpow_of_ne_zero hglobal.ne',
    <- Family8ActiveCoarseFrostmanCardScaleMassSmallDeltaV4.firstLongFrostmanExponent_add_absorb
      (epsilon0 := epsilon0) (beta := beta) (gamma := gamma) P j]
  exact hcore

#print axioms
  parameterLadder_global_rpow_le_activeCoarseCardScaleMass_of_canonical

end StickyScaleCover

end
end Family8ActiveCoarseCanonicalFrostmanXLowerParameterLadderV8
