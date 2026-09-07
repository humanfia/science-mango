import Family8Grounding.Family8CanonicalGraphFrozenDirectSameObjectMiddleV1
import Family8Grounding.Family8Family7GraphKatzTaoRelativeCardCapV3
import Mathlib.Tactic

/-!
# Automatic relative count for the direct same-graph middle

The greedy proxy selection is contained in its critical ball, the critical
ball is contained in the literal graph stored by the canonical identity, and
that graph is Katz--Tao inside its literal parent tube.  Hence the count input
of the direct middle theorem is structural: it does not need to be supplied as
an analytic callback.
-/

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 3000000

open Set MeasureTheory
open scoped BigOperators ENNReal NNReal

namespace Family8CanonicalGraphFrozenDirectMiddleAutomaticCountV1

open LeanEval.Analysis.WangZahlKakeya
open Submission.Kakeya.ConvexGeometry
open Submission.Kakeya.ConvexFactoring
open Submission.Kakeya.Uniformity
open Family8CanonicalGraphFrozenDirectSameObjectMiddleV1
open Family8CanonicalGraphFrozenRawEq66IdentityBridgeV1
open Family8EighthNormalizedWZL3SourceV3
open Family8Family7FirstCrossingFamilyGraphBucketV12
open Family8Family7FirstCrossingFullCoefficientGraphCertificateV4
open Family8Family7GraphKatzTaoRelativeCardCapV3
open Family8Family7WeightedVerticalGraphCBucketV1
open Family8FiniteRandomRigidMotionB2NormalizedDatumV1
open Family8FullCoefficientActualMassCriticalScaleV5
open Family8FrozenComparableActualAverageMassDensityV1.Assembly
open Family8FrozenNeighborhoodAssemblyV1
open Family8StickyScaleCoverFrostmanInheritanceV1.StickyScaleCover
open FamilyStickyAtEveryScaleCoreV1

noncomputable section

private theorem coe_div_rpow_neg_eq_reverse_rpow
    (a b : NNReal) (ha : 0 < a) (hb : 0 < b) (x : Real) :
    (((a : ENNReal) / (b : ENNReal)) ^ (-x)) =
      (((b : ENNReal) / (a : ENNReal)) ^ x) := by
  rw [← ENNReal.coe_div hb.ne',
    ← ENNReal.coe_div ha.ne',
    ← ENNReal.coe_rpow_of_ne_zero (div_pos ha hb).ne',
    ← ENNReal.coe_rpow_of_ne_zero (div_pos hb ha).ne',
    ENNReal.coe_inj]
  rw [NNReal.rpow_neg, ← NNReal.inv_rpow, inv_div]

/-- The exact direct proxy selection obeys the inverse-square relative count
bound with the Katz--Tao constant of the same graph.  This is precisely the
`hproxyCount` shape of `SameGraphDirectProxySelection.gainedMiddle`, with
`kappa = 0` and `K = 16 * Cgraph`. -/
theorem SameGraphDirectProxySelection.selected_card_le_sameGraphKatzTao_relativePower
    {tau rho : NNReal} {fineIndex : Type}
    [Fintype fineIndex] [DecidableEq fineIndex]
    (F : UniformTubeFamily tau fineIndex)
    (T : StickyScaleCover F rho)
    (P : ConvexFactorization F.bodyFamily T.coarse.bodyFamily)
    (Y : Shading F.bodyFamily) (fibreCF : ENNReal)
    (R : SameAssemblyFullCoefficientGraphIdentity F T P Y fibreCF)
    (htau8 : 0 < tau / 8)
    (htenTau8Sixteen : 10 * (((tau / 8 : NNReal) : Real)) <= 16)
    (O : SameGraphDirectProxySelection
      F T P Y fibreCF R htau8 htenTau8Sixteen)
    (htau : 0 < tau) (htauHalf : tau <= (2 : NNReal)⁻¹)
    (hrho : 0 < rho) (hrhoHalf : rho <= (2 : NNReal)⁻¹) :
    let baseLoss : ENNReal :=
      (R.A.loss : ENNReal) * (P.index.coarse.card : ENNReal)
    let d : ENNReal :=
      (sourceActiveFineShading P Y).shadingDensity / baseLoss
    let graphLoss : ENNReal :=
      ((3 * verticalGraphCBucketLoss ((tau : Real) / 2) : Nat) : ENNReal)
    let effectiveCF : ENNReal := fibreCF * (d⁻¹ * graphLoss)
    (O.output.selected.card : ENNReal) <=
      (16 * fullCoefficientGraphKatzTaoConstant
        R.axis R.label F T P R.k effectiveCF) *
        (((tau : ENNReal) / (rho : ENNReal)) ^ (-(2 + (0 : Real)))) := by
  dsimp only
  let cert := selectedCertificate R
  let baseLoss : ENNReal :=
    (R.A.loss : ENNReal) * (P.index.coarse.card : ENNReal)
  let d : ENNReal :=
    (sourceActiveFineShading P Y).shadingDensity / baseLoss
  let graphLoss : ENNReal :=
    ((3 * verticalGraphCBucketLoss ((tau : Real) / 2) : Nat) : ENNReal)
  let effectiveCF : ENNReal := fibreCF * (d⁻¹ * graphLoss)
  let graph := verticalSourceGraphCBucketFiber
    ((tau : Real) / 2) (firstCrossingFamilyVerticalSource R.axis F P R.k)
      R.label
  let Wproxy := fullCoefficientActualMassNormData
    (eighthNormalizedWZL3Source
      (firstCrossingFamilyVerticalSource R.axis F P R.k))
    graph cert.graph_nonempty htau8 htenTau8Sixteen
    (eighthNormalizedShading
      (firstCrossingFamilyVerticalSource R.axis F P R.k).family
      (firstCrossingFamilyVerticalShading R.axis F P R.A R.k))
    Set.univ
  have hselectedCritical :
      O.output.selected.card <= Wproxy.criticalBall.card := by
    have hcard : O.output.selected.card <=
        Fintype.card {i // i ∈ Wproxy.criticalBall} :=
      Finset.card_le_univ O.output.selected
    simpa only [Fintype.card_coe] using hcard
  have hcriticalGraph : Wproxy.criticalBall.card <= graph.card :=
    Finset.card_le_card Wproxy.criticalBall_subset_family
  have hselectedGraph : (O.output.selected.card : ENNReal) <=
      (graph.card : ENNReal) := by
    exact_mod_cast hselectedCritical.trans hcriticalGraph
  have hgraphContained : forall i, i ∈ graph ->
      (F.tubes i).carrier ⊆ (T.coarse.tubes R.k).carrier := by
    intro i hi
    exact T.fiber_carrier_subset_parent R.k ⟨i, cert.graph_subset hi⟩
  have hgraphCap : (graph.card : ENNReal) <=
      16 * fullCoefficientGraphKatzTaoConstant
          R.axis R.label F T P R.k effectiveCF *
        (((rho / tau : NNReal) : ENNReal) ^ 2) := by
    exact graph_card_le_sixteen_mul_katzTao_mul_relativeSquare
      F graph (T.coarse.tubes R.k) htau htauHalf hrhoHalf
        hgraphContained cert.graph_katz_tao
  calc
    (O.output.selected.card : ENNReal) <= (graph.card : ENNReal) :=
      hselectedGraph
    _ <= 16 * fullCoefficientGraphKatzTaoConstant
          R.axis R.label F T P R.k effectiveCF *
        (((rho / tau : NNReal) : ENNReal) ^ 2) := hgraphCap
    _ = (16 * fullCoefficientGraphKatzTaoConstant
          R.axis R.label F T P R.k effectiveCF) *
        (((tau : ENNReal) / (rho : ENNReal)) ^ (-(2 + (0 : Real)))) := by
      rw [show (2 : Real) + 0 = 2 by ring]
      rw [coe_div_rpow_neg_eq_reverse_rpow tau rho htau hrho 2]
      simp only [ENNReal.coe_div htau.ne', ENNReal.rpow_two]

#print axioms
  SameGraphDirectProxySelection.selected_card_le_sameGraphKatzTao_relativePower

end
end Family8CanonicalGraphFrozenDirectMiddleAutomaticCountV1
