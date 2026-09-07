import Family8Grounding.Family8Family7NativeHighArbitraryWeightedCriticalScaleProxyV1
import Family8Grounding.Family8ActualDatumDirectFreshGreedyV1
import Mathlib.Tactic

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 3000000

open Set MeasureTheory
open scoped ENNReal NNReal BigOperators

namespace Family8Family7NativeHighArbitraryWeightedProxyGreedyV3

open LeanEval.Analysis.WangZahlKakeya
open Submission.Kakeya.ConvexGeometry
open Family8ActualDatumDirectFreshGreedyV1
open Family8Family7NativeHighArbitraryWeightedCriticalScaleProxyV1
open Family8Family7NativeHighCriticalScaleProxyGeometryV1
open Family8Family7NativeHighWeightedCriticalBallV1
open Family8FiniteRandomRigidMotionRefinementV1
open Family8GeneralizedKatzTaoMultiplicityV1
open Family8RestrictedActualDatumDensityRetentionV1
open Family8SelectedParentPlankFineProxyDatumV1
open FamilyStickyCinematicL32PyzActualNormFirstAllCenterMassWeightedBranchTypesV5C

noncomputable section

/-!
# Greedy admissible refinement for an arbitrary weighted critical proxy

The weighted choice itself does not need a special greedy argument.  Once its
literal proxy radius is at most one half and its proxy tubes are supported in
the unit ball, the existing direct greedy theorem applies verbatim.  The
conflict loss is bounded by the original native ambient cardinality because
the selected weighted ball is a genuine physical-ambient subfamily.

V1 was a namespace-typo draft and V2 omitted the proxy-geometry namespace; neither is imported.
-/

theorem nativeHighArbitraryWeightedCriticalBallIndex_card_le_ambient_card
    {radius : NNReal} {iota : Type} [Fintype iota] [DecidableEq iota]
    (D : NativeBranchCore radius iota)
    (W : NativeHighArbitraryWeightedProxyInput D) :
    Fintype.card (NativeHighArbitraryWeightedCriticalBallIndex D W) ≤
      D.ambient.card := by
  rw [Fintype.card_coe]
  exact Finset.card_le_card
    (nativeHighArbitraryWeightedCriticalBall_subset_physicalAmbient D W)

theorem nativeHighArbitraryWeightedProxy_directConflict_card_le_ambient_card
    {radius : NNReal} {iota : Type} [Fintype iota] [DecidableEq iota]
    (D : NativeBranchCore radius iota)
    (W : NativeHighArbitraryWeightedProxyInput D)
    (hambientSource : D.ambient ⊆ D.S.source)
    (Y : Shading D.S.family.bodyFamily)
    (a : NativeHighArbitraryWeightedCriticalBallIndex D W) :
    (directConflictIndices
      (nativeHighArbitraryWeightedCriticalScaleProxyDatum
        D W hambientSource Y) a).card ≤ D.ambient.card := by
  calc
    (directConflictIndices
      (nativeHighArbitraryWeightedCriticalScaleProxyDatum
        D W hambientSource Y) a).card ≤
        Fintype.card (NativeHighArbitraryWeightedCriticalBallIndex D W) :=
      Finset.card_le_univ _
    _ ≤ D.ambient.card :=
      nativeHighArbitraryWeightedCriticalBallIndex_card_le_ambient_card D W

/-- The exact generic greedy handoff.  Its only new inputs are the two
geometric admissibility facts not implied by an arbitrary weight: the proxy
radius cap and unit-ball support. -/
theorem exists_nativeHighArbitraryWeightedProxy_greedyAdmissible
    {radius : NNReal} {iota : Type} [Fintype iota] [DecidableEq iota]
    (D : NativeBranchCore radius iota)
    (W : NativeHighArbitraryWeightedProxyInput D)
    (hambientSource : D.ambient ⊆ D.S.source)
    (Y : Shading D.S.family.bodyFamily)
    (hdeltaHalf :
      criticalScaleProxyRadius radius
          (nativeHighWeightedNormData D W.center W.weight).criticalScale
          (nativeHighArbitraryWeightedCriticalScale_pos D W) ≤
        (2 : NNReal)⁻¹)
    (hsupport :
      ∀ i : NativeHighArbitraryWeightedCriticalBallIndex D W,
        ((nativeHighArbitraryWeightedCriticalScaleProxyFamily
          D W).tubes i).carrier ⊆ Metric.closedBall (0 : Space) 1) :
    let A := nativeHighArbitraryWeightedCriticalScaleProxyDatum
      D W hambientSource Y
    ∃ selected : Finset
        (NativeHighArbitraryWeightedCriticalBallIndex D W),
      selected.Nonempty ∧
      (restrictActualTubeDatum A selected).IsAdmissible ∧
      (Fintype.card
          (NativeHighArbitraryWeightedCriticalBallIndex D W) : ENNReal) ≤
        (D.ambient.card + 1 : Nat) * (selected.card : ENNReal) ∧
      A.shading.shadingMass ≤
        (D.ambient.card + 1 : Nat) *
          (restrictActualTubeDatum A selected).shading.shadingMass ∧
      A.shading.shadingDensity / (D.ambient.card + 1 : Nat) ≤
        (restrictActualTubeDatum A selected).shading.shadingDensity ∧
      A.shading.averageMultiplicity ≤
        (D.ambient.card + 1 : Nat) *
          (restrictActualTubeDatum A selected).shading.averageMultiplicity := by
  classical
  let A := nativeHighArbitraryWeightedCriticalScaleProxyDatum
    D W hambientSource Y
  let _ : Nonempty (NativeHighArbitraryWeightedCriticalBallIndex D W) := by
    rcases (nativeHighWeightedNormData
      D W.center W.weight).criticalBall_nonempty with ⟨i, hi⟩
    exact ⟨⟨i, hi⟩⟩
  have hdeltaPos : 0 < criticalScaleProxyRadius radius
      (nativeHighWeightedNormData D W.center W.weight).criticalScale
      (nativeHighArbitraryWeightedCriticalScale_pos D W) := by
    apply NNReal.coe_pos.mp
    rw [criticalScaleProxyRadius_coe]
    exact div_pos (mul_pos (by norm_num) (NNReal.coe_pos.mpr D.hradius))
      (nativeHighArbitraryWeightedCriticalScale_pos D W)
  have hconflict :
      ∀ a : NativeHighArbitraryWeightedCriticalBallIndex D W,
        (directConflictIndices A a).card ≤ D.ambient.card := by
    intro a
    exact nativeHighArbitraryWeightedProxy_directConflict_card_le_ambient_card
      D W hambientSource Y a
  exact exists_direct_refinement_admissible
    (conflictThreshold := D.ambient.card) A hdeltaPos hdeltaHalf
      hsupport hconflict

#print axioms
  nativeHighArbitraryWeightedCriticalBallIndex_card_le_ambient_card
#print axioms
  nativeHighArbitraryWeightedProxy_directConflict_card_le_ambient_card
#print axioms exists_nativeHighArbitraryWeightedProxy_greedyAdmissible

end

end Family8Family7NativeHighArbitraryWeightedProxyGreedyV3
