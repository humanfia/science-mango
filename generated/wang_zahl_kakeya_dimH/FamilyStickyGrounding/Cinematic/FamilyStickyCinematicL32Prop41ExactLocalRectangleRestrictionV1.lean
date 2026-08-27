import FamilyStickyGrounding.Cinematic.FamilyStickyCinematicL32Lemma55CenteredRectangleDilationV1
import FamilyStickyGrounding.Cinematic.FamilyStickyCinematicL32Prop41FiniteGeneralPositionExactRootReproductionV1
import Mathlib.Tactic

set_option autoImplicit false
set_option warningAsError true

open Set

namespace FamilyStickyCinematicL32Prop41ExactLocalRectangleRestrictionV1

open Submission.Kakeya.ConvexGeometry
open FamilyStickyCinematicL32CenteredFractionIntervalsV1
open FamilyStickyCinematicL32CurvilinearRectangleCarrierV1
open FamilyStickyCinematicL32CurvilinearRectanglePointMultiplicityV1
open FamilyStickyCinematicL32Lemma55CenteredRectangleDilationV1
open FamilyStickyCinematicL32Prop41PairLocalActualLensRectangleCoreV1
open FamilyStickyCinematicL32Prop41FiniteGeneralPositionExactRootReproductionV1

noncomputable section

/-!
# Exact-local restriction of a wider source rectangle

The paper fine rectangle can be wider than the harmonic local lens scale.
Keeping the same graph and jets while restricting its centred base produces
the exact length needed by Lemmas 3.12--3.16.  All pair-local root and
tangency data restrict monotonically to this smaller carrier.
-/

/-- Same graph and C2 jets, with centred base of exact length
`sqrt (delta / localScale)`. -/
def exactLocalC2GraphRectangle
    (R : C2GraphRectangle) (delta localScale : Real) : C2GraphRectangle :=
  centeredC2GraphRectangleDilation R delta localScale 1

@[simp]
theorem exactLocalC2GraphRectangle_length
    (R : C2GraphRectangle) (delta localScale : Real) :
    (exactLocalC2GraphRectangle R delta localScale).rectangle.right -
        (exactLocalC2GraphRectangle R delta localScale).rectangle.left =
      Real.sqrt (delta / localScale) := by
  simp [exactLocalC2GraphRectangle]

theorem exactLocalC2GraphRectangle_base_subset
    (R : C2GraphRectangle) {delta localScale : Real}
    (hwidth : Real.sqrt (delta / localScale) <=
      R.rectangle.right - R.rectangle.left) :
    (exactLocalC2GraphRectangle R delta localScale).rectangle.base ⊆
      R.rectangle.base := by
  intro theta htheta
  have hthetaPrime : theta ∈ Icc
      (graphRectangleCenter R.rectangle -
        Real.sqrt (delta / localScale) / 2)
      (graphRectangleCenter R.rectangle +
        Real.sqrt (delta / localScale) / 2) := by
    simpa [exactLocalC2GraphRectangle,
      centeredC2GraphRectangleDilation, GraphRectangle.base] using htheta
  change theta ∈ Icc R.rectangle.left R.rectangle.right
  dsimp only [graphRectangleCenter] at hthetaPrime
  constructor <;>
    linarith [R.rectangle.left_le_right, hthetaPrime.1, hthetaPrime.2]

theorem exactLocalC2GraphRectangle_carrier_subset
    (R : C2GraphRectangle) {delta localScale : Real}
    (hwidth : Real.sqrt (delta / localScale) <=
      R.rectangle.right - R.rectangle.left) :
    (exactLocalC2GraphRectangle R delta localScale).carrier delta ⊆
      R.carrier delta := by
  intro q hq
  refine ⟨exactLocalC2GraphRectangle_base_subset R hwidth hq.1, ?_⟩
  simpa [exactLocalC2GraphRectangle,
    centeredC2GraphRectangleDilation] using hq.2

/-- Restrict a perturbation-ready pair-local record to the exact local
subrectangle.  No root, coefficient, or tangency assumption is added. -/
def PerturbationReadyPairLocalActualLensRectangleData.toExactLocalRectangle
    {radius : NNReal} {T U : Tube radius} {f : Real -> Real}
    {R : C2GraphRectangle}
    {A B delta localScale lambda0 lambda1 : Real}
    (P : PerturbationReadyPairLocalActualLensRectangleData
      T U f R A B delta localScale lambda0 lambda1) :
    PerturbationReadyPairLocalActualLensRectangleData
      T U f (exactLocalC2GraphRectangle R delta localScale)
        A B delta localScale lambda0 lambda1 := by
  let Rlocal := exactLocalC2GraphRectangle R delta localScale
  have hbaseSubset : Rlocal.rectangle.base ⊆ R.rectangle.base := by
    exact exactLocalC2GraphRectangle_base_subset R P.data.rectangle_width
  have hleftBase : Rlocal.rectangle.left ∈ R.rectangle.base := by
    apply hbaseSubset
    exact ⟨le_rfl, Rlocal.rectangle.left_le_right⟩
  have hrightBase : Rlocal.rectangle.right ∈ R.rectangle.base := by
    apply hbaseSubset
    exact ⟨Rlocal.rectangle.left_le_right, le_rfl⟩
  have hleftQuarter : Rlocal.rectangle.left ∈
      centeredFractionIcc A B (1 / 4 : Real) := by
    rcases P.data.left_mem_quarter with ⟨hAL, _hLB⟩
    rcases P.data.right_mem_quarter with ⟨_hAR, hRB⟩
    exact ⟨hAL.trans hleftBase.1, hleftBase.2.trans hRB⟩
  have hrightQuarter : Rlocal.rectangle.right ∈
      centeredFractionIcc A B (1 / 4 : Real) := by
    rcases P.data.left_mem_quarter with ⟨hAL, _hLB⟩
    rcases P.data.right_mem_quarter with ⟨_hAR, hRB⟩
    exact ⟨hAL.trans hrightBase.1, hrightBase.2.trans hRB⟩
  have hcarrier : Rlocal.carrier delta ⊆ R.carrier delta := by
    exact exactLocalC2GraphRectangle_carrier_subset R P.data.rectangle_width
  refine {
    data := {
      thetaLeft := P.data.thetaLeft
      thetaRight := P.data.thetaRight
      theta_order := P.data.theta_order
      thetaLeft_mem := P.data.thetaLeft_mem
      thetaRight_mem := P.data.thetaRight_mem
      left_mem_quarter := hleftQuarter
      right_mem_quarter := hrightQuarter
      rectangle_width := by
        rw [exactLocalC2GraphRectangle_length]
      common_c := P.data.common_c
      root_left := P.data.root_left
      root_right := P.data.root_right
      exact_root_set := P.data.exact_root_set
      coefficient_lower := P.data.coefficient_lower
      tangent_first := by
        intro q hq
        have hold := P.data.tangent_first (hcarrier hq)
        exact ⟨hq.1, hold.2⟩
      tangent_second := by
        intro q hq
        have hold := P.data.tangent_second (hcarrier hq)
        exact ⟨hq.1, hold.2⟩ }
    thetaLeft_interior := P.thetaLeft_interior
    thetaRight_interior := P.thetaRight_interior
    coefficient_strict := P.coefficient_strict
    tangency_slack := P.tangency_slack }

#print axioms exactLocalC2GraphRectangle
#print axioms exactLocalC2GraphRectangle_base_subset
#print axioms exactLocalC2GraphRectangle_carrier_subset
#print axioms PerturbationReadyPairLocalActualLensRectangleData.toExactLocalRectangle

end

end FamilyStickyCinematicL32Prop41ExactLocalRectangleRestrictionV1
