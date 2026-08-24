import FamilyStickyGrounding.Cinematic.FamilyStickyCinematicL32Prop41FirstGenerationLensCarrierV1
import Mathlib.Logic.Equiv.Fin.Basic

set_option autoImplicit false

open Set

namespace FamilyStickyCinematicL32Prop41FourLensCodeRealizationV1

open FamilyStickyCinematicL32Prop41FirstGenerationLensCarrierV1

noncomputable section

/-!
# Four nontrivial lens codes from an oriented two-arc decomposition

For two closed curves meeting transversely at exactly two points, each curve
is split into two oriented closed arcs.  A nontrivial first-generation lens
chooses one arc from each curve, hence is indexed canonically by
`Fin 2 × Fin 2 ≃ Fin 4`.  This file is the finite/cyclic combinatorial layer;
constructing the arc decomposition from rectangular-skirt Jordan curves is
kept as the next topological source obligation.
-/

/-- Faithful source interface for one unordered pair of distinct curves:
an orientation of the pair, two distinct crossings, and the two closed arcs
of each oriented curve.  The endpoint/cover/intersection fields record the
exact Jordan source obligations even though the four-code calculation only
uses the labeled arcs. -/
structure OrientedTwoArcPairRealization
    {curve point : Type*} [DecidableEq curve]
    (curves : Finset curve) (curveSet : FirstGenerationCurve curves ->
      Set point) (p : FirstGenerationCurvePair curves) where
  firstCurve : FirstGenerationCurve curves
  secondCurve : FirstGenerationCurve curves
  pair_eq : p.1 = s(firstCurve, secondCurve)
  first_ne_second : firstCurve ≠ secondCurve
  crossing : Fin 2 -> point
  crossing_ne : crossing 0 ≠ crossing 1
  firstArc : Fin 2 -> Set point
  secondArc : Fin 2 -> Set point
  firstArc_subset : forall i, firstArc i ⊆ curveSet firstCurve
  secondArc_subset : forall i, secondArc i ⊆ curveSet secondCurve
  firstArc_endpoints : forall i,
    crossing 0 ∈ firstArc i ∧ crossing 1 ∈ firstArc i
  secondArc_endpoints : forall i,
    crossing 0 ∈ secondArc i ∧ crossing 1 ∈ secondArc i
  firstArc_cover : firstArc 0 ∪ firstArc 1 = curveSet firstCurve
  secondArc_cover : secondArc 0 ∪ secondArc 1 = curveSet secondCurve
  firstArc_meet : firstArc 0 ∩ firstArc 1 =
    {crossing 0, crossing 1}
  secondArc_meet : secondArc 0 ∩ secondArc 1 =
    {crossing 0, crossing 1}
  curve_intersection : curveSet firstCurve ∩ curveSet secondCurve =
    {crossing 0, crossing 1}

/-- The canonical equivalence witnessing `2 × 2 = 4`. -/
def fourLensSlotEquiv : Fin 2 × Fin 2 ≃ Fin 4 :=
  finProdFinEquiv

/-- The canonical `2 × 2 = 4` slot for one choice of arc from each curve. -/
def fourLensSlot (firstChoice secondChoice : Fin 2) : Fin 4 :=
  fourLensSlotEquiv (firstChoice, secondChoice)

/-- The four slots are genuinely distinct. -/
theorem fourLensSlot_pair_injective :
    Function.Injective
      (fun choices : Fin 2 × Fin 2 =>
        fourLensSlot choices.1 choices.2) := by
  exact fourLensSlotEquiv.injective

/-- Every `Fin 4` code is mechanically a unique pair of binary arc choices. -/
theorem exists_unique_choices_for_fourLensSlot (slot : Fin 4) :
    ∃! choices : Fin 2 × Fin 2,
      fourLensSlot choices.1 choices.2 = slot := by
  refine ⟨fourLensSlotEquiv.symm slot, ?_, ?_⟩
  · exact fourLensSlotEquiv.apply_symm_apply slot
  · intro choices hchoices
    exact fourLensSlotEquiv.injective (hchoices.trans
      (fourLensSlotEquiv.apply_symm_apply slot).symm)

/-- The boundary selected by one of the four nontrivial slots. -/
def pairLensBoundary
    {curve point : Type*} [DecidableEq curve]
    {curves : Finset curve}
    {curveSet : FirstGenerationCurve curves -> Set point}
    {p : FirstGenerationCurvePair curves}
    (D : OrientedTwoArcPairRealization curves curveSet p)
    (slot : Fin 4) : Set point :=
  D.firstArc (fourLensSlotEquiv.symm slot).1 ∪
    D.secondArc (fourLensSlotEquiv.symm slot).2

/-- Realize the complete finite first-generation code carrier: a left code
is a whole curve, while a right code is one of the four pair boundaries. -/
def firstGenerationLensBoundary
    {curve point : Type*} [DecidableEq curve]
    (curves : Finset curve)
    (curveSet : FirstGenerationCurve curves -> Set point)
    (pairData : forall p : FirstGenerationCurvePair curves,
      OrientedTwoArcPairRealization curves curveSet p)
    (code : FirstGenerationLensCode curves) : Set point :=
  match code with
  | Sum.inl c => curveSet c
  | Sum.inr ps => pairLensBoundary (pairData ps.1) ps.2

/-- Decoding the slot selected from two oriented arc choices returns exactly
those choices. -/
theorem pairLensBoundary_fourLensSlot
    {curve point : Type*} [DecidableEq curve]
    {curves : Finset curve}
    {curveSet : FirstGenerationCurve curves -> Set point}
    {p : FirstGenerationCurvePair curves}
    (D : OrientedTwoArcPairRealization curves curveSet p)
    (firstChoice secondChoice : Fin 2) :
    pairLensBoundary D (fourLensSlot firstChoice secondChoice) =
      D.firstArc firstChoice ∪ D.secondArc secondChoice := by
  simp [pairLensBoundary, fourLensSlot]

/-- The corresponding finite right-hand lens code has exactly the union of
the two chosen oriented arcs as its realized boundary. -/
theorem firstGenerationLensBoundary_pairSlot
    {curve point : Type*} [DecidableEq curve]
    (curves : Finset curve)
    (curveSet : FirstGenerationCurve curves -> Set point)
    (pairData : forall p : FirstGenerationCurvePair curves,
      OrientedTwoArcPairRealization curves curveSet p)
    (p : FirstGenerationCurvePair curves)
    (firstChoice secondChoice : Fin 2) :
    firstGenerationLensBoundary curves curveSet pairData
        (Sum.inr (p, fourLensSlot firstChoice secondChoice)) =
      (pairData p).firstArc firstChoice ∪
        (pairData p).secondArc secondChoice := by
  exact pairLensBoundary_fourLensSlot (pairData p)
    firstChoice secondChoice

/-- If the two selected arcs are the actual ordered-root graph arcs, the
mechanically selected `Fin 4` code realizes exactly that actual boundary. -/
theorem firstGenerationLensBoundary_pairSlot_eq_actualBoundary
    {curve point : Type*} [DecidableEq curve]
    (curves : Finset curve)
    (curveSet : FirstGenerationCurve curves -> Set point)
    (pairData : forall p : FirstGenerationCurvePair curves,
      OrientedTwoArcPairRealization curves curveSet p)
    (p : FirstGenerationCurvePair curves)
    (firstChoice secondChoice : Fin 2)
    (actualFirstArc actualSecondArc : Set point)
    (hfirst : (pairData p).firstArc firstChoice = actualFirstArc)
    (hsecond : (pairData p).secondArc secondChoice = actualSecondArc) :
    firstGenerationLensBoundary curves curveSet pairData
        (Sum.inr (p, fourLensSlot firstChoice secondChoice)) =
      actualFirstArc ∪ actualSecondArc := by
  rw [firstGenerationLensBoundary_pairSlot, hfirst, hsecond]

#print axioms OrientedTwoArcPairRealization
#print axioms fourLensSlotEquiv
#print axioms fourLensSlot
#print axioms fourLensSlot_pair_injective
#print axioms exists_unique_choices_for_fourLensSlot
#print axioms pairLensBoundary
#print axioms firstGenerationLensBoundary
#print axioms pairLensBoundary_fourLensSlot
#print axioms firstGenerationLensBoundary_pairSlot
#print axioms firstGenerationLensBoundary_pairSlot_eq_actualBoundary

end

end FamilyStickyCinematicL32Prop41FourLensCodeRealizationV1
