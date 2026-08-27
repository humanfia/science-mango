import FamilyStickyGrounding.Cinematic.FamilyStickyCinematicL32Prop41ActualY1SamplingPaperFineGPrimeLabelFirstExactCProvenanceV2

set_option autoImplicit false
set_option warningAsError true

namespace FamilyStickyCinematicL32Prop41ActualGPrimeLabelFirstLabelInjectivityV1

open FamilyStickyCinematicL32Prop41ActualY1SamplingPaperFineGPrimeLabelFirstProvenanceV1
open FamilyStickyCinematicL32Prop41ActualY1SamplingPaperFineGPrimeLabelFirstExactCProvenanceV2
open FamilyStickyCinematicL32Prop41CoarseRectangleIncidenceDataV1
open FamilyStickyCinematicL32Prop41CanonicalMaximizerNonconcentrationV1

noncomputable section

universe u v

/-!
# Fine-label multiplicity of label-first survivors

The ordinary label-first survivor is a subtype of the bilateral fine-label
finset itself.  Hence its fine-label projection is injective.  The Exact-C
variant is instead a subtype of `(fineLabel × Real)` cells: its label alone
need not be injective, but the pair `(label, c)` is injective, and the label
is injective on every fixed-`c` fibre.
-/

theorem actualGPrimeLabelFirstLabel_injective
    {radius : NNReal} {iota : Type u} [DecidableEq iota]
    {fineLabel : Type v} [DecidableEq fineLabel]
    (N : CanonicalNormNonconcentrationData iota)
    (D : CoarseRectangleIncidenceData (point := Real × Real)
      (radius := radius) (iota := iota) fineLabel)
    (keep : iota -> fineLabel -> Prop) (left right : iota)
    (ballRadius : Real)
    (omega : (N.family -> Fin 1) × (N.family -> Fin 1)) :
    Function.Injective
      (actualGPrimeLabelFirstLabel
        N D keep left right ballRadius omega) := by
  intro a b hab
  apply Subtype.ext
  apply Subtype.ext
  exact hab

theorem actualGPrimeLabelFirstExactCLabelValue_injective
    {radius : NNReal} {iota : Type u} [DecidableEq iota]
    {fineLabel : Type v} [DecidableEq fineLabel]
    (N : CanonicalNormNonconcentrationData iota)
    (D : CoarseRectangleIncidenceData (point := Real × Real)
      (radius := radius) (iota := iota) fineLabel)
    (keep : iota -> fineLabel -> Prop) (left right : iota)
    (ballRadius : Real)
    (omega : (N.family -> Fin 1) × (N.family -> Fin 1)) :
    Function.Injective (fun a : ActualGPrimeLabelFirstExactCSurvivor
        N D keep left right ballRadius omega =>
      (actualGPrimeLabelFirstExactCLabel
          N D keep left right ballRadius omega a,
        actualGPrimeLabelFirstExactCValue
          N D keep left right ballRadius omega a)) := by
  intro a b hab
  apply Subtype.ext
  apply Subtype.ext
  exact Prod.ext (congrArg Prod.fst hab) (congrArg Prod.snd hab)

theorem actualGPrimeLabelFirstExactCLabel_injective_on_value_fibre
    {radius : NNReal} {iota : Type u} [DecidableEq iota]
    {fineLabel : Type v} [DecidableEq fineLabel]
    (N : CanonicalNormNonconcentrationData iota)
    (D : CoarseRectangleIncidenceData (point := Real × Real)
      (radius := radius) (iota := iota) fineLabel)
    (keep : iota -> fineLabel -> Prop) (left right : iota)
    (ballRadius : Real)
    (omega : (N.family -> Fin 1) × (N.family -> Fin 1))
    (c : Real) {a b : ActualGPrimeLabelFirstExactCSurvivor
      N D keep left right ballRadius omega}
    (ha : actualGPrimeLabelFirstExactCValue
      N D keep left right ballRadius omega a = c)
    (hb : actualGPrimeLabelFirstExactCValue
      N D keep left right ballRadius omega b = c)
    (hlabel : actualGPrimeLabelFirstExactCLabel
      N D keep left right ballRadius omega a =
        actualGPrimeLabelFirstExactCLabel
          N D keep left right ballRadius omega b) :
    a = b := by
  apply actualGPrimeLabelFirstExactCLabelValue_injective
    N D keep left right ballRadius omega
  apply Prod.ext hlabel
  exact ha.trans hb.symm

#print axioms actualGPrimeLabelFirstLabel_injective
#print axioms actualGPrimeLabelFirstExactCLabelValue_injective
#print axioms actualGPrimeLabelFirstExactCLabel_injective_on_value_fibre

end

end FamilyStickyCinematicL32Prop41ActualGPrimeLabelFirstLabelInjectivityV1
