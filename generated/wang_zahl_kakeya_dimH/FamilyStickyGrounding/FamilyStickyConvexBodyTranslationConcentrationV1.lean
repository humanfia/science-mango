import FamilyStickyGrounding.FamilyStickyActualTubeTranslationV1
import Submission.Kakeya.ConvexGeometry.Family

open Set MeasureTheory
open scoped ENNReal NNReal Pointwise

namespace FamilyStickyConvexBodyTranslationConcentrationV1

open LeanEval.Analysis.WangZahlKakeya
open Submission.Kakeya.ConvexGeometry
open FamilyStickyActualTubeTranslationV1

noncomputable section

/-!
# Translation invariance of convex-family concentration

GWZ Appendix Section 7 uses
`|T[R_j^{-1}K]| <= Delta_max(T) |K| / |T_delta|`.
This requires the maximal concentration of a family to be unchanged by a
common Euclidean translation.  The result is proved here from an actual
translation constructor for `ConvexBody`, exact containment, and Haar-volume
invariance; it is not assumed as a density callback.
-/

/-- Translate a convex body by one ambient vector. -/
def translateConvexBody (K : ConvexBody Space) (v : Space) :
    ConvexBody Space where
  carrier := (fun x => v + x) '' (K : Set Space)
  convex' := K.convex.translate v
  isCompact' := K.isCompact.image (continuous_const_add v)
  nonempty' := K.nonempty.image fun x => v + x

@[simp] theorem coe_translateConvexBody
    (K : ConvexBody Space) (v : Space) :
    (translateConvexBody K v : Set Space) =
      (fun x => v + x) '' (K : Set Space) := rfl

@[simp] theorem translateConvexBody_zero (K : ConvexBody Space) :
    translateConvexBody K 0 = K := by
  apply ConvexBody.ext
  simp [translateConvexBody]

theorem translateConvexBody_translateConvexBody
    (K : ConvexBody Space) (v w : Space) :
    translateConvexBody (translateConvexBody K w) v =
      translateConvexBody K (v + w) := by
  apply ConvexBody.ext
  ext x
  constructor
  · rintro ⟨y, ⟨z, hz, rfl⟩, rfl⟩
    exact ⟨z, hz, by abel_nf⟩
  · rintro ⟨z, hz, rfl⟩
    exact ⟨w + z, ⟨z, hz, rfl⟩, by abel_nf⟩

theorem translateConvexBody_neg_cancel
    (K : ConvexBody Space) (v : Space) :
    translateConvexBody (translateConvexBody K (-v)) v = K := by
  rw [translateConvexBody_translateConvexBody, add_neg_cancel,
    translateConvexBody_zero]

theorem volume_translateConvexBody
    (K : ConvexBody Space) (v : Space) :
    volume (translateConvexBody K v : Set Space) =
      volume (K : Set Space) := by
  change volume (v +ᵥ (K : Set Space)) = volume (K : Set Space)
  exact MeasureTheory.measure_vadd volume v (K : Set Space)

theorem translateConvexBody_subset_translateConvexBody_iff
    (K L : ConvexBody Space) (v : Space) :
    (translateConvexBody K v : Set Space) ⊆
        (translateConvexBody L v : Set Space) ↔
      (K : Set Space) ⊆ (L : Set Space) := by
  constructor
  · intro h x hx
    have hvx : v + x ∈ (translateConvexBody K v : Set Space) :=
      ⟨x, hx, rfl⟩
    obtain ⟨y, hy, hxy⟩ := h hvx
    have : x = y := (add_left_cancel hxy).symm
    simpa [this] using hy
  · exact fun h => Set.image_mono h

/-- Translate every member of an indexed convex family by the same vector. -/
def translateFamily {ι : Type*} (F : ConvexFamily ι) (v : Space) :
    ConvexFamily ι :=
  fun i => translateConvexBody (F i) v

theorem containedIndices_translateFamily
    {ι : Type*} [Fintype ι]
    (F : ConvexFamily ι) (K : ConvexBody Space) (v : Space) :
    containedIndices (translateFamily F v) (translateConvexBody K v) =
      containedIndices F K := by
  classical
  ext i
  simp only [containedIndices, Finset.mem_filter, Finset.mem_univ, true_and]
  exact translateConvexBody_subset_translateConvexBody_iff (F i) K v

theorem concentration_translateFamily
    {ι : Type*} [Fintype ι]
    (F : ConvexFamily ι) (K : ConvexBody Space) (v : Space) :
    concentration (translateFamily F v) (translateConvexBody K v) =
      concentration F K := by
  unfold concentration
  rw [containedIndices_translateFamily, volume_translateConvexBody]
  apply congrArg₂ (fun a b : ENNReal => a / b) ?_ rfl
  apply Finset.sum_congr rfl
  intro i hi
  exact volume_translateConvexBody (F i) v

/-- A common translation preserves the exact supremal concentration. -/
theorem maximalConcentration_translateFamily
    {ι : Type*} [Fintype ι]
    (F : ConvexFamily ι) (v : Space) :
    maximalConcentration (translateFamily F v) = maximalConcentration F := by
  apply le_antisymm
  · apply iSup_le
    intro K
    have hK : translateConvexBody (translateConvexBody K (-v)) v = K :=
      translateConvexBody_neg_cancel K v
    rw [← hK, concentration_translateFamily]
    exact concentration_le_maximalConcentration F
      (translateConvexBody K (-v))
  · apply iSup_le
    intro K
    calc
      concentration F K =
          concentration (translateFamily F v) (translateConvexBody K v) :=
        (concentration_translateFamily F K v).symm
      _ ≤ maximalConcentration (translateFamily F v) :=
        concentration_le_maximalConcentration _ _

/-- Actual tube translation agrees with convex-body translation. -/
theorem translateTube_body_eq_translateConvexBody
    {delta : NNReal} (T : Tube delta) (v : Space) :
    (translateTube T v).body = translateConvexBody T.body v := by
  apply ConvexBody.ext
  rw [translateTube_coe_body]
  rfl

#print axioms translateConvexBody_translateConvexBody
#print axioms volume_translateConvexBody
#print axioms containedIndices_translateFamily
#print axioms concentration_translateFamily
#print axioms maximalConcentration_translateFamily
#print axioms translateTube_body_eq_translateConvexBody

end


end FamilyStickyConvexBodyTranslationConcentrationV1
