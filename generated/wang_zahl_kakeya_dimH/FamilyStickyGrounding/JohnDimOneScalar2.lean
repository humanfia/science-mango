import FamilyStickyGrounding.JohnDimOneFrame1

open scoped InnerProductSpace
open Set

namespace Submission.Kakeya.ConvexGeometry

open LeanEval.Analysis.WangZahlKakeya

noncomputable section

def affineDirectionBasisOne (K : ConvexBody Space)
    (hdim : Module.finrank ℝ (affineSpan ℝ (K : Set Space)).direction = 1) :
    OrthonormalBasis (Fin 1) ℝ (affineSpan ℝ (K : Set Space)).direction :=
  (stdOrthonormalBasis ℝ (affineSpan ℝ (K : Set Space)).direction).reindex
    (finCongr hdim)

def affineUnitDirection (K : ConvexBody Space)
    (hdim : Module.finrank ℝ (affineSpan ℝ (K : Set Space)).direction = 1) : Space :=
  (affineDirectionBasisOne K hdim 0 :
    (affineSpan ℝ (K : Set Space)).direction)

theorem norm_affineUnitDirection (K : ConvexBody Space)
    (hdim : Module.finrank ℝ (affineSpan ℝ (K : Set Space)).direction = 1) :
    ‖affineUnitDirection K hdim‖ = 1 := by
  change ‖(affineDirectionBasisOne K hdim) 0‖ = 1
  exact (affineDirectionBasisOne K hdim).norm_eq_one 0

def affineLineCoord (K : ConvexBody Space)
    (hdim : Module.finrank ℝ (affineSpan ℝ (K : Set Space)).direction = 1)
    (c x : Space) : ℝ :=
  ⟪affineUnitDirection K hdim, x - c⟫_ℝ

theorem eq_add_affineLineCoord_smul (K : ConvexBody Space)
    (hdim : Module.finrank ℝ (affineSpan ℝ (K : Set Space)).direction = 1)
    {c x : Space} (hc : c ∈ affineSpan ℝ (K : Set Space))
    (hx : x ∈ affineSpan ℝ (K : Set Space)) :
    x = c + affineLineCoord K hdim c x • affineUnitDirection K hdim := by
  let v : (affineSpan ℝ (K : Set Space)).direction :=
    ⟨x - c, AffineSubspace.vsub_mem_direction hx hc⟩
  have hrepr := (affineDirectionBasisOne K hdim).sum_repr' v
  have hreprVal := congrArg Subtype.val hrepr
  rw [Fin.sum_univ_one] at hreprVal
  have hv : x - c = affineLineCoord K hdim c x • affineUnitDirection K hdim := by
    simpa [v, affineLineCoord, affineUnitDirection, real_inner_comm] using hreprVal.symm
  calc
    x = c + (x - c) := by abel
    _ = c + affineLineCoord K hdim c x • affineUnitDirection K hdim := by rw [hv]

#print axioms norm_affineUnitDirection
#print axioms eq_add_affineLineCoord_smul

end
end Submission.Kakeya.ConvexGeometry
