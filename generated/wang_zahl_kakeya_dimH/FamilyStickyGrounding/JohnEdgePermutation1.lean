import FamilyStickyGrounding.JohnDimThreeBallToBox4

open Set

namespace Submission.Kakeya.ConvexGeometry

open LeanEval.Analysis.WangZahlKakeya

noncomputable section

theorem edgeLinearImageBallThree4_swap01
    (c e₀ e₁ e₂ : Space) (R : ℝ) :
    edgeLinearImageBallThree4 c e₁ e₀ e₂ R =
      edgeLinearImageBallThree4 c e₀ e₁ e₂ R := by
  ext x
  constructor
  · rintro ⟨u, v, w, h, rfl⟩
    refine ⟨v, u, w, by nlinarith, ?_⟩
    module
  · rintro ⟨u, v, w, h, rfl⟩
    refine ⟨v, u, w, by nlinarith, ?_⟩
    module

theorem edgeLinearImageBallThree4_swap12
    (c e₀ e₁ e₂ : Space) (R : ℝ) :
    edgeLinearImageBallThree4 c e₀ e₂ e₁ R =
      edgeLinearImageBallThree4 c e₀ e₁ e₂ R := by
  ext x
  constructor
  · rintro ⟨u, v, w, h, rfl⟩
    refine ⟨u, w, v, by nlinarith, ?_⟩
    module
  · rintro ⟨u, v, w, h, rfl⟩
    refine ⟨u, w, v, by nlinarith, ?_⟩
    module

theorem linearIndependent_three_swap01
    {e₀ e₁ e₂ : Space} (h : LinearIndependent ℝ ![e₀, e₁, e₂]) :
    LinearIndependent ℝ ![e₁, e₀, e₂] := by
  let σ : Equiv.Perm (Fin 3) := Equiv.swap 0 1
  have hc := h.comp σ σ.injective
  convert hc using 1
  funext i
  fin_cases i <;> rfl

theorem linearIndependent_three_swap12
    {e₀ e₁ e₂ : Space} (h : LinearIndependent ℝ ![e₀, e₁, e₂]) :
    LinearIndependent ℝ ![e₀, e₂, e₁] := by
  let σ : Equiv.Perm (Fin 3) := Equiv.swap 1 2
  have hc := h.comp σ σ.injective
  convert hc using 1
  funext i
  fin_cases i <;> rfl

#print axioms edgeLinearImageBallThree4_swap01
#print axioms edgeLinearImageBallThree4_swap12
#print axioms linearIndependent_three_swap01
#print axioms linearIndependent_three_swap12

end
end Submission.Kakeya.ConvexGeometry
