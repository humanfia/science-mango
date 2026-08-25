import FamilyStickyGrounding.JohnEdgePermutation1
import FamilyStickyGrounding.JohnDimThreeSimplexSandwich1

open scoped NNReal
open Set

namespace Submission.Kakeya.ConvexGeometry
open LeanEval.Analysis.WangZahlKakeya
open TransverseCoordinateOverlap
noncomputable section

theorem edge_three_linearIndependent_of_tetraVolume_pos2
    {p q r s : Space} (hpos : 0 < tetraVolume p q r s) :
    LinearIndependent ℝ ![q-p,r-p,s-p] := by
  have hdet : LinearMap.det (innerCoordinateMap ![q-p,r-p,s-p]) ≠ 0 := by
    rw [← tetraSignedVolume_eq_det]
    rw [tetraVolume_def] at hpos
    exact abs_pos.mp hpos
  apply Matrix.det_gram_ne_zero_iff_linearIndependent.mp
  rw [← det_innerCoordinateMap_sq_eq_det_gram]
  exact pow_ne_zero 2 hdet

theorem exists_boxDimensionsCertificate_288_of_finrank_direction_affineSpan_eq_three2
    (K : ConvexBody Space)
    (hdim : Module.finrank ℝ (affineSpan ℝ (K : Set Space)).direction = 3) :
    ∃ side : Fin 3 → ℝ≥0, Nonempty (BoxDimensionsCertificate 288 side K) := by
  obtain ⟨p,hp,q,hq,r,hr,s,hs,hpos,hinT,houtT⟩ :=
    exists_dimThree_tetraEdgeBall_sandwich K hdim
  let c := tetraBarycenter p q r s
  let e₀ := q-p
  let e₁ := r-p
  let e₂ := s-p
  have hli : LinearIndependent ℝ ![e₀,e₁,e₂] := by
    simpa [e₀,e₁,e₂] using edge_three_linearIndependent_of_tetraVolume_pos2 hpos
  have hin : edgeLinearImageBallThree4 c e₀ e₁ e₂ (1/12) ⊆ (K:Set Space) := by
    simpa [c,e₀,e₁,e₂,tetraEdgeBall,edgeLinearImageBallThree4] using hinT
  have hout : (K:Set Space) ⊆ edgeLinearImageBallThree4 c e₀ e₁ e₂ 3 := by
    intro x hx
    rcases houtT hx with ⟨u,v,w,huv,hrep⟩
    refine ⟨u,v,w,?_,?_⟩
    · nlinarith
    · simpa [c,e₀,e₁,e₂,tetraEdgeBall] using hrep
  have finish : ∀ (a b d : Space),
      LinearIndependent ℝ ![a,b,d] →
      ‖b‖ ≤ ‖a‖ → ‖d‖ ≤ ‖a‖ →
      ‖firstResidual2 a d‖ ≤ ‖firstResidual2 a b‖ →
      (∀ R, edgeLinearImageBallThree4 c a b d R =
        edgeLinearImageBallThree4 c e₀ e₁ e₂ R) →
      ∃ side : Fin 3 → ℝ≥0, Nonempty (BoxDimensionsCertificate 288 side K) := by
    intro a b d habd hba hda hres hball
    apply ordered_edgeBallThree_to_boxDimensionsCertificate4 K c a b d habd hba hda hres
    · rw [hball]
      exact hin
    · rw [hball]
      exact hout
  have finishResidual : ∀ (a b d : Space),
      LinearIndependent ℝ ![a,b,d] →
      ‖b‖ ≤ ‖a‖ → ‖d‖ ≤ ‖a‖ →
      (∀ R, edgeLinearImageBallThree4 c a b d R =
        edgeLinearImageBallThree4 c e₀ e₁ e₂ R) →
      ∃ side : Fin 3 → ℝ≥0, Nonempty (BoxDimensionsCertificate 288 side K) := by
    intro a b d habd hba hda hball
    by_cases hres : ‖firstResidual2 a d‖ ≤ ‖firstResidual2 a b‖
    · exact finish a b d habd hba hda hres hball
    · apply finish a d b (linearIndependent_three_swap12 habd) hda hba
        (le_of_lt (lt_of_not_ge hres))
      intro R
      calc
        edgeLinearImageBallThree4 c a d b R =
            edgeLinearImageBallThree4 c a b d R :=
          edgeLinearImageBallThree4_swap12 c a b d R
        _ = edgeLinearImageBallThree4 c e₀ e₁ e₂ R := hball R
  by_cases h₁₀ : ‖e₁‖ ≤ ‖e₀‖
  · by_cases h₂₀ : ‖e₂‖ ≤ ‖e₀‖
    · exact finishResidual e₀ e₁ e₂ hli h₁₀ h₂₀ (fun _ ↦ rfl)
    · have h₀₂ : ‖e₀‖ ≤ ‖e₂‖ := le_of_lt (lt_of_not_ge h₂₀)
      have h₁₂ : ‖e₁‖ ≤ ‖e₂‖ := h₁₀.trans h₀₂
      have hli' : LinearIndependent ℝ ![e₂,e₀,e₁] :=
        linearIndependent_three_swap01 (linearIndependent_three_swap12 hli)
      apply finishResidual e₂ e₀ e₁ hli' h₀₂ h₁₂
      intro R
      calc
        edgeLinearImageBallThree4 c e₂ e₀ e₁ R =
            edgeLinearImageBallThree4 c e₀ e₂ e₁ R :=
          edgeLinearImageBallThree4_swap01 c e₀ e₂ e₁ R
        _ = edgeLinearImageBallThree4 c e₀ e₁ e₂ R :=
          edgeLinearImageBallThree4_swap12 c e₀ e₁ e₂ R
  · have h₀₁ : ‖e₀‖ ≤ ‖e₁‖ := le_of_lt (lt_of_not_ge h₁₀)
    by_cases h₂₁ : ‖e₂‖ ≤ ‖e₁‖
    · apply finishResidual e₁ e₀ e₂ (linearIndependent_three_swap01 hli)
        h₀₁ h₂₁
      exact edgeLinearImageBallThree4_swap01 c e₀ e₁ e₂
    · have h₁₂ : ‖e₁‖ ≤ ‖e₂‖ := le_of_lt (lt_of_not_ge h₂₁)
      have h₀₂ : ‖e₀‖ ≤ ‖e₂‖ := h₀₁.trans h₁₂
      have hli' : LinearIndependent ℝ ![e₂,e₀,e₁] :=
        linearIndependent_three_swap01 (linearIndependent_three_swap12 hli)
      apply finishResidual e₂ e₀ e₁ hli' h₀₂ h₁₂
      intro R
      calc
        edgeLinearImageBallThree4 c e₂ e₀ e₁ R =
            edgeLinearImageBallThree4 c e₀ e₂ e₁ R :=
          edgeLinearImageBallThree4_swap01 c e₀ e₂ e₁ R
        _ = edgeLinearImageBallThree4 c e₀ e₁ e₂ R :=
          edgeLinearImageBallThree4_swap12 c e₀ e₁ e₂ R

#print axioms edge_three_linearIndependent_of_tetraVolume_pos2
#print axioms exists_boxDimensionsCertificate_288_of_finrank_direction_affineSpan_eq_three2
end
end Submission.Kakeya.ConvexGeometry
