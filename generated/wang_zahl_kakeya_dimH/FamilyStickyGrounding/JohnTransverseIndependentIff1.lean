import FamilyStickyGrounding.JohnTransverseNonzero4
import FamilyStickyGrounding.JohnTriangleReplacement1

namespace Submission.Kakeya.ConvexGeometry

open LeanEval.Analysis.WangZahlKakeya

noncomputable section

theorem transverseVector_ne_zero_iff_linearIndependent (u v : Space) :
    transverseVector u v ≠ 0 ↔ LinearIndependent ℝ ![u, v] := by
  constructor
  · intro hcross
    have hu : u ≠ 0 := by
      intro hu
      subst u
      apply hcross
      simp [transverseVector]
    rw [LinearIndependent.pair_iff' hu]
    intro a hav
    apply hcross
    rw [← hav, transverseVector_smul_right]
    simp [transverseVector]
  · exact transverseVector_ne_zero_of_linearIndependent

#print axioms transverseVector_ne_zero_iff_linearIndependent

end
end Submission.Kakeya.ConvexGeometry
