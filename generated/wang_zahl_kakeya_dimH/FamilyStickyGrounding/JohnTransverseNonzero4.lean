import FamilyStickyGrounding.JohnTriangleContinuity2

namespace Submission.Kakeya.ConvexGeometry

open LeanEval.Analysis.WangZahlKakeya

noncomputable section

/-- The transported cross product is nonzero on a linearly independent pair. -/
theorem transverseVector_ne_zero_of_linearIndependent {u v : Space}
    (h : LinearIndependent ℝ ![u, v]) : transverseVector u v ≠ 0 := by
  let e := WithLp.linearEquiv 2 ℝ (Fin 3 → ℝ)
  have hu : u ≠ 0 := h.ne_zero 0
  have heu : WithLp.ofLp u ≠ 0 := by
    intro hz
    apply hu
    exact e.injective (by simpa [e] using hz)
  have hpair := (LinearIndependent.pair_iff' hu).mp h
  have hplain : LinearIndependent ℝ ![WithLp.ofLp u, WithLp.ofLp v] := by
    rw [LinearIndependent.pair_iff' heu]
    intro a ha
    apply hpair a
    exact e.injective (by simpa [e] using ha)
  have hcross : crossProduct (WithLp.ofLp u) (WithLp.ofLp v) ≠ 0 :=
    crossProduct_ne_zero_iff_linearIndependent.mpr hplain
  intro hzero
  apply hcross
  have := congrArg WithLp.ofLp hzero
  simpa [transverseVector] using this

#print axioms transverseVector_ne_zero_of_linearIndependent

end
end Submission.Kakeya.ConvexGeometry
