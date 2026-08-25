import FamilyStickyGrounding.JohnTriangleContinuity2
import Submission.Kakeya.ConvexFactoring.DeterminantAngleBridge

set_option autoImplicit false

open scoped InnerProductSpace Matrix

namespace Submission.Kakeya.ConvexGeometry

open LeanEval.Analysis.WangZahlKakeya
open TransverseCoordinateOverlap

noncomputable section

/-- Oriented six-times-volume of the tetrahedron `p q r s`. -/
def tetraSignedVolume (p q r s : Space) : ℝ :=
  ⟪q - p, transverseVector (r - p) (s - p)⟫_ℝ

/-- Absolute six-times-volume of the tetrahedron `p q r s`. -/
irreducible_def tetraVolume (p q r s : Space) : ℝ :=
  |tetraSignedVolume p q r s|

/-- The oriented tetrahedron volume is the determinant of its three edge
vectors in standard Euclidean coordinates. -/
theorem tetraSignedVolume_eq_det (p q r s : Space) :
    tetraSignedVolume p q r s =
      LinearMap.det (innerCoordinateMap ![q - p, r - p, s - p]) := by
  rw [det_innerCoordinateMap_vec3_eq_tripleProduct]
  simp only [tetraSignedVolume, transverseVector,
    EuclideanSpace.inner_eq_star_dotProduct]
  have hstar : star (q - p).ofLp = (q - p).ofLp := by
    ext i
    simp
  rw [hstar]
  exact dotProduct_comm _ _

/-- Absolute tetrahedron volume is continuous on the nested product used for
compact optimization over `K⁴`. -/
theorem continuous_tetraVolume :
    Continuous (fun x : Space × (Space × (Space × Space)) ↦
      tetraVolume x.1 x.2.1 x.2.2.1 x.2.2.2) := by
  rw [show (fun x : Space × (Space × (Space × Space)) ↦
      tetraVolume x.1 x.2.1 x.2.2.1 x.2.2.2) =
      (fun x ↦ |⟪x.2.1 - x.1,
        transverseVector (x.2.2.1 - x.1) (x.2.2.2 - x.1)⟫_ℝ|) by
        funext x
        rw [tetraVolume_def]
        rfl]
  have hedge0 : Continuous
      (fun x : Space × (Space × (Space × Space)) ↦ x.2.1 - x.1) := by
    fun_prop
  have hcross : Continuous
      (fun x : Space × (Space × (Space × Space)) ↦
        transverseVector (x.2.2.1 - x.1) (x.2.2.2 - x.1)) := by
    have hargs : Continuous
        (fun x : Space × (Space × (Space × Space)) ↦
          (x.2.2.1 - x.1, x.2.2.2 - x.1)) := by
      fun_prop
    exact transverseCLM.continuous₂.comp hargs
  exact (hedge0.inner hcross).abs

#print axioms tetraSignedVolume_eq_det
#print axioms continuous_tetraVolume

end
end Submission.Kakeya.ConvexGeometry
