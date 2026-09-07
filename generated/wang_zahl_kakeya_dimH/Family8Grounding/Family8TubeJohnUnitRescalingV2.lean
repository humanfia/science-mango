import Family8Grounding.Family8TubeJohnAxisWitnessV1

set_option autoImplicit false
set_option warningAsError true

open Set
open scoped NNReal InnerProductSpace

namespace Family8TubeJohnUnitRescalingV2

open LeanEval.Analysis.WangZahlKakeya
open Submission.Kakeya.ConvexGeometry
open Family8Def212ConvexWolffAtEveryScaleV2
open Family8TubeJohnAxisWitnessV1

noncomputable section

/-!
# Exact unit normalization of the explicit tube John ellipsoid

The map first takes coordinates in the aligned orthonormal frame, divides
coordinate `i` by `3 * radius i`, and returns to the same ambient frame.
Translation by the ellipsoid center then sends the scale-three ellipsoid
exactly to the closed unit ball.
-/

theorem tubeJohnRadii_pos {rho : NNReal} (hrho : 0 < rho) (i : Fin 3) :
    0 < tubeJohnRadii rho i := by
  fin_cases i <;> simp [tubeJohnRadii, hrho]

/-- Diagonal division by the scale-three semiaxes, expressed in an
orthonormal ambient frame. -/
def axisEllipsoidNormalizationLinearEquiv
    (frame : OrthonormalBasis (Fin 3) Real Space)
    (radius : Fin 3 -> NNReal) (hradius : forall i, 0 < radius i) :
    Space ≃ₗ[Real] Space :=
  (frame.toBasis.equivFun.trans
    (LinearEquiv.piCongrRight fun i =>
      (LinearEquiv.smulOfNeZero Real Real
        (3 * (radius i : Real)) (by
          exact mul_ne_zero (by norm_num) (by
            exact_mod_cast (hradius i).ne'))).symm)).trans
    frame.toBasis.equivFun.symm

@[simp]
theorem axisEllipsoidNormalizationLinearEquiv_apply
    (frame : OrthonormalBasis (Fin 3) Real Space)
    (radius : Fin 3 -> NNReal) (hradius : forall i, 0 < radius i)
    (x : Space) :
    axisEllipsoidNormalizationLinearEquiv frame radius hradius x =
      ∑ i, (⟪frame i, x⟫_Real / (3 * (radius i : Real))) • frame i := by
  classical
  apply frame.toBasis.equivFun.injective
  funext i
  simp [axisEllipsoidNormalizationLinearEquiv,
    OrthonormalBasis.repr_apply_apply, Pi.single_apply, div_eq_inv_mul, Units.smul_def, Units.val_inv_eq_inv_val]

@[simp]
theorem axisEllipsoidNormalizationLinearEquiv_symm_apply
    (frame : OrthonormalBasis (Fin 3) Real Space)
    (radius : Fin 3 -> NNReal) (hradius : forall i, 0 < radius i)
    (x : Space) :
    (axisEllipsoidNormalizationLinearEquiv frame radius hradius).symm x =
      ∑ i, ((3 * (radius i : Real)) * ⟪frame i, x⟫_Real) • frame i := by
  classical
  apply frame.toBasis.equivFun.injective
  funext i
  simp [axisEllipsoidNormalizationLinearEquiv,
    OrthonormalBasis.repr_apply_apply, Pi.single_apply]

/-- The center-to-origin affine normalization attached to positive semiaxes. -/
def axisEllipsoidNormalizationAffineEquiv
    (center : Space) (frame : OrthonormalBasis (Fin 3) Real Space)
    (radius : Fin 3 -> NNReal) (hradius : forall i, 0 < radius i) :
    Space ≃ᵃ[Real] Space :=
  AffineEquiv.ofLinearEquiv
    (axisEllipsoidNormalizationLinearEquiv frame radius hradius)
    center 0

@[simp]
theorem axisEllipsoidNormalizationAffineEquiv_apply
    (center : Space) (frame : OrthonormalBasis (Fin 3) Real Space)
    (radius : Fin 3 -> NNReal) (hradius : forall i, 0 < radius i)
    (x : Space) :
    axisEllipsoidNormalizationAffineEquiv center frame radius hradius x =
      ∑ i, (⟪frame i, x - center⟫_Real /
        (3 * (radius i : Real))) • frame i := by
  simp [axisEllipsoidNormalizationAffineEquiv]

#print axioms axisEllipsoidNormalizationAffineEquiv_apply

end
end Family8TubeJohnUnitRescalingV2
