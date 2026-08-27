import ArchonPhysics.ThreeFrequencyLiftedJacobianFactorization
import ArchonPhysics.ThreeParameterProjectorWeightJacobian

/-!
# Exact determinant of the lifted three-frequency row transform

The child-child-mismatch coordinates are obtained from the three raw
frequencies by a fixed row operation.  Its determinant is exactly the sign
coefficient of the parent-frequency row, hence has absolute value one.  This
upgrades the previously used nonvanishing equivalence to an exact identity.
-/

namespace ArchonPhysics.ThreeFrequencyLiftedJacobianDeterminant

open ArchonPhysics
open ArchonPhysics.ModalPhaseMismatch
open ArchonPhysics.ThreeFrequencyLiftedJacobianFactorization
open ArchonPhysics.ThreeParameterProjectorWeightJacobian
open ArchonPhysics.ThreeParameterSpectralAveragingDensity
open scoped Matrix

noncomputable section

/-- Matrix of the output row transform
`(omega0,omega1,omega2) ↦ (omega1,omega2,mismatch)`. -/
def liftedFrequencyOutputMatrix (sign : Fin 3 → InteractionSign) :
    Matrix (Fin 3) (Fin 3) Real :=
  !![0, 1, 0;
     0, 0, 1;
     (sign 0).coefficient, (sign 1).coefficient,
       (sign 2).coefficient]

/-- The output row transform as a continuous endomorphism of `MassTriple`. -/
def liftedFrequencyOutputTransform (sign : Fin 3 → InteractionSign) :
    MassTriple →L[Real] MassTriple :=
  massTripleLinearMapOfMatrix (liftedFrequencyOutputMatrix sign)

theorem liftedFrequencyOutputTransform_apply
    (sign : Fin 3 → InteractionSign) (x : MassTriple) :
    liftedFrequencyOutputTransform sign x =
      ((x.1.2, x.2),
        (sign 0).coefficient * x.1.1 +
          (sign 1).coefficient * x.1.2 +
            (sign 2).coefficient * x.2) := by
  simp [liftedFrequencyOutputTransform, liftedFrequencyOutputMatrix,
    massTripleLinearMapOfMatrix_apply]

/-- The row transform determinant is exactly the coefficient of the omitted
parent-frequency row. -/
theorem liftedFrequencyOutputTransform_det
    (sign : Fin 3 → InteractionSign) :
    (liftedFrequencyOutputTransform sign).det =
      (sign 0).coefficient := by
  rw [liftedFrequencyOutputTransform,
    det_massTripleLinearMapOfMatrix, Matrix.det_fin_three]
  simp [liftedFrequencyOutputMatrix]

/-- The lifted derivative is the fixed output transform composed with the
raw three-frequency derivative. -/
theorem liftedFrequencyDerivative_eq_outputTransform_comp
    (sign : Fin 3 → InteractionSign)
    (derivative : Fin 3 → MassTriple →L[Real] Real) :
    liftedFrequencyDerivative sign derivative =
      (liftedFrequencyOutputTransform sign).comp
        (frequencyTripleDerivative derivative) := by
  apply ContinuousLinearMap.ext
  intro x
  simp [liftedFrequencyDerivative, frequencyTripleDerivative,
    liftedFrequencyOutputTransform_apply, Fin.sum_univ_succ]
  ring

/-- Exact determinant identity for the lifted chart. -/
theorem liftedFrequencyDerivative_det_eq
    (sign : Fin 3 → InteractionSign)
    (derivative : Fin 3 → MassTriple →L[Real] Real) :
    (liftedFrequencyDerivative sign derivative).det =
      (sign 0).coefficient *
        (frequencyTripleDerivative derivative).det := by
  rw [liftedFrequencyDerivative_eq_outputTransform_comp]
  change LinearMap.det
      ((liftedFrequencyOutputTransform sign).toLinearMap.comp
        (frequencyTripleDerivative derivative).toLinearMap) = _
  rw [LinearMap.det_comp]
  change (liftedFrequencyOutputTransform sign).det *
      (frequencyTripleDerivative derivative).det = _
  rw [liftedFrequencyOutputTransform_det]

/-- In particular, lifting preserves the determinant absolute value. -/
theorem abs_liftedFrequencyDerivative_det_eq
    (sign : Fin 3 → InteractionSign)
    (derivative : Fin 3 → MassTriple →L[Real] Real) :
    |(liftedFrequencyDerivative sign derivative).det| =
      |(frequencyTripleDerivative derivative).det| := by
  rw [liftedFrequencyDerivative_det_eq, abs_mul]
  cases sign 0 <;> simp

end

end ArchonPhysics.ThreeFrequencyLiftedJacobianDeterminant
