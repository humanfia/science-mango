import Mathlib.Analysis.InnerProductSpace.NormDet
import Mathlib.Tactic
import ArchonPhysics.ModalPhaseMismatch
import ArchonPhysics.ThreeParameterSpectralAveragingDensity

namespace ArchonPhysics.ThreeFrequencyLiftedJacobianFactorization

open ArchonPhysics
open ArchonPhysics.ModalPhaseMismatch
open ArchonPhysics.ThreeParameterSpectralAveragingDensity

noncomputable section

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace Real E]

def frequencyTripleDerivative (derivative : Fin 3 -> E →L[Real] Real) :
    E →L[Real] MassTriple :=
  ((derivative 0).prod (derivative 1)).prod (derivative 2)

def liftedFrequencyDerivative (sign : Fin 3 -> InteractionSign)
    (derivative : Fin 3 -> E →L[Real] Real) : E →L[Real] MassTriple :=
  ((derivative 1).prod (derivative 2)).prod
    (Finset.univ.sum fun r => (sign r).coefficient • derivative r)

theorem injective_liftedFrequencyDerivative_iff
    (sign : Fin 3 -> InteractionSign)
    (derivative : Fin 3 -> E →L[Real] Real) :
    Function.Injective (liftedFrequencyDerivative sign derivative) <->
      Function.Injective (frequencyTripleDerivative derivative) := by
  constructor
  · intro hlifted x y hxy
    apply hlifted
    have h0 := congrArg (fun z : MassTriple => z.1.1) hxy
    have h1 := congrArg (fun z : MassTriple => z.1.2) hxy
    have h2 := congrArg (fun z : MassTriple => z.2) hxy
    simp only [frequencyTripleDerivative, ContinuousLinearMap.prod_apply] at h0 h1 h2
    apply Prod.ext
    · exact Prod.ext h1 h2
    · simp only [liftedFrequencyDerivative, ContinuousLinearMap.prod_apply,
        sum_apply, smul_apply,
        smul_eq_mul]
      simp [Fin.sum_univ_succ, h0, h1, h2]
  · intro hfrequency x y hxy
    apply hfrequency
    have h1 := congrArg (fun z : MassTriple => z.1.1) hxy
    have h2 := congrArg (fun z : MassTriple => z.1.2) hxy
    have hmismatch := congrArg (fun z : MassTriple => z.2) hxy
    have h0 : derivative 0 x = derivative 0 y := by
      simp only [liftedFrequencyDerivative, ContinuousLinearMap.prod_apply] at h1 h2 hmismatch
      simp only [sum_apply, smul_apply,
        smul_eq_mul] at hmismatch
      norm_num [Fin.sum_univ_succ] at hmismatch
      rw [h1, h2] at hmismatch
      cases hsign : sign 0 <;> simp [hsign] at hmismatch <;> linarith
    apply Prod.ext
    · exact Prod.ext h0 h1
    · exact h2

theorem continuousLinearMap_det_ne_zero_iff_injective
    (f : MassTriple →L[Real] MassTriple) :
    f.det ≠ 0 ↔ Function.Injective f := by
  rw [ContinuousLinearMap.det]
  constructor
  · intro hdet
    have hker : f.toLinearMap.ker = ⊥ := by
      by_contra hne
      exact hdet (LinearMap.det_eq_zero_iff_ker_ne_bot.mpr hne)
    exact LinearMap.ker_eq_bot.mp hker
  · intro hinjective hzero
    have hker : f.toLinearMap.ker = ⊥ :=
      LinearMap.ker_eq_bot.mpr hinjective
    exact (LinearMap.det_eq_zero_iff_ker_ne_bot.mp hzero) hker

theorem liftedFrequencyDerivative_det_ne_zero_iff
    (sign : Fin 3 → InteractionSign)
    (derivative : Fin 3 → MassTriple →L[Real] Real) :
    (liftedFrequencyDerivative sign derivative).det ≠ 0 ↔
      (frequencyTripleDerivative derivative).det ≠ 0 := by
  rw [continuousLinearMap_det_ne_zero_iff_injective,
    continuousLinearMap_det_ne_zero_iff_injective]
  exact injective_liftedFrequencyDerivative_iff sign derivative

end

end ArchonPhysics.ThreeFrequencyLiftedJacobianFactorization
