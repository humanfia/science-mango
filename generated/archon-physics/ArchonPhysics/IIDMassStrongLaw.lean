import ArchonPhysics.FrozenUniformMassMoments
import Mathlib.Probability.StrongLaw

/-!
# Strong laws for the frozen iid mass coordinates

Every measurable transform that is uniformly bounded on the frozen support
obeys a strong law along the verified iid mass sequence.  Specializing to the
identity and to the squared centered mass gives almost-sure convergence of
the empirical mean to `1` and of the empirical centered second moment to
`1/75`.

These statements concern only the input disorder.  They do not assert a
spectral, Lyapunov, collision-kernel, or thermalization limit.
-/

namespace ArchonPhysics.IIDMassStrongLaw

open ArchonPhysics
open ArchonPhysics.FrozenUniformMassMoments
open Filter Function MeasureTheory ProbabilityTheory Set Topology

noncomputable section

/-- Strong law for any measurable transform bounded on the frozen mass
support. -/
theorem transform_strongLaw
    {Omega : Type*} [MeasurableSpace Omega]
    (ensemble : IIDMassPhaseEnsemble Omega)
    (transform : Real → Real) (htransform : Measurable transform)
    (C : Real)
    (hbound : ∀ x ∈ RandomEnsemble.massSupport, ‖transform x‖ ≤ C) :
    ∀ᵐ omega ∂ensemble.probability,
      Tendsto
        (fun n : Nat ↦
          (∑ i ∈ Finset.range n, transform (ensemble.mass i omega)) / n)
        atTop
        (𝓝 (∫ omega, transform (ensemble.mass 0 omega)
          ∂ensemble.probability)) := by
  let _ : IsProbabilityMeasure ensemble.probability :=
    ⟨ensemble.probability_univ⟩
  let X : Nat → Omega → Real :=
    fun n omega ↦ transform (ensemble.mass n omega)
  have hint : Integrable (X 0) ensemble.probability :=
    Integrable.of_bound
      (htransform.comp (ensemble.mass_measurable 0)).aestronglyMeasurable C
      (ae_of_all _ fun omega ↦
        hbound (ensemble.mass 0 omega) (ensemble.mass_mem_support 0 omega))
  have hindep : Pairwise ((· ⟂ᵢ[ensemble.probability] ·) on X) := by
    intro i j hij
    exact (ensemble.mass_iIndep.indepFun hij).comp htransform htransform
  have hident : ∀ i, IdentDistrib (X i) (X 0)
      ensemble.probability ensemble.probability := by
    intro i
    exact ((ensemble.mass_hasLaw i).identDistrib
      (ensemble.mass_hasLaw 0)).comp htransform
  simpa [X] using strong_law_ae_real X hint hindep hident

/-- Almost surely, the empirical mass mean converges to the exact frozen mean
`1`. -/
theorem mass_empiricalMean_tendsto_ae
    {Omega : Type*} [MeasurableSpace Omega]
    (ensemble : IIDMassPhaseEnsemble Omega) :
    ∀ᵐ omega ∂ensemble.probability,
      Tendsto
        (fun n : Nat ↦
          (∑ i ∈ Finset.range n, ensemble.mass i omega) / (n : Real))
        atTop (𝓝 1) := by
  have hbound : ∀ x ∈ RandomEnsemble.massSupport,
      ‖(id x : Real)‖ ≤ RandomEnsemble.massUpper := by
    intro x hx
    change |x| ≤ RandomEnsemble.massUpper
    rw [abs_of_pos
      (RandomEnsemble.massLower_pos.trans_le hx.1)]
    exact hx.2
  have h := transform_strongLaw ensemble id measurable_id
    RandomEnsemble.massUpper hbound
  simpa [id, ensemble_mass_mean ensemble 0] using h

/-- Almost surely, the empirical squared fluctuation around the exact mean
converges to `1/75`. -/
theorem mass_empiricalCenteredSecondMoment_tendsto_ae
    {Omega : Type*} [MeasurableSpace Omega]
    (ensemble : IIDMassPhaseEnsemble Omega) :
    ∀ᵐ omega ∂ensemble.probability,
      Tendsto
        (fun n : Nat ↦
          (∑ i ∈ Finset.range n, (ensemble.mass i omega - 1) ^ 2) /
            (n : Real))
        atTop (𝓝 (1 / 75 : Real)) := by
  have hbound : ∀ x ∈ RandomEnsemble.massSupport,
      ‖(x - 1) ^ 2‖ ≤ (1 / 25 : Real) := by
    intro x hx
    have hlower : -(1 / 5 : Real) ≤ x - 1 := by
      have hx' : (4 / 5 : Real) ≤ x := by
        simpa [RandomEnsemble.massLower] using hx.1
      linarith
    have hupper : x - 1 ≤ (1 / 5 : Real) := by
      have hx' : x ≤ (6 / 5 : Real) := by
        simpa [RandomEnsemble.massUpper] using hx.2
      linarith
    have hmul : 0 ≤
        ((1 / 5 : Real) - (x - 1)) * ((1 / 5 : Real) + (x - 1)) :=
      mul_nonneg (sub_nonneg.mpr hupper) (by linarith)
    rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
    nlinarith
  have h := transform_strongLaw ensemble (fun x : Real ↦ (x - 1) ^ 2)
    (by fun_prop) (1 / 25 : Real) hbound
  rw [ensemble_mass_centeredSecondMoment ensemble 0] at h
  exact h

end

end ArchonPhysics.IIDMassStrongLaw
