import ArchonPhysics.ActualThreeMassLiftedSimpleEigenvalueDifferentiability
import ArchonPhysics.ThreeFrequencyLiftedJacobianFactorization

/-!
# Factorization of the actual lifted three-frequency Jacobian

At an interior simple-positive configuration, choose the strict derivative of
each of the three ordered frequencies.  The derivative of the actual
child-child-mismatch chart is their universal lifted row transform.  Hence its
determinant is nonzero exactly when the raw three-frequency derivative matrix
has nonzero determinant.
-/

namespace ArchonPhysics.ActualThreeMassLiftedJacobianFactorization

open ArchonPhysics
open ArchonPhysics.ActualThreeMassLiftedSimpleEigenvalueDifferentiability
open ArchonPhysics.ActualThreeMassLiftedSpectralChart
open ArchonPhysics.FixedEnergySpectrumAvoidance
open ArchonPhysics.MeasurableOrderedSpectrum
open ArchonPhysics.ModalPhaseMismatch
open ArchonPhysics.OrderedSingleModeProjector
open ArchonPhysics.OrderedSpectrumContinuity
open ArchonPhysics.ThreeFrequencyLiftedJacobianFactorization
open ArchonPhysics.ThreeParameterSpectralAveragingDensity
open Set

noncomputable section

/-- At every interior simple-positive point, the actual lifted Jacobian is
nondegenerate exactly when the derivative of the three raw frequencies is
nondegenerate.  The interaction signs therefore introduce no extra Jacobian
degeneracy. -/
theorem exists_frequencyDerivatives_actualThreeMassLifted_det_ne_zero_iff
    {N : Nat} [NeZero N] (fixed : Lattice.PositiveMassConfig N)
    {site₀ site₁ site₂ : Lattice.Site N}
    (h₁₀ : site₁ ≠ site₀) (h₂₀ : site₂ ≠ site₀)
    (h₂₁ : site₂ ≠ site₁)
    (sign : Fin 3 → InteractionSign)
    (modes : Fin 3 → Fin (Fintype.card (Lattice.Site N)))
    {triple : MassTriple} (htriple : triple ∈ interior iidMassTripleSupport)
    (hsimple : SimpleOrderedSpectrum
      (threeMassHarmonicHermitian fixed site₀ site₁ site₂ triple))
    (hpositive : ∀ r, 0 < orderedEigenvalue
      (threeMassHarmonicHermitian fixed site₀ site₁ site₂ triple)
        (modes r)) :
    ∃ derivative : Fin 3 → MassTriple →L[Real] Real,
      (∀ r, HasStrictFDerivAt
        (fun nearby => orderedModeFrequency
          (threeMassHarmonicHermitian fixed site₀ site₁ site₂ nearby)
          (modes r))
        (derivative r) triple) ∧
      ((actualThreeMassLiftedFrequencyJacobian
          fixed site₀ site₁ site₂ sign modes triple).det ≠ 0 ↔
        (frequencyTripleDerivative derivative).det ≠ 0) := by
  choose derivative hderivative using fun r =>
    exists_hasStrictFDerivAt_actualThreeMassOrderedModeFrequency
      fixed h₁₀ h₂₀ h₂₁ htriple hsimple (modes r) (hpositive r)
  refine ⟨derivative, hderivative, ?_⟩
  let mismatchDerivative : MassTriple →L[Real] Real :=
    ∑ r, (sign r).coefficient • derivative r
  have hmismatch : HasStrictFDerivAt
      (fun nearby => ∑ r, (sign r).coefficient *
        orderedModeFrequency
          (threeMassHarmonicHermitian fixed site₀ site₁ site₂ nearby)
          (modes r)) mismatchDerivative triple := by
    change HasStrictFDerivAt
      (∑ r, fun nearby : MassTriple => (sign r).coefficient *
        orderedModeFrequency
          (threeMassHarmonicHermitian fixed site₀ site₁ site₂ nearby)
          (modes r)) mismatchDerivative triple
    simpa only [mismatchDerivative] using
      HasStrictFDerivAt.sum (u := Finset.univ)
        (fun r _hr => (hderivative r).const_mul (sign r).coefficient)
  have hlifted : HasStrictFDerivAt
      (actualThreeMassLiftedFrequencyChart
        fixed site₀ site₁ site₂ sign modes)
      (liftedFrequencyDerivative sign derivative) triple := by
    convert ((hderivative 1).prodMk (hderivative 2)).prodMk hmismatch using 1 <;>
      rfl
  have hactual :
      actualThreeMassLiftedFrequencyJacobian
          fixed site₀ site₁ site₂ sign modes triple =
        liftedFrequencyDerivative sign derivative := by
    simpa [actualThreeMassLiftedFrequencyJacobian] using
      hlifted.hasFDerivAt.fderiv
  rw [hactual]
  exact liftedFrequencyDerivative_det_ne_zero_iff sign derivative

end

end ArchonPhysics.ActualThreeMassLiftedJacobianFactorization
