import ArchonPhysics.ActualThreeMassHellmannFeynmanJacobian
import ArchonPhysics.ThreeFrequencyLiftedJacobianDeterminant

/-!
# Exact actual lifted-Jacobian determinant identity

At every interior simple-positive point, the genuine random-mass lifted
Jacobian is the fixed child-child-mismatch row transform of the exact
Hellmann--Feynman three-frequency Jacobian.  The row transform has determinant
`sign(0) = ±1`, so no quantitative determinant loss is introduced by lifting.
-/

namespace ArchonPhysics.ActualThreeMassLiftedJacobianDeterminantIdentity

open ArchonPhysics
open ArchonPhysics.ActualThreeMassHellmannFeynmanJacobian
open ArchonPhysics.ActualThreeMassLiftedSimpleEigenvalueDifferentiability
open ArchonPhysics.ActualThreeMassLiftedSpectralChart
open ArchonPhysics.ActualThreeMassProjectorWeightJacobian
open ArchonPhysics.MeasurableOrderedSpectrum
open ArchonPhysics.ModalPhaseMismatch
open ArchonPhysics.OrderedSingleModeProjector
open ArchonPhysics.OrderedSpectrumContinuity
open ArchonPhysics.ThreeFrequencyLiftedJacobianDeterminant
open ArchonPhysics.ThreeFrequencyLiftedJacobianFactorization
open ArchonPhysics.ThreeParameterProjectorWeightJacobian
open ArchonPhysics.ThreeParameterSpectralAveragingDensity
open Set

noncomputable section

/-- The true lifted determinant equals the exact scaled-projector frequency
determinant up to the parent interaction sign. -/
theorem actualThreeMassLiftedFrequencyJacobian_det_eq_frequencyProjector
    {N : Nat} [NeZero N] (fixed : Lattice.PositiveMassConfig N)
    {site₀ site₁ site₂ : Lattice.Site N}
    (h₁₀ : site₁ ≠ site₀) (h₂₀ : site₂ ≠ site₀)
    (h₂₁ : site₂ ≠ site₁)
    (sign : Fin 3 → InteractionSign)
    (modes : Fin 3 → Fin (Fintype.card (Lattice.Site N)))
    {triple : MassTriple}
    (htriple : triple ∈ interior iidMassTripleSupport)
    (hsimple : SimpleOrderedSpectrum
      (threeMassHarmonicHermitian fixed site₀ site₁ site₂ triple))
    (hpositive : ∀ r, 0 < orderedEigenvalue
      (threeMassHarmonicHermitian fixed site₀ site₁ site₂ triple)
        (modes r)) :
    (actualThreeMassLiftedFrequencyJacobian
      fixed site₀ site₁ site₂ sign modes triple).det =
      (sign 0).coefficient *
        (actualThreeMassFrequencyProjectorJacobianMatrix
          fixed site₀ site₁ site₂ modes triple).det := by
  obtain ⟨derivative, hderivative, hfrequencyMatrix⟩ :=
    exists_actualThreeMassFrequencyDerivatives_eq_projectorJacobian
      fixed h₁₀ h₂₀ h₂₁ modes htriple hsimple hpositive
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
  calc
    (actualThreeMassLiftedFrequencyJacobian
        fixed site₀ site₁ site₂ sign modes triple).det =
        (liftedFrequencyDerivative sign derivative).det := by
      rw [hactual]
    _ = (sign 0).coefficient *
        (frequencyTripleDerivative derivative).det :=
      liftedFrequencyDerivative_det_eq sign derivative
    _ = (sign 0).coefficient *
        (actualThreeMassFrequencyProjectorJacobianMatrix
          fixed site₀ site₁ site₂ modes triple).det := by
      rw [hfrequencyMatrix, det_massTripleLinearMapOfMatrix]

/-- Fully expanded actual determinant: positive-frequency row scales, the
dual-cycle projector minor, and raw-mass column scales. -/
theorem actualThreeMassLiftedFrequencyJacobian_det_eq_projectorScales
    {N : Nat} [NeZero N] (fixed : Lattice.PositiveMassConfig N)
    {site₀ site₁ site₂ : Lattice.Site N}
    (h₁₀ : site₁ ≠ site₀) (h₂₀ : site₂ ≠ site₀)
    (h₂₁ : site₂ ≠ site₁)
    (sign : Fin 3 → InteractionSign)
    (modes : Fin 3 → Fin (Fintype.card (Lattice.Site N)))
    {triple : MassTriple}
    (htriple : triple ∈ interior iidMassTripleSupport)
    (hsimple : SimpleOrderedSpectrum
      (threeMassHarmonicHermitian fixed site₀ site₁ site₂ triple))
    (hpositive : ∀ r, 0 < orderedEigenvalue
      (threeMassHarmonicHermitian fixed site₀ site₁ site₂ triple)
        (modes r)) :
    (actualThreeMassLiftedFrequencyJacobian
      fixed site₀ site₁ site₂ sign modes triple).det =
      (sign 0).coefficient *
        ((∏ r, actualThreeMassFrequencyRowScale
          fixed site₀ site₁ site₂ modes triple r) *
          (actualThreeMassProjectorWeightMatrix
            fixed site₀ site₁ site₂ modes triple).det *
            (∏ s, actualThreeMassRawMassColumnScale triple s)) := by
  rw [actualThreeMassLiftedFrequencyJacobian_det_eq_frequencyProjector
    fixed h₁₀ h₂₀ h₂₁ sign modes htriple hsimple hpositive]
  rw [actualThreeMassFrequencyProjectorJacobianMatrix_det]

/-- Lifting preserves the exact absolute determinant of the actual raw
three-frequency Jacobian. -/
theorem abs_actualThreeMassLiftedFrequencyJacobian_det_eq_frequencyProjector
    {N : Nat} [NeZero N] (fixed : Lattice.PositiveMassConfig N)
    {site₀ site₁ site₂ : Lattice.Site N}
    (h₁₀ : site₁ ≠ site₀) (h₂₀ : site₂ ≠ site₀)
    (h₂₁ : site₂ ≠ site₁)
    (sign : Fin 3 → InteractionSign)
    (modes : Fin 3 → Fin (Fintype.card (Lattice.Site N)))
    {triple : MassTriple}
    (htriple : triple ∈ interior iidMassTripleSupport)
    (hsimple : SimpleOrderedSpectrum
      (threeMassHarmonicHermitian fixed site₀ site₁ site₂ triple))
    (hpositive : ∀ r, 0 < orderedEigenvalue
      (threeMassHarmonicHermitian fixed site₀ site₁ site₂ triple)
        (modes r)) :
    |(actualThreeMassLiftedFrequencyJacobian
      fixed site₀ site₁ site₂ sign modes triple).det| =
      |(actualThreeMassFrequencyProjectorJacobianMatrix
        fixed site₀ site₁ site₂ modes triple).det| := by
  rw [actualThreeMassLiftedFrequencyJacobian_det_eq_frequencyProjector
    fixed h₁₀ h₂₀ h₂₁ sign modes htriple hsimple hpositive, abs_mul]
  cases sign 0 <;> simp

end

end ArchonPhysics.ActualThreeMassLiftedJacobianDeterminantIdentity
