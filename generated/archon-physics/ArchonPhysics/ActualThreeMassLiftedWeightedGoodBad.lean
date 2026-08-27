import ArchonPhysics.ActualThreeMassLiftedRegularSpectralPatch
import ArchonPhysics.CanonicalOnShellChildPairUniformIntegrability
import ArchonPhysics.QuantitativeJacobianPushforward

/-!
# Kernel-weighted good/bad control for the actual lifted chart

A plain exceptional-set mass is not uniform in the broadening time because
the normalized sinc-squared kernel has height of order T.  This module keeps
the exceptional contribution with its exact kernel weight.  On a regular
three-mass patch, the actual lifted chart contributes the quantitative
Jacobian density bound; all remaining work is isolated in one genuinely
weighted bad-region term.
-/

namespace ArchonPhysics.ActualThreeMassLiftedWeightedGoodBad

open ArchonPhysics
open ArchonPhysics.ActualThreeMassLiftedSpectralChart
open ArchonPhysics.CanonicalOnShellChildPairUniformIntegrability
open ArchonPhysics.ModalPhaseMismatch
open ArchonPhysics.NormalizedResonancePeakKernel
open ArchonPhysics.QuantitativeJacobianPushforward
open ArchonPhysics.UniformCollisionDensityTransfer
open ArchonPhysics.RandomEnsemble
open ArchonPhysics.ThreeParameterSpectralAveragingDensity
open MeasureTheory Set
open scoped ENNReal

noncomputable section

local instance pairVolumeIsAddHaarMeasure :
    Measure.IsAddHaarMeasure (volume : Measure (Real × Real)) :=
  Measure.prod.instIsAddHaarMeasure _ _

local instance tripleVolumeIsAddHaarMeasure :
    Measure.IsAddHaarMeasure (volume : Measure MassTriple) :=
  Measure.prod.instIsAddHaarMeasure _ _

/-- The finite-time resonance density, viewed on lifted
(child-pair, mismatch) coordinates. -/
def liftedResonanceKernelDensity (T : Real) (value : MassTriple) : ENNReal :=
  ENNReal.ofReal (normalizedFiniteTimeResonanceKernel value.2 T)

theorem measurable_liftedResonanceKernelDensity
    {T : Real} (hT : 0 < T) :
    Measurable (liftedResonanceKernelDensity T) := by
  exact ENNReal.measurable_ofReal.comp
    ((continuous_normalizedFiniteTimeResonanceKernel hT).measurable.comp
      measurable_snd)

/-- Integrating the lifted kernel and forgetting mismatch preserves planar
Lebesgue measure exactly. -/
theorem map_fst_volume_withDensity_liftedResonanceKernelDensity
    {T : Real} (hT : 0 < T) :
    Measure.map Prod.fst
        ((volume : Measure MassTriple).withDensity
          (liftedResonanceKernelDensity T)) =
      (volume : Measure (Real × Real)) := by
  conv_lhs =>
    congr
    · skip
    · rw [Measure.volume_eq_prod]
  have hkernelMeasurable : Measurable (fun mismatch : Real =>
      ENNReal.ofReal (normalizedFiniteTimeResonanceKernel mismatch T)) :=
    ENNReal.measurable_ofReal.comp
      (continuous_normalizedFiniteTimeResonanceKernel hT).measurable
  have hprod :
      (((volume : Measure (Real × Real)).prod
        (volume : Measure Real)).withDensity
          (liftedResonanceKernelDensity T)) =
        (volume : Measure (Real × Real)).prod
          ((volume : Measure Real).withDensity (fun mismatch =>
            ENNReal.ofReal
              (normalizedFiniteTimeResonanceKernel mismatch T))) := by
    change (((volume : Measure (Real × Real)).prod
      (volume : Measure Real)).withDensity (fun value =>
        ENNReal.ofReal
          (normalizedFiniteTimeResonanceKernel value.2 T))) = _
    exact (prod_withDensity_right hkernelMeasurable).symm
  rw [hprod]
  change Measure.map Prod.fst
      ((volume : Measure (Real × Real)).prod
        (normalizedFiniteTimeResonanceKernelFiniteMeasure T hT :
          Measure Real)) =
    (volume : Measure (Real × Real))
  rw [Measure.map_fst_prod,
    normalizedFiniteTimeResonanceKernelFiniteMeasure_univ, one_smul]

/-- A regular lifted density bound plus an arbitrary bad lifted measure gives
an exact kernel-weighted good/bad bound after forgetting mismatch. -/
theorem map_fst_withDensity_good_add_bad_le
    (goodLifted badLifted : Measure MassTriple)
    {T : Real} (hT : 0 < T) (C : ENNReal)
    (hgoodLifted :
      goodLifted ≤ C • (volume : Measure MassTriple)) :
    Measure.map Prod.fst
        ((goodLifted + badLifted).withDensity
          (liftedResonanceKernelDensity T)) ≤
      C • (volume : Measure (Real × Real)) +
        Measure.map Prod.fst
          (badLifted.withDensity (liftedResonanceKernelDensity T)) := by
  rw [withDensity_add_measure,
    Measure.map_add
      (goodLifted.withDensity (liftedResonanceKernelDensity T))
      (badLifted.withDensity (liftedResonanceKernelDensity T))
      measurable_fst]
  apply add_le_add_left
  calc
    Measure.map Prod.fst
        (goodLifted.withDensity (liftedResonanceKernelDensity T)) ≤
      Measure.map Prod.fst
        ((C • (volume : Measure MassTriple)).withDensity
          (liftedResonanceKernelDensity T)) :=
      Measure.map_mono
        (withDensity_mono_measure hgoodLifted
          (liftedResonanceKernelDensity T)) measurable_fst
    _ = C • Measure.map Prod.fst
        ((volume : Measure MassTriple).withDensity
          (liftedResonanceKernelDensity T)) := by
      rw [withDensity_smul_measure, Measure.map_smul]
    _ = C • (volume : Measure (Real × Real)) := by
      rw [map_fst_volume_withDensity_liftedResonanceKernelDensity hT]

/-- Pointwise form: the exceptional contribution is its exact sinc-squared
weighted mass, not its unweighted source mass. -/
theorem map_fst_withDensity_good_add_bad_apply_le
    (goodLifted badLifted : Measure MassTriple)
    {T : Real} (hT : 0 < T) (C : ENNReal)
    (hgoodLifted :
      goodLifted ≤ C • (volume : Measure MassTriple))
    {target : Set (Real × Real)} (htarget : MeasurableSet target) :
    Measure.map Prod.fst
        ((goodLifted + badLifted).withDensity
          (liftedResonanceKernelDensity T)) target ≤
      C * (volume : Measure (Real × Real)) target +
        badLifted.withDensity (liftedResonanceKernelDensity T) univ := by
  have hbound :=
    map_fst_withDensity_good_add_bad_le
      goodLifted badLifted hT C hgoodLifted
  have hbad :
      Measure.map Prod.fst
          (badLifted.withDensity (liftedResonanceKernelDensity T)) target ≤
        badLifted.withDensity (liftedResonanceKernelDensity T) univ := by
    rw [Measure.map_apply measurable_fst htarget]
    exact measure_mono (subset_univ _)
  calc
    Measure.map Prod.fst
        ((goodLifted + badLifted).withDensity
          (liftedResonanceKernelDensity T)) target ≤
      (C • (volume : Measure (Real × Real)) +
        Measure.map Prod.fst
          (badLifted.withDensity
            (liftedResonanceKernelDensity T))) target :=
      hbound target
    _ = C * (volume : Measure (Real × Real)) target +
        Measure.map Prod.fst
          (badLifted.withDensity
            (liftedResonanceKernelDensity T)) target := by
      simp only [Measure.add_apply, Measure.smul_apply, smul_eq_mul]
    _ ≤ C * (volume : Measure (Real × Real)) target +
        badLifted.withDensity (liftedResonanceKernelDensity T) univ :=
      add_le_add_right hbad _

/-- Concrete actual-chart estimate on one good determinant patch.

The first term is the quantitative three-mass spectral-averaging density.
The second is precisely the kernel-weighted complement that must be bounded
uniformly in T to close the canonical weak-limit argument. -/
theorem actualThreeMassLifted_broadenedChild_apply_le_density_add_weightedBad
    {N : Nat} [NeZero N] (fixed : Lattice.PositiveMassConfig N)
    (site₀ site₁ site₂ : Lattice.Site N)
    (sign : Fin 3 → InteractionSign)
    (modes : Fin 3 → Fin (Fintype.card (Lattice.Site N)))
    {good : Set MassTriple} (hgood : MeasurableSet good)
    (hderivative : ∀ point ∈ good,
      HasFDerivWithinAt
        (actualThreeMassLiftedFrequencyChart
          fixed site₀ site₁ site₂ sign modes)
        (actualThreeMassLiftedFrequencyJacobian
          fixed site₀ site₁ site₂ sign modes point) good point)
    (hinjective : InjOn
      (actualThreeMassLiftedFrequencyChart
        fixed site₀ site₁ site₂ sign modes) good)
    {detLower : Real} (hdetLower : 0 < detLower)
    (hdet : ∀ point ∈ good,
      detLower ≤
        |(actualThreeMassLiftedFrequencyJacobian
          fixed site₀ site₁ site₂ sign modes point).det|)
    {T : Real} (hT : 0 < T)
    {target : Set (Real × Real)} (htarget : MeasurableSet target) :
    Measure.map Prod.fst
        ((Measure.map
          (actualThreeMassLiftedFrequencyChart
            fixed site₀ site₁ site₂ sign modes)
          iidMassTripleLaw).withDensity
            (liftedResonanceKernelDensity T)) target ≤
      ((27 : ENNReal) * (ENNReal.ofReal detLower)⁻¹) *
          (volume : Measure (Real × Real)) target +
        (Measure.map
          (actualThreeMassLiftedFrequencyChart
            fixed site₀ site₁ site₂ sign modes)
          (iidMassTripleLaw.restrict goodᶜ)).withDensity
            (liftedResonanceKernelDensity T) univ := by
  let chart := actualThreeMassLiftedFrequencyChart
    fixed site₀ site₁ site₂ sign modes
  have hchart : Measurable chart :=
    (continuous_actualThreeMassLiftedFrequencyChart
      fixed site₀ site₁ site₂ sign modes).measurable
  have hsourceGood :
      iidMassTripleLaw.restrict good ≤
        (27 : ENNReal) •
          (volume : Measure MassTriple).restrict good := by
    calc
      iidMassTripleLaw.restrict good ≤
          ((27 : ENNReal) •
            (volume : Measure MassTriple)).restrict good :=
        Measure.restrict_mono_measure
          iidMassTripleLaw_le_twentySeven_smul_volume good
      _ = (27 : ENNReal) •
          (volume : Measure MassTriple).restrict good := by
        rw [Measure.restrict_smul]
  have hgoodLifted :
      Measure.map chart (iidMassTripleLaw.restrict good) ≤
        ((27 : ENNReal) * (ENNReal.ofReal detLower)⁻¹) •
          (volume : Measure MassTriple) :=
    map_le_smul_volume_of_le_volume_restrict_of_det_lower
      (volume : Measure MassTriple) hgood chart hchart
      (fun point =>
        actualThreeMassLiftedFrequencyJacobian
          fixed site₀ site₁ site₂ sign modes point)
      hderivative hinjective hdetLower hdet
      (iidMassTripleLaw.restrict good) 27 hsourceGood
  have hmapSplit :
      Measure.map chart iidMassTripleLaw =
        Measure.map chart (iidMassTripleLaw.restrict good) +
          Measure.map chart (iidMassTripleLaw.restrict goodᶜ) := by
    rw [← Measure.map_add _ _ hchart,
      iidMassTripleLaw.restrict_add_restrict_compl hgood]
  rw [hmapSplit]
  exact map_fst_withDensity_good_add_bad_apply_le
    (Measure.map chart (iidMassTripleLaw.restrict good))
    (Measure.map chart (iidMassTripleLaw.restrict goodᶜ))
    hT ((27 : ENNReal) * (ENNReal.ofReal detLower)⁻¹)
    hgoodLifted htarget

end

end ArchonPhysics.ActualThreeMassLiftedWeightedGoodBad
