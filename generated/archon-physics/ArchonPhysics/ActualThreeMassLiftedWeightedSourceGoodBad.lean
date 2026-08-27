import ArchonPhysics.ActualThreeMassLiftedWeightedGoodBad

/-!
# Collision-weighted sources in the actual lifted good/bad estimate

Finite collision tuples carry a mass-dependent nonnegative interaction
weight.  This module extends the actual three-mass coarea estimate from the
bare iid mass law to any source dominated by a scalar multiple of that law,
and in particular to an iid law with a bounded measurable density.
-/

namespace ArchonPhysics.ActualThreeMassLiftedWeightedSourceGoodBad

open ArchonPhysics
open ArchonPhysics.ActualThreeMassLiftedSpectralChart
open ArchonPhysics.ActualThreeMassLiftedWeightedGoodBad
open ArchonPhysics.ModalPhaseMismatch
open ArchonPhysics.QuantitativeJacobianPushforward
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

/-- Actual lifted good/bad estimate for a source dominated by the iid
mass-triple law. -/
theorem actualThreeMassLifted_weightedSource_broadenedChild_apply_le
    {N : Nat} [NeZero N] (fixed : Lattice.PositiveMassConfig N)
    (site₀ site₁ site₂ : Lattice.Site N)
    (sign : Fin 3 → InteractionSign)
    (modes : Fin 3 → Fin (Fintype.card (Lattice.Site N)))
    (source : Measure MassTriple) (sourceCeiling : ENNReal)
    (hsource : source ≤ sourceCeiling • iidMassTripleLaw)
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
          source).withDensity
            (liftedResonanceKernelDensity T)) target ≤
      (sourceCeiling * 27 * (ENNReal.ofReal detLower)⁻¹) *
          (volume : Measure (Real × Real)) target +
        (Measure.map
          (actualThreeMassLiftedFrequencyChart
            fixed site₀ site₁ site₂ sign modes)
          (source.restrict goodᶜ)).withDensity
            (liftedResonanceKernelDensity T) univ := by
  let chart := actualThreeMassLiftedFrequencyChart
    fixed site₀ site₁ site₂ sign modes
  have hchart : Measurable chart :=
    (continuous_actualThreeMassLiftedFrequencyChart
      fixed site₀ site₁ site₂ sign modes).measurable
  have hsourceVolume :
      source ≤ (sourceCeiling * 27) •
        (volume : Measure MassTriple) := by
    calc
      source ≤ sourceCeiling • iidMassTripleLaw := hsource
      _ ≤ sourceCeiling •
          ((27 : ENNReal) • (volume : Measure MassTriple)) :=
        smul_mono_right sourceCeiling
          iidMassTripleLaw_le_twentySeven_smul_volume
      _ = (sourceCeiling * 27) •
          (volume : Measure MassTriple) := by
        rw [mul_smul]
  have hsourceGood :
      source.restrict good ≤
        (sourceCeiling * 27) •
          (volume : Measure MassTriple).restrict good := by
    calc
      source.restrict good ≤
          ((sourceCeiling * 27) •
            (volume : Measure MassTriple)).restrict good :=
        Measure.restrict_mono_measure hsourceVolume good
      _ = (sourceCeiling * 27) •
          (volume : Measure MassTriple).restrict good := by
        rw [Measure.restrict_smul]
  have hgoodLifted :
      Measure.map chart (source.restrict good) ≤
        (sourceCeiling * 27 * (ENNReal.ofReal detLower)⁻¹) •
          (volume : Measure MassTriple) :=
    map_le_smul_volume_of_le_volume_restrict_of_det_lower
      (volume : Measure MassTriple) hgood chart hchart
      (fun point =>
        actualThreeMassLiftedFrequencyJacobian
          fixed site₀ site₁ site₂ sign modes point)
      hderivative hinjective hdetLower hdet
      (source.restrict good) (sourceCeiling * 27) hsourceGood
  have hmapSplit :
      Measure.map chart source =
        Measure.map chart (source.restrict good) +
          Measure.map chart (source.restrict goodᶜ) := by
    rw [← Measure.map_add _ _ hchart,
      source.restrict_add_restrict_compl hgood]
  rw [hmapSplit]
  exact map_fst_withDensity_good_add_bad_apply_le
    (Measure.map chart (source.restrict good))
    (Measure.map chart (source.restrict goodᶜ))
    hT (sourceCeiling * 27 * (ENNReal.ofReal detLower)⁻¹)
    hgoodLifted htarget

/-- Specialization to a bounded measurable collision weight on the selected
mass triple. -/
theorem actualThreeMassLifted_boundedDensity_broadenedChild_apply_le
    {N : Nat} [NeZero N] (fixed : Lattice.PositiveMassConfig N)
    (site₀ site₁ site₂ : Lattice.Site N)
    (sign : Fin 3 → InteractionSign)
    (modes : Fin 3 → Fin (Fintype.card (Lattice.Site N)))
    (weight : MassTriple → ENNReal) (weightCeiling : ENNReal)
    (hweight : ∀ᵐ point ∂iidMassTripleLaw,
      weight point ≤ weightCeiling)
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
          (iidMassTripleLaw.withDensity weight)).withDensity
            (liftedResonanceKernelDensity T)) target ≤
      (weightCeiling * 27 * (ENNReal.ofReal detLower)⁻¹) *
          (volume : Measure (Real × Real)) target +
        (Measure.map
          (actualThreeMassLiftedFrequencyChart
            fixed site₀ site₁ site₂ sign modes)
          ((iidMassTripleLaw.withDensity weight).restrict goodᶜ)).withDensity
            (liftedResonanceKernelDensity T) univ := by
  apply actualThreeMassLifted_weightedSource_broadenedChild_apply_le
    fixed site₀ site₁ site₂ sign modes
    (iidMassTripleLaw.withDensity weight) weightCeiling
  · calc
      iidMassTripleLaw.withDensity weight ≤
          iidMassTripleLaw.withDensity (fun _ => weightCeiling) :=
        withDensity_mono hweight
      _ = weightCeiling • iidMassTripleLaw :=
        withDensity_const weightCeiling
  · exact hgood
  · exact hderivative
  · exact hinjective
  · exact hdetLower
  · exact hdet
  · exact hT
  · exact htarget

end

end ArchonPhysics.ActualThreeMassLiftedWeightedSourceGoodBad
