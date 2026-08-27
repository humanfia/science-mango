import ArchonPhysics.ActualThreeMassLiftedWeightedSourceGoodBad
import ArchonPhysics.CanonicalOnShellChildPairUniformIntegrabilityClosure
import ArchonPhysics.CompactResonanceJacobianSeparation
import ArchonPhysics.NormalizedResonanceBadRegionDecay

/-!
# Combining lifted Jacobian control with an off-resonance bad region

The normalized sinc-squared kernel has height of order `T`, so ordinary
smallness of the bad source is not uniform in the broadening time.  This
module records the useful alternative: a quantitative Jacobian density bound
on the good lifted region, together with a fixed positive mismatch gap on the
bad lifted region.  The latter contribution is then `O(T⁻¹)`.

The actual-chart specialization keeps the exact collision-weighted source.
It neither assumes that a paper theorem is an axiom nor identifies the still
model-specific algebraic statement excluding simultaneous resonance and
Jacobian degeneracy.
-/

namespace ArchonPhysics.ResonanceSeparatedJacobianGoodBad

open ArchonPhysics
open ArchonPhysics.ActualThreeMassLiftedSpectralChart
open ArchonPhysics.ActualThreeMassLiftedWeightedGoodBad
open ArchonPhysics.ActualThreeMassLiftedWeightedSourceGoodBad
open ArchonPhysics.CanonicalOnShellChildPairUniformIntegrabilityClosure
open ArchonPhysics.LocalCollisionDensityTransfer
open ArchonPhysics.ModalPhaseMismatch
open ArchonPhysics.NormalizedResonanceBadRegionDecay
open ArchonPhysics.RandomEnsemble
open ArchonPhysics.ThreeParameterSpectralAveragingDensity
open ArchonPhysics.TwoParameterSpectralAveragingAtlas
open Filter MeasureTheory Set
open scoped ENNReal

noncomputable section

/-- A lifted good-density estimate and an almost-everywhere mismatch gap on
the bad lifted law combine into an explicit planar estimate.  The regular
constant is independent of `T`; the exceptional coefficient is exactly the
off-gap sinc-square tail. -/
theorem map_fst_withDensity_good_add_bad_apply_le_offGap
    (goodLifted badLifted : Measure MassTriple)
    {T : Real} (hT : 0 < T) (C : ENNReal)
    (hgoodLifted :
      goodLifted <= C • (volume : Measure MassTriple))
    {eta : Real} (heta : 0 < eta)
    (hgap : ∀ᵐ value ∂badLifted, eta <= |value.2|)
    {target : Set (Real × Real)} (htarget : MeasurableSet target) :
    Measure.map Prod.fst
        ((goodLifted + badLifted).withDensity
          (liftedResonanceKernelDensity T)) target <=
      C * (volume : Measure (Real × Real)) target +
        ENNReal.ofReal (offGapCoefficient eta T) * badLifted univ := by
  calc
    Measure.map Prod.fst
        ((goodLifted + badLifted).withDensity
          (liftedResonanceKernelDensity T)) target <=
      C * (volume : Measure (Real × Real)) target +
        badLifted.withDensity (liftedResonanceKernelDensity T) univ :=
      map_fst_withDensity_good_add_bad_apply_le
        goodLifted badLifted hT C hgoodLifted htarget
    _ <= C * (volume : Measure (Real × Real)) target +
        ENNReal.ofReal (offGapCoefficient eta T) * badLifted univ :=
      add_le_add_right
        (liftedResonanceKernelDensity_weightedBad_le_offGap
          badLifted heta hT hgap) _

/-- Uniform-budget form of the combined estimate.  In applications `B` is
the total collision-weighted source ceiling.  This formulation is stable
under the lattice-volume limit because neither `C` nor `B` contains a mode
tuple cardinality. -/
theorem map_fst_withDensity_good_add_bad_apply_le_offGap_of_badMass_le
    (goodLifted badLifted : Measure MassTriple)
    {T : Real} (hT : 0 < T) (C : ENNReal)
    (hgoodLifted :
      goodLifted <= C • (volume : Measure MassTriple))
    {eta : Real} (heta : 0 < eta)
    (hgap : ∀ᵐ value ∂badLifted, eta <= |value.2|)
    (B : ENNReal) (hbadMass : badLifted univ <= B)
    {target : Set (Real × Real)} (htarget : MeasurableSet target) :
    Measure.map Prod.fst
        ((goodLifted + badLifted).withDensity
          (liftedResonanceKernelDensity T)) target <=
      C * (volume : Measure (Real × Real)) target +
        ENNReal.ofReal (offGapCoefficient eta T) * B := by
  calc
    Measure.map Prod.fst
        ((goodLifted + badLifted).withDensity
          (liftedResonanceKernelDensity T)) target <=
      C * (volume : Measure (Real × Real)) target +
        ENNReal.ofReal (offGapCoefficient eta T) * badLifted univ :=
      map_fst_withDensity_good_add_bad_apply_le_offGap
        goodLifted badLifted hT C hgoodLifted heta hgap htarget
    _ <= C * (volume : Measure (Real × Real)) target +
        ENNReal.ofReal (offGapCoefficient eta T) * B := by
      gcongr

/-- Pointwise determinant/mismatch separation on a source region transports
to the exact lifted bad pushforward.  This is the measure-theoretic bridge
needed after a source-side good/bad determinant decomposition. -/
theorem ae_map_mismatch_gap_of_jacobian_separation
    (chart : MassTriple -> MassTriple) (hchart : Measurable chart)
    (badSource : Measure MassTriple) (jacobian : MassTriple -> Real)
    (compactSet : Set MassTriple) {jacobianThreshold eta : Real}
    (hseparation : ∀ point ∈ compactSet,
      |jacobian point| < jacobianThreshold ->
        eta <= |(chart point).2|)
    (hcompact : ∀ᵐ point ∂badSource, point ∈ compactSet)
    (hsmall : ∀ᵐ point ∂badSource,
      |jacobian point| < jacobianThreshold) :
    ∀ᵐ value ∂Measure.map chart badSource,
      eta <= |value.2| := by
  apply (ae_map_iff
    (p := fun value : MassTriple => eta <= |value.2|)
    hchart.aemeasurable
    (measurableSet_le measurable_const measurable_snd.abs)).2
  filter_upwards [hcompact, hsmall] with point hpoint hpointSmall
  exact hseparation point hpoint hpointSmall

/-- Compact exclusion of a simultaneous Jacobian zero and resonance zero
produces fixed positive thresholds.  Any bad source concentrated on the
compact set and below the resulting Jacobian threshold then has an
off-resonance lifted pushforward.

The final implication is intentional: the spectral atlas must still prove
that its complementary determinant region is below the selected threshold.
-/
theorem exists_positive_thresholds_ae_map_gap_of_noCommonZero
    (chart : MassTriple -> MassTriple) (hchart : Continuous chart)
    (badSource : Measure MassTriple) (jacobian : MassTriple -> Real)
    (compactSet : Set MassTriple) (hcompactSet : IsCompact compactSet)
    (hjacobian : ContinuousOn jacobian compactSet)
    (hnoCommonZero : ∀ point ∈ compactSet,
      jacobian point ≠ 0 ∨ (chart point).2 ≠ 0)
    (hbadCompact : ∀ᵐ point ∂badSource, point ∈ compactSet) :
    ∃ jacobianThreshold eta : Real,
      0 < jacobianThreshold ∧ 0 < eta ∧
      ((∀ᵐ point ∂badSource,
          |jacobian point| < jacobianThreshold) ->
        ∀ᵐ value ∂Measure.map chart badSource,
          eta <= |value.2|) := by
  obtain ⟨jacobianThreshold, eta,
      hjacobianThreshold, heta, hseparation⟩ :=
    ArchonPhysics.CompactResonanceJacobianSeparation.exists_positive_jacobianThreshold_resonanceGap
        compactSet hcompactSet jacobian (fun point => (chart point).2)
        hjacobian ((continuous_snd.comp hchart).continuousOn)
        hnoCommonZero
  refine ⟨jacobianThreshold, eta,
    hjacobianThreshold, heta, ?_⟩
  intro hsmall
  exact ae_map_mismatch_gap_of_jacobian_separation
    chart hchart.measurable badSource jacobian compactSet
    hseparation hbadCompact hsmall

/-- A source dominated by `sourceCeiling` times the iid mass-triple law has
at most `sourceCeiling` total mass after restriction and measurable
pushforward. -/
theorem map_restrict_compl_univ_le_sourceCeiling
    (chart : MassTriple -> MassTriple) (hchart : Measurable chart)
    (source : Measure MassTriple) (sourceCeiling : ENNReal)
    (hsource : source <= sourceCeiling • iidMassTripleLaw)
    (good : Set MassTriple) :
    Measure.map chart (source.restrict goodᶜ) univ <= sourceCeiling := by
  rw [Measure.map_apply hchart MeasurableSet.univ]
  calc
    source.restrict goodᶜ (chart ⁻¹' univ) = source goodᶜ := by
      simp only [preimage_univ]
      rw [Measure.restrict_apply MeasurableSet.univ]
      simp
    _ <= source univ := measure_mono (subset_univ _)
    _ <= (sourceCeiling • iidMassTripleLaw) univ := hsource univ
    _ = sourceCeiling := by
      simp [iidMassTripleLaw, iidMassPairLaw]

/-- The actual three-mass lifted chart on one injective good patch.  A source
ceiling supplies the coarea density, while an a.e. mismatch gap on the exact
pushforward of the complementary source turns the weighted remainder into an
explicit `O(T⁻¹)` term. -/
theorem actualThreeMassLifted_weightedSource_broadenedChild_apply_le_offGap
    {N : Nat} [NeZero N] (fixed : Lattice.PositiveMassConfig N)
    (site₀ site₁ site₂ : Lattice.Site N)
    (sign : Fin 3 → InteractionSign)
    (modes : Fin 3 → Fin (Fintype.card (Lattice.Site N)))
    (source : Measure MassTriple) (sourceCeiling : ENNReal)
    (hsource : source <= sourceCeiling • iidMassTripleLaw)
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
      detLower <=
        |(actualThreeMassLiftedFrequencyJacobian
          fixed site₀ site₁ site₂ sign modes point).det|)
    {eta : Real} (heta : 0 < eta)
    (hgap : ∀ᵐ value ∂Measure.map
      (actualThreeMassLiftedFrequencyChart
        fixed site₀ site₁ site₂ sign modes)
      (source.restrict goodᶜ), eta <= |value.2|)
    {T : Real} (hT : 0 < T)
    {target : Set (Real × Real)} (htarget : MeasurableSet target) :
    Measure.map Prod.fst
        ((Measure.map
          (actualThreeMassLiftedFrequencyChart
            fixed site₀ site₁ site₂ sign modes)
          source).withDensity
            (liftedResonanceKernelDensity T)) target <=
      (sourceCeiling * 27 * (ENNReal.ofReal detLower)⁻¹) *
          (volume : Measure (Real × Real)) target +
        ENNReal.ofReal (offGapCoefficient eta T) *
          Measure.map
            (actualThreeMassLiftedFrequencyChart
              fixed site₀ site₁ site₂ sign modes)
            (source.restrict goodᶜ) univ := by
  let chart := actualThreeMassLiftedFrequencyChart
    fixed site₀ site₁ site₂ sign modes
  have hchart : Measurable chart :=
    (continuous_actualThreeMassLiftedFrequencyChart
      fixed site₀ site₁ site₂ sign modes).measurable
  have hsplit :
      Measure.map chart source =
        Measure.map chart (source.restrict good) +
          Measure.map chart (source.restrict goodᶜ) := by
    rw [← Measure.map_add _ _ hchart,
      source.restrict_add_restrict_compl hgood]
  rw [hsplit]
  have hbase :=
    actualThreeMassLifted_weightedSource_broadenedChild_apply_le
      fixed site₀ site₁ site₂ sign modes source sourceCeiling
      hsource hgood hderivative hinjective hdetLower hdet hT htarget
  rw [hsplit] at hbase
  calc
    Measure.map Prod.fst
        ((Measure.map chart (source.restrict good) +
          Measure.map chart (source.restrict goodᶜ)).withDensity
            (liftedResonanceKernelDensity T)) target <=
      (sourceCeiling * 27 * (ENNReal.ofReal detLower)⁻¹) *
          (volume : Measure (Real × Real)) target +
        (Measure.map chart
          (source.restrict goodᶜ)).withDensity
            (liftedResonanceKernelDensity T) univ := hbase
    _ <= (sourceCeiling * 27 * (ENNReal.ofReal detLower)⁻¹) *
          (volume : Measure (Real × Real)) target +
        ENNReal.ofReal (offGapCoefficient eta T) *
          Measure.map chart (source.restrict goodᶜ) univ :=
      add_le_add_right
        (liftedResonanceKernelDensity_weightedBad_le_offGap
          (Measure.map chart (source.restrict goodᶜ)) heta hT hgap) _


/-- Weak-limit closure for a uniformly dominated good part plus a bad part
whose total mass vanishes.  This is the limit-level companion to the
Jacobian-good/off-resonance-bad estimate above. -/
theorem childPlane_le_of_tendsto_add_of_badMass_tendsto_zero
    (source good bad : Nat → FiniteMeasure (Real × Real))
    (target : FiniteMeasure (Real × Real))
    (reference : Measure (Real × Real)) [reference.OuterRegular]
    (hweak : Tendsto source Filter.atTop (nhds target))
    (hsplit : ∀ n, (source n : Measure (Real × Real)) =
      (good n : Measure (Real × Real)) +
        (bad n : Measure (Real × Real)))
    (hbadMass : Tendsto
      (fun n ↦ (bad n : Measure (Real × Real)).real univ)
      Filter.atTop (nhds 0))
    (hgood : ∀ n, (good n : Measure (Real × Real)) ≤ reference) :
    (target : Measure (Real × Real)) ≤ reference := by
  have hgoodWeak : Tendsto good Filter.atTop (nhds target) := by
    apply (FiniteMeasure.tendsto_iff_forall_integral_tendsto).2
    intro test
    have hsourceIntegral :=
      (FiniteMeasure.tendsto_iff_forall_integral_tendsto).1 hweak test
    have hbadIntegral : Tendsto
        (fun n ↦ ∫ x, test x ∂(bad n : Measure (Real × Real)))
        Filter.atTop (nhds 0) := by
      rw [tendsto_zero_iff_norm_tendsto_zero]
      have hupper : Tendsto
          (fun n ↦ ‖test‖ *
            (bad n : Measure (Real × Real)).real univ)
          Filter.atTop (nhds 0) := by
        simpa using tendsto_const_nhds.mul hbadMass
      exact tendsto_of_tendsto_of_tendsto_of_le_of_le
        (show Tendsto (fun _ : Nat ↦ (0 : Real))
            Filter.atTop (nhds 0) from tendsto_const_nhds)
        hupper
        (fun _ ↦ norm_nonneg _)
        (fun n ↦ norm_integral_le_of_norm_le_const
          (μ := (bad n : Measure (Real × Real)))
          (C := ‖test‖)
          (ae_of_all _ fun x ↦ test.norm_coe_le_norm x))
    have hsub := hsourceIntegral.sub hbadIntegral
    convert hsub using 1
    · funext n
      rw [hsplit n, integral_add_measure
        (BoundedContinuousFunction.integrable (good n) test)
        (BoundedContinuousFunction.integrable (bad n) test)]
      ring
    · simp
  exact childPlane_le_of_tendsto_of_forall_le
    good target reference hgoodWeak hgood

end

end ArchonPhysics.ResonanceSeparatedJacobianGoodBad
