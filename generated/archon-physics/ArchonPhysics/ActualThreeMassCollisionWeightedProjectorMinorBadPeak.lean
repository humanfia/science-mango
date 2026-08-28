import ArchonPhysics.ActualThreeMassWeightedProjectorMinorDistribution
import ArchonPhysics.ResonanceKernelLipschitz

open scoped Matrix BigOperators ENNReal

namespace ArchonPhysics.ActualThreeMassCollisionWeightedProjectorMinorBadPeak

open ArchonPhysics
open ArchonPhysics.ActualThreeMassAllDistinctAnnealedBroadeningTrace
open ArchonPhysics.ActualThreeMassLiftedPerSiteBudget
open ArchonPhysics.ActualThreeMassLiftedSpectralChart
open ArchonPhysics.ActualThreeMassLiftedWeightedGoodBad
open ArchonPhysics.ActualThreeMassWeightedProjectorMinorDistribution
open ArchonPhysics.ModalPhaseMismatch
open ArchonPhysics.NormalizedResonancePeakKernel
open ArchonPhysics.RandomMassPositiveCollisionData
open ArchonPhysics.ResonanceKernelLipschitz
open ArchonPhysics.ThreeParameterSpectralAveragingDensity
open MeasureTheory Set

noncomputable section

/-- Actual iid, collision-weighted, per-site distribution of the absolute
projector minor.  Unlike the residual distribution, this uses the original
physical tuple weight and therefore measures the source mass of the sinc
bad region exactly. -/
def actualThreeMassAllDistinctCollisionWeightedProjectorMinorDistribution
    {N : Nat} [NeZero N] (fixed : Lattice.PositiveMassConfig N)
    (site₀ site₁ site₂ : Lattice.Site N) : Measure Real :=
  (N : ENNReal)⁻¹ •
    ∑ modes : OrderedModeTriple N,
      Measure.map
        (actualThreeMassProjectorMinorMagnitude
          fixed site₀ site₁ site₂ modes)
        (iidMassTripleLaw.withDensity
          (actualThreeMassAllDistinctTupleWeight
            fixed site₀ site₁ site₂ modes))

/-- Collision-weighted mass of the actual projector-minor level
`|det Q| < delta`. -/
def actualThreeMassAllDistinctCollisionWeightedProjectorMinorBadLevel
    {N : Nat} [NeZero N] (fixed : Lattice.PositiveMassConfig N)
    (site₀ site₁ site₂ : Lattice.Site N) (delta : Real) : ENNReal :=
  actualThreeMassAllDistinctCollisionWeightedProjectorMinorDistribution
    fixed site₀ site₁ site₂ (Iio delta)

theorem actualThreeMassAllDistinctCollisionWeightedProjectorMinorBadLevel_eq_source
    {N : Nat} [NeZero N] (fixed : Lattice.PositiveMassConfig N)
    (site₀ site₁ site₂ : Lattice.Site N) (delta : Real) :
    actualThreeMassAllDistinctCollisionWeightedProjectorMinorBadLevel
        fixed site₀ site₁ site₂ delta =
      (N : ENNReal)⁻¹ *
        ∑ modes : OrderedModeTriple N,
          (iidMassTripleLaw.withDensity
            (actualThreeMassAllDistinctTupleWeight
              fixed site₀ site₁ site₂ modes))
            {triple |
              actualThreeMassProjectorMinorMagnitude
                  fixed site₀ site₁ site₂ modes triple < delta} := by
  classical
  unfold actualThreeMassAllDistinctCollisionWeightedProjectorMinorBadLevel
    actualThreeMassAllDistinctCollisionWeightedProjectorMinorDistribution
  rw [Measure.smul_apply, Measure.coe_finsetSum]
  simp only [Finset.sum_apply, smul_eq_mul]
  congr 1
  apply Finset.sum_congr rfl
  intro modes _hmodes
  rw [Measure.map_apply
    (measurable_actualThreeMassProjectorMinorMagnitude
      fixed site₀ site₁ site₂ modes) measurableSet_Iio]
  rfl

/-- Raw determinant-threshold source set.  It intentionally contains no
claim of simplicity or local injectivity; those are separate coarea inputs. -/
def actualThreeMassProjectorRawGoodDetSet
    {N : Nat} [NeZero N] (fixed : Lattice.PositiveMassConfig N)
    (site₀ site₁ site₂ : Lattice.Site N)
    (modes : OrderedModeTriple N) (delta : Real) : Set MassTriple :=
  {triple |
    delta ≤ actualThreeMassProjectorMinorMagnitude
      fixed site₀ site₁ site₂ modes triple}

theorem measurableSet_actualThreeMassProjectorRawGoodDetSet
    {N : Nat} [NeZero N] (fixed : Lattice.PositiveMassConfig N)
    (site₀ site₁ site₂ : Lattice.Site N)
    (modes : OrderedModeTriple N) (delta : Real) :
    MeasurableSet (actualThreeMassProjectorRawGoodDetSet
      fixed site₀ site₁ site₂ modes delta) :=
  measurableSet_Ici.preimage
    (measurable_actualThreeMassProjectorMinorMagnitude
      fixed site₀ site₁ site₂ modes)

/-- Exact normalized sinc peak height used on a determinant-bad source. -/
def actualNormalizedResonancePeakHeight (T : Real) : ENNReal :=
  ENNReal.ofReal (T / (2 * Real.pi))

theorem liftedResonanceKernelDensity_le_actualNormalizedResonancePeakHeight
    {T : Real} (hT : 0 < T) (value : MassTriple) :
    liftedResonanceKernelDensity T value ≤
      actualNormalizedResonancePeakHeight T := by
  unfold liftedResonanceKernelDensity actualNormalizedResonancePeakHeight
  exact ENNReal.ofReal_le_ofReal
    (normalizedFiniteTimeResonanceKernel_le_height value.2 hT)

theorem withDensity_liftedResonanceKernelDensity_univ_le_peak
    (source : Measure MassTriple) {T : Real} (hT : 0 < T) :
    source.withDensity (liftedResonanceKernelDensity T) univ ≤
      actualNormalizedResonancePeakHeight T * source univ := by
  rw [withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ]
  calc
    (∫⁻ value, liftedResonanceKernelDensity T value ∂source) ≤
        ∫⁻ _value : MassTriple,
          actualNormalizedResonancePeakHeight T ∂source := by
      apply lintegral_mono
      intro value
      exact
        liftedResonanceKernelDensity_le_actualNormalizedResonancePeakHeight
          hT value
    _ = actualNormalizedResonancePeakHeight T * source univ := by simp

/-- Correct `T`-dependent determinant-bad estimate.  The sinc peak multiplies
the genuine collision-weighted minor tail; no inverse determinant moment is
assumed.  To make this term vanish along `T`, one must prove an actual tail
rate for the concrete bad level strong enough to beat the linear peak. -/
theorem actualThreeMassAllDistinctWeightedBadPerSiteBudget_le_peak_mul_collisionBadLevel
    {N : Nat} [NeZero N] (fixed : Lattice.PositiveMassConfig N)
    (site₀ site₁ site₂ : Lattice.Site N)
    (sign : Fin 3 → InteractionSign)
    (delta : Real) {T : Real} (hT : 0 < T) :
    actualThreeMassWeightedBadPerSiteBudget
        fixed site₀ site₁ site₂ sign
        (actualThreeMassAllDistinctTupleWeight
          fixed site₀ site₁ site₂)
        (fun modes => actualThreeMassProjectorRawGoodDetSet
          fixed site₀ site₁ site₂ modes delta) T ≤
      actualNormalizedResonancePeakHeight T *
        actualThreeMassAllDistinctCollisionWeightedProjectorMinorBadLevel
          fixed site₀ site₁ site₂ delta := by
  classical
  have hmode (modes : OrderedModeTriple N) :
      (Measure.map
        (actualThreeMassLiftedFrequencyChart
          fixed site₀ site₁ site₂ sign modes)
        ((iidMassTripleLaw.withDensity
          (actualThreeMassAllDistinctTupleWeight
            fixed site₀ site₁ site₂ modes)).restrict
              (actualThreeMassProjectorRawGoodDetSet
                fixed site₀ site₁ site₂ modes delta)ᶜ)).withDensity
            (liftedResonanceKernelDensity T) univ ≤
        actualNormalizedResonancePeakHeight T *
          (iidMassTripleLaw.withDensity
            (actualThreeMassAllDistinctTupleWeight
              fixed site₀ site₁ site₂ modes))
            {triple |
              actualThreeMassProjectorMinorMagnitude
                  fixed site₀ site₁ site₂ modes triple < delta} := by
    let source := iidMassTripleLaw.withDensity
      (actualThreeMassAllDistinctTupleWeight
        fixed site₀ site₁ site₂ modes)
    let bad := (actualThreeMassProjectorRawGoodDetSet
      fixed site₀ site₁ site₂ modes delta)ᶜ
    let chart := actualThreeMassLiftedFrequencyChart
      fixed site₀ site₁ site₂ sign modes
    have hchart : Measurable chart :=
      (continuous_actualThreeMassLiftedFrequencyChart
        fixed site₀ site₁ site₂ sign modes).measurable
    have hbad : MeasurableSet bad :=
      (measurableSet_actualThreeMassProjectorRawGoodDetSet
        fixed site₀ site₁ site₂ modes delta).compl
    have hbadEq : bad =
        {triple |
          actualThreeMassProjectorMinorMagnitude
              fixed site₀ site₁ site₂ modes triple < delta} := by
      ext triple
      simp [bad, actualThreeMassProjectorRawGoodDetSet]
    calc
      (Measure.map chart (source.restrict bad)).withDensity
          (liftedResonanceKernelDensity T) univ ≤
        actualNormalizedResonancePeakHeight T *
          Measure.map chart (source.restrict bad) univ :=
        withDensity_liftedResonanceKernelDensity_univ_le_peak
          (Measure.map chart (source.restrict bad)) hT
      _ = actualNormalizedResonancePeakHeight T *
          source
            {triple |
              actualThreeMassProjectorMinorMagnitude
                  fixed site₀ site₁ site₂ modes triple < delta} := by
        rw [Measure.map_apply hchart MeasurableSet.univ]
        simp only [preimage_univ]
        rw [Measure.restrict_apply MeasurableSet.univ]
        simp only [univ_inter]
        rw [hbadEq]
  unfold actualThreeMassWeightedBadPerSiteBudget
  calc
    (N : ENNReal)⁻¹ *
        ∑ modes : OrderedModeTriple N,
          (Measure.map
            (actualThreeMassLiftedFrequencyChart
              fixed site₀ site₁ site₂ sign modes)
            ((iidMassTripleLaw.withDensity
              (actualThreeMassAllDistinctTupleWeight
                fixed site₀ site₁ site₂ modes)).restrict
                  (actualThreeMassProjectorRawGoodDetSet
                    fixed site₀ site₁ site₂ modes delta)ᶜ)).withDensity
              (liftedResonanceKernelDensity T) univ ≤
      (N : ENNReal)⁻¹ *
        ∑ modes : OrderedModeTriple N,
          actualNormalizedResonancePeakHeight T *
            (iidMassTripleLaw.withDensity
              (actualThreeMassAllDistinctTupleWeight
                fixed site₀ site₁ site₂ modes))
              {triple |
                actualThreeMassProjectorMinorMagnitude
                    fixed site₀ site₁ site₂ modes triple < delta} := by
      exact mul_le_mul_right
        (Finset.sum_le_sum fun modes _hmodes => hmode modes) _
    _ = actualNormalizedResonancePeakHeight T *
        ((N : ENNReal)⁻¹ *
          ∑ modes : OrderedModeTriple N,
            (iidMassTripleLaw.withDensity
              (actualThreeMassAllDistinctTupleWeight
                fixed site₀ site₁ site₂ modes))
              {triple |
                actualThreeMassProjectorMinorMagnitude
                    fixed site₀ site₁ site₂ modes triple < delta}) := by
      rw [← Finset.mul_sum]
      ac_rfl
    _ = actualNormalizedResonancePeakHeight T *
        actualThreeMassAllDistinctCollisionWeightedProjectorMinorBadLevel
          fixed site₀ site₁ site₂ delta := by
      rw [actualThreeMassAllDistinctCollisionWeightedProjectorMinorBadLevel_eq_source]

end

end ArchonPhysics.ActualThreeMassCollisionWeightedProjectorMinorBadPeak
