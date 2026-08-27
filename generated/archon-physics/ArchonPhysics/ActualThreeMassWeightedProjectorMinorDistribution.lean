import ArchonPhysics.ActualThreeMassAllDistinctSpectralBadBudget
import ArchonPhysics.ActualThreeMassCollisionJacobianResidual
import ArchonPhysics.ActualThreeMassProjectorMinorRegularity

/-!
# Actual collision-weighted projector-minor distribution

The exact residual coarea singularity is one inverse power of the actual
projector minor.  This module packages its genuine iid, all-distinct,
per-site weighted distribution.  No abstract surrogate law is introduced:
the source density is the physical collision weight times the exact
frequency/mass scale left by the Jacobian cancellation.

The main identity says that the inverse first moment of this distribution is
exactly the complete complement-integrated reciprocal-minor budget.  A second
identity evaluates every small-determinant level as the corresponding actual
iid weighted mass.  Uniform control of these explicit bad levels is the
remaining model-specific estimate; it is not asserted here.
-/

open scoped Matrix BigOperators ENNReal

namespace ArchonPhysics.ActualThreeMassWeightedProjectorMinorDistribution

open ArchonPhysics
open ArchonPhysics.ActualThreeMassAllDistinctAnnealedBroadeningTrace
open ArchonPhysics.ActualThreeMassLiftedPerSiteBudget
open ArchonPhysics.ActualThreeMassLiftedSpectralChart
open ArchonPhysics.ActualThreeMassProjectorMinorRegularity
open ArchonPhysics.ActualThreeMassProjectorWeightJacobian
open ArchonPhysics.LocalCollisionMarkContinuity
open ArchonPhysics.MeasurableOrderedModeCoupling.Harmonic
open ArchonPhysics.MeasurableOrderedSpectrum
open ArchonPhysics.OrderedSpectrumContinuity
open ArchonPhysics.RandomMassPositiveCollisionData
open ArchonPhysics.ThreeParameterSpectralAveragingDensity
open MeasureTheory Set

noncomputable section

/-- The exact nonsingular frequency/mass multiplier converting the normalized
collision weight into the numerator of the residual projector-minor ratio. -/
def actualThreeMassProjectorResidualScale
    {N : Nat} [NeZero N] (fixed : Lattice.PositiveMassConfig N)
    (site₀ site₁ site₂ : Lattice.Site N)
    (modes : OrderedModeTriple N) (triple : MassTriple) : ENNReal :=
  ENNReal.ofReal
    ((∏ r, 2 * orderedModeFrequency
      (threeMassHarmonicHermitian fixed site₀ site₁ site₂ triple)
        (modes r)) *
      (∏ s, (actualThreeMassRawCoordinate triple s) ^ 2))

theorem measurable_actualThreeMassProjectorResidualScale
    {N : Nat} [NeZero N] (fixed : Lattice.PositiveMassConfig N)
    (site₀ site₁ site₂ : Lattice.Site N)
    (modes : OrderedModeTriple N) :
    Measurable (actualThreeMassProjectorResidualScale
      fixed site₀ site₁ site₂ modes) := by
  unfold actualThreeMassProjectorResidualScale
  apply ENNReal.measurable_ofReal.comp
  apply Measurable.mul
  · apply Finset.measurable_prod
    intro r _hr
    exact measurable_const.mul
      (((continuous_orderedModeFrequency (modes r)).comp
        (continuous_threeMassHarmonicHermitian
          fixed site₀ site₁ site₂)).measurable)
  · apply Finset.measurable_prod
    intro s _hs
    fin_cases s
    · change Measurable fun triple : MassTriple => triple.1.1 ^ 2
      fun_prop
    · change Measurable fun triple : MassTriple => triple.1.2 ^ 2
      fun_prop
    · change Measurable fun triple : MassTriple => triple.2 ^ 2
      fun_prop

/-- Genuine all-distinct collision density after the exact elementary
Jacobian scales have been moved into the numerator. -/
def actualThreeMassAllDistinctProjectorResidualWeight
    {N : Nat} [NeZero N] (fixed : Lattice.PositiveMassConfig N)
    (site₀ site₁ site₂ : Lattice.Site N)
    (modes : OrderedModeTriple N) (triple : MassTriple) : ENNReal :=
  actualThreeMassAllDistinctTupleWeight
      fixed site₀ site₁ site₂ modes triple *
    actualThreeMassProjectorResidualScale
      fixed site₀ site₁ site₂ modes triple

theorem measurable_actualThreeMassAllDistinctProjectorResidualWeight
    {N : Nat} [NeZero N] (fixed : Lattice.PositiveMassConfig N)
    (site₀ site₁ site₂ : Lattice.Site N)
    (modes : OrderedModeTriple N) :
    Measurable (actualThreeMassAllDistinctProjectorResidualWeight
      fixed site₀ site₁ site₂ modes) :=
  (measurable_actualThreeMassAllDistinctTupleWeight
    fixed site₀ site₁ site₂ modes).mul
      (measurable_actualThreeMassProjectorResidualScale
        fixed site₀ site₁ site₂ modes)

/-- Absolute determinant of the genuine dual-cycle projector minor. -/
def actualThreeMassProjectorMinorMagnitude
    {N : Nat} [NeZero N] (fixed : Lattice.PositiveMassConfig N)
    (site₀ site₁ site₂ : Lattice.Site N)
    (modes : OrderedModeTriple N) (triple : MassTriple) : Real :=
  |(actualThreeMassProjectorWeightMatrix
    fixed site₀ site₁ site₂ modes triple).det|

theorem measurable_actualThreeMassProjectorMinorMagnitude
    {N : Nat} [NeZero N] (fixed : Lattice.PositiveMassConfig N)
    (site₀ site₁ site₂ : Lattice.Site N)
    (modes : OrderedModeTriple N) :
    Measurable (actualThreeMassProjectorMinorMagnitude
      fixed site₀ site₁ site₂ modes) :=
  (measurable_actualThreeMassProjectorWeightMatrix_det
    fixed site₀ site₁ site₂ modes).abs

/-- The actual iid, collision-weighted, per-site distribution of absolute
projector-minor determinants, summed jointly over all ordered mode triples. -/
def actualThreeMassAllDistinctWeightedProjectorMinorDistribution
    {N : Nat} [NeZero N] (fixed : Lattice.PositiveMassConfig N)
    (site₀ site₁ site₂ : Lattice.Site N) : Measure Real :=
  (N : ENNReal)⁻¹ •
    ∑ modes : OrderedModeTriple N,
      Measure.map
        (actualThreeMassProjectorMinorMagnitude
          fixed site₀ site₁ site₂ modes)
        (iidMassTripleLaw.withDensity
          (actualThreeMassAllDistinctProjectorResidualWeight
            fixed site₀ site₁ site₂ modes))

/-- The inverse first moment of the actual weighted minor distribution is
exactly the full per-site reciprocal-projector-minor budget. -/
theorem lintegral_inv_actualThreeMassAllDistinctWeightedProjectorMinorDistribution
    {N : Nat} [NeZero N] (fixed : Lattice.PositiveMassConfig N)
    (site₀ site₁ site₂ : Lattice.Site N) :
    ∫⁻ x, (ENNReal.ofReal x)⁻¹
        ∂actualThreeMassAllDistinctWeightedProjectorMinorDistribution
          fixed site₀ site₁ site₂ =
      (N : ENNReal)⁻¹ *
        ∑ modes : OrderedModeTriple N,
          ∫⁻ triple,
            actualThreeMassAllDistinctProjectorResidualWeight
                fixed site₀ site₁ site₂ modes triple *
              (ENNReal.ofReal
                (actualThreeMassProjectorMinorMagnitude
                  fixed site₀ site₁ site₂ modes triple))⁻¹
            ∂iidMassTripleLaw := by
  classical
  unfold actualThreeMassAllDistinctWeightedProjectorMinorDistribution
  rw [lintegral_smul_measure, lintegral_finsetSum_measure]
  simp only [smul_eq_mul]
  congr 1
  apply Finset.sum_congr rfl
  intro modes _hmodes
  let inverse : Real → ENNReal := fun x => (ENNReal.ofReal x)⁻¹
  have hinverse : Measurable inverse :=
    ENNReal.measurable_ofReal.inv
  rw [lintegral_map hinverse
    (measurable_actualThreeMassProjectorMinorMagnitude
      fixed site₀ site₁ site₂ modes)]
  change ∫⁻ a,
      (inverse ∘ actualThreeMassProjectorMinorMagnitude
        fixed site₀ site₁ site₂ modes) a
        ∂iidMassTripleLaw.withDensity
          (actualThreeMassAllDistinctProjectorResidualWeight
            fixed site₀ site₁ site₂ modes) = _
  rw [lintegral_withDensity_eq_lintegral_mul iidMassTripleLaw
    (measurable_actualThreeMassAllDistinctProjectorResidualWeight
      fixed site₀ site₁ site₂ modes)
    (hinverse.comp
      (measurable_actualThreeMassProjectorMinorMagnitude
        fixed site₀ site₁ site₂ modes))]
  rfl

/-- Actual weighted mass of projector minors smaller than `delta`. -/
def actualThreeMassAllDistinctWeightedProjectorMinorBadLevel
    {N : Nat} [NeZero N] (fixed : Lattice.PositiveMassConfig N)
    (site₀ site₁ site₂ : Lattice.Site N) (delta : Real) : ENNReal :=
  actualThreeMassAllDistinctWeightedProjectorMinorDistribution
    fixed site₀ site₁ site₂ (Iio delta)

/-- Exact source-side formula for every actual weighted bad determinant
level.  This is the concrete quantity whose volume-uniform decay must be
proved to control the residual inverse minor. -/
theorem actualThreeMassAllDistinctWeightedProjectorMinorBadLevel_eq
    {N : Nat} [NeZero N] (fixed : Lattice.PositiveMassConfig N)
    (site₀ site₁ site₂ : Lattice.Site N) (delta : Real) :
    actualThreeMassAllDistinctWeightedProjectorMinorBadLevel
        fixed site₀ site₁ site₂ delta =
      (N : ENNReal)⁻¹ *
        ∑ modes : OrderedModeTriple N,
          ∫⁻ triple in
              {triple |
                actualThreeMassProjectorMinorMagnitude
                    fixed site₀ site₁ site₂ modes triple < delta},
            actualThreeMassAllDistinctProjectorResidualWeight
              fixed site₀ site₁ site₂ modes triple
            ∂iidMassTripleLaw := by
  classical
  unfold actualThreeMassAllDistinctWeightedProjectorMinorBadLevel
    actualThreeMassAllDistinctWeightedProjectorMinorDistribution
  rw [Measure.smul_apply, Measure.coe_finsetSum]
  simp only [Finset.sum_apply, smul_eq_mul]
  congr 1
  apply Finset.sum_congr rfl
  intro modes _hmodes
  have hmagnitude :=
    measurable_actualThreeMassProjectorMinorMagnitude
      fixed site₀ site₁ site₂ modes
  rw [Measure.map_apply hmagnitude measurableSet_Iio]
  rw [withDensity_apply _
    (measurableSet_Iio.preimage hmagnitude)]
  rfl

end

end ArchonPhysics.ActualThreeMassWeightedProjectorMinorDistribution
