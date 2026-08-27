import ArchonPhysics.CanonicalChildRepeatedAnnealedSectorBridge

/-!
# Child-repeated annealed small-ball certificate from actual two-mass atlases

This module turns a volume-indexed family of genuine frozen-environment
two-mass spectral atlases into the canonical annealed `ChildRepeated`
small-ball input.  The only remaining model obligations are a uniform regular
budget and a vanishing exceptional budget.
-/

open scoped Topology ENNReal

namespace ArchonPhysics.CanonicalChildRepeatedAnnealedAtlasSmallBall

open ArchonPhysics
open ArchonPhysics.ActualTwoMassChildRepeatedAnnealedLInfinity
open ArchonPhysics.ActualTwoMassChildRepeatedAnnealedReconstruction
open ArchonPhysics.ActualTwoMassChildRepeatedPerSiteBudget
open ArchonPhysics.CanonicalChildRepeatedAnnealedSectorBridge
open ArchonPhysics.CanonicalDecayAnnealedSmallBallCertificate
open ArchonPhysics.ChildRepeatedAnnealedReducedMeasure
open ArchonPhysics.ChildRepeatedDiagonalHybridKernel
open ArchonPhysics.ChildRepeatedReducedResonanceStripVolume
open ArchonPhysics.DecayChannelModeEqualityPartition
open ArchonPhysics.IIDMassPairFiniteVolumeReconstruction
open ArchonPhysics.IIDMassTripleFiniteEnvironment
open ArchonPhysics.RandomEnsemble
open ArchonPhysics.RepeatedParentChildMismatchSmallBall
open Filter MeasureTheory Set

noncomputable section

/-- Actual two-mass atlases at the physical volumes associated with marked
index `n`, together with precisely the two cross-volume estimates still
needed: one uniform finite regular budget and one vanishing finite bad budget.
-/
structure ActualTwoMassChildRepeatedAnnealedAtlasSequence where
  site₁ : (n : Nat) → Lattice.Site ((n + 1) + 2)
  site₂ : (n : Nat) → Lattice.Site ((n + 1) + 2)
  site_ne : ∀ n, site₁ n ≠ site₂ n
  atlas : (n : Nat) → ActualTwoMassChildRepeatedFrozenAtlasData
    (n + 1) (site₁ n) (site₂ n)
  regularCeiling : ENNReal
  regularCeiling_ne_top : regularCeiling ≠ ∞
  regular_le : ∀ n, (atlas n).regularCeiling ≤ regularCeiling
  badError : Nat → ENNReal
  badError_ne_top : ∀ n, badError n ≠ ∞
  badError_tendsto_zero : Tendsto badError atTop (nhds 0)
  bad_le : ∀ n, (atlas n).badCeiling ≤ badError n

/-- Conditional two-mass coarea, exact pair/complement Fubini, and the
frequency-square resonance-strip estimate give the required annealed ENNReal
bound at every marked volume. -/
theorem canonicalChildRepeatedReducedAnnealed_resonanceStrip_le
    (data : ActualTwoMassChildRepeatedAnnealedAtlasSequence)
    (n : Nat) {delta : Real} (hdelta : 0 ≤ delta) :
    (canonicalChildRepeatedReducedAnnealedPerSiteFiniteMeasure (n + 1) :
        Measure (Real × Real))
        (childRepeatedReducedResonanceStrip delta) ≤
      data.regularCeiling *
          ENNReal.ofReal (2 * Real.sqrt 5 * delta) +
        data.badError n := by
  apply
    canonicalChildRepeatedReducedAnnealedPerSiteFiniteMeasure_apply_le_of_conditional
      (n + 1) (data.site₁ n) (data.site₂ n) (data.site_ne n)
      (childRepeatedReducedResonanceStrip_isClosed delta).measurableSet
      (data.regularCeiling *
        ENNReal.ofReal (2 * Real.sqrt 5 * delta) + data.badError n)
  intro rest
  let atlas := data.atlas n
  exact
    actualTwoMassChildRepeatedConditionalPerSite_resonanceStrip_apply_le_of_budgets
      (finitePairEnvironmentPositiveMassConfig
        (data.site₁ n) (data.site₂ n) rest)
      (fun site ↦ finitePairEnvironmentPositiveMassConfig_mass_mem_support
        (data.site₁ n) (data.site₂ n) rest site)
      (data.site₁ n) (data.site₂ n)
      (actualTwoMassChildRepeatedPositivePairWeight
        (finitePairEnvironmentPositiveMassConfig
          (data.site₁ n) (data.site₂ n) rest)
        (data.site₁ n) (data.site₂ n))
      (atlas.weightCeiling rest) (atlas.hweight rest)
      (atlas.good rest) (atlas.hgood rest)
      (atlas.hderivative rest) (atlas.hinjective rest)
      (atlas.detLower rest) (atlas.hdetLower rest) (atlas.hdet rest)
      data.regularCeiling (data.badError n)
      ((atlas.hregular rest).trans (data.regular_le n))
      ((atlas.hbad rest).trans (data.bad_le n)) hdelta

end


end ArchonPhysics.CanonicalChildRepeatedAnnealedAtlasSmallBall
