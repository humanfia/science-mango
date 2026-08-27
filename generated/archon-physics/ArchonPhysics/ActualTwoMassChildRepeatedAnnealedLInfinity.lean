import ArchonPhysics.ActualTwoMassChildRepeatedAnnealedReconstruction
import ArchonPhysics.ActualTwoMassChildRepeatedPerSiteLInfinity

/-!
# Actual conditional coarea to annealed child `L∞`

This module packages the remaining frozen-environment atlas data and composes
the already proved actual two-mass area estimate with exact iid
pair/complement reconstruction.  The conclusion is a setwise bound on the
annealed law only.
-/

open scoped ENNReal

namespace ArchonPhysics.ActualTwoMassChildRepeatedAnnealedLInfinity

open ArchonPhysics
open ArchonPhysics.ActualTwoMassChildRepeatedAnnealedReconstruction
open ArchonPhysics.ActualTwoMassChildRepeatedPerSiteBudget
open ArchonPhysics.ActualTwoMassChildRepeatedPerSiteLInfinity
open ArchonPhysics.ActualTwoMassSpectralChart
open ArchonPhysics.ChildRepeatedAnnealedReducedMeasure
open ArchonPhysics.IIDMassPairFiniteVolumeReconstruction
open ArchonPhysics.IIDMassTripleFiniteEnvironment
open ArchonPhysics.RandomEnsemble
open ArchonPhysics.TwoParameterSpectralAveragingAtlas
open MeasureTheory Set

noncomputable section

abbrev ChildRepeatedFrozenEnvironment
    (n : Nat) (site₁ site₂ : Lattice.Site (n + 2)) :=
  FiniteMassVector (finiteVolumeMassPairComplement site₁ site₂)

abbrev childRepeatedFrozenMass
    (n : Nat) (site₁ site₂ : Lattice.Site (n + 2))
    (rest : ChildRepeatedFrozenEnvironment n site₁ site₂) :
    Lattice.PositiveMassConfig (n + 2) :=
  finitePairEnvironmentPositiveMassConfig site₁ site₂ rest

/-- All local information required from a two-mass spectral atlas, together
with uniform bounds on its exact reciprocal-Jacobian and exceptional budgets.
No existence of this structure is postulated. -/
structure ActualTwoMassChildRepeatedFrozenAtlasData
    (n : Nat) (site₁ site₂ : Lattice.Site (n + 2)) where
  weightCeiling : ChildRepeatedFrozenEnvironment n site₁ site₂ →
    ChildRepeatedModePair (n + 2) → ENNReal
  good : ChildRepeatedFrozenEnvironment n site₁ site₂ →
    ChildRepeatedModePair (n + 2) → Set (Real × Real)
  detLower : ChildRepeatedFrozenEnvironment n site₁ site₂ →
    ChildRepeatedModePair (n + 2) → Real
  hweight : ∀ rest modes,
    ∀ᵐ point ∂iidMassPairLaw,
      actualTwoMassChildRepeatedPositivePairWeight
          (childRepeatedFrozenMass n site₁ site₂ rest)
          site₁ site₂ modes point ≤
        weightCeiling rest modes
  hgood : ∀ rest modes, MeasurableSet (good rest modes)
  hderivative : ∀ rest modes point, point ∈ good rest modes →
    HasFDerivWithinAt
      (actualTwoMassChildFrequencyChart
        (childRepeatedFrozenMass n site₁ site₂ rest)
        site₁ site₂ modes.1 modes.2)
      (actualTwoMassChildFrequencyJacobian
        (childRepeatedFrozenMass n site₁ site₂ rest)
        site₁ site₂ modes.1 modes.2 point)
      (good rest modes) point
  hinjective : ∀ rest modes,
    InjOn
      (actualTwoMassChildFrequencyChart
        (childRepeatedFrozenMass n site₁ site₂ rest)
        site₁ site₂ modes.1 modes.2)
      (good rest modes)
  hdetLower : ∀ rest modes, 0 < detLower rest modes
  hdet : ∀ rest modes point, point ∈ good rest modes →
    detLower rest modes ≤
      |(actualTwoMassChildFrequencyJacobian
        (childRepeatedFrozenMass n site₁ site₂ rest)
        site₁ site₂ modes.1 modes.2 point).det|
  regularCeiling : ENNReal
  badCeiling : ENNReal
  hregular : ∀ rest,
    actualTwoMassChildRepeatedRegularPerSiteBudget
      (weightCeiling rest) (detLower rest) ≤ regularCeiling
  hbad : ∀ rest,
    actualTwoMassChildRepeatedBadPerSiteBudget
      (actualTwoMassChildRepeatedPositivePairWeight
        (childRepeatedFrozenMass n site₁ site₂ rest) site₁ site₂)
      (good rest) ≤ badCeiling

/-- Actual two-mass coarea/Fubini gives an arbitrary-measurable-set density
estimate for the genuine canonical annealed child law. -/
theorem canonicalChildRepeatedReducedAnnealedPerSiteFiniteMeasure_apply_le_of_frozenAtlas
    (n : Nat) (site₁ site₂ : Lattice.Site (n + 2))
    (hsite : site₁ ≠ site₂)
    (atlas : ActualTwoMassChildRepeatedFrozenAtlasData n site₁ site₂)
    {A : Set (Real × Real)} (hA : MeasurableSet A) :
    (canonicalChildRepeatedReducedAnnealedPerSiteFiniteMeasure n :
      Measure (Real × Real)) A ≤
      atlas.regularCeiling * (volume : Measure (Real × Real)) A +
        atlas.badCeiling := by
  apply
    canonicalChildRepeatedReducedAnnealedPerSiteFiniteMeasure_apply_le_of_conditional
      n site₁ site₂ hsite hA
      (atlas.regularCeiling * (volume : Measure (Real × Real)) A +
        atlas.badCeiling)
  intro rest
  exact
    actualTwoMassChildRepeatedConditionalPerSite_apply_le_of_budgets
      (childRepeatedFrozenMass n site₁ site₂ rest)
      site₁ site₂
      (actualTwoMassChildRepeatedPositivePairWeight
        (childRepeatedFrozenMass n site₁ site₂ rest) site₁ site₂)
      (atlas.weightCeiling rest) (atlas.hweight rest)
      (atlas.good rest) (atlas.hgood rest)
      (atlas.hderivative rest) (atlas.hinjective rest)
      (atlas.detLower rest) (atlas.hdetLower rest) (atlas.hdet rest)
      atlas.regularCeiling atlas.badCeiling
      (atlas.hregular rest) (atlas.hbad rest) hA

end

end ArchonPhysics.ActualTwoMassChildRepeatedAnnealedLInfinity
