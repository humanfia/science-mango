import ArchonPhysics.ActualTwoMassChildRepeatedAnnealedReconstruction

/-!
# Almost-everywhere frozen-environment reconstruction

The pair/complement identity is an integral over the complementary iid mass
environment.  Accordingly, a conditional estimate is needed only almost
everywhere in that environment; exceptional frozen configurations of measure
zero do not need artificial pointwise atlas data.
-/

namespace ArchonPhysics.ActualTwoMassChildRepeatedAnnealedAEReconstruction

open ArchonPhysics
open ArchonPhysics.ActualTwoMassChildRepeatedAnnealedReconstruction
open ArchonPhysics.ActualTwoMassChildRepeatedPerSiteBudget
open ArchonPhysics.ChildRepeatedAnnealedReducedMeasure
open ArchonPhysics.IIDMassPairFiniteVolumeReconstruction
open ArchonPhysics.IIDMassTripleFiniteEnvironment
open MeasureTheory Set

noncomputable section

/-- An almost-everywhere conditional bound integrates to the same canonical
annealed bound. -/
theorem canonicalChildRepeatedReducedAnnealedPerSiteFiniteMeasure_apply_le_of_conditional_ae
    (n : Nat) (site₁ site₂ : Lattice.Site (n + 2))
    (hsite : site₁ ≠ site₂)
    {A : Set (Real × Real)} (hA : MeasurableSet A)
    (bound : ENNReal)
    (hbound : ∀ᵐ rest ∂(iidFiniteMassVectorLaw
        (finiteVolumeMassPairComplement site₁ site₂)),
      actualTwoMassChildRepeatedConditionalPerSiteMeasure
        (finitePairEnvironmentPositiveMassConfig site₁ site₂ rest)
        site₁ site₂
        (actualTwoMassChildRepeatedPositivePairWeight
          (finitePairEnvironmentPositiveMassConfig site₁ site₂ rest)
          site₁ site₂) A ≤ bound) :
    (canonicalChildRepeatedReducedAnnealedPerSiteFiniteMeasure n :
      Measure (Real × Real)) A ≤ bound := by
  rw [canonicalChildRepeatedReducedAnnealedPerSiteFiniteMeasure_apply_eq_complement_conditional
    n site₁ site₂ hsite hA]
  calc
    (∫⁻ rest,
        actualTwoMassChildRepeatedConditionalPerSiteMeasure
          (finitePairEnvironmentPositiveMassConfig site₁ site₂ rest)
          site₁ site₂
          (actualTwoMassChildRepeatedPositivePairWeight
            (finitePairEnvironmentPositiveMassConfig site₁ site₂ rest)
            site₁ site₂) A
        ∂(iidFiniteMassVectorLaw
          (finiteVolumeMassPairComplement site₁ site₂))) ≤
      ∫⁻ _rest,
        bound
        ∂(iidFiniteMassVectorLaw
          (finiteVolumeMassPairComplement site₁ site₂)) :=
      lintegral_mono_ae hbound
    _ = bound := by
      rw [lintegral_const]
      simp [iidFiniteMassVectorLaw]

end

end ArchonPhysics.ActualTwoMassChildRepeatedAnnealedAEReconstruction
