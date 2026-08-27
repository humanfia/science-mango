import ArchonPhysics.ActualSixSiteIIDGoodBlockPositiveDensity

namespace ArchonPhysicsConsumers.Thermalization

open ArchonPhysics

open ArchonPhysics.ActualSixSiteFullIIDPositiveWeightedNearResonancePatch
open ArchonPhysics.ActualSixSiteIIDGoodBlockPositiveDensity
open ArchonPhysics.RandomEnsemble
open Filter MeasureTheory Set Topology

noncomputable section

/-- Standalone acceptance theorem for the genuine iid six-block density
bridge. -/
theorem problem_actual_six_site_iid_good_block_positive_density
    {epsilon : Real} (hepsilon : 0 < epsilon) :
    ∃ patch : Set SixMassVector, ∃ probability : Real,
      IsOpen patch ∧
      probability = (finiteMassLaw 6).real patch ∧
      0 < probability ∧
      patch ⊆ fullSixPhysicalWeightedNearResonanceWithProjectorMinor epsilon ∧
      (∀ᵐ omega ∂ RandomEnsemble.canonicalLaw,
        Tendsto (fun blockCount : Nat =>
          fullSixPatchBlockDensity patch blockCount omega) atTop
          (𝓝 probability)) ∧
      (∀ᵐ omega ∂ RandomEnsemble.canonicalLaw,
        ∀ᶠ blockCount : Nat in atTop,
          probability / 2 <
            fullSixPatchBlockDensity patch blockCount omega) := by
  exact
    exists_fullSix_physicalWeightedNearResonancePatch_positiveDensity_ae
      hepsilon

end

end ArchonPhysicsConsumers.Thermalization
