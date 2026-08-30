import ArchonPhysics.ActualEightSiteIIDGoodBlockPositiveDensity

namespace ArchonPhysicsConsumers.Thermalization

open ArchonPhysics
open ArchonPhysics.ActualEightSiteExactDecayIVTBridge
open ArchonPhysics.ActualEightSiteFullIIDPositiveWeightedNearResonancePatch
open ArchonPhysics.ActualEightSiteIIDGoodBlockPositiveDensity
open ArchonPhysics.RandomEnsemble
open Filter MeasureTheory Set Topology

noncomputable section

/-- Standalone acceptance theorem for the genuine iid eight-block density
bridge. -/
theorem problem_actual_eight_site_iid_good_block_positive_density
    {epsilon : Real} (hepsilon : 0 < epsilon) :
    ∃ patch : Set EightMassVector, ∃ probability : Real,
      IsOpen patch ∧
      probability = (finiteMassLaw 8).real patch ∧
      0 < probability ∧
      patch ⊆ fullEightPhysicalWeightedNearResonanceWithProjectorMinor epsilon ∧
      (∀ᵐ omega ∂ RandomEnsemble.canonicalLaw,
        Tendsto (fun blockCount : Nat ↦
          fullEightPatchBlockDensity patch blockCount omega) atTop
          (𝓝 probability)) ∧
      (∀ᵐ omega ∂ RandomEnsemble.canonicalLaw,
        ∀ᶠ blockCount : Nat in atTop,
          probability / 2 <
            fullEightPatchBlockDensity patch blockCount omega) := by
  exact
    exists_fullEight_physicalWeightedNearResonancePatch_positiveDensity_ae
      hepsilon

end

end ArchonPhysicsConsumers.Thermalization
