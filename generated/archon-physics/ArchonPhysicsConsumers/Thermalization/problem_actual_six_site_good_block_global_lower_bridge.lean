import ArchonPhysics.ActualSixSiteGoodBlockGlobalLowerBridge

namespace ArchonPhysicsConsumers.Thermalization

open ArchonPhysics
open ArchonPhysics.ActualSixSiteFullIIDPositiveWeightedNearResonancePatch
open ArchonPhysics.ActualSixSiteGoodBlockGlobalLowerBridge
open ArchonPhysics.ModalPhaseMismatch
open ArchonPhysics.RandomEnsemble
open ArchonPhysics.RepeatedParentChildMismatchSmallBall
open Filter MeasureTheory Set Topology

noncomputable section

/-- Standalone acceptance theorem for the exact good-block contribution
interface. -/
theorem problem_actual_six_site_good_block_global_lower_bridge
    {patch : Set SixMassVector} (hpatch : MeasurableSet patch)
    (hpatchPos : 0 < finiteMassLaw 6 patch)
    (rawMismatch : Nat -> RandomEnsemble.SampleSpace -> FiniteMeasure Real)
    {coefficient deltaMax : Real}
    (hcoefficient : 0 < coefficient) (hdeltaMax : 0 < deltaMax)
    (hcontribution : GoodSixBlockAdditiveContribution patch rawMismatch
      coefficient deltaMax) :
    ∃ constant : Real, 0 < constant ∧
      ∀ᵐ omega ∂ RandomEnsemble.canonicalLaw,
        ∀ᶠ blockCount : Nat in atTop,
          ∀ delta : Real, 0 < delta -> delta <= deltaMax ->
            constant * delta <=
              ((rawMismatch blockCount omega : Measure Real)
                (absoluteMismatchSublevel delta)).toReal /
                  (6 * (blockCount : Real)) := by
  exact exists_eventual_perSite_linearLower_of_goodSixBlockContribution
    hpatch hpatchPos rawMismatch hcoefficient hdeltaMax hcontribution

end

end ArchonPhysicsConsumers.Thermalization
