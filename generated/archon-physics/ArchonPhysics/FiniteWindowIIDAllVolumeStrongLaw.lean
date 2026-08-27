import ArchonPhysics.PolynomialMarkedLegWindowStrongLaw
import ArchonPhysics.SpatialAverageBlockExtension

/-!
# Fixed-window iid strong law at every volume

The residue-class argument supplies a strong law along volumes `W * n`.
The deterministic incomplete-block estimate then promotes it to the ordinary
prefix average along every natural volume.
-/

namespace ArchonPhysics.FiniteWindowIIDAllVolumeStrongLaw

open ArchonPhysics
open ArchonPhysics.FiniteWindowIIDStrongLaw
open ArchonPhysics.PolynomialMarkedLegWindowStrongLaw
open ArchonPhysics.RandomEnsemble
open ArchonPhysics.SpatialAverageBlockExtension
open Filter MeasureTheory ProbabilityTheory Set Topology

noncomputable section

variable {Omega : Type*} [MeasurableSpace Omega]

/-- Every bounded measurable real observable of a fixed iid mass window obeys
the ordinary all-volume sliding-window spatial strong law. -/
theorem spatialRangeWindowAverage_allVolume_strongLaw_ae
    (ensemble : IIDMassPhaseEnsemble Omega)
    (W : Nat) (hW : 0 < W)
    (f : (Fin W → Real) → Real) (hf : Measurable f)
    (C : Real)
    (hbound : ∀ x : Fin W → Real,
      (∀ j, x j ∈ massSupport) → ‖f x‖ ≤ C) :
    ∀ᵐ omega ∂ensemble.probability,
      Tendsto
        (fun n : Nat ↦
          (∑ i ∈ Finset.range n,
            windowObservable ensemble W i f 0 omega) / (n : Real))
        atTop
        (𝓝 (∫ omega,
          windowObservable ensemble W 0 f 0 omega
            ∂ensemble.probability)) := by
  filter_upwards [spatialRangeWindowAverage_strongLaw_ae
    ensemble W hW f hf C hbound] with omega hmultiple
  let u : Nat → Real := fun i ↦
    windowObservable ensemble W i f 0 omega
  have hu : ∀ i, ‖u i‖ ≤ C := by
    intro i
    exact hbound (massWindow ensemble W i 0 omega)
      (massWindow_mem_support ensemble W i 0 omega)
  have hmultiple' : Tendsto
      (fun n : Nat ↦ prefixAverage u (W * n)) atTop
      (𝓝 (∫ omega,
        windowObservable ensemble W 0 f 0 omega
          ∂ensemble.probability)) := by
    simpa [prefixAverage, u] using hmultiple
  change Tendsto (prefixAverage u) atTop
    (𝓝 (∫ omega,
      windowObservable ensemble W 0 f 0 omega
        ∂ensemble.probability))
  exact tendsto_prefixAverage_of_mul u hW C hu hmultiple'

end


end ArchonPhysics.FiniteWindowIIDAllVolumeStrongLaw
