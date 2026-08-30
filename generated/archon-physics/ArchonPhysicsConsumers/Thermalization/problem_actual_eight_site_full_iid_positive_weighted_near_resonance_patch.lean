import ArchonPhysics.ActualEightSiteFullIIDPositiveWeightedNearResonancePatch

/-!
# Full-eight iid positive weighted near-resonance consumer

This consumer transfers the positive finite product-law patch to the mass
restriction of an arbitrary verified iid mass-phase ensemble.
-/

namespace ArchonPhysicsConsumers.Thermalization

open ArchonPhysics
open ArchonPhysics.ActualEightSiteExactDecayIVTBridge
open ArchonPhysics.ActualEightSiteFullIIDPositiveWeightedNearResonancePatch
open ArchonPhysics.RandomEnsemble
open MeasureTheory ProbabilityTheory Set

noncomputable section

/-- Every verified iid ensemble assigns positive probability to an open
eight-mass event retaining the certified physical near-resonance data. -/
theorem exists_positive_probability_fullEight_physicalWeightedNearResonancePatch
    {Omega : Type*} [MeasurableSpace Omega]
    (ensemble : IIDMassPhaseEnsemble Omega)
    {epsilon : Real} (hepsilon : 0 < epsilon) :
    ∃ patch : Set EightMassVector,
      IsOpen patch ∧
      0 < ensemble.probability
        {omega |
          ensemble.restrictMassFin (N := 8) omega ∈ patch} ∧
      ∀ omega,
        ensemble.restrictMassFin (N := 8) omega ∈ patch →
        ensemble.restrictMassFin (N := 8) omega ∈
          fullEightPhysicalWeightedNearResonanceWithProjectorMinor epsilon := by
  obtain ⟨patch, hopen, hmass, hsubset⟩ :=
    exists_positive_finiteMassLaw_fullEight_physicalWeightedNearResonancePatch
      hepsilon
  have hmeasure :=
    (ensemble.restrictMassFin_hasLaw (N := 8)).measure_eq
      hopen.measurableSet
  refine ⟨patch, hopen, ?_, ?_⟩
  · change 0 < ensemble.probability
      {omega | patch (ensemble.restrictMassFin (N := 8) omega)}
    rw [hmeasure]
    exact hmass
  · intro omega homega
    exact hsubset homega

end

end ArchonPhysicsConsumers.Thermalization
