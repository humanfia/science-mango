import ArchonPhysics.ActualSixSiteFullIIDPositiveWeightedNearResonancePatch

/-!
# Full-six iid positive weighted near-resonance consumer

This consumer transfers the finite six-coordinate product-law statement to
the canonical mass restriction of any verified iid mass-phase ensemble.  The
nonzero determinant retained in the patch is the explicitly named
first-three-coordinate projector-minor proxy, not a six-coordinate physical
Jacobian.
-/

namespace ArchonPhysicsConsumers.Thermalization

open ArchonPhysics
open ArchonPhysics.ActualSixSiteFullIIDPositiveWeightedNearResonancePatch
open ArchonPhysics.RandomEnsemble
open MeasureTheory ProbabilityTheory Set

noncomputable section

/-- In every canonical iid ensemble, every positive mismatch width contains a
positive-probability open event of six genuinely random masses with simple
spectrum, positive selected energies, physical mismatch below the width,
positive physical selected collision weight, and nonzero projector-minor
proxy. -/
theorem exists_positive_probability_fullSix_physicalWeightedNearResonancePatch
    {Omega : Type*} [MeasurableSpace Omega]
    (ensemble : IIDMassPhaseEnsemble Omega)
    {epsilon : Real} (hepsilon : 0 < epsilon) :
    ∃ patch : Set (Fin 6 → Real),
      IsOpen patch ∧
      0 < ensemble.probability
        {omega |
          ensemble.restrictMassFin (N := 6) omega ∈ patch} ∧
      ∀ omega,
        ensemble.restrictMassFin (N := 6) omega ∈ patch →
        ensemble.restrictMassFin (N := 6) omega ∈
          fullSixPhysicalWeightedNearResonanceWithProjectorMinor epsilon := by
  obtain ⟨patch, hopen, hmass, hsubset⟩ :=
    exists_positive_finiteMassLaw_fullSix_physicalWeightedNearResonancePatch
      hepsilon
  have hmeasure :=
    (ensemble.restrictMassFin_hasLaw (N := 6)).measure_eq
      hopen.measurableSet
  refine ⟨patch, hopen, ?_, ?_⟩
  · change 0 < ensemble.probability
      {omega | patch (ensemble.restrictMassFin (N := 6) omega)}
    rw [hmeasure]
    exact hmass
  · intro omega homega
    exact hsubset homega

end

end ArchonPhysicsConsumers.Thermalization
