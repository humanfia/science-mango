import ArchonPhysics.CanonicalRankFrequencyMarkedBroadenedLimit

/-!
# Scalar marginal of the canonical broadened marked limit

The total broadened mass is unchanged if one first pushes a finite measure
forward through its mismatch and then weights the scalar pushforward by the
same fixed-time resonance peak.  For the canonical marked thermodynamic
limit, the scalar pushforward is already identified with the deterministic
per-site collision-measure limit.  Thus the fixed-time collision coefficient
is reduced exactly to one scalar integral, with no marked cluster point or
finite-volume ambiguity left.
-/

open scoped Topology InnerProductSpace RealInnerProductSpace

namespace ArchonPhysics.CanonicalRankFrequencyMarkedBroadenedMarginal

open ArchonPhysics
open ArchonPhysics.BroadenedResonanceMeasure
open ArchonPhysics.CanonicalRankFrequencyMarkedBroadenedLimit
open ArchonPhysics.CanonicalRankFrequencyMarkedFiniteMeasureWeakLimit
open ArchonPhysics.CanonicalRankFrequencyMarkedMeasure
open ArchonPhysics.CanonicalRankFrequencyMarkedResonanceLimit
open ArchonPhysics.UniformCollisionDensityTransfer
open Filter MeasureTheory Topology

noncomputable section

variable {X : Type*} [MeasurableSpace X]

/-- Pushing forward through the mismatch before broadening leaves the real
total broadened mass unchanged. -/
theorem broadenedResonanceMeasure_mass_eq_map
    (mu : FiniteMeasure X) (mismatch : X -> Real)
    (hmismatch : Measurable mismatch) (T : Real) (hT : 0 < T) :
    ((broadenedResonanceMeasure mu mismatch hmismatch T hT).mass : Real) =
      ((broadenedResonanceMeasure (mu.map mismatch) id measurable_id T hT).mass :
        Real) := by
  rw [broadenedResonanceMeasure_mass_eq_integral,
    broadenedResonanceMeasure_mass_eq_integral]
  simp only [id_eq, FiniteMeasure.toMeasure_map]
  rw [integral_map hmismatch.aemeasurable
    (continuous_normalizedFiniteTimeResonanceKernel hT).aestronglyMeasurable]

variable {Omega : Type*} [MeasurableSpace Omega]

/-- The deterministic scalar per-site collision limit weighted by the fixed
positive-time normalized resonance peak. -/
def canonicalBroadenedCollisionPerSiteMeasureLimit
    (ensemble : IIDMassPhaseEnsemble Omega)
    (sign : Fin 3 -> ModalPhaseMismatch.InteractionSign)
    (T : Real) (hT : 0 < T) : FiniteMeasure Real :=
  broadenedResonanceMeasure
    (CanonicalCollisionMeasureWeakLimit.canonicalCollisionPerSiteMeasureLimit
      ensemble sign)
    id measurable_id T hT

/-- The total mass of the deterministic marked broadened limit is exactly
the total mass of its deterministic scalar collision-mismatch broadening. -/
theorem canonicalRankFrequencyMarkedBroadenedPerSiteMeasureLimit_mass_eq_scalar
    (ensemble : IIDMassPhaseEnsemble Omega)
    (sign : Fin 3 -> ModalPhaseMismatch.InteractionSign)
    (T : Real) (hT : 0 < T) :
    ((canonicalRankFrequencyMarkedBroadenedPerSiteMeasureLimit
        ensemble sign T hT).mass : Real) =
      ((canonicalBroadenedCollisionPerSiteMeasureLimit
        ensemble sign T hT).mass : Real) := by
  unfold canonicalRankFrequencyMarkedBroadenedPerSiteMeasureLimit
    canonicalBroadenedCollisionPerSiteMeasureLimit
  calc
    ((broadenedResonanceMeasure
        (canonicalRankFrequencyMarkedPerSiteMeasureLimit ensemble)
        (markedFrequencyMismatch sign)
        (measurable_markedFrequencyMismatch sign) T hT).mass : Real) =
      ((broadenedResonanceMeasure
        ((canonicalRankFrequencyMarkedPerSiteMeasureLimit ensemble).map
          (markedFrequencyMismatch sign))
        id measurable_id T hT).mass : Real) :=
      broadenedResonanceMeasure_mass_eq_map
        (canonicalRankFrequencyMarkedPerSiteMeasureLimit ensemble)
        (markedFrequencyMismatch sign)
        (measurable_markedFrequencyMismatch sign) T hT
    _ = ((broadenedResonanceMeasure
        (CanonicalCollisionMeasureWeakLimit.canonicalCollisionPerSiteMeasureLimit
          ensemble sign)
        id measurable_id T hT).mass : Real) := by
      rw [map_canonicalRankFrequencyMarkedPerSiteMeasureLimit_eq_collision]

/-- Almost surely, the complete finite-volume broadened marked collision
mass sequence converges to the scalar deterministic broadened collision
coefficient. -/
theorem canonicalRankFrequencyTripleBroadenedPerSiteMass_tendsto_scalar_limit_ae
    (sign : Fin 3 -> ModalPhaseMismatch.InteractionSign)
    (T : Real) (hT : 0 < T) :
    ∀ᵐ omega ∂(RandomEnsemble.canonicalLaw),
      Tendsto
        (fun n : Nat =>
          (canonicalRankFrequencyTripleBroadenedPerSiteFiniteMeasure
            canonicalIIDMassPhaseEnsemble (n + 1) omega sign T hT).mass)
        atTop
        (nhds
          (canonicalBroadenedCollisionPerSiteMeasureLimit
            canonicalIIDMassPhaseEnsemble sign T hT).mass) := by
  filter_upwards
    [canonicalRankFrequencyTripleBroadenedPerSiteMass_tendsto_limit_ae
      sign T hT] with omega hmass
  convert hmass using 1
  exact congrArg nhds (NNReal.eq
    (canonicalRankFrequencyMarkedBroadenedPerSiteMeasureLimit_mass_eq_scalar
      canonicalIIDMassPhaseEnsemble sign T hT).symm)

end

end ArchonPhysics.CanonicalRankFrequencyMarkedBroadenedMarginal
