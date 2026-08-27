import ArchonPhysics.CanonicalRankFrequencyMarkedFiniteMeasureWeakLimit
import ArchonPhysics.BroadenedResonanceMeasure
import ArchonPhysics.ResonanceKernelLipschitz

/-!
# Complete-sequence marked broadened-resonance limit

Weak convergence of finite measures is preserved when the measures are
weighted by one fixed bounded continuous density.  Applying this elementary
fact to the normalized finite-time resonance peak upgrades the canonical raw
rank-frequency marked limit to a deterministic complete-sequence broadened
collision limit at every fixed positive observation time.

The time is fixed in this module.  No `T -> infinity` assertion, density at
zero mismatch, or exact-resonance support theorem is used here.
-/

open scoped Topology InnerProductSpace RealInnerProductSpace

namespace ArchonPhysics.CanonicalRankFrequencyMarkedBroadenedLimit

open ArchonPhysics
open ArchonPhysics.BroadenedResonanceMeasure
open ArchonPhysics.CanonicalRankFrequencyMarkedFiniteMeasureWeakLimit
open ArchonPhysics.CanonicalRankFrequencyMarkedMeasure
open ArchonPhysics.CanonicalRankFrequencyMarkedResonanceLimit
open ArchonPhysics.NormalizedResonancePeakKernel
open ArchonPhysics.ResonanceKernelLipschitz
open ArchonPhysics.UniformCollisionDensityTransfer
open Filter MeasureTheory Topology

noncomputable section

variable {X I : Type*} [TopologicalSpace X]

/-- The fixed-time resonance peak composed with a continuous mismatch,
bundled as a bounded continuous test function. -/
def normalizedFiniteTimeResonanceWeightBCF
    (mismatch : X -> Real) (hmismatch : Continuous mismatch)
    (T : Real) (hT : 0 < T) : BoundedContinuousFunction X Real :=
  BoundedContinuousFunction.ofNormedAddCommGroup
    (fun x => normalizedFiniteTimeResonanceKernel (mismatch x) T)
    ((continuous_normalizedFiniteTimeResonanceKernel hT).comp hmismatch)
    (T / (2 * Real.pi))
    (fun x => by
      rw [Real.norm_eq_abs]
      exact abs_normalizedFiniteTimeResonanceKernel_le_height
        (mismatch x) hT)

@[simp]
theorem normalizedFiniteTimeResonanceWeightBCF_apply
    (mismatch : X -> Real) (hmismatch : Continuous mismatch)
    (T : Real) (hT : 0 < T) (x : X) :
    normalizedFiniteTimeResonanceWeightBCF mismatch hmismatch T hT x =
      normalizedFiniteTimeResonanceKernel (mismatch x) T := by
  rfl

variable [MeasurableSpace X] [OpensMeasurableSpace X]

/-- Multiplication by one fixed normalized finite-time resonance peak is a
continuous operation for weakly convergent finite measures. -/
theorem broadenedResonanceMeasure_tendsto_of_tendsto
    {l : Filter I} {mu : I -> FiniteMeasure X} {target : FiniteMeasure X}
    (hmu : Tendsto mu l (nhds target))
    (mismatch : X -> Real) (hmismatch : Continuous mismatch)
    (T : Real) (hT : 0 < T) :
    Tendsto
      (fun i => broadenedResonanceMeasure (mu i) mismatch
        hmismatch.measurable T hT)
      l
      (nhds (broadenedResonanceMeasure target mismatch
        hmismatch.measurable T hT)) := by
  apply (FiniteMeasure.tendsto_iff_forall_integral_tendsto).2
  intro test
  have hweighted :=
    (FiniteMeasure.tendsto_iff_forall_integral_tendsto).1 hmu
      (normalizedFiniteTimeResonanceWeightBCF
        mismatch hmismatch T hT * test)
  simpa only [integral_broadenedResonanceMeasure,
    BoundedContinuousFunction.coe_mul,
    normalizedFiniteTimeResonanceWeightBCF_apply,
    Pi.mul_apply, smul_eq_mul] using hweighted

variable {Omega : Type*} [MeasurableSpace Omega]

/-- The canonical deterministic raw marked collision measure weighted by the
fixed-time normalized resonance peak. -/
def canonicalRankFrequencyMarkedBroadenedPerSiteMeasureLimit
    (ensemble : IIDMassPhaseEnsemble Omega)
    (sign : Fin 3 -> ModalPhaseMismatch.InteractionSign)
    (T : Real) (hT : 0 < T) :
    FiniteMeasure (Fin 3 -> RankFrequencyMark) :=
  broadenedResonanceMeasure
    (canonicalRankFrequencyMarkedPerSiteMeasureLimit ensemble)
    (markedFrequencyMismatch sign)
    (measurable_markedFrequencyMismatch sign) T hT

/-- The finite-volume canonical raw marked measure with the same fixed-time
resonance weight. -/
def canonicalRankFrequencyTripleBroadenedPerSiteFiniteMeasure
    (ensemble : IIDMassPhaseEnsemble Omega) (N : Nat) (omega : Omega)
    (sign : Fin 3 -> ModalPhaseMismatch.InteractionSign)
    (T : Real) (hT : 0 < T) :
    FiniteMeasure (Fin 3 -> RankFrequencyMark) :=
  broadenedResonanceMeasure
    (canonicalRankFrequencyTriplePerSiteFiniteMeasure ensemble N omega)
    (markedFrequencyMismatch sign)
    (measurable_markedFrequencyMismatch sign) T hT

/-- Almost surely, for every fixed sign channel and positive observation
time, the complete canonical broadened marked sequence converges weakly to
the deterministic broadened per-site limit.  Marked size `n + 1` corresponds
to physical spectral volume `n + 3`. -/
theorem canonicalRankFrequencyTripleBroadenedPerSiteFiniteMeasure_tendsto_limit_ae
    (sign : Fin 3 -> ModalPhaseMismatch.InteractionSign) (T : Real) (hT : 0 < T) :
    ∀ᵐ omega ∂(RandomEnsemble.canonicalLaw),
      Tendsto
        (fun n : Nat =>
          canonicalRankFrequencyTripleBroadenedPerSiteFiniteMeasure
            canonicalIIDMassPhaseEnsemble (n + 1) omega sign T hT)
        atTop
        (nhds
          (canonicalRankFrequencyMarkedBroadenedPerSiteMeasureLimit
            canonicalIIDMassPhaseEnsemble sign T hT)) := by
  filter_upwards
    [canonicalRankFrequencyTriplePerSiteFiniteMeasure_tendsto_limit_ae]
      with omega hmarked
  exact broadenedResonanceMeasure_tendsto_of_tendsto hmarked
    (markedFrequencyMismatch sign)
    (continuous_markedFrequencyMismatch sign) T hT

/-- The total fixed-time broadened collision mass converges along the same
complete sequence. -/
theorem canonicalRankFrequencyTripleBroadenedPerSiteMass_tendsto_limit_ae
    (sign : Fin 3 -> ModalPhaseMismatch.InteractionSign) (T : Real) (hT : 0 < T) :
    ∀ᵐ omega ∂(RandomEnsemble.canonicalLaw),
      Tendsto
        (fun n : Nat =>
          (canonicalRankFrequencyTripleBroadenedPerSiteFiniteMeasure
            canonicalIIDMassPhaseEnsemble (n + 1) omega sign T hT).mass)
        atTop
        (nhds
          (canonicalRankFrequencyMarkedBroadenedPerSiteMeasureLimit
            canonicalIIDMassPhaseEnsemble sign T hT).mass) := by
  filter_upwards
    [canonicalRankFrequencyTripleBroadenedPerSiteFiniteMeasure_tendsto_limit_ae
      sign T hT] with omega hmeasure
  exact hmeasure.mass

end

end ArchonPhysics.CanonicalRankFrequencyMarkedBroadenedLimit
