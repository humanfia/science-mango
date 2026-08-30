import ArchonPhysics.CanonicalIIDCoerciveIteratedA2ExternalWeakCouplingScaling
import ArchonPhysics.WeakCouplingA2ChannelFamilyKineticAccumulation

/-!
# External-`g` finite-volume families of actual A2 channels

The earlier finite-family adapter fixes one lattice volume `N` before the
channel index is introduced.  That type is too restrictive for a kinetic
limit in which the active finite volume grows as the external `g` decreases.

Here every channel datum carries its own positive finite volume.  All data
are nevertheless sampled from one fixed infinite `IIDMassPhaseEnsemble`;
the existing `restrictPositiveMass` operation selects the finite prefix
needed by each datum.

Each datum holds the standard alpha coefficient `kappa` fixed.  The separate
weak parameter `g` supplies the extracted external factor `g^2`, and the
kinetic window has length `g^-2`.  Fixed and `g`-dependent finite sums are
controlled by compact Fourier certificates at the fixed `kappa` values.

This interface does not construct the nonlinear mismatch charts, bound
their costs uniformly in volume, control recollisions, or derive the full
Hamiltonian-to-kinetic limit.
-/

namespace ArchonPhysics.DependentVolumeActualA2FamilyKineticAccumulation

open ArchonPhysics
open ArchonPhysics.CanonicalIIDCoerciveIteratedA2ExpectationFourierDecay
open ArchonPhysics.CanonicalIIDCoerciveIteratedA2ExternalWeakCouplingScaling
open ArchonPhysics.PhyslibFPUTIteratedQuadraticSecondPicardCharacterFamily
open ArchonPhysics.WeakCouplingA2ChannelFamilyKineticAccumulation
open ArchonPhysics.WeakCouplingLogarithmicKineticScale
open ArchonPhysics.WeightedMismatchCompactIntervalFourierDecay
open
  WeakCouplingA2ChannelFamilyKineticAccumulation.WeightedMismatchCompactIntervalFourierCertificate
open Filter
open scoped BigOperators Topology

noncomputable section

/-! ## One channel whose finite volume is part of the datum -/

/-- One actual iterated-A2 channel at a positive finite volume.  The volume
is a field, so different indices in one family may genuinely use different
site types, fixed `kappa` values, and second-Picard terms. -/
structure DependentActualA2ChannelDatum (Omega : Type*) where
  N : Nat
  N_pos : 0 < N
  channel : IteratedA2MismatchChannel
  kappa : Real
  radius : Omega -> Lattice.Site N -> Real
  observed : Lattice.Site N
  term : IteratedQuadraticSecondPicardCharacterTerm N

namespace DependentActualA2ChannelDatum

variable {Omega : Type*}

/-- The positivity stored in a datum supplies the finite-volume typeclass
needed by the physical eigenmode definitions. -/
theorem neZero (datum : DependentActualA2ChannelDatum Omega) : NeZero datum.N :=
  ⟨Nat.ne_of_gt datum.N_pos⟩

variable [MeasurableSpace Omega]

/-- Fixed-`kappa` expectation signal for one dependent-volume datum. -/
def fixedKappaStaticWeightSignal
    (datum : DependentActualA2ChannelDatum Omega)
    (ensemble : IIDMassPhaseEnsemble Omega) : Real -> Complex :=
  letI : NeZero datum.N := datum.neZero
  actualIteratedA2StaticWeightedChannelExpectation ensemble datum.channel
    datum.kappa datum.radius datum.observed datum.term

/-- Externally scaled kinetic-window accumulation.  Here `kappa` is fixed in
the datum, while `g` is the weak parameter multiplying the perturbation. -/
def externalWeakCouplingAccumulation
    (datum : DependentActualA2ChannelDatum Omega)
    (ensemble : IIDMassPhaseEnsemble Omega) (g : Real) : Real :=
  letI : NeZero datum.N := datum.neZero
  actualIteratedA2StaticExternalWeakCouplingAccumulation ensemble datum.channel
    datum.kappa datum.radius datum.observed datum.term g

/-- Compact Fourier certificate at the fixed `kappa` of one datum, with its
own finite volume restored locally. -/
abbrev CompactCertificate
    (datum : DependentActualA2ChannelDatum Omega)
    (ensemble : IIDMassPhaseEnsemble Omega) : Type :=
  letI : NeZero datum.N := datum.neZero
  ActualIteratedA2WeightedChannelCompactIntervalCertificate ensemble
    datum.channel
    (actualIteratedA2StaticWeightSample ensemble datum.kappa datum.radius
      datum.observed
      datum.term)
    datum.observed datum.term

/-- Explicit combined near-time and Fourier-variation cost of a datum. -/
def compactKineticCost
    (datum : DependentActualA2ChannelDatum Omega)
    (ensemble : IIDMassPhaseEnsemble Omega)
    (certificate : datum.CompactCertificate ensemble) : Real :=
  compactCertificateKineticCost certificate

/-- Exact bridge from the physical external `g^2 A2(kappa)` accumulation to
the abstract kinetically weighted fixed-`kappa` signal. -/
theorem externalWeakCouplingAccumulation_eq_kinetic
    (datum : DependentActualA2ChannelDatum Omega)
    (ensemble : IIDMassPhaseEnsemble Omega) (g : Real) :
    datum.externalWeakCouplingAccumulation ensemble g =
      weakCouplingKineticAccumulation
        (datum.fixedKappaStaticWeightSignal ensemble) g := by
  let _ : NeZero datum.N := datum.neZero
  simpa [externalWeakCouplingAccumulation, fixedKappaStaticWeightSignal] using
    actualIteratedA2StaticExternalWeakCouplingAccumulation_eq_kinetic ensemble
      datum.channel datum.kappa datum.radius datum.observed datum.term g

/-- A dependent-volume externally scaled accumulation is nonnegative. -/
theorem externalWeakCouplingAccumulation_nonneg
    (datum : DependentActualA2ChannelDatum Omega)
    (ensemble : IIDMassPhaseEnsemble Omega) (g : Real) :
    0 <= datum.externalWeakCouplingAccumulation ensemble g := by
  rw [datum.externalWeakCouplingAccumulation_eq_kinetic ensemble g]
  exact weakCouplingKineticAccumulation_nonneg _ g

/-- One compact certificate bounds the external-`g` accumulation by the common
kinetic logarithmic factor times its explicit certificate cost. -/
theorem externalWeakCouplingAccumulation_le_logFactor_mul_cost
    (datum : DependentActualA2ChannelDatum Omega)
    (ensemble : IIDMassPhaseEnsemble Omega)
    (certificate : datum.CompactCertificate ensemble)
    {g : Real} (hg : 0 < g)
    (hgOne : g < 1) :
    datum.externalWeakCouplingAccumulation ensemble g <=
      weakCouplingLogarithmicFactor g *
        datum.compactKineticCost ensemble certificate := by
  rw [datum.externalWeakCouplingAccumulation_eq_kinetic ensemble g]
  let : NeZero datum.N := datum.neZero
  exact kineticAccumulation_le_logFactor_mul_cost certificate hg
    hgOne

/-- At every fixed finite volume, a supplied compact mismatch certificate
makes the fixed-`kappa` channel negligible on the external `g^-2` window. -/
theorem tendsto_externalWeakCouplingAccumulation_compact
    (datum : DependentActualA2ChannelDatum Omega)
    (ensemble : IIDMassPhaseEnsemble Omega)
    (certificate : datum.CompactCertificate ensemble) :
    Tendsto (datum.externalWeakCouplingAccumulation ensemble)
      (𝓝[>] 0) (𝓝 0) := by
  let : NeZero datum.N := datum.neZero
  exact
    tendsto_actualIteratedA2StaticExternalWeakCouplingAccumulation_compact
      ensemble datum.channel datum.kappa datum.radius datum.observed datum.term
        certificate

end DependentActualA2ChannelDatum

/-! ## Fixed and growing families with genuinely varying volumes -/

/-- A fixed finite family may contain channels from several different
finite volumes because volume is stored inside each datum. -/
theorem tendsto_finset_dependentActualA2ExternalWeakCouplingAccumulation
    {Index Omega : Type*} [MeasurableSpace Omega]
    (indices : Finset Index) (ensemble : IIDMassPhaseEnsemble Omega)
    (datum : Index -> DependentActualA2ChannelDatum Omega)
    (certificate : forall index,
      (datum index).CompactCertificate ensemble) :
    Tendsto
      (fun g => ∑ index ∈ indices,
        (datum index).externalWeakCouplingAccumulation ensemble g)
      (𝓝[>] 0) (𝓝 0) := by
  apply tendsto_finset_sum_nhds_zero indices
  intro index _hindex
  exact (datum index).tendsto_externalWeakCouplingAccumulation_compact ensemble
    (certificate index)

/-- External-`g`-dependent active-family criterion with an aggregate cost
envelope.  The active channels may have different volumes. -/
theorem
    tendsto_growing_dependentActualA2ExternalWeakCouplingAccumulation_of_costEnvelope
    {Index Omega : Type*} [MeasurableSpace Omega]
    (active : Real -> Finset Index) (ensemble : IIDMassPhaseEnsemble Omega)
    (datum : Index -> DependentActualA2ChannelDatum Omega)
    (certificate : forall index,
      (datum index).CompactCertificate ensemble)
    (costEnvelope : Real -> Real)
    (hcostEnvelope : ∀ᶠ g in 𝓝[>] (0 : Real),
      (∑ index ∈ active g,
        (datum index).compactKineticCost ensemble (certificate index)) <=
          costEnvelope g)
    (hscaledEnvelope : Tendsto
      (fun g =>
        weakCouplingLogarithmicFactor g * costEnvelope g)
      (𝓝[>] 0) (𝓝 0)) :
    Tendsto
      (fun g => ∑ index ∈ active g,
        (datum index).externalWeakCouplingAccumulation ensemble g)
      (𝓝[>] 0) (𝓝 0) := by
  apply tendsto_growingFinset_sum_of_logCostEnvelope active
    (fun index g =>
      (datum index).externalWeakCouplingAccumulation ensemble g)
    (fun index =>
      (datum index).compactKineticCost ensemble (certificate index))
    costEnvelope
  · intro index g
    exact (datum index).externalWeakCouplingAccumulation_nonneg ensemble g
  · have hfilter : (𝓝[>] (0 : Real)) <= 𝓝 0 := inf_le_left
    have hgLtOne : ∀ᶠ g in 𝓝[>] (0 : Real), g < 1 :=
      hfilter (Iio_mem_nhds (show (0 : Real) < 1 by norm_num))
    filter_upwards [self_mem_nhdsWithin, hgLtOne] with
        g hg hgOne
    intro index _hindex
    exact
      (datum index).externalWeakCouplingAccumulation_le_logFactor_mul_cost
        ensemble (certificate index) hg hgOne
  · exact hcostEnvelope
  · exact hscaledEnvelope

/-- Count-times-uniform-cost version of the growing dependent-volume
criterion.  This displays the exact volume/channel-growth condition still
needed from model-specific chart estimates. -/
theorem
    tendsto_growing_dependentActualA2ExternalWeakCouplingAccumulation_of_card_uniformCost
    {Index Omega : Type*} [MeasurableSpace Omega]
    (active : Real -> Finset Index) (ensemble : IIDMassPhaseEnsemble Omega)
    (datum : Index -> DependentActualA2ChannelDatum Omega)
    (certificate : forall index,
      (datum index).CompactCertificate ensemble)
    (uniformCost : Real -> Real)
    (huniformCost : ∀ᶠ g in 𝓝[>] (0 : Real),
      ∀ index ∈ active g,
        (datum index).compactKineticCost ensemble (certificate index) <=
          uniformCost g)
    (hscaledCardCost : Tendsto
      (fun g => weakCouplingLogarithmicFactor g *
        ((active g).card : Real) * uniformCost g)
      (𝓝[>] 0) (𝓝 0)) :
    Tendsto
      (fun g => ∑ index ∈ active g,
        (datum index).externalWeakCouplingAccumulation ensemble g)
      (𝓝[>] 0) (𝓝 0) := by
  apply tendsto_growingFinset_sum_of_card_mul_uniformCost active
    (fun index g =>
      (datum index).externalWeakCouplingAccumulation ensemble g)
    (fun index =>
      (datum index).compactKineticCost ensemble (certificate index))
    uniformCost
  · intro index g
    exact (datum index).externalWeakCouplingAccumulation_nonneg ensemble g
  · have hfilter : (𝓝[>] (0 : Real)) <= 𝓝 0 := inf_le_left
    have hgLtOne : ∀ᶠ g in 𝓝[>] (0 : Real), g < 1 :=
      hfilter (Iio_mem_nhds (show (0 : Real) < 1 by norm_num))
    filter_upwards [self_mem_nhdsWithin, hgLtOne] with
        g hg hgOne
    intro index _hindex
    exact
      (datum index).externalWeakCouplingAccumulation_le_logFactor_mul_cost
        ensemble (certificate index) hg hgOne
  · exact huniformCost
  · exact hscaledCardCost

/-! ## Transparent volume-schedule adapter -/

/-- Every channel active at external `g` belongs to the scheduled finite
volume.  The schedule itself need not be constant. -/
def ActiveFamilyMatchesVolumeSchedule
    {Index Omega : Type*}
    (volumeSchedule : Real -> Nat) (active : Real -> Finset Index)
    (datum : Index -> DependentActualA2ChannelDatum Omega) : Prop :=
  forall g index, index ∈ active g ->
    (datum index).N = volumeSchedule g

/-- A schedule-facing adapter for the count-times-uniform-cost theorem.
The matching premise makes the varying finite volume explicit in the type.
No assertion that `volumeSchedule g -> infinity` is smuggled into the
proof; such a thermodynamic-limit statement must be supplied separately. -/
theorem
    tendsto_volumeScheduled_dependentActualA2ExternalWeakCouplingAccumulation
    {Index Omega : Type*} [MeasurableSpace Omega]
    (volumeSchedule : Real -> Nat) (active : Real -> Finset Index)
    (ensemble : IIDMassPhaseEnsemble Omega)
    (datum : Index -> DependentActualA2ChannelDatum Omega)
    (_hvolume : ActiveFamilyMatchesVolumeSchedule volumeSchedule active datum)
    (certificate : forall index,
      (datum index).CompactCertificate ensemble)
    (uniformCost : Real -> Real)
    (huniformCost : ∀ᶠ g in 𝓝[>] (0 : Real),
      ∀ index ∈ active g,
        (datum index).compactKineticCost ensemble (certificate index) <=
          uniformCost g)
    (hscaledCardCost : Tendsto
      (fun g => weakCouplingLogarithmicFactor g *
        ((active g).card : Real) * uniformCost g)
      (𝓝[>] 0) (𝓝 0)) :
    Tendsto
      (fun g => ∑ index ∈ active g,
        (datum index).externalWeakCouplingAccumulation ensemble g)
      (𝓝[>] 0) (𝓝 0) :=
  tendsto_growing_dependentActualA2ExternalWeakCouplingAccumulation_of_card_uniformCost
    active ensemble datum certificate uniformCost huniformCost
      hscaledCardCost

end

end ArchonPhysics.DependentVolumeActualA2FamilyKineticAccumulation
