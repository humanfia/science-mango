import ArchonPhysics.WeakCouplingLogarithmicKineticScale

/-!
# Weak-coupling kinetic accumulation for finite and growing A2 families

A fixed finite sum of expectation-level A2 channels remains negligible on the
kinetic scale because every summand tends to zero.  For a family whose active
channel set grows with the coupling, the required uniformity is different:
the logarithmic kinetic factor multiplied by the aggregate channel-cost
envelope must itself tend to zero.

The endpoint-aware actual-A2 adapters below retain one compact mismatch-chart
certificate per channel.  They neither construct those charts nor control
recollisions or the full nested history expansion.
-/

namespace ArchonPhysics.WeakCouplingA2ChannelFamilyKineticAccumulation

open ArchonPhysics
open ArchonPhysics.CanonicalIIDCoerciveIteratedA2ExpectationFourierDecay
open ArchonPhysics.CanonicalIIDCoerciveIteratedA2ExpectationFiniteTimeLogBound
open ArchonPhysics.PhyslibFPUTIteratedQuadraticSecondPicardCharacterFamily
open ArchonPhysics.WeakCouplingLogarithmicKineticScale
open ArchonPhysics.WeightedMismatchCompactIntervalFourierDecay
open Filter MeasureTheory
open scoped BigOperators Topology

noncomputable section

/-! ## Scalar logarithmic factor and one-channel bounds -/

/-- The common kinetic-logarithmic multiplier used for channel-cost
envelopes.  The extra `1` also pays the bounded near-time contribution. -/
def weakCouplingLogarithmicFactor (coupling : Real) : Real :=
  coupling ^ 2 *
    (1 + Real.log ((coupling ^ 2)⁻¹))

/-- The common kinetic-logarithmic multiplier tends to zero. -/
theorem tendsto_weakCouplingLogarithmicFactor_nhdsGT_zero :
    Tendsto weakCouplingLogarithmicFactor (𝓝[>] 0) (𝓝 0) := by
  change Tendsto
    (fun coupling : Real => coupling ^ 2 *
      (1 + Real.log ((coupling ^ 2)⁻¹)))
    (𝓝[>] 0) (𝓝 0)
  simpa only [one_mul] using
    (tendsto_square_mul_splitLog_nhdsGT_zero 1 1)

/-- On the weak-coupling region `0 < g < 1`, the logarithmic multiplier is
nonnegative. -/
theorem weakCouplingLogarithmicFactor_nonneg_of_pos_of_lt_one
    {coupling : Real} (hcoupling : 0 < coupling)
    (hcouplingOne : coupling < 1) :
    0 <= weakCouplingLogarithmicFactor coupling := by
  have hsquarePos : 0 < coupling ^ 2 := sq_pos_of_pos hcoupling
  have hsquareLeOne : coupling ^ 2 <= 1 := by
    have hproduct : 0 <= coupling * (1 - coupling) :=
      mul_nonneg hcoupling.le (sub_nonneg.mpr hcouplingOne.le)
    nlinarith
  have hinv : 1 <= (coupling ^ 2)⁻¹ :=
    (one_le_inv_iff₀).2 ⟨hsquarePos, hsquareLeOne⟩
  exact mul_nonneg (sq_nonneg coupling)
    (add_nonneg zero_le_one (Real.log_nonneg hinv))

/-- Pointwise split-logarithmic control of one kinetic accumulation.  This is
the finite-coupling estimate underlying the scalar limit theorem. -/
theorem weakCouplingKineticAccumulation_le_splitLog
    (signal : Real -> Complex) (nearCost farCost : Real)
    (hcontinuous : Continuous signal)
    (hnear : forall time, ‖signal time‖ <= nearCost)
    (hfar : forall time, time ≠ 0 ->
      ‖signal time‖ <= farCost / |time|)
    {coupling : Real} (hcoupling : 0 < coupling)
    (hcouplingOne : coupling < 1) :
    weakCouplingKineticAccumulation signal coupling <=
      coupling ^ 2 *
        (nearCost +
          farCost * Real.log ((coupling ^ 2)⁻¹)) := by
  have hsquarePos : 0 < coupling ^ 2 := sq_pos_of_pos hcoupling
  have hsquareLeOne : coupling ^ 2 <= 1 := by
    have hproduct : 0 <= coupling * (1 - coupling) :=
      mul_nonneg hcoupling.le (sub_nonneg.mpr hcouplingOne.le)
    nlinarith
  have htime : 1 <= weakCouplingKineticTime coupling := by
    unfold weakCouplingKineticTime
    exact (one_le_inv_iff₀).2 ⟨hsquarePos, hsquareLeOne⟩
  have hlogBound := intervalIntegral_norm_le_split_log
    signal nearCost farCost 1 (weakCouplingKineticTime coupling)
    hcontinuous hnear hfar one_pos htime
  have hscaled := mul_le_mul_of_nonneg_left hlogBound
    (sq_nonneg coupling)
  simpa [weakCouplingKineticAccumulation, weakCouplingKineticTime] using
    hscaled

/-- Combined per-channel cost for one endpoint-aware compact mismatch chart. -/
def compactCertificateKineticCost
    {Omega : Type*} [MeasurableSpace Omega]
    {measure : Measure Omega} {mismatch : Omega -> Real}
    {weight : Omega -> Complex}
    (certificate : WeightedMismatchCompactIntervalFourierCertificate
      measure mismatch weight) : Real :=
  certificate.densityL1Cost + certificate.variationCost

theorem compactCertificateKineticCost_nonneg
    {Omega : Type*} [MeasurableSpace Omega]
    {measure : Measure Omega} {mismatch : Omega -> Real}
    {weight : Omega -> Complex}
    (certificate : WeightedMismatchCompactIntervalFourierCertificate
      measure mismatch weight) :
    0 <= compactCertificateKineticCost certificate :=
  add_nonneg certificate.densityL1Cost_nonneg
    certificate.variationCost_nonneg

/-- A compact mismatch certificate pays its complete one-channel accumulation
by the common logarithmic factor times one explicit combined cost. -/
theorem
    WeightedMismatchCompactIntervalFourierCertificate.kineticAccumulation_le_logFactor_mul_cost
    {Omega : Type*} [MeasurableSpace Omega]
    {measure : Measure Omega} {mismatch : Omega -> Real}
    {weight : Omega -> Complex}
    (certificate : WeightedMismatchCompactIntervalFourierCertificate
      measure mismatch weight)
    {coupling : Real} (hcoupling : 0 < coupling)
    (hcouplingOne : coupling < 1) :
    weakCouplingKineticAccumulation
        (weightedMismatchExpectation measure mismatch weight) coupling <=
      weakCouplingLogarithmicFactor coupling *
        compactCertificateKineticCost certificate := by
  let logarithm := Real.log ((coupling ^ 2)⁻¹)
  have hsplit := weakCouplingKineticAccumulation_le_splitLog
    (weightedMismatchExpectation measure mismatch weight)
    certificate.densityL1Cost certificate.variationCost
    certificate.continuous_expectation
    certificate.norm_expectation_le_densityL1
    (fun time htime => certificate.norm_expectation_le_div_abs_time htime)
    hcoupling hcouplingOne
  have hsquarePos : 0 < coupling ^ 2 := sq_pos_of_pos hcoupling
  have hsquareLeOne : coupling ^ 2 <= 1 := by
    have hproduct : 0 <= coupling * (1 - coupling) :=
      mul_nonneg hcoupling.le (sub_nonneg.mpr hcouplingOne.le)
    nlinarith
  have hlogarithm : 0 <= logarithm := by
    exact Real.log_nonneg
      ((one_le_inv_iff₀).2 ⟨hsquarePos, hsquareLeOne⟩)
  have hextra : 0 <= coupling ^ 2 *
      (certificate.variationCost +
        certificate.densityL1Cost * logarithm) := by
    exact mul_nonneg (sq_nonneg coupling)
      (add_nonneg certificate.variationCost_nonneg
        (mul_nonneg certificate.densityL1Cost_nonneg hlogarithm))
  have hidentity :
      weakCouplingLogarithmicFactor coupling *
          compactCertificateKineticCost certificate =
        coupling ^ 2 *
            (certificate.densityL1Cost +
              certificate.variationCost * logarithm) +
          coupling ^ 2 *
            (certificate.variationCost +
              certificate.densityL1Cost * logarithm) := by
    unfold weakCouplingLogarithmicFactor compactCertificateKineticCost
    dsimp [logarithm]
    ring
  rw [hidentity]
  exact hsplit.trans (le_add_of_nonneg_right hextra)

/-! ## Fixed finite channel families -/

/-- A fixed finite sum of real-valued families tending to zero still tends
to zero. -/
theorem tendsto_finset_sum_nhds_zero
    {Index : Type*}
    (indices : Finset Index) (family : Index -> Real -> Real)
    (hfamily : ∀ index ∈ indices,
      Tendsto (family index) (𝓝[>] 0) (𝓝 0)) :
    Tendsto (fun coupling => ∑ index ∈ indices, family index coupling)
      (𝓝[>] 0) (𝓝 0) := by
  simpa using tendsto_finsetSum indices hfamily

/-- Fixed finite actual-A2 family with global `C^1 cap W^{1,1}` certificates. -/
theorem
    tendsto_finset_actualIteratedA2WeightedChannel_kineticAccumulation
    {Index Omega : Type*} [MeasurableSpace Omega]
    (indices : Finset Index) (ensemble : IIDMassPhaseEnsemble Omega)
    {N : Nat} [NeZero N]
    (channel : Index -> IteratedA2MismatchChannel)
    (weight : Index -> Omega -> Complex)
    (observed : Index -> Lattice.Site N)
    (term : Index -> IteratedQuadraticSecondPicardCharacterTerm N)
    (certificate : forall index,
      ActualIteratedA2WeightedChannelC1L1Certificate ensemble
        (channel index) (weight index) (observed index) (term index)) :
    Tendsto
      (fun coupling => ∑ index ∈ indices,
        weakCouplingKineticAccumulation
          (actualIteratedA2WeightedChannelExpectation ensemble
            (channel index) (weight index) (observed index) (term index))
          coupling)
      (𝓝[>] 0) (𝓝 0) := by
  apply tendsto_finset_sum_nhds_zero indices
  intro index _hindex
  exact tendsto_actualIteratedA2WeightedChannel_kineticAccumulation
    ensemble (channel index) (weight index) (observed index) (term index)
      (certificate index)

/-- Fixed finite actual-A2 family with endpoint-aware compact certificates. -/
theorem
    tendsto_finset_actualIteratedA2WeightedChannel_compact_kineticAccumulation
    {Index Omega : Type*} [MeasurableSpace Omega]
    (indices : Finset Index) (ensemble : IIDMassPhaseEnsemble Omega)
    {N : Nat} [NeZero N]
    (channel : Index -> IteratedA2MismatchChannel)
    (weight : Index -> Omega -> Complex)
    (observed : Index -> Lattice.Site N)
    (term : Index -> IteratedQuadraticSecondPicardCharacterTerm N)
    (certificate : forall index,
      ActualIteratedA2WeightedChannelCompactIntervalCertificate ensemble
        (channel index) (weight index) (observed index) (term index)) :
    Tendsto
      (fun coupling => ∑ index ∈ indices,
        weakCouplingKineticAccumulation
          (actualIteratedA2WeightedChannelExpectation ensemble
            (channel index) (weight index) (observed index) (term index))
          coupling)
      (𝓝[>] 0) (𝓝 0) := by
  apply tendsto_finset_sum_nhds_zero indices
  intro index _hindex
  exact tendsto_actualIteratedA2WeightedChannel_compact_kineticAccumulation
    ensemble (channel index) (weight index) (observed index) (term index)
      (certificate index)

/-! ## Growing-family uniformity criteria -/

/-- Abstract growing-family criterion.  The active finite set may depend on
the coupling.  The exact required uniformity is that the common kinetic-log
factor times an envelope for the aggregate active-channel cost tends to zero. -/
theorem tendsto_growingFinset_sum_of_logCostEnvelope
    {Index : Type*}
    (active : Real -> Finset Index)
    (family : Index -> Real -> Real) (cost : Index -> Real)
    (costEnvelope : Real -> Real)
    (hfamilyNonneg : forall index coupling,
      0 <= family index coupling)
    (hfamilyBound : ∀ᶠ coupling in 𝓝[>] (0 : Real),
      ∀ index ∈ active coupling,
        family index coupling <=
          weakCouplingLogarithmicFactor coupling * cost index)
    (hcostEnvelope : ∀ᶠ coupling in 𝓝[>] (0 : Real),
      (∑ index ∈ active coupling, cost index) <= costEnvelope coupling)
    (hscaledEnvelope : Tendsto
      (fun coupling =>
        weakCouplingLogarithmicFactor coupling * costEnvelope coupling)
      (𝓝[>] 0) (𝓝 0)) :
    Tendsto
      (fun coupling =>
        ∑ index ∈ active coupling, family index coupling)
      (𝓝[>] 0) (𝓝 0) := by
  have hnonneg : ∀ᶠ coupling in 𝓝[>] (0 : Real),
      0 <= ∑ index ∈ active coupling, family index coupling :=
    Eventually.of_forall fun coupling =>
      Finset.sum_nonneg fun index _hindex =>
        hfamilyNonneg index coupling
  have hfilter : (𝓝[>] (0 : Real)) <= 𝓝 0 := inf_le_left
  have hcouplingLtOne : ∀ᶠ coupling in 𝓝[>] (0 : Real), coupling < 1 :=
    hfilter (Iio_mem_nhds (show (0 : Real) < 1 by norm_num))
  have hupper : ∀ᶠ coupling in 𝓝[>] (0 : Real),
      (∑ index ∈ active coupling, family index coupling) <=
        weakCouplingLogarithmicFactor coupling * costEnvelope coupling := by
    filter_upwards [hfamilyBound, hcostEnvelope, self_mem_nhdsWithin,
      hcouplingLtOne] with coupling hfamilyAt hcostAt hcoupling
        hcouplingOne
    have hfactor : 0 <= weakCouplingLogarithmicFactor coupling :=
      weakCouplingLogarithmicFactor_nonneg_of_pos_of_lt_one
        hcoupling hcouplingOne
    calc
      (∑ index ∈ active coupling, family index coupling) <=
          ∑ index ∈ active coupling,
            weakCouplingLogarithmicFactor coupling * cost index :=
        Finset.sum_le_sum fun index hindex => hfamilyAt index hindex
      _ = weakCouplingLogarithmicFactor coupling *
          ∑ index ∈ active coupling, cost index := by
        rw [Finset.mul_sum]
      _ <= weakCouplingLogarithmicFactor coupling * costEnvelope coupling :=
        mul_le_mul_of_nonneg_left hcostAt hfactor
  exact squeeze_zero' hnonneg hupper hscaledEnvelope

/-- A count-times-uniform-cost version of the growing-family criterion.  This
is the explicit condition needed when lattice size or history multiplicity
causes the number of active channels to grow. -/
theorem tendsto_growingFinset_sum_of_card_mul_uniformCost
    {Index : Type*}
    (active : Real -> Finset Index)
    (family : Index -> Real -> Real) (cost : Index -> Real)
    (uniformCost : Real -> Real)
    (hfamilyNonneg : forall index coupling,
      0 <= family index coupling)
    (hfamilyBound : ∀ᶠ coupling in 𝓝[>] (0 : Real),
      ∀ index ∈ active coupling,
        family index coupling <=
          weakCouplingLogarithmicFactor coupling * cost index)
    (huniformCost : ∀ᶠ coupling in 𝓝[>] (0 : Real),
      ∀ index ∈ active coupling, cost index <= uniformCost coupling)
    (hscaledCardCost : Tendsto
      (fun coupling => weakCouplingLogarithmicFactor coupling *
        ((active coupling).card : Real) * uniformCost coupling)
      (𝓝[>] 0) (𝓝 0)) :
    Tendsto
      (fun coupling =>
        ∑ index ∈ active coupling, family index coupling)
      (𝓝[>] 0) (𝓝 0) := by
  apply tendsto_growingFinset_sum_of_logCostEnvelope active family cost
    (fun coupling =>
      ((active coupling).card : Real) * uniformCost coupling)
    hfamilyNonneg hfamilyBound
  · filter_upwards [huniformCost] with coupling hcost
    have hsum := Finset.sum_le_card_nsmul
      (active coupling) cost (uniformCost coupling) hcost
    simpa [nsmul_eq_mul] using hsum
  · simpa [mul_assoc] using hscaledCardCost

/-! ## Growing actual-A2 compact-certificate families -/

/-- Actual-A2 growing-family adapter with an explicit aggregate certificate
cost envelope.  Dependence of `active` on the coupling represents a growing
lattice, history set, or both. -/
theorem
    tendsto_growing_actualIteratedA2WeightedChannel_compact_of_costEnvelope
    {Index Omega : Type*} [MeasurableSpace Omega]
    (active : Real -> Finset Index)
    (ensemble : IIDMassPhaseEnsemble Omega)
    {N : Nat} [NeZero N]
    (channel : Index -> IteratedA2MismatchChannel)
    (weight : Index -> Omega -> Complex)
    (observed : Index -> Lattice.Site N)
    (term : Index -> IteratedQuadraticSecondPicardCharacterTerm N)
    (certificate : forall index,
      ActualIteratedA2WeightedChannelCompactIntervalCertificate ensemble
        (channel index) (weight index) (observed index) (term index))
    (costEnvelope : Real -> Real)
    (hcostEnvelope : ∀ᶠ coupling in 𝓝[>] (0 : Real),
      (∑ index ∈ active coupling,
        compactCertificateKineticCost (certificate index)) <=
          costEnvelope coupling)
    (hscaledEnvelope : Tendsto
      (fun coupling =>
        weakCouplingLogarithmicFactor coupling * costEnvelope coupling)
      (𝓝[>] 0) (𝓝 0)) :
    Tendsto
      (fun coupling => ∑ index ∈ active coupling,
        weakCouplingKineticAccumulation
          (actualIteratedA2WeightedChannelExpectation ensemble
            (channel index) (weight index) (observed index) (term index))
          coupling)
      (𝓝[>] 0) (𝓝 0) := by
  apply tendsto_growingFinset_sum_of_logCostEnvelope active
    (fun index coupling =>
      weakCouplingKineticAccumulation
        (actualIteratedA2WeightedChannelExpectation ensemble
          (channel index) (weight index) (observed index) (term index))
        coupling)
    (fun index => compactCertificateKineticCost (certificate index))
    costEnvelope
  · intro index coupling
    exact weakCouplingKineticAccumulation_nonneg _ coupling
  · have hfilter : (𝓝[>] (0 : Real)) <= 𝓝 0 := inf_le_left
    have hcouplingLtOne : ∀ᶠ coupling in 𝓝[>] (0 : Real), coupling < 1 :=
      hfilter (Iio_mem_nhds (show (0 : Real) < 1 by norm_num))
    filter_upwards [self_mem_nhdsWithin, hcouplingLtOne] with
        coupling hcoupling hcouplingOne
    intro index _hindex
    exact
      WeightedMismatchCompactIntervalFourierCertificate.kineticAccumulation_le_logFactor_mul_cost
        (certificate index) hcoupling hcouplingOne
  · exact hcostEnvelope
  · exact hscaledEnvelope

/-- Actual-A2 count-times-uniform-cost criterion.  The displayed limit is the
precise additional uniformity requirement beyond per-channel Fourier decay. -/
theorem
    tendsto_growing_actualIteratedA2WeightedChannel_compact_of_card_uniformCost
    {Index Omega : Type*} [MeasurableSpace Omega]
    (active : Real -> Finset Index)
    (ensemble : IIDMassPhaseEnsemble Omega)
    {N : Nat} [NeZero N]
    (channel : Index -> IteratedA2MismatchChannel)
    (weight : Index -> Omega -> Complex)
    (observed : Index -> Lattice.Site N)
    (term : Index -> IteratedQuadraticSecondPicardCharacterTerm N)
    (certificate : forall index,
      ActualIteratedA2WeightedChannelCompactIntervalCertificate ensemble
        (channel index) (weight index) (observed index) (term index))
    (uniformCost : Real -> Real)
    (huniformCost : ∀ᶠ coupling in 𝓝[>] (0 : Real),
      ∀ index ∈ active coupling,
        compactCertificateKineticCost (certificate index) <=
          uniformCost coupling)
    (hscaledCardCost : Tendsto
      (fun coupling => weakCouplingLogarithmicFactor coupling *
        ((active coupling).card : Real) * uniformCost coupling)
      (𝓝[>] 0) (𝓝 0)) :
    Tendsto
      (fun coupling => ∑ index ∈ active coupling,
        weakCouplingKineticAccumulation
          (actualIteratedA2WeightedChannelExpectation ensemble
            (channel index) (weight index) (observed index) (term index))
          coupling)
      (𝓝[>] 0) (𝓝 0) := by
  apply tendsto_growingFinset_sum_of_card_mul_uniformCost active
    (fun index coupling =>
      weakCouplingKineticAccumulation
        (actualIteratedA2WeightedChannelExpectation ensemble
          (channel index) (weight index) (observed index) (term index))
        coupling)
    (fun index => compactCertificateKineticCost (certificate index))
    uniformCost
  · intro index coupling
    exact weakCouplingKineticAccumulation_nonneg _ coupling
  · have hfilter : (𝓝[>] (0 : Real)) <= 𝓝 0 := inf_le_left
    have hcouplingLtOne : ∀ᶠ coupling in 𝓝[>] (0 : Real), coupling < 1 :=
      hfilter (Iio_mem_nhds (show (0 : Real) < 1 by norm_num))
    filter_upwards [self_mem_nhdsWithin, hcouplingLtOne] with
        coupling hcoupling hcouplingOne
    intro index _hindex
    exact
      WeightedMismatchCompactIntervalFourierCertificate.kineticAccumulation_le_logFactor_mul_cost
        (certificate index) hcoupling hcouplingOne
  · exact huniformCost
  · exact hscaledCardCost

end

end ArchonPhysics.WeakCouplingA2ChannelFamilyKineticAccumulation
