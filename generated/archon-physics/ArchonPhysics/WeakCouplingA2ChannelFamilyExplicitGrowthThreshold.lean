import ArchonPhysics.WeakCouplingA2ChannelFamilyKineticAccumulation

/-!
# Explicit power-growth threshold for weak-coupling A2 channel families

The abstract growing-family criterion asks that the kinetic logarithmic
factor times `cardinality * uniformCost` tend to zero.  This module supplies
an explicit sufficient condition.  If the active-channel cardinality grows
at most like `g ^ (-p)` and the uniform per-channel cost grows at most like
`g ^ (-q)`, their total growth is harmless whenever `p + q < 2`.

The statement is only an asymptotic envelope theorem.  It does not construct
a coupling-dependent lattice size, an active channel family, or the Fourier
certificates whose costs enter that envelope.
-/

namespace ArchonPhysics.WeakCouplingA2ChannelFamilyExplicitGrowthThreshold

open ArchonPhysics.WeakCouplingA2ChannelFamilyKineticAccumulation
open Filter
open scoped BigOperators Topology

noncomputable section

/-! ## Scalar threshold -/

/-- The kinetic logarithmic factor tolerates every real power-growth exponent
strictly below two. -/
theorem tendsto_logarithmicFactor_mul_rpow_neg_of_lt_two
    (exponent : Real) (hexponent : exponent < 2) :
    Tendsto
      (fun coupling : Real =>
        weakCouplingLogarithmicFactor coupling *
          coupling ^ (-exponent))
      (𝓝[>] 0) (𝓝 0) := by
  let gap : Real := 2 - exponent
  have hgap : 0 < gap := sub_pos.mpr hexponent
  have hpowerFull : Tendsto (fun coupling : Real => coupling ^ gap)
      (𝓝 0) (𝓝 0) := by
    simpa [gap, Real.zero_rpow hgap.ne'] using
      (Real.continuous_rpow_const hgap.le).tendsto 0
  have hfilter : (𝓝[>] (0 : Real)) <= 𝓝 0 := inf_le_left
  have hpower : Tendsto (fun coupling : Real => coupling ^ gap)
      (𝓝[>] 0) (𝓝 0) := hpowerFull.mono_left hfilter
  have hlogPower : Tendsto
      (fun coupling : Real => Real.log coupling * coupling ^ gap)
      (𝓝[>] 0) (𝓝 0) :=
    tendsto_log_mul_rpow_nhdsGT_zero hgap
  have hconstant : Tendsto (fun _coupling : Real => (-2 : Real))
      (𝓝[>] 0) (𝓝 (-2)) := tendsto_const_nhds
  have hscaledLog : Tendsto
      (fun coupling : Real =>
        (-2 : Real) * (Real.log coupling * coupling ^ gap))
      (𝓝[>] 0) (𝓝 0) := by
    simpa using hconstant.mul hlogPower
  have hsum : Tendsto
      (fun coupling : Real =>
        coupling ^ gap +
          (-2 : Real) * (Real.log coupling * coupling ^ gap))
      (𝓝[>] 0) (𝓝 0) := by
    simpa using hpower.add hscaledLog
  apply hsum.congr'
  filter_upwards [self_mem_nhdsWithin] with coupling hcoupling
  have hcouplingPos : 0 < coupling := hcoupling
  have hpow : coupling ^ (2 : Real) * coupling ^ (-exponent) =
      coupling ^ gap := by
    rw [<- Real.rpow_add hcouplingPos]
    congr 1
  unfold weakCouplingLogarithmicFactor
  rw [Real.log_inv, Real.log_pow, <- Real.rpow_two, <- hpow]
  ring

/-- Separate cardinality and per-channel exponents may be added: only their
sum has to remain strictly below the kinetic exponent two. -/
theorem tendsto_logarithmicFactor_mul_rpow_neg_add_of_add_lt_two
    (cardExponent costExponent : Real)
    (hexponents : cardExponent + costExponent < 2) :
    Tendsto
      (fun coupling : Real =>
        weakCouplingLogarithmicFactor coupling *
          coupling ^ (-(cardExponent + costExponent)))
      (𝓝[>] 0) (𝓝 0) :=
  tendsto_logarithmicFactor_mul_rpow_neg_of_lt_two
    (cardExponent + costExponent) hexponents

/-! ## Cardinality-times-cost envelope -/

/-- Explicit power envelopes for cardinality and uniform per-channel cost
imply the scaled aggregate-cost limit required by the growing-family theorem.
No concrete `active` family is constructed here. -/
theorem tendsto_logarithmicFactor_mul_card_mul_uniformCost_of_rpow_envelopes
    {Index : Type*}
    (active : Real -> Finset Index) (uniformCost : Real -> Real)
    (cardExponent costExponent cardConstant costConstant : Real)
    (hexponents : cardExponent + costExponent < 2)
    (hcardConstant : 0 <= cardConstant)
    (hcard : ∀ᶠ coupling in 𝓝[>] (0 : Real),
      ((active coupling).card : Real) <=
        cardConstant * coupling ^ (-cardExponent))
    (hcostNonneg : ∀ᶠ coupling in 𝓝[>] (0 : Real),
      0 <= uniformCost coupling)
    (hcost : ∀ᶠ coupling in 𝓝[>] (0 : Real),
      uniformCost coupling <=
        costConstant * coupling ^ (-costExponent)) :
    Tendsto
      (fun coupling =>
        weakCouplingLogarithmicFactor coupling *
          ((active coupling).card : Real) * uniformCost coupling)
      (𝓝[>] 0) (𝓝 0) := by
  let upper : Real -> Real := fun coupling =>
    weakCouplingLogarithmicFactor coupling *
      (cardConstant * coupling ^ (-cardExponent)) *
        (costConstant * coupling ^ (-costExponent))
  have hbase :=
    tendsto_logarithmicFactor_mul_rpow_neg_add_of_add_lt_two
      cardExponent costExponent hexponents
  have hconstants : Tendsto
      (fun _coupling : Real => cardConstant * costConstant)
      (𝓝[>] 0) (𝓝 (cardConstant * costConstant)) :=
    tendsto_const_nhds
  have hupper : Tendsto upper (𝓝[>] 0) (𝓝 0) := by
    have hproduct : Tendsto
        (fun coupling : Real =>
          (cardConstant * costConstant) *
            (weakCouplingLogarithmicFactor coupling *
              coupling ^ (-(cardExponent + costExponent))))
        (𝓝[>] 0) (𝓝 0) := by
      simpa only [mul_zero] using hconstants.mul hbase
    apply hproduct.congr'
    filter_upwards [self_mem_nhdsWithin] with coupling hcoupling
    have hcouplingPos : 0 < coupling := hcoupling
    have hrpow :
        coupling ^ (-cardExponent) * coupling ^ (-costExponent) =
          coupling ^ (-(cardExponent + costExponent)) := by
      rw [<- Real.rpow_add hcouplingPos]
      congr 1
      ring
    dsimp [upper]
    rw [<- hrpow]
    ring
  have hfilter : (𝓝[>] (0 : Real)) <= 𝓝 0 := inf_le_left
  have hcouplingLtOne : ∀ᶠ coupling in 𝓝[>] (0 : Real),
      coupling < 1 :=
    hfilter (Iio_mem_nhds (show (0 : Real) < 1 by norm_num))
  have hlower : ∀ᶠ coupling in 𝓝[>] (0 : Real),
      0 <= weakCouplingLogarithmicFactor coupling *
        ((active coupling).card : Real) * uniformCost coupling := by
    filter_upwards [self_mem_nhdsWithin, hcouplingLtOne, hcostNonneg] with
      coupling hcoupling hcouplingOne hcostAt
    exact mul_nonneg
      (mul_nonneg
        (weakCouplingLogarithmicFactor_nonneg_of_pos_of_lt_one
          hcoupling hcouplingOne)
        (Nat.cast_nonneg (active coupling).card))
      hcostAt
  have hbound : ∀ᶠ coupling in 𝓝[>] (0 : Real),
      weakCouplingLogarithmicFactor coupling *
          ((active coupling).card : Real) * uniformCost coupling <=
        upper coupling := by
    filter_upwards [self_mem_nhdsWithin, hcouplingLtOne, hcard,
      hcostNonneg, hcost] with coupling hcoupling hcouplingOne hcardAt
        hcostNonnegAt hcostAt
    have hfactor : 0 <= weakCouplingLogarithmicFactor coupling :=
      weakCouplingLogarithmicFactor_nonneg_of_pos_of_lt_one
        hcoupling hcouplingOne
    have hcardEnvelopeNonneg :
        0 <= cardConstant * coupling ^ (-cardExponent) :=
      mul_nonneg hcardConstant (Real.rpow_nonneg hcoupling.le _)
    calc
      weakCouplingLogarithmicFactor coupling *
          ((active coupling).card : Real) * uniformCost coupling <=
        weakCouplingLogarithmicFactor coupling *
          (cardConstant * coupling ^ (-cardExponent)) *
            uniformCost coupling :=
        mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_left hcardAt hfactor) hcostNonnegAt
      _ <= weakCouplingLogarithmicFactor coupling *
          (cardConstant * coupling ^ (-cardExponent)) *
            (costConstant * coupling ^ (-costExponent)) :=
        mul_le_mul_of_nonneg_left hcostAt
          (mul_nonneg hfactor hcardEnvelopeNonneg)
      _ = upper coupling := rfl
  exact squeeze_zero' hlower hbound hupper

/-! ## Direct growing-family corollary -/

/-- The existing growing-family criterion with its final abstract limit
discharged by explicit real-power cardinality and cost envelopes. -/
theorem tendsto_growingFinset_sum_of_rpow_card_uniformCost
    {Index : Type*}
    (active : Real -> Finset Index)
    (family : Index -> Real -> Real) (cost : Index -> Real)
    (uniformCost : Real -> Real)
    (cardExponent costExponent cardConstant costConstant : Real)
    (hexponents : cardExponent + costExponent < 2)
    (hcardConstant : 0 <= cardConstant)
    (hfamilyNonneg : forall index coupling,
      0 <= family index coupling)
    (hfamilyBound : ∀ᶠ coupling in 𝓝[>] (0 : Real),
      ∀ index ∈ active coupling,
        family index coupling <=
          weakCouplingLogarithmicFactor coupling * cost index)
    (huniformCost : ∀ᶠ coupling in 𝓝[>] (0 : Real),
      ∀ index ∈ active coupling,
        cost index <= uniformCost coupling)
    (hcard : ∀ᶠ coupling in 𝓝[>] (0 : Real),
      ((active coupling).card : Real) <=
        cardConstant * coupling ^ (-cardExponent))
    (hcostNonneg : ∀ᶠ coupling in 𝓝[>] (0 : Real),
      0 <= uniformCost coupling)
    (hcost : ∀ᶠ coupling in 𝓝[>] (0 : Real),
      uniformCost coupling <=
        costConstant * coupling ^ (-costExponent)) :
    Tendsto
      (fun coupling =>
        ∑ index ∈ active coupling, family index coupling)
      (𝓝[>] 0) (𝓝 0) := by
  apply tendsto_growingFinset_sum_of_card_mul_uniformCost active family cost
    uniformCost hfamilyNonneg hfamilyBound huniformCost
  exact
    tendsto_logarithmicFactor_mul_card_mul_uniformCost_of_rpow_envelopes
      active uniformCost cardExponent costExponent cardConstant costConstant
      hexponents hcardConstant hcard hcostNonneg hcost

end

end ArchonPhysics.WeakCouplingA2ChannelFamilyExplicitGrowthThreshold
