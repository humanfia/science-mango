import Family8Grounding.Family8CanonicalBufferedGlobalRelativeScaleGainV1
import Family8Grounding.Family8NormalizedFirstCrossingFullRefinementAssemblyV1
import Mathlib.Tactic

/-!
# Relative scale gain for an arbitrary FirstCrossing buffered radius

The crossing witness stores an actual buffered radius, not necessarily the
canonical lower endpoint.  Its buffered lower inequality says that this
radius is at least the canonical lower endpoint, so the canonical
`tau/rho` gain transfers by denominator monotonicity.
-/

set_option autoImplicit false
set_option warningAsError true

open scoped ENNReal NNReal

namespace Family8FirstCrossingBufferedRelativeScaleGainV1

open Family8CanonicalBufferedGlobalRelativeScaleGainV1
open Family8CanonicalLowerBufferedScaleV4
open Family8KatzTaoFrostmanPropertiesV1
open Family8NormalizedCFDividingWitnessFiniteSelectionV4.CoherentStickyMultiscaleCover
open Family8NormalizedFirstCrossingFullRefinementAssemblyV1
open FamilyStickyDividingScalesFiniteStoppingV1
open FamilyStickyScaleChainCoherentIntervalProducerV1

noncomputable section

variable {delta : NNReal} {index : Type}
  [Fintype index] [DecidableEq index]
  {depth : Nat}

/-- Every actual buffered radius carried by a first-crossing witness retains
the same `epsilon^2` relative-scale gain as the lower canonical endpoint. -/
theorem firstCrossing_tau_div_rho_le_rpow_sq
    (D : ActualTubeDatum delta index) (hD : D.IsAdmissible)
    (C : CoherentStickyMultiscaleCover D.family)
    (S : FiniteScaleSequence delta depth)
    (epsilon : Real) (hepsilon : 0 ≤ epsilon)
    (eta : Nat → Real) (N : Nat)
    (W : FirstActualNormalizedCrossingWitness
      D hD C S epsilon hepsilon eta N) :
    S.tau W.m / W.rho ≤ delta ^ (epsilon ^ 2) := by
  have htau : 0 < S.tau W.m :=
    hD.delta_pos.trans_le (S.delta_le_tau W.m)
  have htheta : 0 < S.theta W.m :=
    htau.trans_le (S.tau_le_theta W.m)
  have hnotLarge := W.notLarge
  unfold FiniteScaleSequence.IsLarge at hnotLarge
  have hlong :
      (S.tau W.m : ENNReal) ≤
        (delta : ENNReal) ^ epsilon * (S.theta W.m : ENNReal) :=
    le_of_not_ge hnotLarge
  have hlower :
      canonicalLowerBufferedScale (S.tau W.m) (S.theta W.m) epsilon ≤
        W.rho := by
    rw [← ENNReal.coe_le_coe,
      canonicalLowerBufferedScale_eq_lowerEndpoint htau epsilon]
    simpa only [ENNReal.coe_mul,
      ENNReal.coe_rpow_of_ne_zero (div_pos htheta htau).ne'] using
        W.buffered.1
  have hlowerPos :
      0 < canonicalLowerBufferedScale
        (S.tau W.m) (S.theta W.m) epsilon := by
    rw [canonicalLowerBufferedScale_eq_lowerEndpoint htau epsilon]
    positivity
  calc
    S.tau W.m / W.rho ≤
        S.tau W.m /
          canonicalLowerBufferedScale
            (S.tau W.m) (S.theta W.m) epsilon := by
      exact div_le_div_of_nonneg_left (by positivity) hlowerPos hlower
    _ ≤ delta ^ (epsilon ^ 2) :=
      tau_div_canonicalLowerBufferedScale_le_rpow_sq
        hD.delta_pos (S.delta_le_tau W.m) (S.tau_le_theta W.m)
          hepsilon hlong

/-- ENNReal form used by relative Katz--Tao power envelopes. -/
theorem firstCrossing_coe_tau_div_rho_le_rpow_sq
    (D : ActualTubeDatum delta index) (hD : D.IsAdmissible)
    (C : CoherentStickyMultiscaleCover D.family)
    (S : FiniteScaleSequence delta depth)
    (epsilon : Real) (hepsilon : 0 ≤ epsilon)
    (eta : Nat → Real) (N : Nat)
    (W : FirstActualNormalizedCrossingWitness
      D hD C S epsilon hepsilon eta N) :
    (S.tau W.m : ENNReal) / (W.rho : ENNReal) ≤
      (delta : ENNReal) ^ (epsilon ^ 2) := by
  have hrho : 0 < W.rho :=
    (hD.delta_pos.trans_le (S.delta_le_tau W.m)).trans_le
      (actualDatum_tau_le_of_isBuffered
        D hD S hepsilon W.m W.rho W.buffered)
  rw [← ENNReal.coe_div hrho.ne',
    ← ENNReal.coe_rpow_of_ne_zero hD.delta_pos.ne',
    ENNReal.coe_le_coe]
  exact firstCrossing_tau_div_rho_le_rpow_sq
    D hD C S epsilon hepsilon eta N W

#print axioms firstCrossing_tau_div_rho_le_rpow_sq
#print axioms firstCrossing_coe_tau_div_rho_le_rpow_sq

end
end Family8FirstCrossingBufferedRelativeScaleGainV1
