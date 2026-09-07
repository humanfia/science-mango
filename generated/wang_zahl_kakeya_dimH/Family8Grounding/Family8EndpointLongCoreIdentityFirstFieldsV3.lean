import Family8Grounding.Family8EndpointIdentityCoreSelectorV2
import Family8Grounding.Family8ThreeScaleFrostmanFactorAlgebraV2
import Mathlib.Tactic

/-!
# Identity first-factor fields on the endpoint long core, V3

The endpoint scale sequence has one interval and its lower endpoint is the
source scale.  Thus the first Section-8 factor is literally one.  This file
packages the exact `firstCount`, `firstAverage`, and `firstLoss` fields used by
the long-core data record; no analytic estimate or small-scale premise is
needed.  V1 and V2 are failed dependent-parsing drafts and are not imported.
-/

set_option autoImplicit false
set_option warningAsError true

open scoped ENNReal NNReal

namespace Family8EndpointLongCoreIdentityFirstFieldsV3

open Submission.Kakeya.Uniformity
open Family8NormalizedLongIntervalCoreConsumerV1
open Family8ThreeScaleFrostmanFactorAlgebraV2
open FamilyStickyAtEveryScaleCoreV1
open FamilyStickyDividingScalesFiniteStoppingV1
open FamilyStickyScaleChainCappedSeedSequenceV2
open FamilyStickyScaleChainCoherentIntervalProducerV1

noncomputable section

variable {delta : NNReal} {iota : Type}
  [Fintype iota] [DecidableEq iota]
  {fine : UniformTubeFamily delta iota}
  {epsilon : Real} {N : Nat} {eta : Nat -> Real}

/-- Every long-core witness on the one-step endpoint sequence has lower scale
exactly `delta`. -/
theorem endpointLongCore_tau_eq_delta
    (hdeltaOne : delta <= 1)
    (C : CoherentStickyMultiscaleCover fine)
    (W : NormalizedLongIntervalCoreWitness fine C N epsilon eta
      (endpointScaleSequence delta hdeltaOne)) :
    (endpointScaleSequence delta hdeltaOne).tau W.m = delta := by
  rw [show W.m = (0 : Fin 1) from Subsingleton.elim _ _,
    endpointScaleSequence_tau_zero]

/-- At equal positive scales and unit count the literal Section-8 factor is
one. -/
theorem sectionEightScaleCountFrostmanFactor_self_one
    (hdelta : 0 < delta) (gamma : Real) :
    sectionEightScaleCountFrostmanFactor delta delta 1 gamma = 1 := by
  unfold sectionEightScaleCountFrostmanFactor
  rw [ENNReal.div_self (ENNReal.coe_ne_zero.mpr hdelta.ne')
    ENNReal.coe_ne_top]
  simp

/-- Exact first-factor fields consumed by `LongCoreThreeScaleDSOData`. -/
structure EndpointLongCoreIdentityFirstFields
    (hdeltaOne : delta <= 1)
    (C : CoherentStickyMultiscaleCover fine)
    (W : NormalizedLongIntervalCoreWitness fine C N epsilon eta
      (endpointScaleSequence delta hdeltaOne))
    (gamma : Real) where
  firstCount : Nat
  firstAverage : ENNReal
  firstLoss : ENNReal
  firstCount_eq_one : firstCount = 1
  firstAverage_eq_one : firstAverage = 1
  firstLoss_eq_one : firstLoss = 1
  hFirst : firstAverage <= firstLoss *
    sectionEightScaleCountFrostmanFactor delta
      ((endpointScaleSequence delta hdeltaOne).tau W.m) firstCount gamma

/-- Canonical callback-free identity fields for every endpoint long core. -/
def endpointLongCoreIdentityFirstFields
    (hdelta : 0 < delta) (hdeltaOne : delta <= 1)
    (C : CoherentStickyMultiscaleCover fine)
    (W : NormalizedLongIntervalCoreWitness fine C N epsilon eta
      (endpointScaleSequence delta hdeltaOne))
    (gamma : Real) :
    EndpointLongCoreIdentityFirstFields hdeltaOne C W gamma where
  firstCount := 1
  firstAverage := 1
  firstLoss := 1
  firstCount_eq_one := rfl
  firstAverage_eq_one := rfl
  firstLoss_eq_one := rfl
  hFirst := by
    rw [endpointLongCore_tau_eq_delta hdeltaOne C W,
      sectionEightScaleCountFrostmanFactor_self_one hdelta]
    norm_num

/-- The identity first loss contributes zero delta-power loss. -/
theorem EndpointLongCoreIdentityFirstFields.firstLoss_le_zeroPower
    {hdeltaOne : delta <= 1}
    {C : CoherentStickyMultiscaleCover fine}
    {W : NormalizedLongIntervalCoreWitness fine C N epsilon eta
      (endpointScaleSequence delta hdeltaOne)}
    {gamma : Real}
    (X : EndpointLongCoreIdentityFirstFields hdeltaOne C W gamma) :
    X.firstLoss <= (delta : ENNReal) ^ (0 : Real) := by
  rw [X.firstLoss_eq_one]
  simp

#print axioms endpointLongCore_tau_eq_delta
#print axioms sectionEightScaleCountFrostmanFactor_self_one
#print axioms EndpointLongCoreIdentityFirstFields
#print axioms endpointLongCoreIdentityFirstFields
#print axioms EndpointLongCoreIdentityFirstFields.firstLoss_le_zeroPower

end
end Family8EndpointLongCoreIdentityFirstFieldsV3
