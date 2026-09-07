import Family8Grounding.Family8NormalizedCFDividingWitnessFiniteSelectionV2

open scoped ENNReal NNReal

namespace Family8NormalizedCFDividingWitnessFiniteSelectionV4

open LeanEval.Analysis.WangZahlKakeya
open Submission.Kakeya.Uniformity
open Family8KatzTaoFrostmanPropertiesV1
open FamilyStickyAtEveryScaleCoreV1
open FamilyStickyDividingScalesFiniteStoppingV1
open FamilyStickyScaleChainCoherentIntervalProducerV1
open Family8NormalizedCFDividingWitnessBridgeV2.StickyScaleCover
open Family8NormalizedCFDividingWitnessFiniteSelectionV1.StickyMultiscaleCover
open Family8NormalizedCFDividingWitnessFiniteSelectionV1.CoherentStickyMultiscaleCover

noncomputable section

set_option autoImplicit false
set_option warningAsError true

/-!
# Actual all-scale upper bounds and legal buffered evaluation

This module connects the computed normalized values used by the first
crossing selector to the existing, genuine `IsFrostmanAtEveryScale` datum.
It also proves directly from admissible positive fine scale and a
nonnegative buffer exponent that a buffered radius is legal, so the
totalized crossing value is the literal coherent interval cover value.
-/

namespace StickyMultiscaleCover

variable {delta : NNReal} {iota : Type*}
  [Fintype iota] [DecidableEq iota]
  {fine : UniformTubeFamily delta iota}

/-- The paper all-scale Frostman predicate is exactly a uniform upper bound
for the totalized computed parent-normalized constants. -/
theorem isFrostmanAtEveryScale_iff_actualParentNormalizedFiberCFMaxAt_le
    (M : StickyMultiscaleCover fine) (hdelta : 0 < delta)
    (error : ENNReal) :
    M.IsFrostmanAtEveryScale error ↔
      ∀ rho (_hdeltaRho : delta <= rho) (_hrhoOne : rho <= 1),
        actualParentNormalizedFiberCFMaxAt M rho <= error := by
  constructor
  · intro hF rho hdeltaRho hrhoOne
    rw [actualParentNormalizedFiberCFMaxAt_eq
      M rho hdeltaRho hrhoOne]
    exact
      (isFrostmanAtScale_iff_parentNormalizedFiberCFMax_le
        (M.cover rho hdeltaRho hrhoOne) hdelta error).mp
        (hF rho hdeltaRho hrhoOne)
  · intro hBound rho hdeltaRho hrhoOne
    apply
      (isFrostmanAtScale_iff_parentNormalizedFiberCFMax_le
        (M.cover rho hdeltaRho hrhoOne) hdelta error).mpr
    simpa only [actualParentNormalizedFiberCFMaxAt_eq
      M rho hdeltaRho hrhoOne] using hBound rho hdeltaRho hrhoOne

end StickyMultiscaleCover

namespace CoherentStickyMultiscaleCover

variable {delta : NNReal} {iota : Type}
  [Fintype iota] [DecidableEq iota]
  {depth : Nat}

/-- The source all-scale Frostman property gives the normalized upper bound
for every literal source-to-`tau_m` cover. -/
theorem actualDatum_sourceToTau_parentNormalizedFiberCFMax_le
    (D : ActualTubeDatum delta iota) (hD : D.IsAdmissible)
    (C : CoherentStickyMultiscaleCover D.family)
    (S : FiniteScaleSequence delta depth)
    {error : ENNReal} (hF : C.base.IsFrostmanAtEveryScale error)
    (m : Fin depth) :
    parentNormalizedFiberCFMax
        (C.base.cover (S.tau m) (S.delta_le_tau m)
          ((S.tau_le_theta m).trans (S.theta_le_one m))) <= error := by
  exact
    (isFrostmanAtScale_iff_parentNormalizedFiberCFMax_le
      (C.base.cover (S.tau m) (S.delta_le_tau m)
        ((S.tau_le_theta m).trans (S.theta_le_one m)))
      hD.delta_pos error).mp
      (hF (S.tau m) (S.delta_le_tau m)
        ((S.tau_le_theta m).trans (S.theta_le_one m)))

/-- A buffered scale lies above `tau_m`, using only positivity of the actual
source scale and nonnegativity of the buffer exponent. -/
theorem actualDatum_tau_le_of_isBuffered
    (D : ActualTubeDatum delta iota) (hD : D.IsAdmissible)
    (S : FiniteScaleSequence delta depth)
    {epsilon : Real} (hepsilon : 0 <= epsilon)
    (m : Fin depth) (rho : NNReal)
    (hbuffered : S.IsBuffered epsilon m rho) :
    S.tau m <= rho := by
  have htauPos : 0 < S.tau m :=
    hD.delta_pos.trans_le (S.delta_le_tau m)
  have hbaseNN : 1 <= S.theta m / S.tau m :=
    (one_le_div htauPos).2 (S.tau_le_theta m)
  have hbaseE : (1 : ENNReal) <=
      (((S.theta m / S.tau m : NNReal) : ENNReal)) := by
    exact_mod_cast hbaseNN
  have hfactor : (1 : ENNReal) <=
      (((S.theta m / S.tau m : NNReal) : ENNReal) ^ epsilon) := by
    simpa using ENNReal.rpow_le_rpow hbaseE hepsilon
  apply ENNReal.coe_le_coe.mp
  calc
    (S.tau m : ENNReal) = (S.tau m : ENNReal) * 1 := by simp
    _ <= (S.tau m : ENNReal) *
        (((S.theta m / S.tau m : NNReal) : ENNReal) ^ epsilon) := by
      gcongr
    _ <= (rho : ENNReal) := hbuffered.1

/-- A buffered scale lies below one under the same honest sign condition. -/
theorem buffered_le_one
    (S : FiniteScaleSequence delta depth)
    {epsilon : Real} (hepsilon : 0 <= epsilon)
    (m : Fin depth) (rho : NNReal)
    (hbuffered : S.IsBuffered epsilon m rho) :
    rho <= 1 := by
  have hratioNN : S.tau m / S.theta m <= 1 :=
    div_le_one_of_le₀ (S.tau_le_theta m) bot_le
  have hratioE :
      (((S.tau m / S.theta m : NNReal) : ENNReal)) <= 1 := by
    exact_mod_cast hratioNN
  have hfactor :
      (((S.tau m / S.theta m : NNReal) : ENNReal) ^ epsilon) <= 1 :=
    ENNReal.rpow_le_one hratioE hepsilon
  have hrhoTheta : rho <= S.theta m := by
    apply ENNReal.coe_le_coe.mp
    calc
      (rho : ENNReal) <= (S.theta m : ENNReal) *
          (((S.tau m / S.theta m : NNReal) : ENNReal) ^ epsilon) :=
        hbuffered.2
      _ <= (S.theta m : ENNReal) * 1 := by gcongr
      _ = (S.theta m : ENNReal) := by simp
  exact hrhoTheta.trans (S.theta_le_one m)

/-- On a buffered radius, the totalized selector value is the literal
parent-normalized constant of the coherent interval cover. -/
theorem actualDatum_normalizedFiberCFValueAt_eq_of_isBuffered
    (D : ActualTubeDatum delta iota) (hD : D.IsAdmissible)
    (C : CoherentStickyMultiscaleCover D.family)
    (S : FiniteScaleSequence delta depth)
    {epsilon : Real} (hepsilon : 0 <= epsilon)
    (m : Fin depth) (rho : NNReal)
    (hbuffered : S.IsBuffered epsilon m rho) :
    normalizedFiberCFValueAt C S m rho =
      parentNormalizedFiberCFMax
        (C.intervalScaleCover (S.tau m) rho
          (S.delta_le_tau m)
          (actualDatum_tau_le_of_isBuffered D hD S hepsilon m rho hbuffered)
          (buffered_le_one S hepsilon m rho hbuffered)) := by
  exact normalizedFiberCFValueAt_eq C S m rho
    (actualDatum_tau_le_of_isBuffered D hD S hepsilon m rho hbuffered)
    (buffered_le_one S hepsilon m rho hbuffered)

#print axioms
  StickyMultiscaleCover.isFrostmanAtEveryScale_iff_actualParentNormalizedFiberCFMaxAt_le
#print axioms actualDatum_sourceToTau_parentNormalizedFiberCFMax_le
#print axioms actualDatum_tau_le_of_isBuffered
#print axioms buffered_le_one
#print axioms actualDatum_normalizedFiberCFValueAt_eq_of_isBuffered

end CoherentStickyMultiscaleCover

end
end Family8NormalizedCFDividingWitnessFiniteSelectionV4
