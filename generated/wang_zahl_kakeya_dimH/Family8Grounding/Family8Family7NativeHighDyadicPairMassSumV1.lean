import FamilyStickyGrounding.Cinematic.FamilyStickyCinematicL32PyzActualNormFirstHighDyadicPairMassUpperV3
import Mathlib.Tactic

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 4000000

open Set MeasureTheory
open scoped BigOperators ENNReal NNReal

namespace Family8Family7NativeHighDyadicPairMassSumV1

open FamilyStickyCinematicL32Prop41CanonicalMaximizerNonconcentrationV1
open FamilyStickyCinematicL32Prop41ActualGPrimeCanonicalSharingCapV3
open FamilyStickyCinematicL32Prop41ActualPositiveCenterHighPayloadWeightedFullyActualConnectorV1
open FamilyStickyCinematicL32PyzE2DyadicDegreeWindowV1
open FamilyStickyCinematicL32PyzActualAllCenterBinUniformityV1
open FamilyStickyCinematicL32PyzActualNormFirstAllCenterHighConcreteQPOutcomeV4
open FamilyStickyCinematicL32PyzActualNormFirstAllCenterHighConcreteQPWeightedGeometricSumV2
open FamilyStickyCinematicL32PyzActualNormFirstAllCenterHighPreMaxFirstHitPairMassV2
open FamilyStickyCinematicL32PyzActualNormFirstAllCenterMassWeightedBranchTypesV5C
open FamilyStickyCinematicL32PyzActualNormFirstHighDyadicPairMassUpperV3

noncomputable section

universe u

/-!
# Sum the native-high dyadic pair-mass bounds over literal high centres

The local Family 7 endpoint already charges each centre's full pre-max
first-hit pair mass to that centre's genuine high-base mass.  This file
performs the missing finite aggregation.  The coefficient is kept as the
maximum of the actual canonical sharing and dyadic-degree losses; no claim
that it is a small power is inserted.
-/

/-- The explicit local coefficient in the callback-free native-high pair
mass upper bound. -/
noncomputable def nativeHighLocalDyadicPairLoss
    {radius : NNReal} {iota : Type u} [Fintype iota] [DecidableEq iota]
    (D : NativeBranchCore radius iota) (G : NativeHighGeometry D)
    (c : D.HighCenter) : ENNReal :=
  let H := D.chosenHighPayloadAt c
  let N := positiveCenterHighPayloadGlobalNormData H
  648 *
    (((automaticCanonicalCenterSharingNatCap N (G.ballRadius c) *
      automaticCanonicalCenterSharingNatCap N (G.ballRadius c) : Nat) :
        ENNReal) *
      ((pyzE2DegreeUpper H.payload.finalLabel *
        pyzE2DegreeUpper H.payload.finalLabel : Nat) : ENNReal))

/-- The single finite loss governing all literal high centres. -/
noncomputable def nativeHighDyadicPairLossMax
    {radius : NNReal} {iota : Type u} [Fintype iota] [DecidableEq iota]
    (D : NativeBranchCore radius iota) (G : NativeHighGeometry D) : ENNReal :=
  Finset.univ.sup (nativeHighLocalDyadicPairLoss D G)

/-- The local endpoint in coefficient-times-base-mass form. -/
theorem nativeHighPreMaxFirstHitCenterPairMass_le_localLoss_mul_highBase
    {radius : NNReal} {iota : Type u} [Fintype iota] [DecidableEq iota]
    (D : NativeBranchCore radius iota) (G : NativeHighGeometry D)
    (hout : NativeHighConcreteQPOutcome D G) (c : D.HighCenter) :
    nativeHighPreMaxFirstHitCenterPairMass D G c <=
      nativeHighLocalDyadicPairLoss D G c * volume (D.highBase c) := by
  simpa only [nativeHighLocalDyadicPairLoss, mul_assoc] using
    nativeHighPreMaxFirstHitCenterPairMass_le_canonicalCap_sq_mul_degreeUpper_sq_mul_highBase
      D G c (nativeHighConcreteQPLocalAt hout c)

/-- The high-base cells form a sub-sum of the exact source-mass partition. -/
theorem sum_nativeHighBase_le_sourceMass
    {radius : NNReal} {iota : Type u} [Fintype iota] [DecidableEq iota]
    (D : NativeBranchCore radius iota) :
    (∑ c : D.HighCenter, volume (D.highBase c)) <= D.sourceMass := by
  classical
  have hbaseSum :
      (∑ c : D.HighCenter, volume (D.highBase c)) =
        ∑ c ∈ D.high, volume (D.cell c.1) := by
    simpa only [NativeBranchCore.highBase,
      NativeBranchCore.positiveBase, Finset.univ_eq_attach] using
        Finset.sum_attach D.high (fun c => volume (D.cell c.1))
  obtain ⟨hpartition, _hhalf, _hhigh, _hlow⟩ := D.payloadAt_spec
  calc
    (∑ c : D.HighCenter, volume (D.highBase c)) =
        ∑ c ∈ D.high, volume (D.cell c.1) := hbaseSum
    _ <= (∑ c ∈ D.high, volume (D.cell c.1)) +
        ∑ c ∈ D.low, volume (D.cell c.1) := le_add_right (le_refl _)
    _ = D.sourceMass := hpartition.symm

/-- Finite high-centre aggregation of the actual local pair-mass bounds. -/
theorem nativeHighPreMaxFirstHitPairMassBudget_le_maxLoss_mul_sourceMass
    {radius : NNReal} {iota : Type u} [Fintype iota] [DecidableEq iota]
    (D : NativeBranchCore radius iota) (G : NativeHighGeometry D)
    (hout : NativeHighConcreteQPOutcome D G) :
    nativeHighPreMaxFirstHitPairMassBudget G <=
      nativeHighDyadicPairLossMax D G * D.sourceMass := by
  classical
  unfold nativeHighPreMaxFirstHitPairMassBudget
  calc
    (∑ c : D.HighCenter, nativeHighPreMaxFirstHitCenterPairMass D G c) <=
        ∑ c : D.HighCenter,
          nativeHighLocalDyadicPairLoss D G c * volume (D.highBase c) := by
      exact Finset.sum_le_sum fun c _hc =>
        nativeHighPreMaxFirstHitCenterPairMass_le_localLoss_mul_highBase
          D G hout c
    _ <= ∑ c : D.HighCenter,
        nativeHighDyadicPairLossMax D G * volume (D.highBase c) := by
      exact Finset.sum_le_sum fun c hc => by
        gcongr
        exact Finset.le_sup
          (f := nativeHighLocalDyadicPairLoss D G) hc
    _ = nativeHighDyadicPairLossMax D G *
        (∑ c : D.HighCenter, volume (D.highBase c)) := by
      rw [Finset.mul_sum]
    _ <= nativeHighDyadicPairLossMax D G * D.sourceMass := by
      gcongr
      exact sum_nativeHighBase_le_sourceMass D

/-- Combining the existing high-half lower endpoint with the newly summed
upper endpoint leaves only the explicit scalar loss. -/
theorem sourceMass_half_le_binLoss_mul_maxDyadicLoss_mul_sourceMass
    {radius : NNReal} {iota : Type u} [Fintype iota] [DecidableEq iota]
    (D : NativeBranchCore radius iota) (G : NativeHighGeometry D)
    (hout : NativeHighConcreteQPOutcome D G)
    (hhalf : D.sourceMass / 2 <=
      ∑ c ∈ D.high, volume (D.cell c.1)) :
    D.sourceMass / 2 <=
      (actualAllCenterPostNormBinLoss radius D.globalScale
          D.physical.ambient.card * nativeHighDyadicPairLossMax D G) *
        D.sourceMass := by
  calc
    D.sourceMass / 2 <=
        actualAllCenterPostNormBinLoss radius D.globalScale
            D.physical.ambient.card *
          nativeHighPreMaxFirstHitPairMassBudget G :=
      NativeHighConcreteQPOutcome.sourceMass_half_le_binLoss_mul_preMaxFirstHitPairMassBudget
        hout hhalf
    _ <= actualAllCenterPostNormBinLoss radius D.globalScale
          D.physical.ambient.card *
        (nativeHighDyadicPairLossMax D G * D.sourceMass) := by
      gcongr
      exact nativeHighPreMaxFirstHitPairMassBudget_le_maxLoss_mul_sourceMass
        D G hout
    _ = (actualAllCenterPostNormBinLoss radius D.globalScale
          D.physical.ambient.card * nativeHighDyadicPairLossMax D G) *
        D.sourceMass := by
      rw [mul_assoc]

#print axioms nativeHighLocalDyadicPairLoss
#print axioms nativeHighDyadicPairLossMax
#print axioms nativeHighPreMaxFirstHitCenterPairMass_le_localLoss_mul_highBase
#print axioms sum_nativeHighBase_le_sourceMass
#print axioms nativeHighPreMaxFirstHitPairMassBudget_le_maxLoss_mul_sourceMass
#print axioms sourceMass_half_le_binLoss_mul_maxDyadicLoss_mul_sourceMass

end
end Family8Family7NativeHighDyadicPairMassSumV1
