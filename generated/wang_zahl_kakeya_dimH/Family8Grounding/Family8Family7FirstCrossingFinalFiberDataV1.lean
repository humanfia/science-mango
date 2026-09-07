import Family8Grounding.Family8FrozenComparableActualAverageMassDensityV1
import FamilyStickyCinematicL32WZL3UniformTubeSourceV1

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 3000000

open Set MeasureTheory
open scoped ENNReal NNReal

namespace Family8Family7FirstCrossingFinalFiberDataV1

open LeanEval.Analysis.WangZahlKakeya
open Submission.Kakeya.ConvexGeometry
open Submission.Kakeya.ConvexFactoring
open Submission.Kakeya.ConvexFactoring.FiberwiseMultiplicityAssembly
open Family8FrozenComparableActualAverageMassDensityV1.Assembly
open Family8FrozenNeighborhoodAssemblyV1
open FamilyStickyCinematicL32WZL3UniformTubeSourceV1

noncomputable section

universe u v

/-!
# Literal selected-fibre data from a frozen first-crossing assembly

These aliases freeze the two objects consumed by the generic native-high
chain: the actual selected factorization fibre and its literal final shading.
They do not choose a new witness, family, or shading.
-/

def selectedFrozenFiberActive
    {radius : NNReal} {iota : Type u} {kappa : Type v}
    [Fintype iota] [DecidableEq iota]
    [Fintype kappa] [DecidableEq kappa]
    (S : WZL3UniformTubeSource radius iota)
    {coarse : ConvexFamily kappa}
    (P : ConvexFactorization S.family.bodyFamily coarse)
    (k : kappa) : Finset iota :=
  P.index.fiber k

def selectedFrozenFiberShading
    {radius : NNReal} {iota : Type u} {kappa : Type v}
    [Fintype iota] [DecidableEq iota]
    [Fintype kappa] [DecidableEq kappa]
    (S : WZL3UniformTubeSource radius iota)
    {coarse : ConvexFamily kappa}
    (P : ConvexFactorization S.family.bodyFamily coarse)
    {Y : Shading S.family.bodyFamily} {r : Real}
    (A : Assembly P Y r) (k : kappa) : Shading S.family.bodyFamily :=
  finalFiberShading A k

@[simp] theorem selectedFrozenFiberActive_eq
    {radius : NNReal} {iota : Type u} {kappa : Type v}
    [Fintype iota] [DecidableEq iota]
    [Fintype kappa] [DecidableEq kappa]
    (S : WZL3UniformTubeSource radius iota)
    {coarse : ConvexFamily kappa}
    (P : ConvexFactorization S.family.bodyFamily coarse)
    (k : kappa) :
    selectedFrozenFiberActive S P k = P.index.fiber k :=
  rfl

@[simp] theorem selectedFrozenFiberShading_eq
    {radius : NNReal} {iota : Type u} {kappa : Type v}
    [Fintype iota] [DecidableEq iota]
    [Fintype kappa] [DecidableEq kappa]
    (S : WZL3UniformTubeSource radius iota)
    {coarse : ConvexFamily kappa}
    (P : ConvexFactorization S.family.bodyFamily coarse)
    {Y : Shading S.family.bodyFamily} {r : Real}
    (A : Assembly P Y r) (k : kappa) :
    selectedFrozenFiberShading S P A k = finalFiberShading A k :=
  rfl

@[simp] theorem selectedFrozenFiberShading_carrier
    {radius : NNReal} {iota : Type u} {kappa : Type v}
    [Fintype iota] [DecidableEq iota]
    [Fintype kappa] [DecidableEq kappa]
    (S : WZL3UniformTubeSource radius iota)
    {coarse : ConvexFamily kappa}
    (P : ConvexFactorization S.family.bodyFamily coarse)
    {Y : Shading S.family.bodyFamily} {r : Real}
    (A : Assembly P Y r) (k : kappa) (i : iota) :
    (selectedFrozenFiberShading S P A k).carrier i =
      if i ∈ selectedFrozenFiberActive S P k then
        A.refinement.shading.carrier i else ∅ := by
  exact fiberShading_carrier P A.refinement.shading k i

#print axioms selectedFrozenFiberActive
#print axioms selectedFrozenFiberShading
#print axioms selectedFrozenFiberActive_eq
#print axioms selectedFrozenFiberShading_eq
#print axioms selectedFrozenFiberShading_carrier

end

end Family8Family7FirstCrossingFinalFiberDataV1
