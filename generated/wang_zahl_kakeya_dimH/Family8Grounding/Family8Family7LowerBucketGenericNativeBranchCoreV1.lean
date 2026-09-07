import Family8Grounding.Family8ShadingAwareGenericNativeBranchCoreV2
import Family8Grounding.Family8ShadingAwareProjectedPhysicalLowerBucketV1
import Mathlib.Tactic

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 2000000

open Set MeasureTheory
open scoped BigOperators ENNReal NNReal

namespace Family8Family7LowerBucketGenericNativeBranchCoreV1

open LeanEval.Analysis.WangZahlKakeya
open Submission.Kakeya.ConvexGeometry
open Submission.Kakeya.Uniformity
open Family8ShadingAwareGenericNativeBranchCoreV2
open Family8ShadingAwareProjectedPhysicalLowerBucketV1
open Family8ShadingAwareProjectedPhysicalV3
open FamilyStickyCinematicL32WZL3UniformTubeSourceV1

noncomputable section

universe u

/-!
# The native branch core specialized to a quantitative fibre bucket

This is the definitional specialization of `GenericNativeBranchCore` to the
literal lower-fibre projected physical datum.  Unlike the old native core,
the physical carrier is not hard-coded to a full analytic tube trace.
Consequently active membership itself supplies the quantitative fibre floor.
-/

abbrev LowerBucketNativeBranchCore
    {radius : NNReal} {iota : Type u} [Fintype iota] [DecidableEq iota]
    (S : WZL3UniformTubeSource radius iota)
    (Y : Shading S.family.bodyFamily) (active : Finset iota)
    (f : Real → Real) (hfContinuous : Continuous f)
    (X : Set (Real × Real)) (hX : MeasurableSet X)
    (I : Set Real) (hI : MeasurableSet I) (fibreFloor : ENNReal) :=
  GenericNativeBranchCore radius iota S
    (shadingAwareProjectedPhysicalLowerBucket Y active f
      hfContinuous.measurable X hX I hI fibreFloor)
    f hfContinuous

namespace LowerBucketNativeBranchCore

variable {radius : NNReal} {iota : Type u}
  [Fintype iota] [DecidableEq iota]
variable {S : WZL3UniformTubeSource radius iota}
variable {Y : Shading S.family.bodyFamily} {active : Finset iota}
variable {f : Real → Real} {hfContinuous : Continuous f}
variable {X : Set (Real × Real)} {hX : MeasurableSet X}
variable {I : Set Real} {hI : MeasurableSet I}
variable {fibreFloor : ENNReal}

@[simp]
theorem physicalDatum_eq
    (D : LowerBucketNativeBranchCore S Y active f hfContinuous
      X hX I hI fibreFloor) :
    D.physicalDatum =
      shadingAwareProjectedPhysicalLowerBucket Y active f
        hfContinuous.measurable X hX I hI fibreFloor := by
  rfl

@[simp]
theorem mem_physical_activeAtPoint
    (D : LowerBucketNativeBranchCore S Y active f hfContinuous
      X hX I hI fibreFloor)
    (u : Real × Real) (i : iota) :
    i ∈ D.physicalDatum.activeAtPoint u ↔
      i ∈ active ∧ u ∈ X ∧
        fibreFloor ≤ shadingFiberMass
          (shadingWindowRestriction Y f hfContinuous.measurable X hX I hI)
            f i u := by
  exact mem_activeAtPoint_shadingAwareProjectedPhysicalLowerBucket
    Y active f hfContinuous.measurable X hX I hI fibreFloor u i

/-- Every physical occurrence in the specialized generic core carries the
literal fibre floor, with no conclusion-valued field. -/
theorem shadingFiberMass_lower_of_mem_physical_activeAtPoint
    (D : LowerBucketNativeBranchCore S Y active f hfContinuous
      X hX I hI fibreFloor)
    {u : Real × Real} {i : iota}
    (hi : i ∈ D.physicalDatum.activeAtPoint u) :
    fibreFloor ≤ shadingFiberMass
      (shadingWindowRestriction Y f hfContinuous.measurable X hX I hI)
        f i u :=
  (D.mem_physical_activeAtPoint u i).mp hi |>.2.2

end LowerBucketNativeBranchCore

#print axioms LowerBucketNativeBranchCore
#print axioms LowerBucketNativeBranchCore.physicalDatum_eq
#print axioms LowerBucketNativeBranchCore.mem_physical_activeAtPoint
#print axioms
  LowerBucketNativeBranchCore.shadingFiberMass_lower_of_mem_physical_activeAtPoint

end

end Family8Family7LowerBucketGenericNativeBranchCoreV1
