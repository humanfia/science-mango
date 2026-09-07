import Family8Grounding.Family8KatzTaoFrostmanPropertiesV1
import Submission.Kakeya.ConvexFactoring.FactoringMultiplicityAssembly

open scoped ENNReal NNReal BigOperators
open MeasureTheory Set

namespace Family8PointwisePackingVolumeV1

open LeanEval.Analysis.WangZahlKakeya
open Submission.Kakeya.ConvexGeometry
open Submission.Kakeya.ConvexFactoring
open Submission.Kakeya.Uniformity
open Family8KatzTaoFrostmanPropertiesV1

noncomputable section

set_option autoImplicit false
set_option warningAsError true

local instance (p : Prop) : Decidable p := Classical.propDecidable p

/-!
# Pointwise tube packing controls total family volume

The same common-point packing estimate needed for the trivial `K_F(1)`
base case also supplies the global volume estimate used by the all-Frostman
branch.  We integrate the full carrier shading inside the unit ball, so no
separate line-space cardinality theorem is needed at this interface.
-/

/-- The full carrier shading of an actual tube family. -/
def actualCarrierShading
    {delta : NNReal} {iota : Type} [Fintype iota] [DecidableEq iota]
    (D : ActualTubeDatum delta iota) : Shading D.family.bodyFamily where
  carrier := fun i => (D.family.tubes i).carrier
  measurable_carrier := fun i => (D.family.tubes i).isCompact_carrier.measurableSet
  carrier_subset := fun _ => subset_rfl

@[simp]
theorem actualCarrierShading_carrier
    {delta : NNReal} {iota : Type} [Fintype iota] [DecidableEq iota]
    (D : ActualTubeDatum delta iota) (i : iota) :
    (actualCarrierShading D).carrier i = (D.family.tubes i).carrier :=
  rfl

@[simp]
theorem actualCarrierShading_pointMultiplicity
    {delta : NNReal} {iota : Type} [Fintype iota] [DecidableEq iota]
    (D : ActualTubeDatum delta iota) (x : Space) :
    (actualCarrierShading D).pointMultiplicity x =
      (Finset.univ.filter fun i => x ∈ (D.family.tubes i).carrier).card := by
  classical
  rfl

/-- Full-carrier shading mass is exactly the actual summed family volume. -/
theorem actualCarrierShading_shadingMass
    {delta : NNReal} {iota : Type} [Fintype iota] [DecidableEq iota]
    (D : ActualTubeDatum delta iota) :
    (actualCarrierShading D).shadingMass = D.actualFamilyVolume := by
  simp only [Shading.shadingMass, actualCarrierShading_carrier,
    ActualTubeDatum.actualFamilyVolume, familyVolume,
    UniformTubeFamily.bodyFamily, Tube.coe_body]

/-- Admissibility puts the union of all full tube carriers in the unit ball. -/
theorem actualCarrierShading_shadedUnion_subset_unitBall
    {delta : NNReal} {iota : Type} [Fintype iota] [DecidableEq iota]
    {D : ActualTubeDatum delta iota} (hD : D.IsAdmissible) :
    (actualCarrierShading D).shadedUnion ⊆ (unitBallBody : Set Space) := by
  intro x hx
  obtain ⟨i, hi⟩ := Set.mem_iUnion.mp hx
  exact hD.contained_in_unit_ball i hi

/-- A natural common-point cap integrates to a global summed-volume bound
inside the normalized unit ball. -/
theorem actualFamilyVolume_le_pointCap_mul_unitBallVolume
    {delta : NNReal} {iota : Type} [Fintype iota] [DecidableEq iota]
    (D : ActualTubeDatum delta iota) (hD : D.IsAdmissible) (M : Nat)
    (hpoint : ∀ x, (actualCarrierShading D).pointMultiplicity x ≤ M) :
    D.actualFamilyVolume ≤
      (M : ENNReal) * volume (unitBallBody : Set Space) := by
  have hmass :
      (actualCarrierShading D).shadingMass ≤
        M • volume (actualCarrierShading D).shadedUnion :=
    FactoringMultiplicityAssembly.ExactAssembly.shadingMass_le_nsmul_volume_shadedUnion_of_pointMultiplicity_le
        (actualCarrierShading D) M hpoint
  rw [actualCarrierShading_shadingMass, nsmul_eq_mul] at hmass
  exact hmass.trans (by
    gcongr
    exact actualCarrierShading_shadedUnion_subset_unitBall hD)

/-- If the natural point cap is at most `C delta^(-2)`, the same finite
constant (times the fixed unit-ball volume) controls total family volume. -/
theorem actualFamilyVolume_le_rpow_neg_two_of_pointCap
    {delta : NNReal} {iota : Type} [Fintype iota] [DecidableEq iota]
    (D : ActualTubeDatum delta iota) (hD : D.IsAdmissible)
    (M : Nat) {C : ENNReal}
    (hpoint : ∀ x, (actualCarrierShading D).pointMultiplicity x ≤ M)
    (hcap : (M : ENNReal) ≤ C * (delta : ENNReal) ^ (-2 : Real)) :
    D.actualFamilyVolume ≤
      (C * volume (unitBallBody : Set Space)) *
        (delta : ENNReal) ^ (-2 : Real) := by
  calc
    D.actualFamilyVolume ≤
        (M : ENNReal) * volume (unitBallBody : Set Space) :=
      actualFamilyVolume_le_pointCap_mul_unitBallVolume D hD M hpoint
    _ ≤ (C * (delta : ENNReal) ^ (-2 : Real)) *
          volume (unitBallBody : Set Space) := by gcongr
    _ = (C * volume (unitBallBody : Set Space)) *
          (delta : ENNReal) ^ (-2 : Real) := by ac_rfl

#print axioms actualCarrierShading_shadingMass
#print axioms actualCarrierShading_shadedUnion_subset_unitBall
#print axioms actualFamilyVolume_le_pointCap_mul_unitBallVolume
#print axioms actualFamilyVolume_le_rpow_neg_two_of_pointCap

end

end Family8PointwisePackingVolumeV1
