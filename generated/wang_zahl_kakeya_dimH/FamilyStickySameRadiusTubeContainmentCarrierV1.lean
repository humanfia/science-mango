import FamilyStickySameRadiusTubeContainmentDirectionV1

set_option autoImplicit false

open Set
open scoped NNReal InnerProductSpace

namespace FamilyStickySameRadiusTubeContainmentCarrierV1

open LeanEval.Analysis.WangZahlKakeya
open Submission.Kakeya.ConvexGeometry

noncomputable section

/-!
# Carrier rigidity of same-radius tube containment

A closed neighborhood of a unit segment cannot be properly contained in a
closed neighborhood of another unit segment with the same radius.  The
direction theorem supplies projective parallelism.  The equality cases at the
two axial extreme points then recover the base point, including the reversed
orientation branch.
-/

theorem unitDirectionEqOrEqNegOfSinAngleEqZero
    (S L : UnitSegment)
    (hsin : Real.sin (InnerProductGeometry.angle
      S.direction L.direction) = 0) :
    S.direction = L.direction ∨ S.direction = -L.direction := by
  have htrig := Real.sin_sq_add_cos_sq
    (InnerProductGeometry.angle S.direction L.direction)
  rw [hsin] at htrig
  norm_num at htrig
  rcases htrig with hcos | hcos
  · left
    have hinter : ⟪S.direction, L.direction⟫_ℝ =
        ‖S.direction‖ * ‖L.direction‖ := by
      rw [InnerProductGeometry.inner_eq_cos_angle_of_norm_eq_one
        S.norm_direction L.norm_direction]
      rw [hcos, S.norm_direction, L.norm_direction]
      norm_num
    have hscaled := inner_eq_norm_mul_iff_real.mp hinter
    simpa [S.norm_direction, L.norm_direction] using hscaled
  · right
    have hinter : ⟪-S.direction, L.direction⟫_ℝ =
        ‖-S.direction‖ * ‖L.direction‖ := by
      rw [inner_neg_left,
        InnerProductGeometry.inner_eq_cos_angle_of_norm_eq_one
          S.norm_direction L.norm_direction]
      rw [hcos, norm_neg, S.norm_direction, L.norm_direction]
      norm_num
    have hscaled := inner_eq_norm_mul_iff_real.mp hinter
    have hneg : -S.direction = L.direction := by
      simpa [S.norm_direction, L.norm_direction] using hscaled
    exact neg_eq_iff_eq_neg.mp hneg

theorem eqSMulOfNormLeOfInnerEq
    (v e : Space) (hv : ‖v‖ = 1) (d : Real) (hd : 0 <= d)
    (hnorm : ‖e‖ <= d) (hinner : ⟪e, v⟫_ℝ = d) :
    e = d • v := by
  apply eq_of_norm_le_re_inner_eq_norm_sq (𝕜 := Real)
  · simpa [norm_smul, Real.norm_eq_abs, abs_of_nonneg hd, hv] using hnorm
  · rw [real_inner_smul_right, hinner, norm_smul, Real.norm_eq_abs,
      abs_of_nonneg hd, hv]
    norm_num
    ring

theorem tubeBaseEqOfSameRadiusCarrierSubsetOfDirectionEq
    {delta : NNReal} (T U : Tube delta)
    (hTU : T.carrier ⊆ U.carrier)
    (hdir : U.axis.direction = T.axis.direction) :
    U.axis.base = T.axis.base := by
  let d : Real := (delta : Real)
  let v : Space := T.axis.direction
  let p : Space := T.axis.base - d • v
  let q : Space := T.axis.endpoint + d • v
  have hd : 0 <= d := by positivity
  have hv : ‖v‖ = 1 := T.axis.norm_direction
  have hpDist : dist p T.axis.base <= d := by
    rw [dist_eq_norm]
    have hpSub : p - T.axis.base = -(d • v) := by
      dsimp only [p]
      module
    rw [hpSub, norm_neg, norm_smul, hv, mul_one,
      Real.norm_eq_abs, abs_of_nonneg hd]
  have hqDist : dist q T.axis.endpoint <= d := by
    rw [dist_eq_norm]
    have hqSub : q - T.axis.endpoint = d • v := by
      dsimp only [q]
      module
    rw [hqSub, norm_smul, hv, mul_one,
      Real.norm_eq_abs, abs_of_nonneg hd]
  have hpT : p ∈ T.carrier :=
    Metric.closedBall_subset_cthickening T.axis.base_mem_carrier d hpDist
  have hqT : q ∈ T.carrier :=
    Metric.closedBall_subset_cthickening T.axis.endpoint_mem_carrier d hqDist
  have hpU := hTU hpT
  have hqU := hTU hqT
  rw [Tube.carrier,
    U.axis.isCompact_carrier.cthickening_eq_biUnion_closedBall hd] at hpU hqU
  simp only [Set.mem_iUnion, Metric.mem_closedBall] at hpU hqU
  obtain ⟨a, haAxis, hpa⟩ := hpU
  obtain ⟨b, hbAxis, hqb⟩ := hqU
  rw [U.axis.carrier_eq_image] at haAxis hbAxis
  obtain ⟨s, hs, rfl⟩ := haAxis
  obtain ⟨t, ht, rfl⟩ := hbAxis
  rw [hdir] at hpa hqb
  let e0 : Space := U.axis.base + s • v - p
  let e1 : Space := q - (U.axis.base + t • v)
  have he0norm : ‖e0‖ <= d := by
    have he0neg : e0 = -(p - (U.axis.base + s • v)) := by
      dsimp only [e0]
      module
    rw [he0neg, norm_neg]
    simpa only [dist_eq_norm] using hpa
  have he1norm : ‖e1‖ <= d := by
    simpa only [e1, dist_eq_norm] using hqb
  have he0innerLe : ⟪e0, v⟫_ℝ <= d := by
    calc
      ⟪e0, v⟫_ℝ <= ‖e0‖ * ‖v‖ := real_inner_le_norm _ _
      _ = ‖e0‖ := by rw [hv, mul_one]
      _ <= d := he0norm
  have he1innerLe : ⟪e1, v⟫_ℝ <= d := by
    calc
      ⟪e1, v⟫_ℝ <= ‖e1‖ * ‖v‖ := real_inner_le_norm _ _
      _ = ‖e1‖ := by rw [hv, mul_one]
      _ <= d := he1norm
  have htsLe : t - s <= 1 := by linarith [hs.1, ht.2]
  have hvec : e0 + (t - s) • v + e1 = (1 + 2 * d) • v := by
    dsimp only [e0, e1, p, q, v]
    simp only [UnitSegment.endpoint]
    module
  have hinnerSum := congrArg (fun w : Space => ⟪w, v⟫_ℝ) hvec
  simp only [inner_add_left, real_inner_smul_left,
    real_inner_self_eq_norm_sq, hv, one_pow, mul_one] at hinnerSum
  have he0inner : ⟪e0, v⟫_ℝ = d := by
    apply le_antisymm he0innerLe
    linarith
  have he1inner : ⟪e1, v⟫_ℝ = d := by
    apply le_antisymm he1innerLe
    linarith
  have hts : t - s = 1 := by linarith
  have hs0 : s = 0 := by linarith [hs.1, ht.2]
  have he0eq : e0 = d • v :=
    eqSMulOfNormLeOfInnerEq v e0 hv d hd he0norm he0inner
  dsimp only [e0, p] at he0eq
  rw [hs0, zero_smul, add_zero] at he0eq
  calc
    U.axis.base =
        (U.axis.base - (T.axis.base - d • v)) +
          (T.axis.base - d • v) := by
            module
    _ = d • v + (T.axis.base - d • v) := by rw [he0eq]
    _ = T.axis.base := by module

def reversedUnitSegment (S : UnitSegment) : UnitSegment where
  base := S.endpoint
  direction := -S.direction
  norm_direction := by rw [norm_neg, S.norm_direction]

@[simp]
theorem reversedUnitSegmentBase (S : UnitSegment) :
    (reversedUnitSegment S).base = S.endpoint := rfl

@[simp]
theorem reversedUnitSegmentDirection (S : UnitSegment) :
    (reversedUnitSegment S).direction = -S.direction := rfl

@[simp]
theorem reversedUnitSegmentEndpoint (S : UnitSegment) :
    (reversedUnitSegment S).endpoint = S.base := by
  simp only [UnitSegment.endpoint, reversedUnitSegmentBase,
    reversedUnitSegmentDirection]
  module

theorem reversedUnitSegmentCarrier (S : UnitSegment) :
    (reversedUnitSegment S).carrier = S.carrier := by
  rw [UnitSegment.carrier, reversedUnitSegmentBase,
    reversedUnitSegmentEndpoint, UnitSegment.carrier]
  exact segment_symm ℝ S.endpoint S.base

theorem unitSegmentEqOfBaseDirectionEq (S L : UnitSegment)
    (hbase : S.base = L.base)
    (hdir : S.direction = L.direction) :
    S = L := by
  cases S
  cases L
  simp_all

def reversedTube {delta : NNReal} (T : Tube delta) : Tube delta where
  axis := reversedUnitSegment T.axis

theorem reversedTubeCarrier {delta : NNReal} (T : Tube delta) :
    (reversedTube T).carrier = T.carrier := by
  rw [Tube.carrier, Tube.carrier]
  exact congrArg (Metric.cthickening (delta : Real))
    (reversedUnitSegmentCarrier T.axis)

theorem tubeCarrierEqOfSameRadiusCarrierSubsetOfDirectionEq
    {delta : NNReal} (T U : Tube delta)
    (hTU : T.carrier ⊆ U.carrier)
    (hdir : U.axis.direction = T.axis.direction) :
    U.carrier = T.carrier := by
  have hbase :=
    tubeBaseEqOfSameRadiusCarrierSubsetOfDirectionEq T U hTU hdir
  have haxis : U.axis = T.axis := by
    exact unitSegmentEqOfBaseDirectionEq U.axis T.axis hbase hdir
  rw [Tube.carrier, Tube.carrier, haxis]

/-- Same-radius closed unit tubes have no proper carrier containment. -/
theorem tubeCarrierEqOfSameRadiusCarrierSubset
    {delta : NNReal} (T U : Tube delta)
    (hTU : T.carrier ⊆ U.carrier) :
    T.carrier = U.carrier := by
  have hsin :=
    FamilyStickySameRadiusTubeContainmentDirectionV1.Tube.sin_angle_direction_eq_zero_of_sameRadius_carrier_subset
      T U hTU
  rcases unitDirectionEqOrEqNegOfSinAngleEqZero T.axis U.axis hsin with
    hsame | hopposite
  · exact (tubeCarrierEqOfSameRadiusCarrierSubsetOfDirectionEq T U
      hTU hsame.symm).symm
  · have hreverseDir :
        (reversedTube U).axis.direction = T.axis.direction := by
      change -U.axis.direction = T.axis.direction
      exact hopposite.symm
    have hreverseSubset : T.carrier ⊆ (reversedTube U).carrier := by
      simpa only [reversedTubeCarrier] using hTU
    have heq := tubeCarrierEqOfSameRadiusCarrierSubsetOfDirectionEq
      T (reversedTube U) hreverseSubset hreverseDir
    rw [reversedTubeCarrier] at heq
    exact heq.symm

#print axioms tubeCarrierEqOfSameRadiusCarrierSubset

end

end FamilyStickySameRadiusTubeContainmentCarrierV1
