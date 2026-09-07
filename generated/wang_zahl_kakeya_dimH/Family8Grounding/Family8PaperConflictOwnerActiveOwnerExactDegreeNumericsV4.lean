import Family8Grounding.Family8PaperConflictOwnerActiveOwnerKatzTaoExactIncidenceDegreeV3
import Family8Grounding.Family8KatzTaoSamplingMultiplicityV1
import Mathlib.Tactic

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 3000000

open scoped ENNReal NNReal

namespace Family8PaperConflictOwnerActiveOwnerExactDegreeNumericsV4

open Family8KatzTaoSamplingMultiplicityV1
open Family8PaperConflictOwnerActiveOwnerKatzTaoDoubledFiberCapV3
open Family8PaperConflictOwnerActiveOwnerKatzTaoExactIncidenceDegreeV3

noncomputable section

/-!
# Ceiling-free numerics for the exact active-owner conflict degree

Both genuine incidence caps in the exact-degree theorem are the same ceiling
of the finite Katz--Tao ratio below.  This file removes both ceilings and
isolates the only scale-dependent input as a bound on that literal ratio.
-/

/-- The literal mass-over-tube-floor ratio used by each incidence cap. -/
def activeOwnerKatzTaoIncidenceRatio
    (delta radius : NNReal) (A : ENNReal) : ENNReal :=
  A * ((240000 : ENNReal) * (radius : ENNReal) ^ 2) /
    ((delta : ENNReal) ^ 2 / 2)

@[simp]
theorem katzTaoDoubledFiberNatCap_eq_samplingMultiplicity
    (delta radius : NNReal) (A : ENNReal) :
    katzTaoDoubledFiberNatCap delta radius A =
      katzTaoSamplingMultiplicity
        (activeOwnerKatzTaoIncidenceRatio delta radius A) :=
  rfl

@[simp]
theorem katzTaoDoubledParentsNatCap_eq_samplingMultiplicity
    (delta radius : NNReal) (A : ENNReal) :
    katzTaoDoubledParentsNatCap delta radius A =
      katzTaoSamplingMultiplicity
        (activeOwnerKatzTaoIncidenceRatio delta radius A) :=
  rfl

/-- Removing both natural ceilings costs only the explicit factor eight.
No geometric or exponent estimate is used here. -/
theorem exactConflictDegree_coe_le_eight_mul_ratio_sq
    {delta radius : NNReal} {A : ENNReal}
    (hratioOne :
      1 <= activeOwnerKatzTaoIncidenceRatio delta radius A)
    (hratioFinite :
      activeOwnerKatzTaoIncidenceRatio delta radius A ≠ ∞) :
    ((1 +
        katzTaoDoubledFiberNatCap delta radius A *
          katzTaoDoubledParentsNatCap delta radius A : Nat) : ENNReal) <=
      8 * (activeOwnerKatzTaoIncidenceRatio delta radius A) ^ 2 := by
  let Q := activeOwnerKatzTaoIncidenceRatio delta radius A
  let n := katzTaoSamplingMultiplicity Q
  have hn : (n : ENNReal) <= 2 * Q := by
    exact katzTaoSamplingMultiplicity_coe_le_two_mul
      (by simpa only [Q] using hratioOne)
      (by simpa only [Q] using hratioFinite)
  have hnSq : (n : ENNReal) ^ 2 <= 4 * Q ^ 2 := by
    calc
      (n : ENNReal) ^ 2 <= (2 * Q) ^ 2 := by gcongr
      _ = 4 * Q ^ 2 := by ring
  have hOneSq : (1 : ENNReal) <= Q ^ 2 := by
    calc
      (1 : ENNReal) = 1 ^ 2 := by norm_num
      _ <= Q ^ 2 := by gcongr
  have hOne : (1 : ENNReal) <= 4 * Q ^ 2 := by
    calc
      (1 : ENNReal) <= Q ^ 2 := hOneSq
      _ = 1 * Q ^ 2 := by simp
      _ <= 4 * Q ^ 2 :=
        mul_le_mul' (by norm_num : (1 : ENNReal) <= 4) le_rfl
  have hfinal :
      (1 : ENNReal) + (n : ENNReal) * (n : ENNReal) <=
        8 * Q ^ 2 := by
    calc
      (1 : ENNReal) + (n : ENNReal) * (n : ENNReal) <=
          4 * Q ^ 2 + 4 * Q ^ 2 := by
        apply add_le_add hOne
        simpa only [pow_two] using hnSq
      _ = 8 * Q ^ 2 := by ring
  simpa only [katzTaoDoubledFiberNatCap_eq_samplingMultiplicity,
    katzTaoDoubledParentsNatCap_eq_samplingMultiplicity, Nat.cast_add,
    Nat.cast_one, Nat.cast_mul, n, Q] using hfinal

/-- Any scale-power estimate for the literal incidence ratio immediately
gives the exact doubled-parent degree estimate.  This is the mechanical seam
used when the radius is later identified with the long-interval scale. -/
theorem exactConflictDegree_coe_le_of_ratio_power
    {delta radius : NNReal} {A K : ENNReal} {power : Real}
    (hratioOne :
      1 <= activeOwnerKatzTaoIncidenceRatio delta radius A)
    (hratioFinite :
      activeOwnerKatzTaoIncidenceRatio delta radius A ≠ ∞)
    (hratioPower :
      activeOwnerKatzTaoIncidenceRatio delta radius A <=
        K * (delta : ENNReal) ^ (-power)) :
    ((1 +
        katzTaoDoubledFiberNatCap delta radius A *
          katzTaoDoubledParentsNatCap delta radius A : Nat) : ENNReal) <=
      8 * (K * (delta : ENNReal) ^ (-power)) ^ 2 := by
  calc
    ((1 +
        katzTaoDoubledFiberNatCap delta radius A *
          katzTaoDoubledParentsNatCap delta radius A : Nat) : ENNReal) <=
        8 * (activeOwnerKatzTaoIncidenceRatio delta radius A) ^ 2 :=
      exactConflictDegree_coe_le_eight_mul_ratio_sq
        hratioOne hratioFinite
    _ <= 8 * (K * (delta : ENNReal) ^ (-power)) ^ 2 := by
      gcongr

#print axioms exactConflictDegree_coe_le_eight_mul_ratio_sq
#print axioms exactConflictDegree_coe_le_of_ratio_power

end
end Family8PaperConflictOwnerActiveOwnerExactDegreeNumericsV4
